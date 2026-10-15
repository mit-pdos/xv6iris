/-
Weak: **r2 glue (ii) — the instruction fetch takes no fault: the `dk` chain at an instruction
fetch** (`PROGRESS-r2glue.md`).  Lean-only.

Under the data-access value predicate `dkB c` at a fetch configuration (`c.perm = .rx`, the walk's
pages and the leaf's page in RAM): the PMA stage of an aligned RAM instruction fetch passes (the
RAM region is executable, `bootPMA`), the PMP stage passes (xv6's entry 0 has `X`), so
`checked_mem_read` / `mem_read` of an instruction fetch never answer `Err`; `fetch_bytes` at an
aligned granule never answers an exception (the translation is `dkTranslateAddrData` at
`InstructionFetch`, `dAccKind`'s third arm).  Spec: Sail `fetch_bytes` (`Fetch.lean:217`),
`pmaCheck` (`Mem.lean:263`), `pmpCheckRWX` (`PmpControl.lean:212`); xv6 `start.c` PMP.  Every helper
is `Weak.PinDataOk.*`.
-/
import Weak.PinDataOkExec

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Functions
open Sail.ArchSem (FreeM)

namespace PinDataOk
open SailCycleOrderK PinCycRun

variable {c : DCfg}

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
/-- **The PMA stage passes** at an aligned RAM instruction fetch. -/
theorem dkPmaCheckRamIF (pa : BitVec 64) (w : Nat) (hram : inRam pa w) (hw : 0 < w) (hw' : w ≤ 16)
    (hal : is_aligned_paddr (.Physaddr pa) w = true) :
    dkB c (fun r => ∀ e, r ≠ .Err e) (pmaCheck (.Physaddr pa) w (.InstructionFetch ()) .PBMT_PMA false) := by
  unfold pmaCheck
  simp only [SailME.run, PreSail.PreSailME.run, ExceptT.run_bind, run_liftM, bind_assoc, pure_bind]
  refine dkReadReg _ _ (fun v hv => ?_)
  have hv' : v = bootPMA := hv.1
  subst hv'
  rw [matching_pma_ram pa w hram hw hw']
  have hex0 : ramRegion.attributes.executable = true := by decide
  rcases hR : ramRegion with ⟨base, size, attrs, incl⟩
  rw [hR] at hex0
  have hex : attrs.executable = true := hex0
  simp only [ExceptT.run_pure, pure_bind, override_PMA]
  simp only [ExceptT.run_bind, run_liftM, bind_assoc, pure_bind, hex,
    Functions.not, Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte, ExceptT.run_pure]
  refine dkBind _ _ _ _ (dkMagAligned _ _ _ _ hal) (fun x hx => ?_)
  match x with
  | .Ok (sp, g) => intro e h; cases h
  | .Err e => exact absurd rfl (hx e)

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
/-- **`checked_mem_read` of an instruction fetch passes** at an aligned RAM address. -/
theorem dkCheckedMemReadIFOk (pa : BitVec 64) (w : Nat) (hram : inRam pa w) (hw : 0 < w) (hw' : w ≤ 8)
    (hal : pa.toNat % w = 0) (priv : Privilege) :
    dkB c (fun r => ∀ e, r ≠ .Err e)
      (checked_mem_read (.InstructionFetch ()) .PBMT_PMA priv (.Physaddr pa) w false false false false) := by
  have hal' : is_aligned_paddr (.Physaddr pa) w = true := by
    simp only [is_aligned_paddr, BitVec.toNatInt, beq_iff_eq]
    rw [Int.ofNat_eq_natCast, ← Int.ofNat_tmod, hal]; rfl
  have hrwx : pmpCheckRWX 0x0f#8 (.InstructionFetch ()) = pure true := rfl
  have hpo : pmpOk pa w := by
    simp only [inRam, ramBase, ramEnd] at hram; unfold pmpOk; omega
  simp only [checked_mem_read, SailME.run, PreSail.PreSailME.run, ExceptT.run_bind, run_liftM,
    bind_assoc, pure_bind, ExceptT.run_pure, check_pma_with_pmp_priority, read_kind_of_flags]
  refine dkBind _ _ _ _ (dkPmaCheckRamIF pa w hram hw (by omega) hal') (fun r hr => ?_)
  cases r with
  | Err e => exact absurd rfl (hr e)
  | Ok info =>
    simp only [ExceptT.run_pure, pure_bind]
    rw [bind_assoc]
    have htm : Int.tmod (BitVec.toNatInt pa) w = 0 := by
      simp only [BitVec.toNatInt]
      rw [Int.ofNat_eq_natCast, ← Int.ofNat_tmod, hal]; rfl
    refine dkXfBind _ _ _ _ (PinFetchPaFp.xfSplitAligned pa w _ _ htm) (fun p hp => ?_)
    subst hp
    simp only [untilFuelM, misaligned_order, sys_misaligned_order_decreasing,
      Bool.false_eq_true, ↓reduceIte]
    rw [show Int.toNat 1 = 0 + 1 from rfl]
    simp only [untilFuelM.go, ExceptT.run_bind, run_liftM, bind_assoc, pure_bind]
    refine dkXfT _ _ (PinDataOk.xfAssertTrue _) (fun _ => ?_)
    have e0 : BitVec.addInt (bits_of_physaddr (physaddr.Physaddr pa)) (↑(Int.toNat 0) * (w : Int)) = pa :=
      SailCycleOrderFp.addInt0 _ _
    have ew : Int.toNat (w : Int) = w := Int.toNat_natCast w
    simp only [e0, ew]
    refine dkBind _ _ _ _ (dkPmpCheck pa w _ priv hpo hrwx) (fun o ho => ?_)
    subst ho
    simp only [ExceptT.run_bind, run_liftM, bind_assoc, pure_bind]
    refine dkXfBind _ _ _ _ (PinFetchPaFp.xfWithinMmioRam (.Physaddr pa) w hram.1) (fun b hb => ?_)
    subst hb
    simp only [Bool.false_eq_true, ↓reduceIte, ExceptT.run_bind, run_liftM, bind_assoc, pure_bind]
    refine dkBind (fun _ => True) _ _ _ (fun w' _ => trivial) (fun _ _ => ?_)
    have hc : (Int.toNat 0 == (1 - 1 : Int).toNat) = true := by decide
    simp only [hc, ↓reduceIte, ExceptT.run_pure, pure_bind]
    intro e h; cases h

set_option maxHeartbeats 40000000 in
/-- `mem_read` of an instruction fetch at an aligned RAM address never answers `Err`. -/
theorem dkMemReadIFOk (pa : BitVec 64) (w : Nat) (hram : inRam pa w) (hw : accW w) (hal : pa.toNat % w = 0) :
    dkB c (fun r => ∀ e, r ≠ .Err e) (mem_read (.InstructionFetch ()) .PBMT_PMA (.Physaddr pa) w false false false) := by
  have hw0 : 0 < w ∧ w ≤ 8 := by rcases hw with rfl | rfl | rfl | rfl <;> decide
  simp only [mem_read, mem_read_priv, mem_read_priv_meta, bind_assoc]
  refine dkReadReg _ _ (fun _ _ => ?_)
  refine dkReadReg _ _ (fun _ _ => ?_)
  refine dkXfT _ _ (PinFetchPaFp.xfEffectivePrivilege _ _ _) (fun priv => ?_)
  refine dkBind _ _ _ _ (dkCheckedMemReadIFOk pa w hram hw0.1 hw0.2 hal priv) (fun r hr => ?_)
  intro e he
  cases r with
  | Ok q => obtain ⟨d, m⟩ := q; simp [MemoryOpResult_drop_meta] at he
  | Err e' => exact hr e' rfl

/-- `fetch_bytes`' answer is no exception (and no extension error). -/
def fbNoExc {w : Nat} (r : FetchBytes_Result w) : Prop :=
  match r with
  | .FetchBytes_Success _ => True
  | _ => False

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
/-- **`fetch_bytes` at an aligned granule of a kernel-text page: no exception.** -/
theorem dkFetchBytesOk (c : DCfg) (hr : c.ram) (hp : c.perm = .rx) (fs gs : BitVec 64) (w : Nat)
    (hw : w = 2 ∨ w = 4) (hva : gs.toNat < 2 ^ 38) (hv : c.vpn = vpnOf gs) (hal : gs.toNat % w = 0) :
    dkB c fbNoExc (fetch_bytes fs gs w) := by
  have hw' : accW w := by rcases hw with rfl | rfl <;> simp [accW]
  simp only [fetch_bytes, ext_fetch_check_pc, SailME.run, PreSail.PreSailME.run, ExceptT.run_bind,
    run_liftM, bind_assoc, pure_bind]
  refine dkBind _ _ _ _ (dkTranslateAddrData c hr gs hva hv _ (Or.inr (Or.inr ⟨rfl, hp⟩)))
    (fun r ht => ?_)
  obtain ⟨e, rfl⟩ := ht
  simp only [ExceptT.run_pure, pure_bind, bind_assoc]
  obtain ⟨hram, hal2⟩ := dPaRam c hr gs w hw' hal
  refine dkBind _ _ _ _ (dkMemReadIFOk _ w hram hw' hal2) (fun r2 h2 => ?_)
  cases r2 with
  | Err q => exact absurd rfl (h2 q)
  | Ok bytes =>
    simp only [ExceptT.run_pure, pure_bind]
    trivial

end PinDataOk
end Weak
