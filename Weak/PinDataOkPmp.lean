/-
Weak: **`dataOkR` (3a) — the PMP stage passes under `dkB`** (xv6's PMP tables after `start()`:
entry 0 TOR over [0, 2^56), R/W/X; the loop's first iteration matches; `PROGRESS-dataOk.md`).
Lean-only.  Every helper is `Weak.PinDataOk.*`.
-/
import Weak.PinDataOk
import MachCSL.WpPmpXv6

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Functions
open Sail.ArchSem (FreeM)

namespace PinDataOk
open SailCycleOrderK

variable {c : DCfg}

/-- xv6's entry 0 matches every access below 2^56 (TOR, `start()`'s tables). -/
theorem pmpMatchXv6 (addr : BitVec 64) (width : Nat) (hram : pmpOk addr width) :
    pmpMatchAddr (.Physaddr addr) (to_bits (l := 64) width) 0x0f#8 0x3fffffffffffff#64 zeros =
      pure .PMP_Match := by
  unfold pmpMatchAddr
  have hA : pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A 0x0f#8) = .TOR := rfl
  have hz : zopz0zKzJ_u (zeros (n := 64)) 0x3fffffffffffff#64 = false := by decide
  simp only [hA, hz, Bool.false_eq_true, ↓reduceIte]
  exact congrArg _ (pmpRangeMatch_xv6' addr width hram)

/-- Entry 0's address register, under the filter. -/
theorem dkPmpReadAddrReg0 : dkB c (fun a => a = 0x3fffffffffffff#64) (pmpReadAddrReg 0) := by
  unfold pmpReadAddrReg
  simp only [bind_assoc, pure_bind]
  refine dkReadReg _ _ (fun v hv => ?_)
  have hv' : v = xv6Pmpcfg := hv.2.2.2.2.2.2.2.1 rfl
  subst hv'
  refine dkReadReg _ _ (fun v hv => ?_)
  have hv' : v = xv6Pmpaddr := hv.2.2.2.2.2.2.2.2.1 rfl
  subst hv'
  rw [xv6Pmpcfg_getNat0]
  split
  · rename_i h; exact absurd h (by decide)
  · rw [if_neg (by decide)]
    exact xv6Pmpaddr_getNat0
  · exact xv6Pmpaddr_getNat0

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
theorem dkPmpCheck (addr : BitVec 64) (width : Nat) (acc : MemoryAccessType mem_payload)
    (priv : Privilege) (hram : pmpOk addr width) (hrwx : pmpCheckRWX 0x0f#8 acc = pure true) :
    dkB c (fun r => r = none) (pmpCheck (.Physaddr addr) width acc priv) := by
  unfold pmpCheck
  simp only [SailME.run, PreSail.PreSailME.run]
  have h64 : (sys_pmp_count == 0) = false := by decide
  simp only [h64, Bool.false_eq_true, ↓reduceIte, ForIn.forIn, ForIn'.forIn',
    MachCSL.IntRange.forIn'_eq]
  rw [MachCSL.IntRange.loop_unfold]
  have hmem : (0 : Int) ∈ ({ stop := sys_pmp_count - 1, step_pos := by decide } : IntRange) := by
    simp only [Membership.mem]; decide
  rw [dif_pos hmem]
  simp only [ExceptT.run_bind, run_liftM, bind_assoc, pure_bind, show ((0 : Int) >b 0) = false from rfl,
    Bool.false_eq_true, ↓reduceIte]
  refine dkReadReg _ _ (fun v hv => ?_)
  have hv' : v = xv6Pmpcfg := hv.2.2.2.2.2.2.2.1 rfl
  subst hv'
  have hc0 : xv6Pmpcfg[(0 : Int)]! = 0x0f#8 := xv6Pmpcfg_getNat0
  simp only [hc0, show Int.toNat 0 = 0 from rfl]
  refine dkBind _ _ _ _ dkPmpReadAddrReg0 (fun a ha => ?_)
  subst ha
  rw [pmpMatchXv6 addr width hram, pure_bind]
  simp only [ExceptT.run_bind, run_liftM, bind_assoc, pure_bind, hrwx, Bool.true_or, ↓reduceIte,
    run_SailME_throw]
  rfl

set_option maxHeartbeats 40000000 in
/-- An aligned access passes the misaligned-access gate. -/
theorem dkMagAligned (pma : PMA) (acc : MemoryAccessType mem_payload) (pa : physaddr) (w : Nat)
    (hal : is_aligned_paddr pa w = true) :
    dkB c (fun r => ∀ e, r ≠ .Err e) (mag_pma_check pma acc pa w) := by
  unfold mag_pma_check
  refine dkXfT _ _ (PinFetchPaFp.xfIsMagApplicableAccess _ _) (fun b => ?_)
  simp only [hal, Bool.true_or, ↓reduceIte]
  intro e h; cases h

/-- The kernel's accesses the PMA stage admits on RAM. -/
def pmaKind (acc : MemoryAccessType mem_payload) (rc : Bool) : Prop :=
  (acc = .Load .Data ∧ rc = false) ∨ (acc = .Store .Data ∧ rc = false) ∨
  acc = .Load .PageTableEntry ∨ acc = .Store .PageTableEntry

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
/-- **The PMA stage passes** at an aligned RAM access of the kernel's kinds. -/
theorem dkPmaCheckRam (pa : BitVec 64) (w : Nat) (acc : MemoryAccessType mem_payload) (rc : Bool)
    (hk : pmaKind acc rc) (hram : inRam pa w) (hw : 0 < w) (hw' : w ≤ 16)
    (hal : is_aligned_paddr (.Physaddr pa) w = true) :
    dkB c (fun r => ∀ e, r ≠ .Err e) (pmaCheck (.Physaddr pa) w acc .PBMT_PMA rc) := by
  unfold pmaCheck
  simp only [SailME.run, PreSail.PreSailME.run, ExceptT.run_bind, run_liftM, bind_assoc, pure_bind]
  refine dkReadReg _ _ (fun v hv => ?_)
  have hv' : v = bootPMA := hv.1
  subst hv'
  rw [matching_pma_ram pa w hram hw hw']
  have hrd0 : ramRegion.attributes.readable = true := by decide
  have hwr0 : ramRegion.attributes.writable = true := by decide
  have hpr0 : ramRegion.attributes.supports_pte_read = true := by decide
  have hpw0 : ramRegion.attributes.supports_pte_write = true := by decide
  rcases hR : ramRegion with ⟨base, size, attrs, incl⟩
  rw [hR] at hrd0 hwr0 hpr0 hpw0
  have hrd : attrs.readable = true := hrd0
  have hwr : attrs.writable = true := hwr0
  have hpr : attrs.supports_pte_read = true := hpr0
  have hpw : attrs.supports_pte_write = true := hpw0
  simp only [ExceptT.run_pure, pure_bind, override_PMA]
  rcases hk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | rfl | rfl <;>
  simp only [ExceptT.run_bind, run_liftM, bind_assoc, pure_bind, hrd, hwr, hpr, hpw,
    Functions.not, Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte, ExceptT.run_pure]
  all_goals
    try (refine dkXfT (assert true _) _ (by xf_walk) (fun _ => ?_))
    refine dkBind _ _ _ _ (dkMagAligned _ _ _ _ hal) (fun x hx => ?_)
    match x with
    | .Ok (sp, g) => intro e h; cases h
    | .Err e => exact absurd rfl (hx e)

set_option maxHeartbeats 40000000 in
@[xf_reg] theorem PinDataOk.xfAssertTrue (msg : String) : PinFetchPaFp.xfT (assert true msg) := by
  xf_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
/-- **`checked_mem_read` of a data load / PTE load passes** at an aligned RAM address (`Ok` only). -/
theorem dkCheckedMemReadOk (pa : BitVec 64) (w : Nat) (acc : MemoryAccessType mem_payload)
    (res : Bool) (hacc : (acc = .Load .Data ∧ res = false) ∨ acc = .Load .PageTableEntry)
    (hram : inRam pa w) (hw : 0 < w) (hw' : w ≤ 8) (hal : pa.toNat % w = 0) (priv : Privilege) :
    dkB c (fun r => ∀ e, r ≠ .Err e)
      (checked_mem_read acc .PBMT_PMA priv (.Physaddr pa) w false false res false) := by
  have hal' : is_aligned_paddr (.Physaddr pa) w = true := by
    simp only [is_aligned_paddr, BitVec.toNatInt, beq_iff_eq]
    rw [Int.ofNat_eq_natCast, ← Int.ofNat_tmod, hal]; rfl
  have hk : pmaKind acc res := by
    rcases hacc with ⟨rfl, rfl⟩ | rfl
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr (Or.inr (Or.inl rfl))
  have hrwx : pmpCheckRWX 0x0f#8 acc = pure true := by rcases hacc with ⟨rfl, -⟩ | rfl <;> rfl
  have hpo : pmpOk pa w := by
    simp only [inRam, ramBase, ramEnd] at hram; unfold pmpOk; omega
  rcases hacc with ⟨rfl, rfl⟩ | rfl
  all_goals (try cases res)
  all_goals
    simp only [checked_mem_read, SailME.run, PreSail.PreSailME.run, ExceptT.run_bind, run_liftM,
      bind_assoc, pure_bind, ExceptT.run_pure, check_pma_with_pmp_priority, read_kind_of_flags] <;>
    refine dkBind _ _ _ _ (dkPmaCheckRam pa w _ _ hk hram hw (by omega) hal') (fun r hr => ?_) <;>
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
      refine dkXfT _ _ (by xf_walk) (fun _ => ?_)
      have hc : (Int.toNat 0 == (1 - 1 : Int).toNat) = true := by decide
      simp only [hc, ↓reduceIte, ExceptT.run_pure, pure_bind]
      intro e h; cases h

end PinDataOk
end Weak
