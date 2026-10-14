/-
Weak: **`dataOkR` (3j) — `vmem_read` / `vmem_write` of a walk access under `dkB`**: the base
register's value plus the offset (no pointer masking: `menvcfgS.PMM = 0`), aligned, in-page, the
translation and the physical access answer `Ok` — NO data-access exception
(`VmemUtils.lean:200-460`; `PROGRESS-dataOk.md`).  Lean-only.  Every helper is `Weak.PinDataOk.*`.
-/
import Weak.PinDataOkAddr

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Functions
open Sail.ArchSem (FreeM)

namespace PinDataOk
open SailCycleOrderK PinFetchPaFp

variable {c : DCfg}

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
/-- No pointer masking in supervisor mode under `menvcfgS`. -/
theorem dkGetPmlenS (acc : MemoryAccessType mem_payload) :
    dkB c (fun l => l = 0) (get_pmlen acc .Supervisor) := by
  unfold get_pmlen
  refine dkXfBind (fun _ => True) _ _ _ (by unfold is_pmm_applicable; xf_walk) (fun b _ => ?_)
  split
  · unfold get_pmm
    simp only [bind_assoc]
    refine dkReadReg _ _ (fun v hv => ?_)
    have hv' := dGMenvcfg hv
    subst hv'
    have h : pmm_mode_backwards (_get_MEnvcfg_PMM menvcfgS) = .PMM_Disabled := rfl
    simp only [h, pure_bind]
    rfl
  · rfl

/-- No masking: the address unchanged. -/
theorem pmTransformVA0 (x : BitVec 64) : pm_transform_VA (.Virtaddr x) 0 = .Virtaddr x := by
  simp only [pm_transform_VA]
  reduce_closed_widths
  simp only [sign_extend, Sail.BitVec.signExtend, Sail.BitVec.extractLsb]
  congr 1
  generalize x = y
  bv_decide

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
/-- `transform_effective_address` of a data access: the address unchanged. -/
theorem dkTransformEA (va : BitVec 64) (acc : MemoryAccessType mem_payload) (hk : dAccKind acc c.perm) :
    dkB c (fun v => v = .Virtaddr va) (transform_effective_address (.Virtaddr va) acc) := by
  unfold transform_effective_address
  try simp only [bind_assoc]
  refine dkReadReg _ _ (fun m hm => ?_)
  refine dkReadReg _ _ (fun p hp => ?_)
  have hp' := dGPriv hp
  subst hp'
  rw [effPrivData acc c.perm hk m (dGMstatus hm), pure_bind]
  refine dkBind _ _ _ _ (dkGetPmlenS acc) (fun l hl => ?_)
  subst hl
  refine dkBind _ _ _ _ dkTranslationModeS (fun mode hmode => ?_)
  subst hmode
  have hb : (SATPMode.Sv39 == SATPMode.Bare) = false := rfl
  simp only [hb, Bool.false_eq_true, ↓reduceIte]
  exact pmTransformVA0 va

/-- The widths of a walk access. -/
def accW (w : Nat) : Prop := w = 1 ∨ w = 2 ∨ w = 4 ∨ w = 8

/-- The physical address the leaf gives: the page and the offset. -/
theorem dPaToNat (c : DCfg) (va : BitVec 64) : (dPa c va).toNat = c.ppn.toNat * 4096 + va.toNat % 4096 := by
  simp only [dPa, zero_extend, Sail.BitVec.zeroExtend, Sail.BitVec.extractLsb, BitVec.toNat_setWidth,
    BitVec.toNat_append, BitVec.extractLsb_toNat]
  simp only [Nat.shiftRight_zero, Nat.sub_zero, Nat.reduceAdd, Nat.reducePow]
  rw [← Nat.shiftLeft_add_eq_or_of_lt (Nat.mod_lt _ (by decide)), Nat.shiftLeft_eq]
  have := c.ppn.isLt
  have := Nat.mod_lt va.toNat (show 4096 > 0 by decide)
  omega

/-- The leaf's physical address is an aligned RAM access. -/
theorem dPaRam (c : DCfg) (hr : c.ram) (va : BitVec 64) (w : Nat) (hw : accW w) (hal : va.toNat % w = 0) :
    inRam (dPa c va) w ∧ (dPa c va).toNat % w = 0 := by
  obtain ⟨-, -, -, h1, h2⟩ := hr
  simp only [inRam, ramBase, ramEnd, dPaToNat]
  rcases hw with rfl | rfl | rfl | rfl <;> omega

/-- The page mask. -/
theorem pageMaskEq :
    (~~~(BitVec.zeroExtend 64 (BitVec.allOnes (11 - 0 + 1)) <<< 0) &&& sail_ones 64 |||
      BitVec.zeroExtend 64 (BitVec.zero 12) <<< 0 : BitVec 64) = 0xFFFFFFFFFFFFF000#64 := by
  decide

theorem pageEq1 (x : BitVec 64) : (x &&& 0xFFFFFFFFFFFFF000#64) = ((x + 1#64 - 1#64) &&& 0xFFFFFFFFFFFFF000#64) := by
  bv_decide
theorem pageEq2 (x : BitVec 64) (h : x % 2#64 = 0#64) :
    (x &&& 0xFFFFFFFFFFFFF000#64) = ((x + 2#64 - 1#64) &&& 0xFFFFFFFFFFFFF000#64) := by
  revert h; bv_decide
theorem pageEq4 (x : BitVec 64) (h : x % 4#64 = 0#64) :
    (x &&& 0xFFFFFFFFFFFFF000#64) = ((x + 4#64 - 1#64) &&& 0xFFFFFFFFFFFFF000#64) := by
  revert h; bv_decide
theorem pageEq8 (x : BitVec 64) (h : x % 8#64 = 0#64) :
    (x &&& 0xFFFFFFFFFFFFF000#64) = ((x + 8#64 - 1#64) &&& 0xFFFFFFFFFFFFF000#64) := by
  revert h; bv_decide

set_option maxHeartbeats 40000000 in
/-- An aligned walk access stays in its page. -/
theorem splitPageAligned (va : BitVec 64) (w : Nat) (hw : accW w) (hal : va.toNat % w = 0) :
    split_on_page_boundary va w = pure ((w : Int), 0) := by
  unfold split_on_page_boundary
  reduce_closed_widths
  rw [if_pos]
  simp only [Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange', ones, zeros, BitVec.addInt, BitVec.subInt,
    beq_iff_eq, Sail.BitVec.length]
  rw [pageMaskEq]
  have hw8 : w ≤ 8 := by rcases hw with rfl | rfl | rfl | rfl <;> decide
  have hb : va % BitVec.ofNat 64 w = 0#64 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_umod, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega : w < 2 ^ 64), hal]
  rcases hw with rfl | rfl | rfl | rfl
  · exact pageEq1 va
  · exact pageEq2 va hb
  · exact pageEq4 va hb
  · exact pageEq8 va hb

set_option maxHeartbeats 40000000 in
/-- `mem_read` of a data load at an aligned RAM address never answers `Err`. -/
theorem dkMemReadData (pa : BitVec 64) (w : Nat) (hram : inRam pa w) (hw : accW w) (hal : pa.toNat % w = 0) :
    dkB c (fun r => ∀ e, r ≠ .Err e) (mem_read (.Load .Data) .PBMT_PMA (.Physaddr pa) w false false false) := by
  have hw0 : 0 < w ∧ w ≤ 8 := by rcases hw with rfl | rfl | rfl | rfl <;> decide
  simp only [mem_read, mem_read_priv, mem_read_priv_meta, bind_assoc]
  refine dkReadReg _ _ (fun _ _ => ?_)
  refine dkReadReg _ _ (fun _ _ => ?_)
  refine dkXfT _ _ (xfEffectivePrivilege _ _ _) (fun priv => ?_)
  refine dkBind _ _ _ _ (dkCheckedMemReadOk pa w _ false (Or.inl ⟨rfl, rfl⟩) hram hw0.1 hw0.2 hal priv)
    (fun r hr => ?_)
  intro e he
  cases r with
  | Ok q => obtain ⟨d, m⟩ := q; simp [MemoryOpResult_drop_meta] at he
  | Err e' => exact hr e' rfl

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
/-- `translate_and_read_value` of a walk load: never `Err`. -/
theorem dkTranslateAndReadValue (c : DCfg) (hr : c.ram) (va : BitVec 64) (hva : va.toNat < 2 ^ 38)
    (hv : c.vpn = vpnOf va) (w : Nat) (hw : accW w) (hal : va.toNat % w = 0) :
    dkB c (fun r => ∀ e, r ≠ .Err e)
      (translate_and_read_value (.Virtaddr va) w (.Load .Data) false false false) := by
  unfold translate_and_read_value
  refine dkBind _ _ _ _ (dkTranslateAddrData c hr va hva hv _ (Or.inl rfl)) (fun r ht => ?_)
  obtain ⟨e, rfl⟩ := ht
  simp only []
  obtain ⟨hram, hal2⟩ := dPaRam c hr va w hw hal
  refine dkBind _ _ _ _ (dkMemReadData _ w hram hw hal2) (fun r2 h2 => ?_)
  match r2 with
  | .Err e' => exact absurd rfl (h2 e')
  | .Ok v => intro e h; cases h

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
/-- **`vmem_read_addr` of a walk load: no exception.** -/
theorem dkVmemReadAddr (c : DCfg) (hr : c.ram) (va : BitVec 64) (hva : va.toNat < 2 ^ 38)
    (hv : c.vpn = vpnOf va) (w : Nat) (hw : accW w) (hal : va.toNat % w = 0) :
    dkB c (fun r => ∀ e, r ≠ .Err e) (vmem_read_addr (.Virtaddr va) w (.Load .Data) false false false) := by
  have hk : dAccKind (.Load .Data) c.perm := Or.inl rfl
  have hal' : is_aligned_vaddr (.Virtaddr va) w = true := by
    simp only [is_aligned_vaddr, BitVec.toNatInt, beq_iff_eq]
    rw [Int.ofNat_eq_natCast, ← Int.ofNat_tmod, hal]; rfl
  unfold vmem_read_addr
  simp only [SailME.run, PreSail.PreSailME.run, ExceptT.run_bind, run_liftM, bind_assoc, pure_bind, hal',
    Functions.not, Bool.not_true, Bool.false_eq_true, ↓reduceIte, ExceptT.run_pure]
  rw [show bits_of_virtaddr (virtaddr.Virtaddr va) = va from rfl, splitPageAligned va w hw hal, pure_bind]
  refine dkReadReg _ _ (fun m hm => ?_)
  refine dkReadReg _ _ (fun p hp => ?_)
  have hp' := dGPriv hp
  subst hp'
  rw [effPrivData _ c.perm hk m (dGMstatus hm), pure_bind]
  refine dkBind _ _ _ _ dkTranslationModeS (fun mode hmode => ?_)
  subst hmode
  have h0 : ((0 : Int) >b 0) = false := rfl
  have ew : Int.toNat (w : Int) = w := Int.toNat_natCast w
  simp only [h0, Bool.and_false, Bool.false_eq_true, ↓reduceIte, ExceptT.run_pure, pure_bind, ite_self]
  simp only [ew, bind_assoc]
  refine dkBind _ _ _ _ (dkTranslateAndReadValue c hr va hva hv w hw hal) (fun r ht => ?_)
  match r with
  | .Err e' => exact absurd rfl (ht e')
  | .Ok (pa, v) =>
    simp only [ExceptT.run_pure, pure_bind, Bool.false_eq_true, ↓reduceIte]
    intro e h; cases h

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
/-- **The base register's read** (`rX_bits`) answers the configuration's value. -/
theorem dkRXBits (i : BitVec 5) (hi : i.toNat = c.base) (h0 : c.base ≠ 0) :
    dkB c (fun v => v = c.bval) (rX_bits (.Regidx i)) := by
  unfold rX_bits rX
  have hlt := i.isLt
  have hc : i.toNat = 1 ∨ i.toNat = 2 ∨ i.toNat = 3 ∨ i.toNat = 4 ∨ i.toNat = 5 ∨ i.toNat = 6 ∨ i.toNat = 7 ∨ i.toNat = 8 ∨ i.toNat = 9 ∨ i.toNat = 10 ∨ i.toNat = 11 ∨ i.toNat = 12 ∨ i.toNat = 13 ∨ i.toNat = 14 ∨ i.toNat = 15 ∨ i.toNat = 16 ∨ i.toNat = 17 ∨ i.toNat = 18 ∨ i.toNat = 19 ∨ i.toNat = 20 ∨ i.toNat = 21 ∨ i.toNat = 22 ∨ i.toNat = 23 ∨ i.toNat = 24 ∨ i.toNat = 25 ∨ i.toNat = 26 ∨ i.toNat = 27 ∨ i.toNat = 28 ∨ i.toNat = 29 ∨ i.toNat = 30 ∨ i.toNat = 31 := by omega
  rcases hc with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
  · have hn : (BitVec.toNatInt i).toNat = i.toNat := by simp [BitVec.toNatInt]
    simp only []
    reduce_closed_widths
    generalize hg : (BitVec.toNatInt i).toNat = n
    have hk : n = i.toNat := hg ▸ hn
    rw [h] at hk
    subst hk
    simp only [bind_assoc, pure_bind]
    intro v hv
    exact hv.2.2.2.2.2.2.2.2.2 rfl (by rw [← hi, h]; rfl)

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
/-- **`vmem_read` of a walk load: NO EXCEPTION.** -/
theorem dkVmemRead (c : DCfg) (hr : c.ram) (rs : regidx) (imm : BitVec 12) (w : Nat) (hw : accW w)
    (hbase : (uxaIdx rs).toNat = c.base) (h0 : c.base ≠ 0) (hva : (c.va imm).toNat < 2 ^ 38)
    (hv : c.vpn = vpnOf (c.va imm)) (hal : (c.va imm).toNat % w = 0) :
    dkB c (fun r => ∀ e, r ≠ .Err e) (vmem_read rs (sign_extend (m := 64) imm) w (.Load .Data) false false false) := by
  obtain ⟨i⟩ := rs
  unfold vmem_read get_transformed_data_addr ext_data_get_addr
  simp only [SailME.run, PreSail.PreSailME.run, ExceptT.run_bind, run_liftM, bind_assoc, pure_bind]
  refine dkBind _ _ _ _ (dkRXBits i hbase h0) (fun v hv' => ?_)
  subst hv'
  try simp only [pure_bind]
  refine dkBind _ _ _ _ (dkTransformEA (c.va imm) _ (Or.inl rfl)) (fun x hx => ?_)
  subst hx
  try simp only [pure_bind, ExceptT.run_pure]
  simp only [bind_assoc, pure_bind]
  exact dkBind _ _ _ _ (dkVmemReadAddr c hr _ hva hv w hw hal) (fun r h => h)

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
/-- **`vmem_write_addr` of a walk store: no exception.** -/
theorem dkVmemWriteAddr (c : DCfg) (hr : c.ram) (hp : c.perm = .rw) (va : BitVec 64) (hva : va.toNat < 2 ^ 38)
    (hv : c.vpn = vpnOf va) (w : Nat) (hw : accW w) (hal : va.toNat % w = 0) (data : BitVec (8 * w)) :
    dkB c (fun r => ∀ e, r ≠ .Err e) (vmem_write_addr (.Virtaddr va) w data (.Store .Data) false false false) := by
  have hk : dAccKind (.Store .Data) c.perm := Or.inr ⟨rfl, hp⟩
  have hal' : is_aligned_vaddr (.Virtaddr va) w = true := by
    simp only [is_aligned_vaddr, BitVec.toNatInt, beq_iff_eq]
    rw [Int.ofNat_eq_natCast, ← Int.ofNat_tmod, hal]; rfl
  unfold vmem_write_addr
  simp only [SailME.run, PreSail.PreSailME.run, ExceptT.run_bind, run_liftM, bind_assoc, pure_bind, hal',
    Functions.not, Bool.not_true, Bool.false_eq_true, ↓reduceIte, ExceptT.run_pure]
  rw [show bits_of_virtaddr (virtaddr.Virtaddr va) = va from rfl, splitPageAligned va w hw hal, pure_bind]
  refine dkReadReg _ _ (fun m hm => ?_)
  refine dkReadReg _ _ (fun p hp' => ?_)
  have hp'' := dGPriv hp'
  subst hp''
  rw [effPrivData _ c.perm hk m (dGMstatus hm), pure_bind]
  refine dkBind _ _ _ _ dkTranslationModeS (fun mode hmode => ?_)
  subst hmode
  have h0 : ((0 : Int) >b 0) = false := rfl
  have ew : Int.toNat (w : Int) = w := Int.toNat_natCast w
  simp only [h0, Bool.and_false, Bool.false_eq_true, ↓reduceIte, ExceptT.run_pure, pure_bind, ite_self]
  simp only [ew, bind_assoc]
  refine dkBind _ _ _ _ (dkTranslateAddrData c hr va hva hv _ hk) (fun r ht => ?_)
  obtain ⟨e, rfl⟩ := ht
  obtain ⟨hram, hal2⟩ := dPaRam c hr va w hw hal
  have hw0 : 0 < w ∧ w ≤ 8 := by rcases hw with rfl | rfl | rfl | rfl <;> decide
  have hsc : (false == is_store_conditional (MemoryAccessType.Store mem_payload.Data)) = true := rfl
  simp only [hsc, Bool.false_and, Bool.false_eq_true, ↓reduceIte, ExceptT.run_bind, run_liftM, bind_assoc,
    pure_bind, ite_self, ew]
  refine dkXfT _ _ (PinDataOk.xfAssertTrue _) (fun _ => ?_)
  refine dkBind _ _ _ _ (dkMemWriteEaOk _ w _ false (Or.inl ⟨rfl, rfl⟩) hram hw0.1 hw0.2 hal2) (fun r h => ?_)
  match r with
  | .Err e' => exact absurd rfl (h e')
  | .Ok () =>
    simp only [ExceptT.run_bind, run_liftM, bind_assoc, pure_bind]
    refine dkBind _ _ _ _ (dkMemWriteValue _ w _ hram hw0.1 hw0.2 hal2) (fun r2 h2 => ?_)
    subst h2
    simp only [ExceptT.run_pure, pure_bind]
    intro e h; cases h

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
/-- **`vmem_write` of a walk store: NO EXCEPTION.** -/
theorem dkVmemWrite (c : DCfg) (hr : c.ram) (hp : c.perm = .rw) (rs : regidx) (imm : BitVec 12) (w : Nat)
    (hw : accW w) (hbase : (uxaIdx rs).toNat = c.base) (h0 : c.base ≠ 0) (hva : (c.va imm).toNat < 2 ^ 38)
    (hv : c.vpn = vpnOf (c.va imm)) (hal : (c.va imm).toNat % w = 0) (data : BitVec (8 * w)) :
    dkB c (fun r => ∀ e, r ≠ .Err e)
      (vmem_write rs (sign_extend (m := 64) imm) w data (.Store .Data) false false false) := by
  obtain ⟨i⟩ := rs
  unfold vmem_write get_transformed_data_addr ext_data_get_addr
  simp only [SailME.run, PreSail.PreSailME.run, ExceptT.run_bind, run_liftM, bind_assoc, pure_bind]
  refine dkBind _ _ _ _ (dkRXBits i hbase h0) (fun v hv' => ?_)
  subst hv'
  try simp only [pure_bind]
  refine dkBind _ _ _ _ (dkTransformEA (c.va imm) _ (Or.inr ⟨rfl, hp⟩)) (fun x hx => ?_)
  subst hx
  try simp only [pure_bind, ExceptT.run_pure]
  simp only [bind_assoc, pure_bind]
  exact dkBind _ _ _ _ (dkVmemWriteAddr c hr hp _ hva hv w hw hal data) (fun r h => h)

end PinDataOk
end Weak
