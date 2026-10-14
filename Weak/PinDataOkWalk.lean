/-
Weak: **`dataOkR` (3f) — the Sv39 walk of a data access under `dkB`**: the leaf checks of a kernel
leaf that allows the access pass (`pte_is_invalid` false, `check_PTE_permission` success, the plain
memory type under `menvcfg = menvcfgS`), the three-level walk answers `Ok` with the leaf's page at
level 0 (`PROGRESS-dataOk.md`).  Mirrors `Weak/PinFetchPaWalk.lean`.  Lean-only.  Every helper is
`Weak.PinDataOk.*`.
-/
import Weak.PinDataOkWr
import Weak.PinFetchPaWalk

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Functions
open Sail.ArchSem (FreeM)

namespace PinDataOk
open SailCycleOrderK PinFetchPaFp

variable {c : DCfg}

set_option maxHeartbeats 40000000 in
/-- A kernel leaf is valid (a closed computation). -/
theorem pteInvalidKLeaf (ppn : BitVec 44) (perm : KPerm) (a d : BitVec 1) :
    pte_is_invalid (Mk_PTE_Flags (Sail.BitVec.extractLsb (kLeaf ppn perm a d) 7 0))
      (ext_bits_of_PTE (kLeaf ppn perm a d)) = pure false := by
  rw [flags_of_kLeaf, ext_of_kLeaf]
  cases perm <;> rcases bv1_cases a with rfl | rfl <;> rcases bv1_cases d with rfl | rfl <;> rfl

set_option maxHeartbeats 40000000 in
/-- A pointer entry is valid. -/
theorem pteInvalidKPtr (b : BitVec 44) :
    pte_is_invalid (Mk_PTE_Flags (Sail.BitVec.extractLsb (kPtr b) 7 0)) (ext_bits_of_PTE (kPtr b)) =
      pure false := by
  rw [flags_of_kPtr, ext_of_kPtr]
  rfl

/-- The data accesses of a walk load/store. -/
def dAccKind (acc : MemoryAccessType mem_payload) (perm : KPerm) : Prop :=
  acc = .Load .Data ∨ (acc = .Store .Data ∧ perm = .rw)

set_option maxHeartbeats 40000000 in
/-- The permission check passes on a kernel leaf allowing the data access, in supervisor mode. -/
theorem checkPermKLeaf (acc : MemoryAccessType mem_payload) (perm : KPerm) (hk : dAccKind acc perm)
    (mxr sum : Bool) (ppn : BitVec 44) (a d : BitVec 1) (e : BitVec 10) (u : Unit) :
    check_PTE_permission acc .Supervisor mxr sum (Mk_PTE_Flags (Sail.BitVec.extractLsb (kLeaf ppn perm a d) 7 0))
      e u = pure (.PTE_Check_Success ()) := by
  rw [flags_of_kLeaf]
  rcases hk with rfl | ⟨rfl, rfl⟩
  · cases perm <;> rcases bv1_cases a with rfl | rfl <;> rcases bv1_cases d with rfl | rfl <;>
      cases mxr <;> cases sum <;> rfl
  · rcases bv1_cases a with rfl | rfl <;> rcases bv1_cases d with rfl | rfl <;>
      cases mxr <;> cases sum <;> rfl

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
/-- **The leaf check** of a kernel leaf allowing the data access, at level 0: `Ok` with the leaf's
page and the plain memory type. -/
theorem dkCheckLeafKLeaf0 (vpn : BitVec 27) (acc : MemoryAccessType mem_payload) (perm : KPerm)
    (hk : dAccKind acc perm) (mxr sum : Bool) (ppn : BitVec 44) (a d : BitVec 1) (addr : physaddr)
    (u : Unit) :
    dkB c (fun r => r = .Ok (ppn, .PBMT_PMA, u))
      (check_leaf_pte 39 vpn acc .Supervisor mxr sum (kLeaf ppn perm a d) addr 0 u) := by
  unfold check_leaf_pte
  simp only [SailME.run, PreSail.PreSailME.run, ExceptT.run_bind, run_liftM, bind_assoc, pure_bind]
  reduce_closed_widths
  have hnl : pte_is_non_leaf (Mk_PTE_Flags (Sail.BitVec.extractLsb (kLeaf ppn perm a d) 7 0)) = false := by
    rw [flags_of_kLeaf]; exact nonLeaf_kLeaf perm a d
  have hN : (_get_PTE_Ext_N (ext_bits_of_PTE (kLeaf ppn perm a d)) == 1#1) = false := by
    rw [ext_of_kLeaf]; decide
  have h00 : ((0 : Nat) >b 0) = false := rfl
  simp only [pteInvalidKLeaf, checkPermKLeaf acc perm hk, hnl, hN, Bool.and_false,
    Bool.false_eq_true, ↓reduceIte, pure_bind, ExceptT.run_bind, run_liftM, bind_assoc]
  refine dkXfT _ _ (xfCurrentlyEnabled _) (fun _ => ?_)
  refine dkReadReg _ _ (fun v hv => ?_)
  have hv' : v = menvcfgS := dGMenvcfg hv
  subst hv'
  have hpb : (_get_MEnvcfg_PBMTE menvcfgS == 0#1) = true := by decide
  simp only [hpb, ↓reduceIte, ExceptT.run_pure, pure_bind, ppn_of_kLeaf, BitVec.setWidth_eq]
  rfl

/-- An entry of a RAM page: a RAM, 8-aligned doubleword. -/
theorem slotRam (b : BitVec 44) (i : BitVec 9) (h : ramPage b) :
    0x80000000 ≤ (pteAddr b i).toNat ∧ (pteAddr b i).toNat + 8 ≤ 0x88000000 ∧ (pteAddr b i).toNat % 8 = 0 := by
  rw [KptInv.pteAddr_toNat]
  have := i.isLt
  unfold ramPage at h
  omega

/-- **The data walk's post**: `Ok` with the leaf's page, a variant of the leaf, its slot, level 0,
the plain memory type. -/
def leafOut (c : DCfg) (a d : BitVec 1) (g : Bool) : PTW_Output 39 where
  ppn := c.ppn
  pte := kLeaf c.ppn c.perm a d
  pteAddr := .Physaddr (pteAddr c.b0 (vpnIdx c.vpn 0))
  level := 0
  pbmt := .PBMT_PMA
  global := g

def walkPostD (c : DCfg) (r : Result (PTW_Output 39 × Unit) (PTW_Error × Unit)) : Prop :=
  ∃ (a d : BitVec 1) (g : Bool) (e : Unit), r = .Ok (leafOut c a d g, e)

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
/-- Level 0: the leaf slot of `b0`. -/
theorem dkPtWalk0 (c : DCfg) (hr : c.ram) (acc : MemoryAccessType mem_payload) (hk : dAccKind acc c.perm)
    (mxr sum g : Bool) (u : Unit) :
    dkB c (walkPostD c) (pt_walk 39 c.vpn acc .Supervisor mxr sum c.b0 0 g u) := by
  rw [pt_walk]
  reduce_closed_widths
  refine dkXfT _ _ (by xf_walk) (fun _ => ?_)
  have hA : zero_extend (m := 64) (c.b0 +++ (Sail.BitVec.extractLsb c.vpn 8 0 +++ (zeros (n := 3)))) =
      pteAddr c.b0 (vpnIdx c.vpn 0) := by
    first | rfl | (simp only [pteAddr, vpnIdx, Sail.BitVec.extractLsb, zero_extend]; bv_decide)
  obtain ⟨h1, h2, h3⟩ := slotRam c.b0 (vpnIdx c.vpn 0) hr.2.2.1
  simp only [hA]
  refine dkBind _ _ _ _ (dkReadPte _ h1 h2 h3) (fun r hrd => ?_)
  cases r with
  | Err e => exact absurd rfl (hrd.1 e)
  | Ok w =>
    obtain ⟨a, d, hwv⟩ := ((hrd.2 w rfl) rfl).2.2 rfl
    have hw : w = kLeaf c.ppn c.perm a d := BitVec.eq_of_toNat_eq hwv
    subst hw
    simp only []
    refine dkXfT _ _ (by xf_walk) (fun _ => ?_)
    rw [if_neg (by first | simp | decide), BitVec.setWidth_eq]
    refine dkBind _ _ _ _ (dkCheckLeafKLeaf0 _ _ _ hk _ _ _ _ _ _ _) (fun r hcl => ?_)
    subst hcl
    exact ⟨a, d, _, _, rfl⟩

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
/-- Level 1: the pointer slot of `b1`. -/
theorem dkPtWalk1 (c : DCfg) (hr : c.ram) (acc : MemoryAccessType mem_payload) (hk : dAccKind acc c.perm)
    (mxr sum g : Bool) (u : Unit) :
    dkB c (walkPostD c) (pt_walk 39 c.vpn acc .Supervisor mxr sum c.b1 1 g u) := by
  rw [pt_walk]
  reduce_closed_widths
  refine dkXfT _ _ (by xf_walk) (fun _ => ?_)
  have hA : zero_extend (m := 64) (c.b1 +++ (Sail.BitVec.extractLsb c.vpn 17 9 +++ (zeros (n := 3)))) =
      pteAddr c.b1 (vpnIdx c.vpn 1) := by
    first | rfl | (simp only [pteAddr, vpnIdx, Sail.BitVec.extractLsb, zero_extend]; bv_decide)
  obtain ⟨h1, h2, h3⟩ := slotRam c.b1 (vpnIdx c.vpn 1) hr.2.1
  simp only [hA]
  refine dkBind _ _ _ _ (dkReadPte _ h1 h2 h3) (fun r hrd => ?_)
  cases r with
  | Err e => exact absurd rfl (hrd.1 e)
  | Ok w =>
    have hw : w = kPtr c.b0 := BitVec.eq_of_toNat_eq (((hrd.2 w rfl) rfl).2.1 rfl)
    subst hw
    simp only [pteInvalidKPtr, pure_bind]
    have hc : (Functions.not false && (pte_is_non_leaf (Mk_PTE_Flags (Sail.BitVec.extractLsb (kPtr c.b0) 7 0)) &&
        ((1 : Nat) >b 0))) = true := by
      rw [flags_of_kPtr, nonLeaf_ptr]; rfl
    rw [if_pos hc, ppn_of_kPtr, BitVec.setWidth_eq]
    exact dkPtWalk0 c hr acc hk mxr sum _ u

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
/-- **Level 2: THE DATA WALK** from the root `b`: `Ok` with the leaf's page at level 0. -/
theorem dkPtWalk2 (c : DCfg) (hr : c.ram) (acc : MemoryAccessType mem_payload) (hk : dAccKind acc c.perm)
    (mxr sum g : Bool) (u : Unit) :
    dkB c (walkPostD c) (pt_walk 39 c.vpn acc .Supervisor mxr sum c.b 2 g u) := by
  rw [pt_walk]
  reduce_closed_widths
  refine dkXfT _ _ (by xf_walk) (fun _ => ?_)
  have hA : zero_extend (m := 64) (c.b +++ (Sail.BitVec.extractLsb c.vpn 26 18 +++ (zeros (n := 3)))) =
      pteAddr c.b (vpnIdx c.vpn 2) := by
    first | rfl | (simp only [pteAddr, vpnIdx, Sail.BitVec.extractLsb, zero_extend]; bv_decide)
  obtain ⟨h1, h2, h3⟩ := slotRam c.b (vpnIdx c.vpn 2) hr.1
  simp only [hA]
  refine dkBind _ _ _ _ (dkReadPte _ h1 h2 h3) (fun r hrd => ?_)
  cases r with
  | Err e => exact absurd rfl (hrd.1 e)
  | Ok w =>
    have hw : w = kPtr c.b1 := BitVec.eq_of_toNat_eq (((hrd.2 w rfl) rfl).1 rfl)
    subst hw
    simp only [pteInvalidKPtr, pure_bind]
    have hc : (Functions.not false && (pte_is_non_leaf (Mk_PTE_Flags (Sail.BitVec.extractLsb (kPtr c.b1) 7 0)) &&
        ((2 : Nat) >b 0))) = true := by
      rw [flags_of_kPtr, nonLeaf_ptr]; rfl
    rw [if_pos hc, ppn_of_kPtr, BitVec.setWidth_eq]
    exact dkPtWalk1 c hr acc hk mxr sum _ u

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
/-- **The A/D write-back** of the walk's leaf (at its slot, level 0) never answers `Err`: Svadu is
supported and `menvcfg.ADUE = 1` (`menvcfgS`), the exclusive re-read answers a leaf variant, its
check passes, the conditional write answers `Ok true`. -/
theorem dkUpdateAndWritePte (c : DCfg) (hr : c.ram) (acc : MemoryAccessType mem_payload)
    (hk : dAccKind acc c.perm) (mxr sum : Bool) (pte : BitVec 64) (u : Unit) :
    dkB c (fun r => ∀ e, r ≠ .Err e)
      (update_and_write_pte 39 c.vpn (.Physaddr (pteAddr c.b0 (vpnIdx c.vpn 0))) pte 0 acc .Supervisor mxr sum u) := by
  unfold update_and_write_pte
  reduce_closed_widths
  split
  · intro e h; cases h
  · have hsv : currentlyEnabled extension.Ext_Svadu = pure true := by
      unfold currentlyEnabled
      have : hartSupports .Ext_Svadu = true := by decide +kernel
      rw [this]
    simp only [hsv, pure_bind, ↓reduceIte, bind_assoc]
    refine dkReadReg _ _ (fun v hv => ?_)
    have hv' : v = menvcfgS := dGMenvcfg hv
    subst hv'
    have had : (_get_MEnvcfg_ADUE menvcfgS == 1#1) = true := by decide
    simp only [had, pure_bind, ↓reduceIte, Bool.true_or]
    obtain ⟨h1, h2, h3⟩ := slotRam c.b0 (vpnIdx c.vpn 0) hr.2.2.1
    refine dkBind _ _ _ _ (dkReadPteExclusive _ h1 h2 h3) (fun r hrd => ?_)
    cases r with
    | Err e => exact absurd rfl (hrd.1 e)
    | Ok w =>
      obtain ⟨a, d, hwv⟩ := ((hrd.2 w rfl) rfl).2.2 rfl
      have hw : w = kLeaf c.ppn c.perm a d := BitVec.eq_of_toNat_eq hwv
      subst hw
      simp only [BitVec.setWidth_eq]
      refine dkBind _ _ _ _ (dkCheckLeafKLeaf0 _ _ _ hk _ _ _ _ _ _ _) (fun r hcl => ?_)
      subst hcl
      simp only []
      split
      · intro e h; cases h
      · refine dkBind _ _ _ _ (dkWritePteCond _ ⟨h1, h2⟩ h3 _) (fun r hw => ?_)
        subst hw
        intro e h; cases h

end PinDataOk
end Weak
