/-
Weak: **W9a (B) B5 r2 part (B) — the Sv39 walk of a kernel-text vpn under `tvB`** (`pt_walk` from
the root `b` at level 2 through `b1`, `b0`: `Ok` only with the identity ppn at level 0; plan rev 52
§D Q-B5-FETCH (r2-a), `PROGRESS-r2.md`).  Lean-only.  Every helper is `Weak.PinFetchPa.*`.
-/
import Weak.PinFetchPaRd
import MachCSL.KptInv
import MachCSL.Tactics

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Functions
open Sail.ArchSem (FreeM)

namespace PinFetchPa
open SailCycleOrderK PinFetchPaFp

set_option maxHeartbeats 40000000 in
/-- `check_leaf_pte` of a kernel leaf at level 0: `Ok` only with the leaf's ppn. -/
theorem xfCheckLeafKLeaf0 (vpn : BitVec 27) (acc : MemoryAccessType mem_payload) (priv : Privilege)
    (mxr sum : Bool) (ppn : BitVec 44) (perm : KPerm) (a d : BitVec 1) (addr : physaddr) (u : Unit) :
    xf (fun r => ∀ p pb e, r = .Ok (p, pb, e) → p = ppn)
      (check_leaf_pte 39 vpn acc priv mxr sum (kLeaf ppn perm a d) addr 0 u) := by
  unfold check_leaf_pte
  xf_walk_v
  all_goals
    rename_i h
    injection h with h
    injection h with h
    first
      | (subst h; simp [ppn_of_kLeaf]; done)
      | (exfalso; simp_all [ext_of_kLeaf, _get_PTE_Ext_N, Sail.BitVec.extractLsb]; done)
      | trace_state

/-- A footprint head with the trivial post. -/
theorem tvXfT {c : TCfg} {X Y : Type} {P : Y → Prop} (m : SailM X) (f : X → SailM Y) (hm : xfT m)
    (hf : ∀ x, tvB c P (f x)) : tvB c P (m >>= f) :=
  tvXfBind _ P m f hm (fun x _ => hf x)

/-- The walk's three pages are RAM pages. -/
def TCfg.ram (c : TCfg) : Prop := 0x80000 ≤ c.b.toNat ∧ 0x80000 ≤ c.b1.toNat ∧ 0x80000 ≤ c.b0.toNat

/-- An entry of a RAM page is a RAM, 8-aligned address. -/
theorem pteAddrRam (b : BitVec 44) (i : BitVec 9) (h : 0x80000 ≤ b.toNat) :
    0x80000000 ≤ (pteAddr b i).toNat ∧ (pteAddr b i).toNat % 8 = 0 := by
  rw [KptInv.pteAddr_toNat]; omega

/-- The walk's post: `Ok` only with the identity ppn, at level 0. -/
def walkPost (c : TCfg) (r : Result (PTW_Output 39 × Unit) (PTW_Error × Unit)) : Prop :=
  ∀ o e, r = .Ok (o, e) → o.ppn = idPpn c.vpn ∧ o.level = 0

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
/-- Level 0: the leaf slot of `b0`. -/
theorem tvPtWalk0 (c : TCfg) (hr : c.ram) (acc : MemoryAccessType mem_payload) (priv : Privilege)
    (mxr sum g : Bool) (u : Unit) :
    tvB c (walkPost c) (pt_walk 39 c.vpn acc priv mxr sum c.b0 0 g u) := by
  rw [pt_walk]
  reduce_closed_widths
  refine tvXfT _ _ (by xf_walk) (fun _ => ?_)
  have hA : zero_extend (m := 64) (c.b0 +++ (Sail.BitVec.extractLsb c.vpn 8 0 +++ (zeros (n := 3)))) =
      pteAddr c.b0 (vpnIdx c.vpn 0) := by
    first | rfl | (simp only [pteAddr, vpnIdx, Sail.BitVec.extractLsb, zero_extend]; bv_decide)
  have hram := pteAddrRam c.b0 (vpnIdx c.vpn 0) hr.2.2
  simp only [hA]
  refine tvBind _ _ _ _ (tvReadPte _ hram.1 hram.2) (fun r hrd => ?_)
  cases r with
  | Err _ => intro o e h; cases h
  | Ok w =>
    obtain ⟨a, d, hwv⟩ := ((hrd w rfl) rfl).2.2 rfl
    have hw : w = kLeaf (idPpn c.vpn) .rx a d := BitVec.eq_of_toNat_eq hwv
    subst hw
    simp only []
    refine tvXfT _ _ (by xf_walk) (fun _ => ?_)
    rw [if_neg (by first | simp | decide), BitVec.setWidth_eq]
    refine tvXfBind _ _ _ _ (xfCheckLeafKLeaf0 _ _ _ _ _ _ _ _ _ _ _) (fun r hcl => ?_)
    match r with
    | .Err _ => intro o e h; cases h
    | .Ok (p, pb, ex) =>
      intro o e h
      injection h with h
      injection h with h
      subst h
      exact ⟨hcl _ _ _ rfl, rfl⟩

set_option maxHeartbeats 40000000 in
/-- `check_leaf_pte` of a pointer entry: never `Ok` (a non-leaf). -/
theorem xfCheckLeafKPtr (vpn : BitVec 27) (acc : MemoryAccessType mem_payload) (priv : Privilege)
    (mxr sum : Bool) (b : BitVec 44) (addr : physaddr) (level : Nat) (u : Unit) :
    xf (fun r => ∀ x, r ≠ .Ok x) (check_leaf_pte 39 vpn acc priv mxr sum (kPtr b) addr level u) := by
  unfold check_leaf_pte
  xf_walk_v
  all_goals first
    | (intro x h; cases h; done)
    | (exfalso; simp_all [flags_of_kPtr, nonLeaf_ptr]; done)
    | trace_state

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
/-- Level 1: the pointer slot of `b1`. -/
theorem tvPtWalk1 (c : TCfg) (hr : c.ram) (acc : MemoryAccessType mem_payload) (priv : Privilege)
    (mxr sum g : Bool) (u : Unit) :
    tvB c (walkPost c) (pt_walk 39 c.vpn acc priv mxr sum c.b1 1 g u) := by
  rw [pt_walk]
  reduce_closed_widths
  refine tvXfT _ _ (by xf_walk) (fun _ => ?_)
  have hA : zero_extend (m := 64) (c.b1 +++ (Sail.BitVec.extractLsb c.vpn 17 9 +++ (zeros (n := 3)))) =
      pteAddr c.b1 (vpnIdx c.vpn 1) := by
    first | rfl | (simp only [pteAddr, vpnIdx, Sail.BitVec.extractLsb, zero_extend]; bv_decide)
  have hram := pteAddrRam c.b1 (vpnIdx c.vpn 1) hr.2.1
  simp only [hA]
  refine tvBind _ _ _ _ (tvReadPte _ hram.1 hram.2) (fun r hrd => ?_)
  cases r with
  | Err _ => intro o e h; cases h
  | Ok w =>
    have hw : w = kPtr c.b0 := BitVec.eq_of_toNat_eq (((hrd w rfl) rfl).2.1 rfl)
    subst hw
    simp only []
    refine tvXfT _ _ (by xf_walk) (fun _ => ?_)
    split
    · rw [ppn_of_kPtr, BitVec.setWidth_eq]
      exact tvPtWalk0 c hr _ _ _ _ _ _
    · rw [BitVec.setWidth_eq]
      refine tvXfBind _ _ _ _ (xfCheckLeafKPtr _ _ _ _ _ _ _ _ _) (fun r hcl => ?_)
      match r with
      | .Err _ => intro o e h; cases h
      | .Ok x => exact absurd rfl (hcl x)

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
/-- **Level 2: THE WALK OF A KERNEL-TEXT VPN** from the root `b`: `Ok` only with the identity
ppn at level 0. -/
theorem tvPtWalk2 (c : TCfg) (hr : c.ram) (acc : MemoryAccessType mem_payload) (priv : Privilege)
    (mxr sum g : Bool) (u : Unit) :
    tvB c (walkPost c) (pt_walk 39 c.vpn acc priv mxr sum c.b 2 g u) := by
  rw [pt_walk]
  reduce_closed_widths
  refine tvXfT _ _ (by xf_walk) (fun _ => ?_)
  have hA : zero_extend (m := 64) (c.b +++ (Sail.BitVec.extractLsb c.vpn 26 18 +++ (zeros (n := 3)))) =
      pteAddr c.b (vpnIdx c.vpn 2) := by
    first | rfl | (simp only [pteAddr, vpnIdx, Sail.BitVec.extractLsb, zero_extend]; bv_decide)
  have hram := pteAddrRam c.b (vpnIdx c.vpn 2) hr.1
  simp only [hA]
  refine tvBind _ _ _ _ (tvReadPte _ hram.1 hram.2) (fun r hrd => ?_)
  cases r with
  | Err _ => intro o e h; cases h
  | Ok w =>
    have hw : w = kPtr c.b1 := BitVec.eq_of_toNat_eq (((hrd w rfl) rfl).1 rfl)
    subst hw
    simp only []
    refine tvXfT _ _ (by xf_walk) (fun _ => ?_)
    split
    · rw [ppn_of_kPtr, BitVec.setWidth_eq]
      exact tvPtWalk1 c hr _ _ _ _ _ _
    · rw [BitVec.setWidth_eq]
      refine tvXfBind _ _ _ _ (xfCheckLeafKPtr _ _ _ _ _ _ _ _ _) (fun r hcl => ?_)
      match r with
      | .Err _ => intro o e h; cases h
      | .Ok x => exact absurd rfl (hcl x)

end PinFetchPa
end Weak
