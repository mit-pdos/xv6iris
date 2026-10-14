/-
Weak: **`dataOkR` (3h) — the TLB and `translate` of a data access under `dkB`**: the miss (walk,
A/D write-back, fill) and the hit (permission check on the cached leaf, A/D write-back through its
slot, refresh) answer `Ok (ppn, PBMT_PMA, _)` with the leaf's page (`PROGRESS-dataOk.md`).  Mirrors
`Weak/PinFetchPaTlb.lean`.  Lean-only.  Every helper is `Weak.PinDataOk.*`.
-/
import Weak.PinDataOkWalk

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Functions
open Sail.ArchSem (FreeM)

namespace PinDataOk
open SailCycleOrderK PinFetchPaFp

/-- The data translation's post: `Ok` with the leaf's page and the plain memory type. -/
def trPostD (c : DCfg) (r : Result (BitVec 44 × page_based_mem_type × Unit) (PTW_Error × Unit)) : Prop :=
  ∃ e, r = .Ok (c.ppn, .PBMT_PMA, e)

set_option maxHeartbeats 40000000 in
/-- The TLB fill: a footprint (any write; `dkB` constrains none). -/
theorem fpAddToTLB (asid : BitVec 16) (vpn : BitVec 27) (ppn : BitVec 44) (pte : BitVec 64) (pa : physaddr)
    (level : Nat) (g : Bool) : SailCycleOrderFp.fpT (add_to_TLB 39 asid vpn ppn pte pa level g) := by
  unfold add_to_TLB
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
/-- **The TLB miss.** -/
theorem dkTranslateTLBMiss (c : DCfg) (hr : c.ram) (asid : BitVec 16) (acc : MemoryAccessType mem_payload)
    (hk : dAccKind acc c.perm) (mxr sum : Bool) (u : Unit) :
    dkB c (trPostD c) (translate_TLB_miss 39 asid c.b c.vpn acc .Supervisor mxr sum u) := by
  unfold translate_TLB_miss
  reduce_closed_widths
  refine dkBind _ _ _ _ (dkPtWalk2 c hr acc hk mxr sum false u) (fun r hw => ?_)
  obtain ⟨a, d, g, e, rfl⟩ := hw
  simp only [leafOut]
  refine dkBind _ _ _ _ (dkUpdateAndWritePte c hr acc hk mxr sum _ e) (fun r2 h2 => ?_)
  match r2 with
  | .Err e' => exact absurd rfl (h2 e')
  | .Ok (some q, e2) =>
    exact dkBind _ _ _ _ (dkOfFp _ _ (fpAddToTLB _ _ _ _ _ _ _)) (fun _ _ => ⟨e2, rfl⟩)
  | .Ok (none, e2) =>
    exact dkBind _ _ _ _ (dkOfFp _ _ (fpAddToTLB _ _ _ _ _ _ _)) (fun _ _ => ⟨e2, rfl⟩)

/-- The cached entry the TLB filter admits. -/
def dEnt (c : DCfg) (a d : BitVec 1) : TLB_Entry :=
  tlbEntryOf 0#16 c.vpn c.ppn (kLeaf c.ppn c.perm a d) (pteAddr c.b0 (vpnIdx c.vpn 0))

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
/-- **The lookup** at ASID 0: a hit gives the walk's cached leaf. -/
theorem dkLookupTLB (c : DCfg) :
    dkB c (fun r => ∀ i ent, r = some (i, ent) → ∃ a d, ent = dEnt c a d) (lookup_TLB 39 0#16 c.vpn) := by
  unfold lookup_TLB
  reduce_closed_widths
  refine dkReadReg _ _ (fun v hv => ?_)
  have hv' := dGTlb hv
  rw [tlbHash_eq, tlb_get! v (tlbHash c.vpn) (tlbHash_lt _)]
  cases hget : v[tlbHash c.vpn]'(tlbHash_lt _) with
  | none => intro i ent h; cases h
  | some ent =>
    simp only []
    split
    · rename_i hm
      intro i e h
      injection h with h
      injection h with _ h
      subst h
      exact hv' _ (tlbHash_lt _) _ hget hm
    · intro i e h; cases h

set_option maxHeartbeats 40000000 in
theorem fpWriteTLB (i : Nat) (ent : TLB_Entry) : SailCycleOrderFp.fpT (write_TLB i ent) := by
  unfold write_TLB
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
/-- **The TLB hit** on the walk's cached leaf. -/
theorem dkTranslateTLBHit (c : DCfg) (hr : c.ram) (asid : BitVec 16) (acc : MemoryAccessType mem_payload)
    (hk : dAccKind acc c.perm) (mxr sum : Bool) (u : Unit) (idx : Nat) (a d : BitVec 1) :
    dkB c (trPostD c) (translate_TLB_hit 39 asid c.vpn acc .Supervisor mxr sum u idx (dEnt c a d)) := by
  unfold translate_TLB_hit dEnt
  reduce_closed_widths
  simp only [tlb_get_pte_tlbEntryOf, pteAddr_tlbEntryOf, tlb_get_level_tlbEntryOf,
    checkPermKLeaf acc c.perm hk, pure_bind, BitVec.setWidth_eq, tlb_get_ppn_tlbEntryOf,
    tlb_get_pbmt_kLeaf]
  refine dkBind _ _ _ _ (dkUpdateAndWritePte c hr acc hk mxr sum _ _) (fun r2 h2 => ?_)
  match r2 with
  | .Err e' => exact absurd rfl (h2 e')
  | .Ok (some q, e2) =>
    exact dkBind _ _ _ _ (dkOfFp _ _ (fpWriteTLB _ _)) (fun _ _ => ⟨e2, rfl⟩)
  | .Ok (none, e2) => exact ⟨e2, rfl⟩

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
/-- **`translate`** of a data access at ASID 0 from the root `b`. -/
theorem dkTranslate (c : DCfg) (hr : c.ram) (acc : MemoryAccessType mem_payload) (hk : dAccKind acc c.perm)
    (mxr sum : Bool) (u : Unit) :
    dkB c (trPostD c) (translate 39 0#16 c.b c.vpn acc .Supervisor mxr sum u) := by
  unfold translate
  refine dkBind _ _ _ _ (dkLookupTLB c) (fun r hl => ?_)
  match r with
  | some (i, ent) =>
    obtain ⟨a, d, rfl⟩ := hl i ent rfl
    exact dkTranslateTLBHit c hr _ acc hk mxr sum u i a d
  | none => exact dkTranslateTLBMiss c hr _ acc hk mxr sum u

end PinDataOk
end Weak
