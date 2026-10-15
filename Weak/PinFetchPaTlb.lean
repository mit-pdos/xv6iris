/-
Weak: **W9a (B) B5 r2 part (B) — the TLB and the translation under `tvB`** (`add_to_TLB` /
`write_TLB` keep `tlbIdOk`; the miss and hit paths, `translate`, `translateAddr`: `Ok` only at the
identity; plan rev 52 §D Q-B5-FETCH (r2-a), `PROGRESS-r2.md`).  Lean-only.  Every helper is
`Weak.PinFetchPa.*`.
-/
import Weak.PinFetchPaWalk

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Functions
open Sail.ArchSem (FreeM)

namespace PinFetchPa
open SailCycleOrderK PinFetchPaFp

variable {c : TCfg}

/-- A register read node. -/
theorem tvReadReg {X : Type} {P : X → Prop} (r : Register) (f : RegisterType r → SailM X)
    (h : ∀ v, tvRk c r v → tvB c P (f v)) : tvB c P (readReg r >>= f) := h

/-- A register write node. -/
theorem tvWriteReg {X : Type} {P : X → Prop} (r : Register) (v : RegisterType r) (f : Unit → SailM X)
    (hv : tvRk c r v) (h : tvB c P (f ())) : tvB c P (writeReg r v >>= f) := ⟨hv, fun _ => h⟩

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
/-- **Caching the identity walk** keeps the TLB filter. -/
theorem tvAddToTLB (c : TCfg) (asid : BitVec 16) (pte : BitVec 64) (pa : physaddr) (g : Bool) :
    tvB c (fun _ => True) (add_to_TLB 39 asid c.vpn (idPpn c.vpn) pte pa 0 g) := by
  unfold add_to_TLB
  simp only []
  reduce_closed_widths
  refine tvReadReg _ _ (fun v hv => ?_)
  refine tvWriteReg _ _ _ ⟨trivial, And.intro (fun (h : Register.tlb = Register.satp) => nomatch h)
    (fun (h : Register.tlb = Register.tlb) => ⟨?_, ?_⟩)⟩ ?_
  · cases h
    have hv' := tvRkTlb hv
    intro i hi ent hent hm
    simp only [cast_eq] at hent
    rw [vectorUpdate, Vector.getElem_set! hi] at hent
    split at hent
    · injection hent with hent
      subst hent
      unfold tlb_get_ppn idPpn
      generalize c.vpn = x
      simp only [ones, zero_extend, sign_extend, trunc, Sail.BitVec.zeroExtend, Sail.BitVec.signExtend,
        Sail.BitVec.truncate]
      bv_decide
    · exact hv' i hi ent hent hm
  · cases h
    intro x hx i hi ent hent hm
    simp only [cast_eq] at hent
    rw [vectorUpdate, Vector.getElem_set! hi] at hent
    split at hent
    · injection hent with hent
      subst hent
      revert hm
      unfold match_TLB_Entry tlb_get_ppn idPpn
      generalize c.vpn = y
      simp only [ones, zero_extend, sign_extend, trunc, Sail.BitVec.zeroExtend, Sail.BitVec.signExtend,
        Sail.BitVec.truncate, Bool.and_eq_true, beq_iff_eq]
      intro hm
      have hm2 := hm.2
      revert hm2
      bv_decide
    · exact tvRkTlbVs hv x hx i hi ent hent hm
  · exact tvReadReg _ _ (fun _ _ => trivial)

/-- The translation's post: `Ok` only with the identity ppn. -/
def trPost (c : TCfg) (r : Result (BitVec 44 × page_based_mem_type × Unit) (PTW_Error × Unit)) : Prop :=
  ∀ p pb e, r = .Ok (p, pb, e) → p = idPpn c.vpn

set_option maxHeartbeats 40000000 in
/-- `update_and_write_pte`: a `satp`/`tlb`-free footprint. -/
@[xf_reg] theorem xfUpdateAndWritePte (vpn : BitVec 27) (addr : physaddr) (pte : BitVec 64) (level : Nat)
    (acc : MemoryAccessType mem_payload) (priv : Privilege) (mxr sum : Bool) (u : Unit) :
    xfT (update_and_write_pte 39 vpn addr pte level acc priv mxr sum u) := by
  unfold update_and_write_pte
  xf_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
/-- **The TLB miss**: the walk from the root, the A/D write-back, the fill. -/
theorem tvTranslateTLBMiss (c : TCfg) (hr : c.ram) (asid : BitVec 16) (acc : MemoryAccessType mem_payload)
    (priv : Privilege) (mxr sum : Bool) (u : Unit) :
    tvB c (trPost c) (translate_TLB_miss 39 asid c.b c.vpn acc priv mxr sum u) := by
  unfold translate_TLB_miss
  reduce_closed_widths
  refine tvBind _ _ _ _ (tvPtWalk2 c hr acc priv mxr sum false u) (fun r hw => ?_)
  match r with
  | .Err _ => intro p pb e h; cases h
  | .Ok (⟨ppn, pte, pa, level, pbmt, global⟩, e) =>
    obtain ⟨hp, hl⟩ := hw _ _ rfl
    simp only at hp hl
    subst hp hl
    simp only []
    refine tvXfT _ _ (xfUpdateAndWritePte _ _ _ _ _ _ _ _ _) (fun r2 => ?_)
    match r2 with
    | .Err _ => intro p pb e h; cases h
    | .Ok (some q, e2) =>
      refine tvBind _ _ _ _ (tvAddToTLB c asid q pa global) (fun _ _ => ?_)
      intro p pb e h; injection h with h; injection h with h; exact h.symm
    | .Ok (none, e2) =>
      refine tvBind _ _ _ _ (tvAddToTLB c asid pte pa global) (fun _ _ => ?_)
      intro p pb e h; injection h with h; injection h with h; exact h.symm

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
/-- **The lookup** at ASID 0: a hit gives an entry whose ppn for `vpn` is the identity. -/
theorem tvLookupTLB (c : TCfg) :
    tvB c (fun r => ∀ i ent, r = some (i, ent) → tlb_get_ppn 39 ent c.vpn = idPpn c.vpn ∧ tlbVsOk c ent)
      (lookup_TLB 39 0#16 c.vpn) := by
  unfold lookup_TLB
  reduce_closed_widths
  refine tvReadReg _ _ (fun v hv => ?_)
  have hv' := tvRkTlb hv
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
      exact ⟨hv' _ (tlbHash_lt _) _ hget hm,
        fun x hx hmx => tvRkTlbVs hv x hx _ (tlbHash_lt _) _ hget hmx⟩
    · intro i e h; cases h

set_option maxHeartbeats 40000000 in
@[xf_reg] theorem xfTlbGetPbmt (ent : TLB_Entry) : xfT (tlb_get_pbmt ent) := by
  unfold tlb_get_pbmt
  xf_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
/-- **The TLB hit** on an entry whose ppn for `vpn` is the identity. -/
theorem tvTranslateTLBHit (c : TCfg) (asid : BitVec 16) (acc : MemoryAccessType mem_payload)
    (priv : Privilege) (mxr sum : Bool) (u : Unit) (idx : Nat) (ent : TLB_Entry)
    (hent : tlb_get_ppn 39 ent c.vpn = idPpn c.vpn) (hvs : tlbVsOk c ent) :
    tvB c (trPost c) (translate_TLB_hit 39 asid c.vpn acc priv mxr sum u idx ent) := by
  unfold translate_TLB_hit
  reduce_closed_widths
  refine tvXfT _ _ (by xf_walk) (fun pc => ?_)
  match pc with
  | .PTE_Check_Failure _ => intro p pb e h; cases h
  | .PTE_Check_Success _ =>
    simp only []
    refine tvXfT _ _ (xfUpdateAndWritePte _ _ _ _ _ _ _ _ _) (fun r2 => ?_)
    match r2 with
    | .Err _ => intro p pb e h; cases h
    | .Ok (none, e2) =>
      refine tvXfT _ _ (xfTlbGetPbmt _) (fun _ => ?_)
      intro p pb e h; injection h with h; injection h with h; exact h.symm.trans hent
    | .Ok (some q, e2) =>
      simp only [write_TLB, bind_assoc]
      refine tvReadReg _ _ (fun v hv => ?_)
      refine tvWriteReg _ _ _ ⟨trivial, And.intro (fun (h : Register.tlb = Register.satp) => nomatch h)
        (fun (h : Register.tlb = Register.tlb) => ⟨?_, ?_⟩)⟩ ?_
      · cases h
        have hv' := tvRkTlb hv
        intro i hi e hen hm
        simp only [cast_eq] at hen
        rw [vectorUpdate, Vector.getElem_set! hi] at hen
        split at hen
        · injection hen with hen
          subst hen
          exact hent
        · exact hv' i hi e hen hm
      · cases h
        intro x hx i hi e hen hm
        simp only [cast_eq] at hen
        rw [vectorUpdate, Vector.getElem_set! hi] at hen
        split at hen
        · injection hen with hen
          subst hen
          exact hvs x hx hm
        · exact tvRkTlbVs hv x hx i hi e hen hm
      · refine tvXfT _ _ (xfTlbGetPbmt _) (fun _ => ?_)
        intro p pb e h; injection h with h; injection h with h; exact h.symm.trans hent

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
/-- **`translate`** at ASID 0 from the root `b`: `Ok` only with the identity ppn. -/
theorem tvTranslate (c : TCfg) (hr : c.ram) (acc : MemoryAccessType mem_payload) (priv : Privilege)
    (mxr sum : Bool) (u : Unit) :
    tvB c (trPost c) (translate 39 0#16 c.b c.vpn acc priv mxr sum u) := by
  unfold translate
  refine tvBind _ _ _ _ (tvLookupTLB c) (fun r hl => ?_)
  match r with
  | some (i, ent) => exact tvTranslateTLBHit c _ acc priv mxr sum u i ent (hl i ent rfl).1 (hl i ent rfl).2
  | none => exact tvTranslateTLBMiss c hr _ acc priv mxr sum u

end PinFetchPa
end Weak
