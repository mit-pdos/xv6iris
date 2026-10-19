/-
Xv6: **the sealed kernel table in plain addresses** (mcslrec (1), [OWN.99] (B)).

The machine's sealed-table record keeps the client's shape of the slots it sealed
(`KernelRsv.kptOk`, xv6's `Xv6.xv6KptOk`: explicit addresses `kSlotP`, indices `kIdxP`, the
mappings `kMapP`), and the export states the table's walks in the same plain vocabulary
(`AccessDiscipline.kptMapsExp`), so the trusted base does not grow.  This file bridges the plain
vocabulary to the tree vocabulary:

* `kSlotP_pteAddr`, `kIdxP_vpnIdx`, `kMapP_iff`: `kSlotP b i = pteAddr b i`, `kIdxP vpn l =
  (vpnIdx vpn l).toNat`, `kMapP pas = kvmMapK pas`;
* `xv6KptOk_of`: the table `kvmmake` returns has xv6's shape (what `KptBoot` registers);
* `kptMapsAt_ofExp` / `kptTextAt_ofExp`: the export gives the consumers' `kptMapsAt σ (kvmMapK
  pas)` (dataRealized's PT answers) and `kptTextAt σ` (r2's `labAnsOk`).

FAITHFUL: facts of xv6's table; Sv39 walk addresses (`pt_base @ vpn_i @ 0b000`).  Helpers are
`Xv6.KptPlain.*`.
-/
import Xv6.KptMapIdent
import Xv6.KvmSeal

namespace Xv6

open MachCSL
open AccessDiscipline (kptSealAt kptSlotDisc kptRootBytes xv6Rsv xv6StartedR_mem)

/-! ## 1. The plain vocabulary is the tree's -/

theorem kSlotP_pteAddr (b : BitVec 44) (i : BitVec 9) : kSlotP b i.toNat = pteAddr b i := by
  rw [pteAddr_rootPA]; rfl

theorem kIdxP_vpnIdx (vpn : BitVec 27) (l : Nat) : kIdxP vpn l = (vpnIdx vpn l).toNat := by
  simp only [kIdxP, vpnIdx, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  rw [Nat.mul_comm l 9]

theorem kSlotP_idx (b : BitVec 44) (vpn : BitVec 27) (l : Nat) :
    kSlotP b (kIdxP vpn l) = pteAddr b (vpnIdx vpn l) := by
  rw [kIdxP_vpnIdx, kSlotP_pteAddr]

theorem kMapP_iff (pas : Nat → BitVec 44) (vpn : BitVec 27) (ppn : BitVec 44) (perm : KPerm) :
    kMapP pas vpn ppn perm ↔ kvmMapK pas vpn ppn perm := by
  unfold kMapP kvmMapK kTextVpn kDataVpn kIdPpn kstackVpn
  constructor
  · rintro (⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | h)
    · exact Or.inl ⟨⟨h1, h2⟩, h3, h4⟩
    · exact Or.inr (Or.inl ⟨⟨h1, by omega⟩, h3, h4⟩)
    · exact Or.inr (Or.inr h)
  · rintro (⟨⟨h1, h2⟩, h3, h4⟩ | ⟨⟨h1, h2⟩, h3, h4⟩ | h)
    · exact Or.inl ⟨h1, h2, h3, h4⟩
    · exact Or.inr (Or.inl ⟨h1, by omega, h3, h4⟩)
    · exact Or.inr (Or.inr h)

/-! ## 2. The table `kvmmake` returns has xv6's shape -/

theorem KptPlain.mem_kptSlots {ra : PAddr} {t : PTree} {e : BitVec 64 × BitVec 64} (he : e ∈ t.entries 2) :
    (⟨e.1, e.2, !pteLeafB e.2⟩ : KSlot) ∈ kptSlots ra t :=
  List.mem_cons_of_mem _ (List.mem_map.2 ⟨e, he, rfl⟩)

/-- **The registered shape** (`KernelRsv.kptOk` at xv6's instance) of the table `kvmmake`
returns, sealed with its root word at `kernel_pagetable`. -/
theorem xv6KptOk_parts {t : PTree} {pas : Nat → BitVec 44} (h : kvmTableOk t pas) :
    (⟨KA.«kernel_pagetable», kSlotP t.base 0, true⟩ : KSlot) ∈ kptSlots KA.«kernel_pagetable» t ∧
    (∀ (vpn : BitVec 27) (ppn : BitVec 44) (perm : KPerm), kMapP pas vpn ppn perm →
      ∃ (b1 b0 : BitVec 44) (a d : BitVec 1),
        (⟨kSlotP t.base (kIdxP vpn 2), kPtr b1, true⟩ : KSlot) ∈ kptSlots KA.«kernel_pagetable» t ∧
        (⟨kSlotP b1 (kIdxP vpn 1), kPtr b0, true⟩ : KSlot) ∈ kptSlots KA.«kernel_pagetable» t ∧
        (⟨kSlotP b0 (kIdxP vpn 0), kLeaf ppn perm a d, false⟩ : KSlot) ∈ kptSlots KA.«kernel_pagetable» t) ∧
    ∀ i, i < 64 → KA.«end».toNat ≤ (kSlotP (pas i) 0).toNat ∧
      ∀ d ∈ kptSlots KA.«kernel_pagetable» t, d.addr ≠ kSlotP (pas i) 0 := by
  refine ⟨?_, fun vpn ppn perm hk => ?_, fun i hi => ?_⟩
  · have e : kSlotP t.base 0 = pteAddr t.base 0#9 := kSlotP_pteAddr t.base 0#9
    rw [e]
    exact List.mem_cons_self
  rotate_left
  · obtain ⟨hpv, hnp⟩ := h.2.2.2.2.2.2 i hi
    have e : kSlotP (pas i) 0 = pageAddr (pas i) := kSlotP_pteAddr (pas i) 0#9
    rw [e]
    refine ⟨?_, fun d hd => ?_⟩
    · obtain ⟨-, h2, -⟩ := hpv
      simp only [BitVec.ult, decide_eq_true_eq, Nat.not_lt, kernelEndAddr] at h2
      exact h2
    · rcases List.mem_cons.1 hd with rfl | hd
      · intro heq
        have h1 : KA.«kernel_pagetable».toNat = (pageAddr (pas i)).toNat := congrArg BitVec.toNat heq
        obtain ⟨-, h2, -⟩ := hpv
        simp only [BitVec.ult, decide_eq_true_eq, Nat.not_lt, kernelEndAddr] at h2
        have h3 : KA.«end».toNat ≤ KA.«kernel_pagetable».toNat := by rw [h1]; exact h2
        revert h3
        decide +kernel
      · obtain ⟨e, he, rfl⟩ := List.mem_map.1 hd
        obtain ⟨b, hb, k, hk⟩ := entries_page 2 t e he
        intro heq0
        have heq : e.1 = pageAddr (pas i) := heq0
        rw [hk] at heq
        have h1 := congrArg BitVec.toNat heq
        rw [KptInv.pteAddr_toNat, pageAddr_toNat] at h1
        have hk' := k.isLt
        have hbb : b = pas i := BitVec.eq_of_toNat_eq (by omega)
        exact hnp (hbb ▸ hb)
  · obtain ⟨addr, a, d, hw⟩ := kvmMapK_maps h vpn ppn perm ((kMapP_iff pas vpn ppn perm).1 hk)
    obtain ⟨c1, g, h2, h1, rfl⟩ := KptTextIdent.walk_path t h.1 vpn _ _ hw
    have h0 := PTree.walk_mem_entries 2 t vpn _ _ hw
    refine ⟨c1.base, g.base, a, d, ?_, ?_, ?_⟩
    · have := KptPlain.mem_kptSlots (ra := KA.«kernel_pagetable») h2
      rw [kSlotP_idx]; simpa [pteLeafB_kPtr] using this
    · have := KptPlain.mem_kptSlots (ra := KA.«kernel_pagetable») h1
      rw [kSlotP_idx]; simpa [pteLeafB_kPtr] using this
    · have := KptPlain.mem_kptSlots (ra := KA.«kernel_pagetable») h0
      rw [kSlotP_idx]; simpa [pteLeafB_kLeaf] using this

theorem xv6KptOk_of {t : PTree} {pas : Nat → BitVec 44} (h : kvmTableOk t pas) :
    xv6KptOk (kptSlots KA.«kernel_pagetable» t) :=
  ⟨pas, t.base, xv6KptOk_parts h⟩

/-! ## 3. The consumers' facts, from the export -/

/-- The export's walk is the tree vocabulary's. -/
theorem kptWalkAt_ofP {σ : MState} {S : Nat} {b : BitVec 44} {vpn : BitVec 27} {ppn : BitVec 44}
    {perm : KPerm} (h : AccessDiscipline.kptWalkP σ S b vpn ppn perm) : kptWalkAt σ S b vpn ppn perm := by
  obtain ⟨b1, b0, a, d, w2, d2, w1, d1, w0, d0⟩ := h
  rw [kSlotP_idx] at w2 d2 w1 d1 d0
  obtain ⟨v, hv, hpv⟩ := w0
  rw [kSlotP_idx] at hv
  exact ⟨b1, b0, a, d, w2, d2, w1, d1, ⟨v, hv, hpv⟩, d0⟩

/-- **dataRealized's PT answers**: once the boot gate is open (`started` written), the export's
plain statement is the sealed table's kernel maps (`kptMapsAt σ (kvmMapK pas)`). -/
theorem kptMapsAt_ofExp (σ : MState) (h : AccessDiscipline.kptMapsExp σ)
    (hg : ¬ ∀ a ∈ xv6StartedR.bytes, ∀ H : Hist, σ.mem[a]? = some H → ∀ e ∈ H, e.t = 0) :
    ∃ pas, kptMapsAt σ (kvmMapK pas) := by
  rcases h with h0 | ⟨pas, S, b, hs, hr, hw⟩
  · exact absurd h0 hg
  refine ⟨pas, S, b, hs, ?_, fun vpn ppn perm hk => kptWalkAt_ofP (hw vpn ppn perm ((kMapP_iff pas vpn ppn perm).2 hk))⟩
  have e : kSlotP b 0 = pteAddr b 0#9 := kSlotP_pteAddr b 0#9
  rw [← e]; exact hr

/-- **r2's `labAnsOk` fact**: once the boot gate is open, the kernel text translates identically
(`kptTextAt σ`). -/
theorem kptTextAt_ofExp (σ : MState) (h : AccessDiscipline.kptMapsExp σ)
    (hg : ¬ ∀ a ∈ xv6StartedR.bytes, ∀ H : Hist, σ.mem[a]? = some H → ∀ e ∈ H, e.t = 0) : kptTextAt σ := by
  obtain ⟨pas, S, b, hs, hr, hw⟩ := kptMapsAt_ofExp σ h hg
  exact ⟨S, b, hs, hr, fun vpn hv => hw vpn (kIdPpn vpn) .rx (Or.inl ⟨hv, rfl, rfl⟩)⟩

end Xv6
