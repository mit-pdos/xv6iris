/-
Xv6: **the sealed kernel table's mappings at the machine — text, data, kernel stacks**
(`dataOkR` [OWN.95] step (2): `Xv6/KptTextIdent.lean` generalised from the text map to every
mapping of the table `kvmmake` returns; `PROGRESS-dataOk.md`).

* `kptMapsAt σ M`: there is a seal position `S` (`kptSealAt`) at which the root word holds the root
  page `b` and, for every `(vpn, ppn, perm)` that `M` admits, the walk's three slots hold, as of
  `S`, two pointers and an A/D variant of the leaf `kLeaf ppn perm a d`, each slot disciplined after
  `S` (`kptSlotDisc`) — `kptWalkAt`.
* `kptMapsAt_of`: from the sealed record WITH its tree (`kptTreeAt`), for `M := t.mapsTo`.
* `kvmMapK pas`: the kernel's three walked maps — the text identity `R|X` (`kTextVpn`), the
  rest of RAM identity `R|W` (`kDataVpn`, `kvmRegions`' sixth region `⟨0x80007, 0x80007, .rw,
  0x7FF9⟩`, kernel/vm.c `kvmmap(kpgtbl, (uint64)etext, (uint64)etext, PHYSTOP-(uint64)etext,
  PTE_R | PTE_W)`), and the 64 process kernel stacks `kstackVpn i ↦ pas i` `R|W`
  (`proc_mapstacks`).  `kptKernelAt_of : kptTreeStateOk σ → ∃ pas, kptMapsAt σ (kvmMapK pas)`.

The gap is `KptTextIdent`'s: `kptTreeStateOk` is not at the export (the MachCSL record keeps the
sealed slots existentially).  FAITHFUL: facts of xv6's table.  Helpers are `Xv6.KptMapIdent.*`.
-/
import Xv6.KptTextIdent

namespace Xv6

open MachCSL
open AccessDiscipline (kptSealAt kptSlotDisc kptRootBytes xv6Rsv xv6StartedR_mem)

/-- **One mapping's walk at the seal `S` from the root `b`**: two pointers, then an A/D variant of
the leaf `kLeaf ppn perm a d`; each slot disciplined after `S`. -/
def kptWalkAt (σ : MState) (S : Nat) (b : BitVec 44) (vpn : BitVec 27) (ppn : BitVec 44)
    (perm : KPerm) : Prop :=
  ∃ (b1 b0 : BitVec 44) (a d : BitVec 1),
    wordAsOf σ.mem (pteAddr b (vpnIdx vpn 2)) S (kPtr b1) ∧
    kptSlotDisc σ S (pteAddr b (vpnIdx vpn 2)) (kPtr b1) ∧
    wordAsOf σ.mem (pteAddr b1 (vpnIdx vpn 1)) S (kPtr b0) ∧
    kptSlotDisc σ S (pteAddr b1 (vpnIdx vpn 1)) (kPtr b0) ∧
    (∃ v, wordAsOf σ.mem (pteAddr b0 (vpnIdx vpn 0)) S v ∧ pteVariant (kLeaf ppn perm a d) v) ∧
    kptSlotDisc σ S (pteAddr b0 (vpnIdx vpn 0)) (kLeaf ppn perm a d)

/-- **The sealed table's mappings `M`, at the machine.** -/
def kptMapsAt (σ : MState) (M : BitVec 27 → BitVec 44 → KPerm → Prop) : Prop :=
  ∃ (S : Nat) (b : BitVec 44), kptSealAt σ S ∧ wordAsOf σ.mem KA.«kernel_pagetable» S (pteAddr b 0#9) ∧
    ∀ vpn ppn perm, M vpn ppn perm → kptWalkAt σ S b vpn ppn perm

/-- The sealed record with its tree `t` (`kptTreeStateOk` with the tree named). -/
def kptTreeAt (σ : MState) (t : PTree) (pas : Nat → BitVec 44) : Prop :=
  kvmTableOk t pas ∧ ∃ S : Nat,
    kptSealOk xv6Rsv σ.mem σ.top S (kptSlots KA.«kernel_pagetable» t) ∧
    kptHistsAt σ.mem S (kptSlots KA.«kernel_pagetable» t)

theorem kptTreeAt_of (σ : MState) (h : kptTreeStateOk σ) : ∃ t pas, kptTreeAt σ t pas := by
  obtain ⟨S, t, pas, hkt, hok, hh⟩ := h
  exact ⟨t, pas, hkt, S, hok, hh⟩

/-- **Every mapping of the tree, at the machine.** -/
theorem kptMapsAt_of (σ : MState) (t : PTree) (pas : Nat → BitVec 44) (h : kptTreeAt σ t pas) :
    kptMapsAt σ (fun v p q => t.mapsTo v p q) := by
  obtain ⟨hkt, S, hok, hh⟩ := h
  obtain ⟨Hs, hm, ⟨v0, hv0, hc0⟩, hent⟩ :=
    hh ⟨KA.«kernel_pagetable», pteAddr t.base 0#9, true⟩ List.mem_cons_self
  have hm' : ∀ j, j < 8 → σ.mem[KA.«kernel_pagetable» + BitVec.ofNat 64 j]? = some (Hs j) := hm
  have hc0' : v0 = pteAddr t.base 0#9 := by
    split at hc0
    · exact hc0
    · rename_i hn; exact absurd rfl hn
  subst hc0'
  refine ⟨S, t.base, ⟨hok.1, ?_, fun a ha H hH e he he0 => hok.2.1 _ _ xv6StartedR_mem a ha H hH e he he0⟩,
    KptTextIdent.wordAsOf_of_hist hm' hv0, ?_⟩
  · intro a ha H hH e he _
    simp only [kptRootBytes, wordBytes, List.mem_map, List.mem_range] at ha
    obtain ⟨j, hj, rfl⟩ := ha
    rw [hm' j hj] at hH
    obtain rfl := Option.some.inj hH
    refine Nat.le_of_not_lt (fun hlt => ?_)
    have hf : true = false := (hent j hj e he hlt).1
    cases hf
  · intro vpn ppn perm hmap
    obtain ⟨addr, a, d, hw⟩ := hmap
    obtain ⟨c1, g, h2, h1, rfl⟩ := KptTextIdent.walk_path t hkt.1 vpn _ _ hw
    obtain ⟨w2, d2⟩ := KptTextIdent.ptr_of hh h2
    obtain ⟨w1, d1⟩ := KptTextIdent.ptr_of hh h1
    obtain ⟨w0, d0⟩ := KptTextIdent.leaf_of hh (PTree.walk_mem_entries 2 t vpn _ _ hw)
    exact ⟨c1.base, g.base, a, d, w2, d2, w1, d1, w0, d0⟩

/-- A kernel-data virtual page: `kvmmake`'s identity `R|W` map of the rest of RAM,
`0x80007 ..< 0x88000`. -/
def kDataVpn (vpn : BitVec 27) : Prop := 0x80007 ≤ vpn.toNat ∧ vpn.toNat < 0x80007 + 0x7FF9

/-- `kvmmake`'s data region maps every kernel-data vpn to itself at `R|W`. -/
theorem kvmData_maps {t : PTree} {pas : Nat → BitVec 44} (h : kvmTableOk t pas) (vpn : BitVec 27)
    (hv : kDataVpn vpn) : t.mapsTo vpn (kIdPpn vpn) .rw := by
  have hr : t.regionMapped ⟨0x80007#27, 0x80007#44, .rw, 0x7FF9⟩ :=
    h.2.2.2.1 _ (by simp only [kvmRegions, List.mem_cons]; simp)
  unfold kDataVpn at hv
  have hi := hr (vpn.toNat - 0x80007) (by show vpn.toNat - 0x80007 < 0x7FF9; omega)
  have hlt := vpn.isLt
  have e1 : (0x80007#27 + BitVec.ofNat 27 (vpn.toNat - 0x80007)) = vpn := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have e2 : (0x80007#44 + BitVec.ofNat 44 (vpn.toNat - 0x80007)) = kIdPpn vpn := by
    apply BitVec.eq_of_toNat_eq
    simp only [kIdPpn, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth]
    omega
  rw [e1, e2] at hi
  exact hi

/-- **The kernel's walked maps**: text `R|X`, data `R|W` (both identity), the stacks `R|W`. -/
def kvmMapK (pas : Nat → BitVec 44) (vpn : BitVec 27) (ppn : BitVec 44) (perm : KPerm) : Prop :=
  (kTextVpn vpn ∧ ppn = kIdPpn vpn ∧ perm = .rx) ∨ (kDataVpn vpn ∧ ppn = kIdPpn vpn ∧ perm = .rw) ∨
    (∃ i, i < 64 ∧ vpn = kstackVpn i ∧ ppn = pas i ∧ perm = .rw)

theorem kvmMapK_maps {t : PTree} {pas : Nat → BitVec 44} (h : kvmTableOk t pas) (vpn : BitVec 27)
    (ppn : BitVec 44) (perm : KPerm) (hk : kvmMapK pas vpn ppn perm) : t.mapsTo vpn ppn perm := by
  rcases hk with ⟨hv, rfl, rfl⟩ | ⟨hv, rfl, rfl⟩ | ⟨i, hi, rfl, rfl, rfl⟩
  · exact kvmText_maps h vpn hv
  · exact kvmData_maps h vpn hv
  · exact h.2.2.2.2.1 i hi

/-- **(2): THE KERNEL'S MAPS AT THE MACHINE**, from the sealed record with its tree. -/
theorem kptKernelAt_of (σ : MState) (h : kptTreeStateOk σ) : ∃ pas, kptMapsAt σ (kvmMapK pas) := by
  obtain ⟨t, pas, ht⟩ := kptTreeAt_of σ h
  obtain ⟨S, b, hs, hr, hw⟩ := kptMapsAt_of σ t pas ht
  exact ⟨pas, S, b, hs, hr, fun v p q hk => hw v p q (kvmMapK_maps ht.1 v p q hk)⟩

end Xv6
