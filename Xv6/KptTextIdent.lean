/-
Xv6: **the sealed kernel table maps the kernel text identically, `R|X`** (W9a (B) B5 r2 part (A),
plan `notes/weak-allocproc-plan.md` rev 52 §D Q-B5-FETCH (r2-a), rulings [OWN.81] [OWN.92]).

`kvmmake` maps the kernel text `0x80000000 ..< 0x80007000` page-for-page onto itself with
permission `R|X` (`kvmRegions`' fifth region `⟨0x80000, 0x80000, .rx, 7⟩`, kernel/vm.c
`kvmmap(kpgtbl, KERNBASE, KERNBASE, (uint64)etext-KERNBASE, PTE_R | PTE_X)`).  This file reads
that off the table `kvmmake` returns (`kvmTableOk`, proved by `KvmCounts.kvmmake_table`) and then
off the sealed table's record in the machine:

* §1 the tree: every kernel-text vpn's Sv39 walk in a `kvmTableOk` table reads a pointer at the
  root page, a pointer at the level-1 page, and the leaf `kLeaf (kIdPpn vpn) .rx a d` at the
  level-0 page (`kvmText_walk`; `kIdPpn vpn` is `vpn` zero-extended: PA = VA).
* §2 the machine: if the sealed record's slots are those of a `kvmTableOk` table with its root
  word at `kernel_pagetable` (`kptTreeStateOk`), then `kptTextAt σ`: there is a seal position `S`
  (`kptSealAt`, the export's own) at which the root word holds the root page and, for every
  kernel-text vpn, the three slots the walk reads hold, as of `S`, the two pointers and an A/D
  variant of the identity `R|X` leaf, and every entry after `S` on each of the three slots is a
  hart's whole-doubleword store of an A/D variant (`kptSlotDisc`: a pointer is never rewritten).

**What this does NOT give.**  The export's record `MachCSL.kptStateOk` keeps the sealed slots
`dyn` existentially, so the shape `dyn = kptSlots kernel_pagetable t` with `kvmTableOk t pas`
(what `MachCSL.kptOn_seal` registers at `Xv6.KptBoot`) is not visible at the final hook.
`kptTextAt_of` takes it as the hypothesis `kptTreeStateOk`; carrying it to the export needs the
record to remember the tree (`MachCSL.kptModelAt` / `kptStateOk` with `dyn = kptSlots ra t` and a
client fact on `t`) -- a MachCSL/Xv6 edit outside this leaf.

Spec: the privileged spec's Sv39 (three levels, a leaf `V ∧ (R ∨ X)`, PA = PPN ++ offset);
Svadu A/D updates are whole-PTE (`pteVariant`).  FAITHFUL: facts of xv6's table, no ISA
assumption.  Helpers are `Xv6.KptTextIdent.*`.
-/
import Xv6.SpecKvmmake
import Xv6.AccessDiscipline

namespace Xv6

open MachCSL
open AccessDiscipline (kptSealAt kptSlotDisc kptRootBytes xv6Rsv xv6StartedR_mem)

/-! ## 1. The tree -/

/-- A kernel-text virtual page: one of `kvmmake`'s seven `R|X` identity pages `0x80000 ..< 0x80007`
(the text and the trampoline's physical page). -/
def kTextVpn (vpn : BitVec 27) : Prop := 0x80000 ≤ vpn.toNat ∧ vpn.toNat < 0x80007

/-- The identity page number of `vpn`: `vpn` zero-extended (so PA = VA). -/
def kIdPpn (vpn : BitVec 27) : BitVec 44 := vpn.setWidth 44

/-- **The walk of `vpn` in `t` is the identity `R|X` walk**: the root page's slot is a pointer to
`b1`, `b1`'s slot a pointer to `b0`, `b0`'s slot the identity `R|X` leaf (some A/D). -/
def kptTextWalkT (t : PTree) (vpn : BitVec 27) : Prop :=
  ∃ (b1 b0 : BitVec 44) (a d : BitVec 1),
    (pteAddr t.base (vpnIdx vpn 2), kPtr b1) ∈ t.entries 2 ∧
    (pteAddr b1 (vpnIdx vpn 1), kPtr b0) ∈ t.entries 2 ∧
    (pteAddr b0 (vpnIdx vpn 0), kLeaf (kIdPpn vpn) .rx a d) ∈ t.entries 2

/-- A successful walk in a well-formed table passes two pointers. -/
theorem KptTextIdent.walk_path (t : PTree) (hwf : t.wf 2) (vpn : BitVec 27) (addr pv : BitVec 64)
    (h : t.walk 2 vpn = some (addr, pv)) :
    ∃ c1 g : PTree, (pteAddr t.base (vpnIdx vpn 2), kPtr c1.base) ∈ t.entries 2 ∧
      (pteAddr c1.base (vpnIdx vpn 1), kPtr g.base) ∈ t.entries 2 ∧ addr = pteAddr g.base (vpnIdx vpn 0) := by
  have e2 : t.walk 2 vpn = (match t.kids (vpnIdx vpn 2) with
      | some c => c.walk 1 vpn
      | none => if t.ents (vpnIdx vpn 2) = 0#64 then none
          else some (pteAddr t.base (vpnIdx vpn 2), t.ents (vpnIdx vpn 2))) := rfl
  have h2 := hwf (vpnIdx vpn 2)
  rw [e2] at h
  cases hk : t.kids (vpnIdx vpn 2) with
  | none =>
    rw [hk] at h h2
    simp only at h h2
    rw [if_pos h2] at h
    cases h
  | some c1 =>
    rw [hk] at h h2
    simp only at h h2
    obtain ⟨hp2, hwf1⟩ := h2
    have e1 : c1.walk 1 vpn = (match c1.kids (vpnIdx vpn 1) with
        | some c => c.walk 0 vpn
        | none => if c1.ents (vpnIdx vpn 1) = 0#64 then none
            else some (pteAddr c1.base (vpnIdx vpn 1), c1.ents (vpnIdx vpn 1))) := rfl
    have h1 := hwf1 (vpnIdx vpn 1)
    rw [e1] at h
    cases hk1 : c1.kids (vpnIdx vpn 1) with
    | none =>
      rw [hk1] at h h1
      simp only at h h1
      rw [if_pos h1] at h
      cases h
    | some g =>
      rw [hk1] at h h1
      simp only at h h1
      obtain ⟨hp1, _⟩ := h1
      have e0 : g.walk 0 vpn = if g.ents (vpnIdx vpn 0) = 0#64 then none
          else some (pteAddr g.base (vpnIdx vpn 0), g.ents (vpnIdx vpn 0)) := rfl
      rw [e0] at h
      split at h
      · cases h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        refine ⟨c1, g, ?_, ?_, h.1.symm⟩
        · rw [← hp2]; exact PTree.self_mem_entries 2 t _
        · rw [← hp1]; exact PTree.kid_mem_entries 1 t c1 _ hk _ (PTree.self_mem_entries 1 c1 _)

/-- `kvmmake`'s text region maps every kernel-text vpn to itself at `R|X`. -/
theorem kvmText_maps {t : PTree} {pas : Nat → BitVec 44} (h : kvmTableOk t pas) (vpn : BitVec 27)
    (hv : kTextVpn vpn) : t.mapsTo vpn (kIdPpn vpn) .rx := by
  have hr : t.regionMapped ⟨0x80000#27, 0x80000#44, .rx, 7⟩ :=
    h.2.2.2.1 _ (by simp only [kvmRegions, List.mem_cons]; simp)
  unfold kTextVpn at hv
  have hi := hr (vpn.toNat - 0x80000) (by show vpn.toNat - 0x80000 < 7; omega)
  have hlt := vpn.isLt
  have e1 : (0x80000#27 + BitVec.ofNat 27 (vpn.toNat - 0x80000)) = vpn := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have e2 : (0x80000#44 + BitVec.ofNat 44 (vpn.toNat - 0x80000)) = kIdPpn vpn := by
    apply BitVec.eq_of_toNat_eq
    simp only [kIdPpn, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth]
    omega
  rw [e1, e2] at hi
  exact hi

/-- **(A), the tree**: in the table `kvmmake` returns, every kernel-text vpn's walk is the identity
`R|X` walk. -/
theorem kvmText_walk {t : PTree} {pas : Nat → BitVec 44} (h : kvmTableOk t pas) (vpn : BitVec 27)
    (hv : kTextVpn vpn) : kptTextWalkT t vpn := by
  obtain ⟨addr, a, d, hw⟩ := kvmText_maps h vpn hv
  obtain ⟨c1, g, h2, h1, rfl⟩ := KptTextIdent.walk_path t h.1 vpn _ _ hw
  exact ⟨c1.base, g.base, a, d, h2, h1, PTree.walk_mem_entries 2 t vpn _ _ hw⟩

/-! ## 2. The machine -/

/-- **The sealed record, with its tree** (the hypothesis the export does not yet carry): the
sealed slots are those of a `kvmmake` table with its root word at `kernel_pagetable`, at a seal
position `S`, with the seal's facts and every slot's histories disciplined. -/
def kptTreeStateOk (σ : MState) : Prop :=
  ∃ (S : Nat) (t : PTree) (pas : Nat → BitVec 44), kvmTableOk t pas ∧
    kptSealOk xv6Rsv σ.mem σ.top S (kptSlots KA.«kernel_pagetable» t) ∧
    kptHistsAt σ.mem S (kptSlots KA.«kernel_pagetable» t)

/-- **(A), the machine: THE KERNEL TEXT TRANSLATES IDENTICALLY**: at a seal position `S` the root
word holds the root page `b` (and, `kptSealAt`, is never written after `S`); for every kernel-text
vpn the walk's three slots hold, as of `S`, the pointers to `b1`, `b0` and an A/D variant of the
identity `R|X` leaf, and every later entry on each slot is an A/D variant of it, whole. -/
def kptTextAt (σ : MState) : Prop :=
  ∃ (S : Nat) (b : BitVec 44), kptSealAt σ S ∧ wordAsOf σ.mem KA.«kernel_pagetable» S (pteAddr b 0#9) ∧
    ∀ vpn : BitVec 27, kTextVpn vpn → ∃ (b1 b0 : BitVec 44) (a d : BitVec 1),
      wordAsOf σ.mem (pteAddr b (vpnIdx vpn 2)) S (kPtr b1) ∧
      kptSlotDisc σ S (pteAddr b (vpnIdx vpn 2)) (kPtr b1) ∧
      wordAsOf σ.mem (pteAddr b1 (vpnIdx vpn 1)) S (kPtr b0) ∧
      kptSlotDisc σ S (pteAddr b1 (vpnIdx vpn 1)) (kPtr b0) ∧
      (∃ v, wordAsOf σ.mem (pteAddr b0 (vpnIdx vpn 0)) S v ∧ pteVariant (kLeaf (kIdPpn vpn) .rx a d) v) ∧
      kptSlotDisc σ S (pteAddr b0 (vpnIdx vpn 0)) (kLeaf (kIdPpn vpn) .rx a d)

/-- A doubleword's value as of `S`, from its eight histories. -/
theorem KptTextIdent.wordAsOf_of_hist {m : FlatMem} {a : PAddr} {S : Nat} {Hs : Nat → Hist}
    {v : BitVec 64} (hm : ∀ j, j < 8 → m[a + BitVec.ofNat 64 j]? = some (Hs j))
    (hh : histWordAsOf Hs S v) : wordAsOf m a S v := by
  intro j hj
  unfold FlatMem.entAsOf
  rw [hm j hj, Option.bind_some]
  exact hh j hj

/-- A sealed entry of the table: its value as of the seal (exact if frozen, a variant if a leaf)
and its discipline after the seal. -/
theorem KptTextIdent.slot_of {σ : MState} {S : Nat} {ra : PAddr} {t : PTree}
    (hh : kptHistsAt σ.mem S (kptSlots ra t)) {addr c : BitVec 64} (he : (addr, c) ∈ t.entries 2) :
    ∃ v, wordAsOf σ.mem addr S v ∧ (if (!pteLeafB c) = true then v = c else pteVariant c v) ∧
      kptSlotDisc σ S addr c := by
  obtain ⟨Hs, hm, ⟨v0, hv0, hc0⟩, hent⟩ :=
    hh ⟨addr, c, !pteLeafB c⟩ (List.mem_cons_of_mem _ (List.mem_map.2 ⟨_, he, rfl⟩))
  have hm' : ∀ j, j < 8 → σ.mem[addr + BitVec.ofNat 64 j]? = some (Hs j) := hm
  refine ⟨v0, KptTextIdent.wordAsOf_of_hist hm' hv0, hc0, ?_⟩
  intro j H e hj hH he' hSe
  rw [hm' j hj] at hH
  obtain rfl := Option.some.inj hH
  obtain ⟨_, htid, v, hv, hev, hall⟩ := hent j hj e he' hSe
  exact ⟨htid, v, hv, hev, fun j' hj' => ⟨Hs j', hm' j' hj', hall j' hj'⟩⟩

/-- A sealed pointer entry: exact as of the seal. -/
theorem KptTextIdent.ptr_of {σ : MState} {S : Nat} {ra : PAddr} {t : PTree}
    (hh : kptHistsAt σ.mem S (kptSlots ra t)) {addr : BitVec 64} {b : BitVec 44}
    (he : (addr, kPtr b) ∈ t.entries 2) :
    wordAsOf σ.mem addr S (kPtr b) ∧ kptSlotDisc σ S addr (kPtr b) := by
  obtain ⟨v, hw, hif, hd⟩ := KptTextIdent.slot_of hh he
  rw [pteLeafB_kPtr] at hif
  split at hif
  · subst hif; exact ⟨hw, hd⟩
  · rename_i hn; exact absurd rfl hn

/-- A sealed leaf entry: a variant as of the seal. -/
theorem KptTextIdent.leaf_of {σ : MState} {S : Nat} {ra : PAddr} {t : PTree}
    (hh : kptHistsAt σ.mem S (kptSlots ra t)) {addr : BitVec 64} {ppn : BitVec 44} {perm : KPerm}
    {a d : BitVec 1} (he : (addr, kLeaf ppn perm a d) ∈ t.entries 2) :
    (∃ v, wordAsOf σ.mem addr S v ∧ pteVariant (kLeaf ppn perm a d) v) ∧
      kptSlotDisc σ S addr (kLeaf ppn perm a d) := by
  obtain ⟨v, hw, hif, hd⟩ := KptTextIdent.slot_of hh he
  rw [pteLeafB_kLeaf] at hif
  split at hif
  · rename_i hn; exact absurd hn (by decide)
  · exact ⟨⟨v, hw, hif⟩, hd⟩

/-- **(A) at the machine, from the record with its tree.** -/
theorem kptTextAt_of (σ : MState) (h : kptTreeStateOk σ) : kptTextAt σ := by
  obtain ⟨S, t, pas, hkt, hok, hh⟩ := h
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
  · intro vpn hv
    obtain ⟨b1, b0, a, d, h2, h1, h0⟩ := kvmText_walk hkt vpn hv
    obtain ⟨w2, d2⟩ := KptTextIdent.ptr_of hh h2
    obtain ⟨w1, d1⟩ := KptTextIdent.ptr_of hh h1
    obtain ⟨w0, d0⟩ := KptTextIdent.leaf_of hh h0
    exact ⟨b1, b0, a, d, w2, d2, w1, d1, w0, d0⟩

end Xv6
