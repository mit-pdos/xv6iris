/-
MachCSL: **the user-epoch custody's A/D write-back arm** (W8 (f3-utext)
[OWN.89] (W-R)).

While a hart's user epoch is open (`MachCSL.uepModelAt`, opened at userret's
`csrw satp`, closed at uservec's), the interpretation holds HALF of every
slot of the user table (`MachCSL.uepCellsE`); the other half is the hart's
(the user tier's `Xv6.userInv`, the trampoline's window state).  The only
writer of a slot in the window is the hardware's A/D write-back of a LEAF,
done by the hart itself: `swp_sail_mem_write_excl_upt` is that write's rule.
The writer presents

* its half of the leaf (`ctxBytes … (3/4) w`) and the store's facts (a whole
  doubleword, `w` a leaf, the new value an A/D variant of `w`);
* its halves of the walk's two pointer slots (read only: they LOCATE the
  leaf in the record -- the record's halves of the same bytes agree, a
  frozen slot's word is its recorded value, so the walk visits the record's
  pages, `uepPageIn`);
* its `satp` cell (the record's root is the table `satp` names) and its
  privilege cell, with the witness that the epoch is open: user mode
  (`MachCSL.uepLink`: no closed record in user mode), or the kernel root's
  ghost and the root being another (`uptOpenWit`).

The rule joins the halves, appends the whole-doubleword hart store, keeps
the slot's discipline (`MachCSL.uslotHistOk`), and splits again.
-/
import MachCSL.WpPtWalkOwn
import MachCSL.UEpochSatp
import MachCSL.PteClass

namespace MachCSL

open Iris Iris.BI Iris.ProofMode Std
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

/-! ## Pure: the variants and the discipline -/

theorem uepAD_iff (c v : BitVec 64) : uepAD c v ↔ pteAD c v := Iff.rfl

theorem uepAD_refl (c : BitVec 64) : uepAD c c := pteAD_refl c

theorem uepAD_trans {u v w : BitVec 64} (h1 : uepAD u v) (h2 : uepAD v w) : uepAD u w := pteAD_trans h1 h2

theorem uepLeafB_setAD (c : BitVec 64) (a d : BitVec 1) : uepLeafB (pteSetAD c a d) = uepLeafB c := by
  unfold uepLeafB
  have h0 : (pteSetAD c a d).getLsbD 0 = c.getLsbD 0 := by
    simp only [pteSetAD, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange',
      BitVec.extractLsb, _update_PTE_Flags_A, _update_PTE_Flags_D]
    bv_decide
  have hE : ((pteSetAD c a d) &&& 0xE#64 != 0#64) = (c &&& 0xE#64 != 0#64) := by
    have : (pteSetAD c a d) &&& 0xE#64 = c &&& 0xE#64 := by
      simp only [pteSetAD, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange',
        BitVec.extractLsb, _update_PTE_Flags_A, _update_PTE_Flags_D]
      bv_decide
    rw [this]
  rw [h0, hE]

theorem uepLeafB_AD {c v : BitVec 64} (h : uepAD c v) : uepLeafB v = uepLeafB c := by
  obtain ⟨a, d, rfl⟩ := h
  exact uepLeafB_setAD c a d

/-- The heads of eight histories spell `w`. -/
def uHeads8 (Hs : Nat → Hist) (w : BitVec 64) : Prop :=
  ∀ j, j < 8 → (Hs j).head?.map HEnt.v = some (nthByte (n := 8) w j)

theorem uHeads8_unique {Hs : Nat → Hist} {w w' : BitVec 64} (h : uHeads8 Hs w) (h' : uHeads8 Hs w') :
    w = w' := by
  apply bv_eq_of_bytes (n := 8)
  intro j hj
  have := (h j hj).symm.trans (h' j hj)
  exact Option.some.inj this

/-- **The current word of a slot of the record**: frozen, its value; a leaf,
a variant of it. -/
theorem uslot_heads {K : Nat} {d : KSlot} {Hs : Nat → Hist} (hk : uslotHistOk K d Hs) {w : BitVec 64}
    (hw : uHeads8 Hs w) : if d.frozen then w = d.c else uepAD d.c w := by
  obtain ⟨-, ⟨w0, hw0, hc⟩, -⟩ := hk
  have := uHeads8_unique hw0 hw
  subst this
  exact hc

/-- **A hart's whole-doubleword A/D store of a leaf past the stamp keeps the
slot's discipline.** -/
theorem uslotHistOk_push {K : Nat} {d : KSlot} {Hs : Nat → Hist} (h : uslotHistOk K d Hs)
    (hleaf : d.frozen = false) (t : Nat) (hKt : K < t) (g : Agent) (hg : g < NCPU) (v : BitVec 64)
    (hv : uepAD d.c v) :
    uslotHistOk K d (fun j => (⟨t, g, nthByte (n := 8) v j⟩ : HEnt) :: Hs j) := by
  obtain ⟨hv0, -, hent⟩ := h
  refine ⟨fun j hj => ?_, ⟨v, fun j _ => rfl, by rw [hleaf]; exact hv⟩, fun j hj e he het => ?_⟩
  · have hn : ¬ (t ≤ K) := by omega
    simp only [List.find?_cons, hn, decide_false]
    exact hv0 j hj
  · rcases List.mem_cons.1 he with rfl | he
    · exact ⟨hleaf, hg, v, hv, rfl, fun j' _ => List.mem_cons_self⟩
    · obtain ⟨h1, h2, w, hw, hwv, hall⟩ := hent j hj e he het
      exact ⟨h1, h2, w, hw, hwv, fun j' hj' => List.mem_cons_of_mem _ (hall j' hj')⟩

/-- **The walk's path, as the writer sees it**: the root page's slot `a2`
holds a pointer to the page `p1`, whose slot `a1` holds a pointer to the
page `p0`, whose slot is `pa`. -/
def uptPathOk (root : BitVec 44) (a2 : PAddr) (v2 : BitVec 64) (a1 : PAddr) (v1 : BitVec 64) (pa : PAddr) :
    Prop :=
  (∃ i, i < 512 ∧ a2 = uepRootPA root + BitVec.ofNat 64 (8 * i)) ∧
  ∃ p1 p0 : PAddr, ptPtrTo v2 p1 ∧ (∃ i, i < 512 ∧ a1 = p1 + BitVec.ofNat 64 (8 * i)) ∧
    ptPtrTo v1 p0 ∧ ∃ i, i < 512 ∧ pa = p0 + BitVec.ofNat 64 (8 * i)

/-- What the record's halves of a slot address say of a word the writer
holds there: frozen, the slot's value; a leaf, a variant of it. -/
def uslotSees (sl : List (Nat × KSlot)) (a : PAddr) (v : BitVec 64) : Prop :=
  ∀ (l : Nat) (d : KSlot), (l, d) ∈ sl → d.addr = a → if d.frozen then v = d.c else uepAD d.c v

/-- **The record locates the leaf**: a path the record's slots agree with
ends at a level-0 LEAF slot of the record. -/
theorem uep_locate {e : UEp} (hf : uepFacts e) {a2 a1 pa : PAddr} {v2 v1 w : BitVec 64}
    (hp : uptPathOk e.root a2 v2 a1 v1 pa) (h2 : uslotSees e.slots a2 v2) (h1 : uslotSees e.slots a1 v1)
    (h0 : uslotSees e.slots pa w) (hw : uepLeafB w = true) :
    ∃ d : KSlot, (0, d) ∈ e.slots ∧ d.addr = pa ∧ d.frozen = false := by
  obtain ⟨⟨i2, hi2, ha2⟩, p1, p0, hpp1, ⟨i1, hi1, ha1⟩, hpp0, ⟨i0, hi0, ha0⟩⟩ := hp
  obtain ⟨d2, hd2, hd2a⟩ := hf.1 i2 hi2
  have hf2 := hf.2 2 d2 hd2
  have hfz2 : d2.frozen = true := hf2.2.1 (by decide)
  have hv2 := h2 2 d2 hd2 (by rw [hd2a, ha2])
  rw [hfz2, if_pos rfl] at hv2
  subst hv2
  obtain ⟨-, hpg1⟩ := hf2.2.2.2.1 p1 hpp1
  obtain ⟨d1, hd1, hd1a⟩ := hpg1 i1 hi1
  have hf1 := hf.2 1 d1 hd1
  have hfz1 : d1.frozen = true := hf1.2.1 (by decide)
  have hv1 := h1 1 d1 hd1 (by rw [hd1a, ha1])
  rw [hfz1, if_pos rfl] at hv1
  subst hv1
  obtain ⟨-, hpg0⟩ := hf1.2.2.2.1 p0 hpp0
  obtain ⟨d0, hd0, hd0a⟩ := hpg0 i0 hi0
  refine ⟨d0, hd0, by rw [hd0a, ha0], ?_⟩
  have hf0 := hf.2 0 d0 hd0
  cases hz : d0.frozen with
  | false => rfl
  | true =>
    exfalso
    have hv0 := h0 0 d0 hd0 (by rw [hd0a, ha0])
    rw [hz, if_pos rfl] at hv0
    subst hv0
    have := hf0.1
    rw [hz, hw] at this
    exact absurd this (by decide)

/-- An entry address is a page address plus eight times the index. -/
theorem pteAddr_rootPA (b : BitVec 44) (i : BitVec 9) :
    pteAddr b i = uepRootPA b + BitVec.ofNat 64 (8 * i.toNat) := by
  have hi := i.isLt
  have e : BitVec.ofNat 64 (8 * i.toNat) = BitVec.setWidth 64 i <<< 3 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth]
    rw [Nat.shiftLeft_eq, Nat.mod_eq_of_lt (a := i.toNat) (by omega)]
    omega
  rw [e]
  unfold pteAddr uepRootPA zero_extend Sail.BitVec.zeroExtend
  bv_decide

/-- A pointer entry points at its page. -/
theorem kPtr_ptPtrTo (b : BitVec 44) : ptPtrTo (kPtr b) (uepRootPA b) := by
  unfold ptPtrTo kPtr mkPte ptrFlags uepRootPA
  refine ⟨by bv_decide, by bv_decide, by bv_decide⟩

theorem uepLeafB_kPtr (b : BitVec 44) : uepLeafB (kPtr b) = false := by
  have h : (kPtr b) &&& 0xE#64 = 0#64 := by unfold kPtr mkPte ptrFlags; bv_decide
  unfold uepLeafB; rw [h]; simp

/-- The path a walk of `vpn` through the pointer entries `kPtr b1`, `kPtr b0`
takes is one the record can locate. -/
theorem uptPath_of (root b1 b0 : BitVec 44) (vpn : BitVec 27) :
    uptPathOk root (pteAddr root (vpnIdx vpn 2)) (kPtr b1) (pteAddr b1 (vpnIdx vpn 1)) (kPtr b0)
      (pteAddr b0 (vpnIdx vpn 0)) :=
  ⟨⟨(vpnIdx vpn 2).toNat, (vpnIdx vpn 2).isLt, pteAddr_rootPA _ _⟩, uepRootPA b1, uepRootPA b0, kPtr_ptPtrTo _,
    ⟨(vpnIdx vpn 1).toNat, (vpnIdx vpn 1).isLt, pteAddr_rootPA _ _⟩, kPtr_ptPtrTo _,
    ⟨(vpnIdx vpn 0).toNat, (vpnIdx vpn 0).isLt, pteAddr_rootPA _ _⟩⟩

section iris
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF]

/-- **The open-epoch witness** of a hart at privilege `p` with root `r`:
user mode, or the kernel root's ghost and `r` being another (outside
machine mode). -/
def uptOpenWit (r : BitVec 44) (p : Privilege) : IProp GF :=
  iprop(⌜p = Privilege.User⌝ ∨ ∃ kroot : BitVec 44,
    (MachGS.kptRootName (hlc := hlc) (GF := GF) ↪VAR{.discard} kroot) ∗ ⌜r ≠ kroot ∧ p ≠ Privilege.Machine⌝)

instance (r : BitVec 44) (p : Privilege) : Persistent (PROP := IProp GF) (uptOpenWit r p) := by
  unfold uptOpenWit; infer_instance

/-- One slot's cell of the record (`MachCSL.uepCellsE`'s summand). -/
abbrev uslotCell (K : Nat) (p : Nat × KSlot) : IProp GF := iprop%
  ∃ Hs : Nat → Hist,
    ([∗list] j ∈ List.range 8, pointsTo (G := (MachGS.era (hlc := hlc) (GF := GF)).mem)
      (p.2.addr + BitVec.ofNat 64 j) (DFrac.own Qp.quarter) (Hs j)) ∗ ⌜uslotHistOk K p.2 Hs⌝

/-- Two holdings of the same window agree on the histories. -/
theorem histBytes_agree (pa : PAddr) (dqs dqs' : Nat → DFrac) (Hs Hs' : Nat → Hist) : ∀ n : Nat,
    ([∗list] j ∈ List.range n, (pa + BitVec.ofNat 64 j) ↦ₕ{dqs j} Hs j) ∗
      ([∗list] j ∈ List.range n, (pa + BitVec.ofNat 64 j) ↦ₕ{dqs' j} Hs' j) ⊢@{IProp GF}
      ⌜∀ j, j < n → Hs j = Hs' j⌝ ∗
      ([∗list] j ∈ List.range n, (pa + BitVec.ofNat 64 j) ↦ₕ{dqs j} Hs j) ∗
      ([∗list] j ∈ List.range n, (pa + BitVec.ofNat 64 j) ↦ₕ{dqs' j} Hs' j)
  | 0 => by
    iintro ⟨H1, H2⟩
    iframe H1 H2
    ipureintro
    intro j hj
    omega
  | n + 1 => by
    rw [List.range_succ]
    iintro ⟨H1, H2⟩
    icases BigSepL.bigSepL_snoc.1 $$ H1 with ⟨H1, A1⟩
    icases BigSepL.bigSepL_snoc.1 $$ H2 with ⟨H2, A2⟩
    icases histBytes_agree pa dqs dqs' Hs Hs' n $$ [H1 H2] with ⟨%h, H1, H2⟩
    · iframe H1 H2
    ihave %hn := pointsTo_agree $$ [A1 A2]
    · iframe A1 A2
    isplitr
    · ipureintro
      intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h' | rfl
      · exact h j h'
      · exact hn
    isplitl [H1 A1]
    · iapply BigSepL.bigSepL_snoc.2
      iframe
    · iapply BigSepL.bigSepL_snoc.2
      iframe

/-- **The record's half of a slot and the writer's word there agree.** -/
theorem uslotCell_sees (K : Nat) (p : Nat × KSlot) (ξ : CtxId) (dq : DFrac) (v : BitVec 64) :
    uslotCell (GF := GF) K p ∗ ctxBytes ξ p.2.addr 8 dq v ⊢
      ⌜if p.2.frozen then v = p.2.c else uepAD p.2.c v⌝ ∗ uslotCell K p ∗ ctxBytes ξ p.2.addr 8 dq v := by
  iintro ⟨⟨%Hs, Hh, %hk⟩, Hb⟩
  unfold ctxBytes
  icases ctxBytes_hist ξ p.2.addr dq (nthByte (n := 8) v) 8 $$ Hb with ⟨%Hs', Hh', %hh', Wb⟩
  icases histBytes_agree p.2.addr (fun _ => DFrac.own Qp.quarter) (fun _ => dq) Hs Hs' 8 $$ [Hh Hh']
    with ⟨%hag, Hh, Hh'⟩
  · iframe Hh Hh'
  have hw : uHeads8 Hs v := fun j hj => by rw [hag j hj]; exact (hh' j hj).2
  isplitr
  · ipureintro; exact uslot_heads hk hw
  isplitl [Hh]
  · iexists Hs
    iframe Hh
    ipureintro; exact hk
  · iapply Wb $$ Hh'

/-- **The record's slots and the writer's word at an address agree.** -/
theorem uslotCells_sees (K : Nat) (ξ : CtxId) (a : PAddr) (dq : DFrac) (v : BitVec 64) :
    ∀ sl : List (Nat × KSlot),
    ([∗list] p ∈ sl, uslotCell (GF := GF) K p) ∗ ctxBytes ξ a 8 dq v ⊢
      ⌜uslotSees sl a v⌝ ∗ ([∗list] p ∈ sl, uslotCell K p) ∗ ctxBytes ξ a 8 dq v
  | [] => by
    iintro ⟨H, Hb⟩
    iframe H Hb
    ipureintro
    intro l d h
    cases h
  | q :: sl => by
    iintro ⟨H, Hb⟩
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨Hq, H⟩
    icases uslotCells_sees K ξ a dq v sl $$ [H Hb] with ⟨%hsl, H, Hb⟩
    · iframe H Hb
    by_cases ha : q.2.addr = a
    · subst ha
      icases uslotCell_sees K q ξ dq v $$ [Hq Hb] with ⟨%hq, Hq, Hb⟩
      · iframe Hq Hb
      iframe Hb
      isplitr
      · ipureintro
        intro l d hd hda
        rcases List.mem_cons.1 hd with rfl | hd
        · exact hq
        · exact hsl l d hd hda
      iapply BigSepL.bigSepL_cons.2
      iframe
    · iframe Hb
      isplitr
      · ipureintro
        intro l d hd hda
        rcases List.mem_cons.1 hd with rfl | hd
        · exact absurd hda ha
        · exact hsl l d hd hda
      iapply BigSepL.bigSepL_cons.2
      iframe

/-- The record's quarter and the writer's three quarters of a window are the
whole. -/
theorem histBytes_join (pa : PAddr) (n : Nat) (Hs : Nat → Hist) :
    histBytes pa n (fun _ => DFrac.own Qp.quarter) Hs ∗ histBytes pa n (fun _ => DFrac.own Qp.threeQuarters) Hs
      ⊢@{IProp GF} histBytes pa n (fun _ => DFrac.own 1) Hs := by
  unfold histBytes
  iintro ⟨H1, H2⟩
  ihave H := (BigSepL.bigSepL_sep_eqv
    (Φ := fun _ (j : Nat) => iprop((pa + BitVec.ofNat 64 j) ↦ₕ{DFrac.own Qp.quarter} Hs j))
    (Ψ := fun _ (j : Nat) => iprop((pa + BitVec.ofNat 64 j) ↦ₕ{DFrac.own Qp.threeQuarters} Hs j))
    (l := List.range n)).2 $$ [H1 H2]
  · iframe
  iapply BigSepL.bigSepL_mono_of_forall _ $$ H
  intro _ j
  have h := pointsTo_combine (GF := GF) (L := PAddr) (V := Hist) (H := MemF)
    (l := pa + BitVec.ofNat 64 j) (dq₁ := DFrac.own Qp.quarter) (dq₂ := DFrac.own Qp.threeQuarters)
    (v₁ := Hs j) (v₂ := Hs j)
  rw [DFrac.op_own, Qp.quarter_add_threeQuarters] at h
  refine h.trans ?_
  iintro ⟨H, _⟩
  iexact H

/-- ...and back. -/
theorem histBytes_split (pa : PAddr) (n : Nat) (Hs : Nat → Hist) :
    histBytes pa n (fun _ => DFrac.own 1) Hs ⊢@{IProp GF}
      histBytes pa n (fun _ => DFrac.own Qp.quarter) Hs ∗ histBytes pa n (fun _ => DFrac.own Qp.threeQuarters) Hs := by
  unfold histBytes
  refine .trans (BigSepL.bigSepL_mono_of_forall
    (Ψ := fun _ (j : Nat) => iprop(((pa + BitVec.ofNat 64 j) ↦ₕ{DFrac.own Qp.quarter} Hs j) ∗
      ((pa + BitVec.ofNat 64 j) ↦ₕ{DFrac.own Qp.threeQuarters} Hs j))) ?_)
    BigSepL.bigSepL_sep_eqv.1
  intro _ j
  have h := (Fractional.fractional (Φ := fun q => iprop((pa + BitVec.ofNat 64 j) ↦ₕ{DFrac.own q} Hs j))
    Qp.quarter Qp.threeQuarters)
  rw [Qp.quarter_add_threeQuarters] at h
  exact h.1

/-- A pushed window, at the new store's key, is the writer's bytes. -/
theorem uepCtxBytes_of_pushed (ξ : CtxId) (pa : PAddr) (n : Nat) (dq : DFrac) (Hs : Nat → Hist) (t : Nat)
    (g : Agent) (w : BitVec (8 * n)) :
    keyAt (MachGS.era (hlc := hlc) (GF := GF)) ξ t ∗ histBytes pa n (fun _ => dq) (pushed Hs t g w) ⊢@{IProp GF}
      ctxBytes ξ pa n dq w := by
  unfold histBytes ctxBytes
  iintro ⟨#Hk, H⟩
  iapply BigSepL.bigSepL_impl $$ H
  imodintro
  iintro %k %j %_ Hj
  unfold ctxByte
  iexists ⟨t, g, nthByte w j⟩, Hs j
  iframe Hj Hk
  ipureintro; rfl

/-- The record's stamp is at or below the hart's instruction view. -/
theorem memModel_iviewLbE (σ : MState) (cpu : CPU) (K : Nat) :
    memModel σ ∗ MonoNat.lb_own ((MachGS.era (hlc := hlc) (GF := GF)).iviewName cpu) (.ofNat K) ⊢@{IProp GF}
      ⌜K ≤ σ.itv cpu⌝ := by
  unfold memModel memModelAt
  iintro ⟨⟨_, _, Hviews, _⟩, Hlb⟩
  icases BigSepL.bigSepL_lookup_acc_impl (Φ := fun _ c => hartViewsAt (MachGS.era (hlc := hlc) (GF := GF)) σ c)
    (cpus_get? cpu) $$ Hviews with ⟨Hc, _⟩
  icases hartViewsAt_cases _ σ cpu $$ Hc with ⟨_, Hv, _⟩
  ihave %Hv := MonoNat.auth_lb_own_valid $$ Hv Hlb
  ipureintro
  have := Hv.2
  simpa [MaxNat.le_toNat] using this

/-- **The interpretation's registers, memory, memory model and user-epoch
record**, the record put back at any state that keeps every other hart's
registers and the devices. -/
theorem machInterp_acc_memU (σ : MState) (cpu : CPU) :
    machInterp (GF := GF) σ ⊢
      regInterp cpu (σ.regs cpu) ∗ genHeapInterp σ.mem ∗ memModel σ ∗ uepModel σ ∗
      ∀ (σ' : MState), ⌜(∀ c, c ≠ cpu → σ'.regs c = σ.regs c) ∧ σ'.devs = σ.devs⌝ -∗
        regInterp cpu (σ'.regs cpu) -∗ genHeapInterp σ'.mem -∗ memModel σ' -∗ uepModel σ' -∗
        machInterp σ' := by
  have hget := cpus_get? cpu
  unfold machInterp
  iintro ⟨Hregs, Hmem, Hmm, Hdev, Huep⟩
  iframe Hmem Hmm Huep
  icases BigSepL.bigSepL_lookup_acc_impl (Φ := fun _ c => regInterp c (σ.regs c)) hget $$ Hregs
    with ⟨Hcpu, Hclose⟩
  iframe Hcpu
  iintro %σ' %hσ' Hf Hmem Hmm Huep
  iframe Hmem Hmm Huep
  ihave Hdev := (show devInterp (GF := GF) σ.devs ⊢ devInterp σ'.devs from by rw [hσ'.2]) $$ Hdev
  iframe Hdev
  iapply Hclose $$ %(fun _ c => regInterp c (σ'.regs c))
  · imodintro
    iintro %k %y %hk %hne Hy
    have hy : y ≠ cpu := cpus_get?_ne hk cpu hne
    simp only [hσ'.1 y hy]
    iexact Hy
  · iexact Hf

/-- `ctxBytes` as its histories (the window form of `ctxBytes_hist`). -/
theorem ctxBytes_histW (ξ : CtxId) (pa : PAddr) (n : Nat) (dq : DFrac) (w : BitVec (8 * n)) :
    ctxBytes (GF := GF) ξ pa n dq w ⊢ ∃ Hs : Nat → Hist, histBytes pa n (fun _ => dq) Hs ∗
      ⌜∀ j, j < n → Hs j ≠ [] ∧ (Hs j).head?.map HEnt.v = some (nthByte w j)⌝ ∗
      (histBytes pa n (fun _ => dq) Hs -∗ ctxBytes ξ pa n dq w) := by
  unfold ctxBytes histBytes
  exact ctxBytes_hist ξ pa dq (nthByte w) n

/-- Only the window's histories matter. -/
theorem uepHistBytes_congr (pa : PAddr) (n : Nat) (dqs : Nat → DFrac) {Hs Hs' : Nat → Hist}
    (h : ∀ j, j < n → Hs j = Hs' j) :
    histBytes (GF := GF) pa n dqs Hs ⊢ histBytes pa n dqs Hs' := by
  unfold histBytes
  apply BigSepL.bigSepL_mono
  intro k j hk
  have hj : j < n := List.mem_range.1 (List.mem_of_getElem? hk)
  rw [h j hj]

/-- The two holdings of a window agree (the `histBytes` form). -/
theorem histBytes_agreeH (pa : PAddr) (n : Nat) (dqs dqs' : Nat → DFrac) (Hs Hs' : Nat → Hist) :
    histBytes (GF := GF) pa n dqs Hs ∗ histBytes pa n dqs' Hs' ⊢
      ⌜∀ j, j < n → Hs j = Hs' j⌝ ∗ histBytes pa n dqs Hs ∗ histBytes pa n dqs' Hs' := by
  unfold histBytes
  exact histBytes_agree pa dqs dqs' Hs Hs' n

/-- A slot cell, opened at its address. -/
theorem uslotCell_open (K : Nat) (p : Nat × KSlot) (a : PAddr) (ha : p.2.addr = a) :
    uslotCell (GF := GF) K p ⊢ ∃ Hs : Nat → Hist, histBytes a 8 (fun _ => DFrac.own Qp.quarter) Hs ∗
      ⌜uslotHistOk K p.2 Hs⌝ := by
  obtain ⟨l, d⟩ := p
  simp only at ha
  subst ha
  iintro ⟨%Hs, H, %hk⟩
  iexists Hs
  unfold histBytes
  iframe H
  ipureintro; exact hk

theorem uslotCell_close (K : Nat) (p : Nat × KSlot) (a : PAddr) (ha : p.2.addr = a) (Hs : Nat → Hist)
    (hk : uslotHistOk K p.2 Hs) :
    histBytes (GF := GF) a 8 (fun _ => DFrac.own Qp.quarter) Hs ⊢ uslotCell K p := by
  obtain ⟨l, d⟩ := p
  simp only at ha
  subst ha
  iintro H
  iexists Hs
  unfold histBytes at *
  iframe H
  ipureintro; exact hk

set_option maxHeartbeats 4000000 in
/-- **THE A/D WRITE-BACK OF A LEAF OF AN OPEN EPOCH'S TABLE** (W8 (f3-utext)):
the write half of the walker's exclusive pair on a slot the interpretation
holds half of.  The writer's half of the leaf, the walk's pointer slots (to
locate the leaf in the record), its `satp` and privilege cells and the
open-epoch witness; the store a whole doubleword, the old word a leaf, the
new one an A/D variant of it. -/
theorem swp_sail_mem_write_excl_upt (cpu : CPU) {vasize : Nat}
    (req : Mem_write_request 8 vasize Arch.pa Arch.translation Arch.arch_ak)
    (ξ : CtxId) (r : Option Resv) (w w' : BitVec 64) (hv : req.value = some w')
    (hk : akExcl req.access_kind = true) (hleaf : uepLeafB w = true) (had : uepAD w w')
    (root : BitVec 44) (s : BitVec 64) (hs : satpTable s = some root) (p : Privilege)
    (dqs dqp dq2 dq1 : DFrac) (a2 a1 : PAddr) (v2 v1 : BitVec 64)
    (hpath : uptPathOk root a2 v2 a1 v1 req.pa)
    (Φ : Result (Option Bool) Arch.abort → IProp GF) :
    ownCtx cpu ξ ∗ resvFragAny cpu r ∗ ctxBytes ξ req.pa 8 (DFrac.own Qp.threeQuarters) w ∗
    ctxBytes ξ a2 8 dq2 v2 ∗ ctxBytes ξ a1 8 dq1 v1 ∗
    Register.satp ↦ᵣ[cpu]{dqs} s ∗ Register.cur_privilege ↦ᵣ[cpu]{dqp} p ∗ uptOpenWit root p ∗
    ▷ (ownCtx cpu ξ -∗ resvFrag cpu none false -∗ ctxBytes ξ req.pa 8 (DFrac.own Qp.threeQuarters) w' -∗
        ctxBytes ξ a2 8 dq2 v2 -∗ ctxBytes ξ a1 8 dq1 v1 -∗
        Register.satp ↦ᵣ[cpu]{dqs} s -∗ Register.cur_privilege ↦ᵣ[cpu]{dqp} p -∗ Φ (.Ok (some true)))
    ⊢ swp cpu (ConcurrencyInterfaceV1.sail_mem_write req) Φ := by
  unfold ConcurrencyInterfaceV1.sail_mem_write PreSail.sail_mem_write PreSail.emit
  iintro ⟨Hctx, Hfrag, Hb, H2, H1, Hs, Hp, #Hw, HΦ⟩
  iloeb as IH
  iapply swp_event_step cpu (.memWrite 8 vasize req) (fun v => FreeM.pure v) Φ
  iintro %σ Hσ
  icases machInterp_acc_memU σ cpu $$ Hσ with ⟨Hregs, Hmem, Hmm, Huep, Hclose⟩
  ihave %hsv : ⌜σ.regs cpu Register.satp = s⌝ $$ [Hregs Hs]
  · icases reg_valid cpu (σ.regs cpu) Register.satp dqs s $$ [$Hregs $Hs] with %_
    itrivial
  ihave %hpv : ⌜σ.regs cpu Register.cur_privilege = p⌝ $$ [Hregs Hp]
  · icases reg_valid cpu (σ.regs cpu) Register.cur_privilege dqp p $$ [$Hregs $Hp] with %_
    itrivial
  icases uepModelAt_acc _ σ cpu $$ Huep with ⟨%k, #Hk, Hc, HcloseU⟩
  unfold uepHartAt
  icases Hc with ⟨%oe, %hl, Hcells⟩
  have hl' := hl
  rw [hsv, hpv] at hl'
  ihave %hoe : ⌜∃ e, oe = some e⌝ $$ [Hk Hw]
  · unfold uptOpenWit
    icases Hw with (%hU | ⟨%kroot, #Hkr, %⟨hne, hpm⟩⟩)
    · ipureintro
      cases oe with
      | none => exact absurd hU (hl'.2 rfl).1
      | some e => exact ⟨e, rfl⟩
    · ihave %hkk := uepKsatAt_agree _ k kroot $$ [Hk Hkr]
      · iframe Hk Hkr
      ipureintro
      cases oe with
      | none => exact (uepLink_none_ne hl' hpm hs (fun rk h => by rw [hkk rk h]; exact hne)).elim
      | some e => exact ⟨e, rfl⟩
  obtain ⟨e, rfl⟩ := hoe
  have her : e.root = root := by
    have := uepLink_some_root hl'
    rw [hs] at this
    exact (Option.some.inj this).symm
  rw [uepCellsAt_some]
  unfold uepCellsE
  icases Hcells with ⟨%hf, #Hiv, Htext, Hslots⟩
  rw [← her] at hpath
  icases uslotCells_sees e.K ξ a2 dq2 v2 e.slots $$ [Hslots H2] with ⟨%h2, Hslots, H2⟩
  · iframe Hslots H2
  icases uslotCells_sees e.K ξ a1 dq1 v1 e.slots $$ [Hslots H1] with ⟨%h1, Hslots, H1⟩
  · iframe Hslots H1
  icases uslotCells_sees e.K ξ req.pa _ w e.slots $$ [Hslots Hb] with ⟨%h0, Hslots, Hb⟩
  · iframe Hslots Hb
  obtain ⟨d0, hd0, hd0a, hd0f⟩ := uep_locate hf hpath h2 h1 h0 hleaf
  icases BigSepL.bigSepL_mem_acc (Φ := uslotCell e.K) hd0 $$ Hslots with ⟨Hd0, HslotsC⟩
  icases uslotCell_open e.K (0, d0) req.pa hd0a $$ Hd0 with ⟨%Hs0, Hh0, %hk0⟩
  icases ctxBytes_histW ξ req.pa 8 _ w $$ Hb with ⟨%Hs', Hh', %hh', Wb⟩
  icases histBytes_agreeH req.pa 8 _ _ Hs0 Hs' $$ [Hh0 Hh'] with ⟨%hag, Hh0, Hh'⟩
  · iframe Hh0 Hh'
  have hw0 : uHeads8 Hs0 w := fun j hj => by rw [hag j hj]; exact (hh' j hj).2
  have hvar : uepAD d0.c w := by
    have := uslot_heads hk0 hw0
    rw [hd0f] at this
    exact this
  have hvar' : uepAD d0.c w' := uepAD_trans hvar had
  ihave %hmm : ⌜mmOk σ⌝ $$ [Hmm]
  · iapply memModel_mmOk $$ Hmm
  ihave %hget : ⌜histsAt σ.mem req.pa 8 Hs0⌝ $$ [Hmem Hh0]
  · iapply histBytes_valid σ.mem req.pa 8 _ Hs0 $$ [Hmem Hh0]
    iframe
  have hram : ramBytes req.pa 8 := ramBytes_of_cells hmm.2.2.2.1 (fun j hj => ⟨Hs0 j, hget j hj⟩)
  ihave %hK : ⌜e.K ≤ σ.itv cpu⌝ $$ [Hmm Hiv]
  · iapply memModel_iviewLbE σ cpu e.K $$ [Hmm Hiv]
    iframe Hmm
    iexact Hiv
  have hitv := (hmm.2.1 cpu).2.1
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hmask
  isplit
  · ipureintro
    by_cases hno : othersReserve σ.resv cpu req.pa 8 ∨ ¬ σ.landNowOk cpu req.pa 8 req.access_kind
    · exact Or.inr ⟨σ, hno.imp id (fun h => ⟨hram, h⟩), rfl⟩
    · exact Or.inl ⟨.Ok (some true), _, Or.inr ⟨hram, w', hv, fun h => hno (Or.inl h),
        Classical.byContradiction (fun h => hno (Or.inr h)), rfl, rfl⟩⟩
  inext
  iintro %σ'
  isplit
  · iintro %v %Hev
    rcases Hev with ⟨hdev, w₀, ds₀, _, hdw, _, _⟩ | ⟨_, w'', hv', hno, _, rfl, rfl⟩
    · exact absurd hdev (not_devBytes_of_ramBytes hram (devWrite_pos hdw))
    rw [hv] at hv'
    obtain rfl := Option.some.inj hv'
    ihave Hh' := uepHistBytes_congr req.pa 8 _ (fun j hj => (hag j hj).symm) $$ Hh'
    ihave Hfull := histBytes_join req.pa 8 Hs0 $$ [Hh0 Hh']
    · iframe Hh0 Hh'
    ihave %hnr := memModel_notRsv_hist σ req.pa Hs0 8 $$ [Hmm Hfull]
    · iframe
    imod ctx_store_excl σ cpu ξ req.pa 8 w' r hram hno hnr $$ [$Hmm $Hctx $Hfrag] with ⟨Hmm, Hctx, Hfrag, #Hkey⟩
    imod histBytes_update σ.mem req.pa 8 Hs0 (σ.top + 1) (hartAgent cpu) w' $$ [$Hmem $Hfull] with ⟨Hmem, Hfull⟩
    icases histBytes_split req.pa 8 _ $$ Hfull with ⟨HhR, HhC⟩
    have hk0' : uslotHistOk e.K d0 (pushed (n := 8) Hs0 (σ.top + 1) (hartAgent cpu) w') :=
      uslotHistOk_push hk0 hd0f (σ.top + 1) (by omega) (hartAgent cpu) cpu.isLt w' hvar'
    ihave Hb := uepCtxBytes_of_pushed ξ req.pa 8 _ Hs0 (σ.top + 1) (hartAgent cpu) w' $$ [HhC]
    · iframe Hkey HhC
    ihave Hd0 := uslotCell_close e.K (0, d0) req.pa hd0a _ hk0' $$ HhR
    ihave Hslots := HslotsC $$ Hd0
    ihave Huep := HcloseU $$ %(σ.store cpu req.pa 8 w' true) %k
      %⟨fun c _ => ⟨rfl, rfl⟩, fun _ => Nat.le_refl _, Or.inl rfl⟩ Hk [Htext Hslots]
    · iexists some e
      isplitr
      · ipureintro; exact hl
      rw [uepCellsAt_some]
      unfold uepCellsE
      iframe Hiv Htext Hslots
      ipureintro; exact hf
    imod Hmask
    imodintro
    rw [hk]
    isplitl [Hregs Hmem Hmm Huep Hclose]
    · iapply Hclose $$ %(σ.store cpu req.pa 8 w' true) %⟨fun _ _ => rfl, rfl⟩ Hregs Hmem Hmm Huep
    · iapply swp_ret
      iapply HΦ $$ Hctx Hfrag Hb H2 H1 Hs Hp
  · iintro %Hbk
    obtain ⟨_, hσ⟩ := Hbk
    subst σ'
    ihave Hb := Wb $$ Hh'
    ihave Hd0 := uslotCell_close e.K (0, d0) req.pa hd0a _ hk0 $$ Hh0
    ihave Hslots := HslotsC $$ Hd0
    ihave Huep := HcloseU $$ %σ %k %⟨fun c _ => ⟨rfl, rfl⟩, fun _ => Nat.le_refl _, Or.inl rfl⟩ Hk [Htext Hslots]
    · iexists some e
      isplitr
      · ipureintro; exact hl
      rw [uepCellsAt_some]
      unfold uepCellsE
      iframe Hiv Htext Hslots
      ipureintro; exact hf
    imod Hmask
    imodintro
    isplitl [Hregs Hmem Hmm Huep Hclose]
    · iapply Hclose $$ %σ %⟨fun _ _ => rfl, rfl⟩ Hregs Hmem Hmm Huep
    · iapply IH $$ Hctx Hfrag Hb H2 H1 Hs Hp
      inext
      iexact HΦ

end iris

end MachCSL
