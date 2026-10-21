/-
**The user epoch's opening deposit** (W8 (f3-utext) [OWN.89] (W-R), the
[OWN.78] USER restatement): at `userret`'s `fence.i` the text pages AND the
table's slots are stamped at the raised instruction view `K`
(`MachCSL.ifenceStep_stamp`); at its `csrw satp` each stamped byte splits
into the user tier's three quarters (`uCustQ`: the table back as
`uptFrameH`, the text as the stamped `ukOwnX … uCustQ`) and the quarter the
interpretation's record takes (`MachCSL.uepPreE`: every history headed at or
below `K`).

The record names the epoch's table by its slots, LEVEL-TAGGED
(`PTree.lentries`, `uptSlots`), and its text by the text pages' addresses
(`ukTextAddrs`); `uepOf_facts` is the record's shape (`MachCSL.uepFacts`):
the root page's slots at level 2, pointers naming whole pages of the next
level, a user text leaf (`U`, `X`, not `W`) mapping a text page of the
process.
-/
import Xv6.UkOpen
import Xv6.TransPt
import MachCSL.UEpochSatp

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Std MachCSL
open Iris.Std.PartialMap Iris.Std.FiniteMap
open LeanRV64D LeanRV64D.Functions

/-! ## §1 The level-tagged entries -/

/-- Every entry of every node page, tagged with its node's level. -/
def _root_.MachCSL.PTree.lentries : Nat → PTree → List (Nat × (BitVec 64 × BitVec 64))
  | 0, t => allIdx.map fun i => (0, (pteAddr t.base i, t.ents i))
  | lvl+1, t => (allIdx.map fun i => (lvl+1, (pteAddr t.base i, t.ents i))) ++
      allIdx.flatMap fun i => match t.kids i with | some c => c.lentries lvl | none => []

set_option maxRecDepth 10000 in
theorem lentries_snd : ∀ (lvl : Nat) (t : PTree), (t.lentries lvl).map Prod.snd = t.entries lvl
  | 0, t => by
    simp only [PTree.lentries, PTree.entries, List.map_map]
    rfl
  | lvl + 1, t => by
    simp only [PTree.lentries, PTree.entries, List.map_append, List.map_map, List.map_flatMap]
    congr 1
    refine congrArg (fun f => allIdx.flatMap f) (funext fun i => ?_)
    cases h : t.kids i with
    | none => rfl
    | some c => exact lentries_snd lvl c

theorem lentries_self (lvl : Nat) (t : PTree) (i : BitVec 9) :
    (lvl, (pteAddr t.base i, t.ents i)) ∈ t.lentries lvl := by
  cases lvl with
  | zero => simp only [PTree.lentries, List.mem_map]; exact ⟨i, mem_allIdx i, rfl⟩
  | succ l =>
    simp only [PTree.lentries, List.mem_append, List.mem_map]
    exact Or.inl ⟨i, mem_allIdx i, rfl⟩

theorem lentries_kid (lvl : Nat) (t c : PTree) (i : BitVec 9) (h : t.kids i = some c)
    (x : Nat × (BitVec 64 × BitVec 64)) (hx : x ∈ c.lentries lvl) : x ∈ t.lentries (lvl + 1) := by
  simp only [PTree.lentries, List.mem_append, List.mem_flatMap]
  exact Or.inr ⟨i, mem_allIdx i, by rw [h]; exact hx⟩

/-- **An entry's node**: every tagged entry is entry `i` of a node of its
level, well formed there, whose own tagged entries are the table's. -/
theorem lentries_shape : ∀ (lvl : Nat) (t : PTree), t.wfU lvl →
    ∀ x ∈ t.lentries lvl, ∃ (c : PTree) (i : BitVec 9), x.2 = (pteAddr c.base i, c.ents i) ∧
      c.wfU x.1 ∧ ∀ y ∈ c.lentries x.1, y ∈ t.lentries lvl
  | 0, t, hwf, x, hx => by
    simp only [PTree.lentries, List.mem_map] at hx
    obtain ⟨i, -, rfl⟩ := hx
    exact ⟨t, i, rfl, hwf, fun y hy => hy⟩
  | lvl + 1, t, hwf, x, hx => by
    simp only [PTree.lentries, List.mem_append, List.mem_map, List.mem_flatMap] at hx
    rcases hx with ⟨i, -, rfl⟩ | ⟨i, -, hm⟩
    · exact ⟨t, i, rfl, hwf, fun y hy => hy⟩
    · have hi := hwf i
      cases hk : t.kids i with
      | none => rw [hk] at hm; cases hm
      | some c =>
        rw [hk] at hm hi
        obtain ⟨c', i', h1, h2, h3⟩ := lentries_shape lvl c hi.2 x hm
        exact ⟨c', i', h1, h2, fun y hy => lentries_kid lvl t c i hk y (h3 y hy)⟩

/-! ## §2 The epoch's record of a table -/

/-- **The table's slots, level-tagged** (the record's `slots`): every entry,
frozen exactly when it is no leaf. -/
def uptSlots (t : PTree) : List (Nat × KSlot) :=
  (t.lentries 2).map fun x => (x.1, (⟨x.2.1, x.2.2, !uepLeafB x.2.2⟩ : KSlot))

/-- **The epoch a `userret` opens** at stamp `K` over the table `t` of `P`. -/
def uepOf (P : UPtd) (t : PTree) (K : Nat) : UEp := ⟨P.root, K, uptSlots t, ukTextAddrs P.um⟩

theorem uptSlots_page (t : PTree) (lvl : Nat) (c : PTree)
    (hc : ∀ i : BitVec 9, (lvl, (pteAddr c.base i, c.ents i)) ∈ t.lentries 2) :
    uepPageIn (uptSlots t) lvl (pteAddr c.base 0#9) := by
  intro i hi
  refine ⟨⟨pteAddr c.base (BitVec.ofNat 9 i), c.ents (BitVec.ofNat 9 i),
    !uepLeafB (c.ents (BitVec.ofNat 9 i))⟩, List.mem_map.2 ⟨_, hc _, rfl⟩, ?_⟩
  have h := KptInv.pteAddr_off c.base (BitVec.ofNat 9 i)
  have hi' : (BitVec.ofNat 9 i).toNat = i := by simp; omega
  rw [hi'] at h
  exact h

/-- `A`/`D` variants agree on `V`, `R`, `W`, `X`, `U`. -/
theorem pteAD_low {c v : BitVec 64} (h : pteAD c v) :
    v.getLsbD 0 = c.getLsbD 0 ∧ v &&& 0xE#64 = c &&& 0xE#64 ∧ v.getLsbD 2 = c.getLsbD 2 ∧
      v.getLsbD 3 = c.getLsbD 3 ∧ v.getLsbD 4 = c.getLsbD 4 := by
  obtain ⟨a, d, rfl⟩ := h
  simp only [pteSetAD, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange',
    BitVec.extractLsb, _update_PTE_Flags_A, _update_PTE_Flags_D]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> bv_decide

/-- A leaf's page is its PPN's. -/
theorem uepLeafPA_pageAddr (v : BitVec 64) : uepLeafPA v = pageAddr (ptePpn v) := by
  unfold uepLeafPA pageAddr ptePpn pteAddr zero_extend Sail.BitVec.zeroExtend
  bv_decide

theorem trampLeaf_bit4 : trampLeaf.getLsbD 4 = false := by decide

theorem tfLeaf_bit4 (p : BitVec 44) : (tfLeaf p).getLsbD 4 = false := by
  unfold tfLeaf leafOf PTE_R PTE_W
  bv_decide

/-- **A user text leaf of the table maps a text page of the process.** -/
theorem uptText_mem (P : UPtd) (t : PTree) (hrep : ptRep t P.leaves) (hwf : uptWf P) {a v : BitVec 64}
    (he : (a, v) ∈ t.entries 2) (ht : uepTextB v = true) (j : Nat) (hj : j < 4096) :
    uepLeafPA v + BitVec.ofNat 64 j ∈ ukTextAddrs P.um := by
  unfold uepTextB uepXB at ht
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at ht
  obtain ⟨⟨⟨hlv, hX⟩, hW⟩, hU⟩ := ht
  obtain ⟨vpn, -, -, -, -, -, -, -, hw⟩ := ptree_leaf_entry t hrep.1 he hlv
  cases hL : get? P.leaves vpn.toNat with
  | none => rw [hrep.2.2.2.2 vpn hL] at hw; cases hw
  | some w =>
    obtain ⟨a', v', hw', hvw⟩ := hrep.2.2.2.1 vpn w hL
    rw [hw] at hw'
    obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj hw')
    obtain ⟨-, -, h2, h3, h4⟩ := pteAD_low hvw
    have hum : get? P.um vpn.toNat = some w := by
      by_cases htr : vpn.toNat = trampVpn.toNat
      · rw [htr, leaves_get_tramp] at hL
        obtain rfl := Option.some.inj hL
        rw [trampLeaf_bit4] at h4; rw [h4] at hU; cases hU
      by_cases htf : vpn.toNat = tfVpn.toNat
      · rw [htf, UPt.leaves_get_tf] at hL
        obtain rfl := Option.some.inj hL
        rw [tfLeaf_bit4] at h4; rw [h4] at hU; cases hU
      rw [← UPt.leaves_get_um P _ htf htr]; exact hL
    have htl : ukTextLeaf w = true := by
      unfold ukTextLeaf; rw [← h4, ← h3, ← h2, hU, hX, hW]; rfl
    have hpa : uepLeafPA v = pte2pa w := by
      rw [uepLeafPA_pageAddr, pteAD_ptePpn hvw, (ub_data_valid P hwf _ w hum).1]
    unfold ukTextAddrs
    refine List.mem_flatMap.2 ⟨(vpn.toNat, w), toList_get.2 hum, ?_⟩
    simp only [htl, if_true]
    rw [hpa]
    exact (ubWin_mem _ _ _).2 ⟨j, hj, rfl⟩

set_option maxRecDepth 10000 in
/-- **The record's shape** (`MachCSL.uepFacts`) of the epoch a `userret`
opens. -/
theorem uepOf_facts (P : UPtd) (t : PTree) (K : Nat) (hb : t.base = P.root) (hrep : ptRep t P.leaves)
    (hwf : uptWf P) : uepFacts (uepOf P t K) := by
  refine ⟨?_, fun l d hd => ?_⟩
  · show uepPageIn (uptSlots t) 2 (uepRootPA P.root)
    have h := uptSlots_page t 2 t (fun i => lentries_self 2 t i)
    rw [pteAddr_rootPA, hb] at h
    simpa using h
  · obtain ⟨x, hx, hxd⟩ := List.mem_map.1 hd
    obtain ⟨lx, ax, vx⟩ := x
    simp only [Prod.mk.injEq] at hxd
    obtain ⟨rfl, rfl⟩ := hxd
    obtain ⟨c, i, hci, hcw, hsub⟩ := lentries_shape 2 t hrep.1 _ hx
    simp only [Prod.mk.injEq] at hci
    obtain ⟨rfl, rfl⟩ := hci
    have hent : (pteAddr c.base i, c.ents i) ∈ t.entries 2 := by
      rw [← lentries_snd]; exact List.mem_map_of_mem hx
    refine ⟨rfl, fun hl => ?_, pteAddr_al8 _ _, fun p hp => ?_, fun ht j hj => uptText_mem P t hrep hwf hent ht j hj⟩
    · cases lx with
      | zero => exact absurd rfl hl
      | succ l =>
        have hi := hcw i
        simp only
        cases hk : c.kids i with
        | none => rw [hk] at hi; rw [hi]; decide
        | some c' => rw [hk] at hi; rw [hi.1, uepLeafB_kPtr]; rfl
    · cases lx with
      | zero =>
        exfalso
        rcases (hcw i).2 with h0 | ⟨_, hne⟩
        · rw [h0] at hp; exact KptInv.not_ptPtrTo_zero p hp
        · exact hne hp.2.1
      | succ l =>
        refine ⟨by omega, ?_⟩
        have hi := hcw i
        cases hk : c.kids i with
        | none =>
          rw [hk] at hi; rw [hi] at hp; exact absurd hp (KptInv.not_ptPtrTo_zero p)
        | some c' =>
          rw [hk] at hi
          rw [hi.1] at hp
          rw [KptInv.ptPtrTo_kPtr_eq _ _ hp]
          exact uptSlots_page t l c' (fun j => hsub _ (lentries_kid l c c' i hk _ (lentries_self l c' j)))

/-! ## §3 The deposit -/

section dep
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF]

/-- A byte's head certified landed at or below `K` (route P, design D11; persistent). -/
abbrev headLandedLe (x : HEnt) (K : Nat) : IProp GF := iprop(⌜x.t = 0⌝ ∨ ∃ p : Nat, landedAt x.t p ∗ ⌜p ≤ K⌝)

/-- **One stamped byte, split**: the user tier's share, stamped, and the
record's quarter, headed by an entry landed at or below the stamp (route P). -/
theorem ctxByteX_custody (ξ : CtxId) (K : Nat) (a : PAddr) (v : BitVec 8) :
    ctxByteX (GF := GF) ξ K a (DFrac.own 1) v ⊢ ctxByteX ξ K a uCustQ v ∗
      ∃ (x : HEnt) (H : Hist), a ↦ₕ{DFrac.own Qp.quarter} (x :: H) ∗ headLandedLe x K ∗ ⌜x.v = v⌝ := by
  unfold ctxByteX
  iintro ⟨%e, %He, Hpt, %hev, #Hkey, #HK⟩
  have h := (Fractional.fractional (Φ := fun q => iprop(a ↦ₕ{DFrac.own q} (e :: He)))
    Qp.threeQuarters Qp.quarter)
  rw [qp_tq_add_q] at h
  icases h.1 $$ Hpt with ⟨H1, H2⟩
  isplitl [H1]
  · iexists e, He; iframe H1 Hkey HK; ipureintro; exact hev
  · iexists e, He; iframe H2 HK; ipureintro; exact hev

/-- **Gathering the heads' certificates into one list** (route P): what a slot's deposit cell
(`MachCSL.uslotPreCell`) carries. -/
theorem certs_gather (K : Nat) (P : Nat → PAddr) (Q : Nat → HEnt → Prop) : ∀ l : List Nat,
    ([∗list] k ∈ l, ∃ (x : HEnt) (H : Hist),
        pointsTo (G := (MachGS.era (hlc := hlc) (GF := GF)).mem) (P k) (DFrac.own Qp.quarter) (x :: H) ∗
        headLandedLe x K ∗ ⌜Q k x⌝) ⊢@{IProp GF}
      ∃ L : List (Nat × Nat), landedAll L ∗ [∗list] k ∈ l, ∃ (x : HEnt) (H : Hist),
        pointsTo (G := (MachGS.era (hlc := hlc) (GF := GF)).mem) (P k) (DFrac.own Qp.quarter) (x :: H) ∗
        ⌜(x.t = 0 ∨ ∃ q, (x.t, q) ∈ L ∧ q ≤ K) ∧ Q k x⌝
  | [] => by
    iintro _
    iexists []
    isplitl []
    · iapply BigSepL.bigSepL_nil.2; itrivial
    · iapply BigSepL.bigSepL_nil.2; itrivial
  | k :: l => by
    iintro H
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨⟨%x, %H0, Hp, #Hx, %hq⟩, H⟩
    icases certs_gather K P Q l $$ H with ⟨%L, #HL, H⟩
    icases Hx with (%h0 | ⟨%p, #Hl, %hpK⟩)
    · iexists L
      iframe HL
      iapply BigSepL.bigSepL_cons.2
      isplitl [Hp]
      · iexists x, H0; iframe Hp; ipureintro; exact ⟨Or.inl h0, hq⟩
      · iexact H
    · iexists (x.t, p) :: L
      isplitl []
      · iapply BigSepL.bigSepL_cons.2; iframe Hl HL
      iapply BigSepL.bigSepL_cons.2
      isplitl [Hp]
      · iexists x, H0; iframe Hp; ipureintro; exact ⟨Or.inr ⟨p, List.mem_cons_self, hpK⟩, hq⟩
      · iapply BigSepL.bigSepL_mono ?_ $$ H
        intro _ k' _
        iintro ⟨%y, %Hy, Hpy, %⟨hy, hq'⟩⟩
        iexists y, Hy
        iframe Hpy
        ipureintro
        refine ⟨?_, hq'⟩
        rcases hy with hy | ⟨q, hq, hqK⟩
        · exact Or.inl hy
        · exact Or.inr ⟨q, List.mem_cons_of_mem _ hq, hqK⟩

/-- A stamped list, split byte by byte. -/
theorem ukOwnX_custody (ξ : CtxId) (K : Nat) (A : List (PAddr × BitVec 8)) :
    ukOwnX (GF := GF) ξ K (DFrac.own 1) A ⊢ ukOwnX ξ K uCustQ A ∗
      [∗list] p ∈ A, ∃ (x : HEnt) (H : Hist), p.1 ↦ₕ{DFrac.own Qp.quarter} (x :: H) ∗ headLandedLe x K ∗ ⌜x.v = p.2⌝ := by
  unfold ukOwnX
  refine .trans (BigSepL.bigSepL_mono fun {_ p} _ => ctxByteX_custody ξ K p.1 p.2) BigSepL.bigSepL_sep_eqv.1

/-- The text's quarters, at the text's addresses. -/
theorem textDep_addrs (K : Nat) (A : List (PAddr × BitVec 8)) (D : List PAddr) (hA : A.map Prod.fst = D) :
    ([∗list] p ∈ A, ∃ (x : HEnt) (H : Hist), p.1 ↦ₕ{DFrac.own Qp.quarter} (x :: H) ∗ headLandedLe x K ∗
      ⌜x.v = p.2⌝) ⊢@{IProp GF}
      [∗list] a ∈ D, ∃ (x : HEnt) (H : Hist),
        pointsTo (G := (MachGS.era (hlc := hlc) (GF := GF)).mem) a (DFrac.own Qp.quarter) (x :: H) ∗
          (⌜x.t = 0⌝ ∨ ∃ q : Nat, landedAt x.t q ∗ ⌜q ≤ K⌝) := by
  rw [← hA, BigSepL.bigSepL_map]
  apply BigSepL.bigSepL_mono
  intro k p _
  iintro ⟨%x, %H, Hp, #HK, %-⟩
  iexists x, H
  iframe Hp HK

set_option maxRecDepth 10000 in
/-- The table's quarters, slot by slot. -/
theorem treeDep_slots (K : Nat) (t : PTree) :
    ([∗list] p ∈ ubTreeBytes 2 t, ∃ (x : HEnt) (H : Hist), p.1 ↦ₕ{DFrac.own Qp.quarter} (x :: H) ∗
      headLandedLe x K ∗ ⌜x.v = p.2⌝) ⊢@{IProp GF} [∗list] p ∈ uptSlots t, uslotPreCell K p := by
  unfold ubTreeBytes uptSlots
  rw [← lentries_snd, List.flatMap_map, BigSepL.bigSepL_flatMap, BigSepL.bigSepL_map]
  apply BigSepL.bigSepL_mono
  intro k x _
  unfold ubWordBytes uslotPreCell
  rw [BigSepL.bigSepL_map]
  exact certs_gather K (fun j => x.2.1 + BitVec.ofNat 64 j) (fun j y => y.v = nthByte (n := 8) x.2.2 j)
    (List.range 8)

set_option maxRecDepth 10000 in
/-- **The deposit at `userret`'s `csrw satp`**: the stamped text and table
(at `K`, the instruction view the `fence.i` raised) are the record's opening
deposit, the table at the user tier's share, and the text at the user tier's
share, stamped. -/
theorem userret_deposit [CurCtx] (cpu : CPU) (P : UPtd) (t : PTree) (M : Nat → List (BitVec 8))
    (hb : t.base = P.root) (hrep : ptRep t P.leaves) (hwf : uptWf P)
    (hl : ∀ kv ∈ toList P.um, (M kv.1).length = 4096) (K : Nat) :
    kmapStatic (GF := GF) ∗ iviewLb cpu K ∗ ukOwnX curCtx K (DFrac.own 1) (ukTextBytes P.um M ++ ubTreeBytes 2 t) ⊢
      ∃ e : UEp, ⌜e.root = P.root⌝ ∗ uepPreE cpu e ∗ uptFrameH P ∗ ukOwnX curCtx K uCustQ (ukTextBytes P.um M) := by
  iintro ⟨#HS, #HK, H⟩
  icases (show ukOwnX (GF := GF) curCtx K (DFrac.own 1) (ukTextBytes P.um M ++ ubTreeBytes 2 t) ⊢
      ukOwnX curCtx K (DFrac.own 1) (ukTextBytes P.um M) ∗ ukOwnX curCtx K (DFrac.own 1) (ubTreeBytes 2 t)
    from by unfold ukOwnX; exact BigSepL.bigSepL_append.1) $$ H with ⟨HX, HT⟩
  icases ukOwnX_custody curCtx K (ukTextBytes P.um M) $$ HX with ⟨HX, HXd⟩
  icases ukOwnX_custody curCtx K (ubTreeBytes 2 t) $$ HT with ⟨HT, HTd⟩
  ihave HT := ukOwnX_forget curCtx K uCustQ _ $$ HT
  ihave HT := ubTree_own_bwdQ 2 t hrep.2.2.1 uCustQ $$ HS HT
  ihave HXd := textDep_addrs K _ _ (ukTextBytes_fst _ _ hl) $$ HXd
  ihave HTd := treeDep_slots K t $$ HTd
  iexists uepOf P t K
  isplitr
  · ipureintro; rfl
  unfold iviewLb iviewLbAt
  icases HK with ⟨#Hlb, -⟩
  iframe HX
  isplitr [HT]
  · unfold uepPreE
    simp only [uepOf]
    iframe Hlb HXd HTd
    ipureintro; exact uepOf_facts P t K hb hrep hwf
  · unfold uptFrameH
    iexists t
    iframe HT
    ipureintro; exact ⟨hb, hrep⟩

end dep

end Xv6
