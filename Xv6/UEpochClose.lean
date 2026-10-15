/-
**The user epoch's closing** (W8 (f3-utext) [OWN.89] (W-R), the [OWN.78]
USER restatement): at `uservec`'s `csrw satp` the interpretation hands the
record's custody back (`MachCSL.satpStep_close`: the cells of an epoch `e`
at the user root), and the user tier's three quarters and the record's
quarter make whole bytes again.

The record names its slots by address; which of them the user tier's table
`t` needs is read off the record itself (`uep_cover`): the record's facts
(`MachCSL.uepFacts`) put the root page's slots in it, and every slot the
table holds a pointer at agrees with the record (`uslotCells_seesL`), whose
pointer slots are frozen at their values and name pages whose slots are in
it.  Likewise every user text page of the process is the page of a user
text leaf of the table, whose slot's page the record's text covers
(`uep_text_cover`).
-/
import Xv6.UEpochDeposit
import Xv6.UserBytesAcc

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Std MachCSL
open Iris.Std.PartialMap Iris.Std.FiniteMap
open LeanRV64D LeanRV64D.Functions

/-! ## §1 What the record covers (pure) -/

/-- **The record covers the table**: every entry of a node the record's
pages name, of a table whose entries the record agrees with, has a slot of
the record at its address, agreeing with it. -/
theorem uep_cover (e : UEp) (hf : uepFacts e) : ∀ (lvl : Nat) (c : PTree), c.wfU lvl →
    uepPageIn e.slots lvl (pteAddr c.base 0#9) →
    (∀ x ∈ c.entries lvl, uslotSees e.slots x.1 x.2) →
    ∀ x ∈ c.entries lvl, ∃ (l : Nat) (d : KSlot), (l, d) ∈ e.slots ∧ d.addr = x.1
  | lvl, c, hwf, hpg, hsees, x, hx => by
    have hnode : ∀ i : BitVec 9, ∃ d : KSlot, (lvl, d) ∈ e.slots ∧ d.addr = pteAddr c.base i := by
      intro i
      obtain ⟨d, hd, hda⟩ := hpg i.toNat i.isLt
      exact ⟨d, hd, by rw [hda, ← KptInv.pteAddr_off]⟩
    cases lvl with
    | zero =>
      simp only [PTree.entries, List.mem_map] at hx
      obtain ⟨i, -, rfl⟩ := hx
      obtain ⟨d, hd, hda⟩ := hnode i
      exact ⟨0, d, hd, hda⟩
    | succ l =>
      simp only [PTree.entries, List.mem_append, List.mem_map, List.mem_flatMap] at hx
      rcases hx with ⟨i, -, rfl⟩ | ⟨i, -, hm⟩
      · obtain ⟨d, hd, hda⟩ := hnode i
        exact ⟨l + 1, d, hd, hda⟩
      · have hi := hwf i
        cases hk : c.kids i with
        | none => rw [hk] at hm; cases hm
        | some c' =>
          rw [hk] at hm hi
          obtain ⟨hei, hwf'⟩ := hi
          obtain ⟨d, hd, hda⟩ := hnode i
          have hfd := hf.2 (l + 1) d hd
          have hfz : d.frozen = true := hfd.2.1 (by omega)
          have hs := hsees _ (PTree.self_mem_entries (l + 1) c i) (l + 1) d hd hda
          rw [hfz, if_pos rfl, hei] at hs
          obtain ⟨-, hpg'⟩ := hfd.2.2.2.1 (uepRootPA c'.base) (by rw [← hs]; exact kPtr_ptPtrTo c'.base)
          have hr : uepRootPA c'.base = pteAddr c'.base 0#9 := by
            rw [pteAddr_rootPA]; simp
          rw [hr] at hpg'
          exact uep_cover e hf l c' hwf' hpg'
            (fun y hy => hsees y (PTree.kid_mem_entries l c c' i hk y hy)) x hm

/-- A valid leaf in the table sense is a leaf. -/
theorem uepLeafB_of_isLeaf {w : BitVec 64} (h : isLeafPte w) : uepLeafB w = true := by
  obtain ⟨h1, h2⟩ := h
  unfold PTE_V at h1
  unfold uepLeafB
  revert h1 h2
  bv_decide

/-- **The record covers the text**: every byte of a user text page of the
process is in the record's text. -/
theorem uep_text_cover (e : UEp) (hf : uepFacts e) (P : UPtd) (t : PTree) (hrep : ptRep t P.leaves)
    (hwf : uptWf P) (hsees : ∀ x ∈ t.entries 2, uslotSees e.slots x.1 x.2)
    (hcov : ∀ x ∈ t.entries 2, ∃ (l : Nat) (d : KSlot), (l, d) ∈ e.slots ∧ d.addr = x.1) :
    ∀ a ∈ ukTextAddrs P.um, a ∈ e.text := by
  intro a ha
  obtain ⟨⟨k, w⟩, hkv, ha⟩ := List.mem_flatMap.1 ha
  have hk : get? P.um k = some w := toList_get.1 hkv
  cases htl : ukTextLeaf w with
  | false => simp only [htl, Bool.false_eq_true, if_false] at ha; cases ha
  | true =>
  simp only [htl, if_true] at ha
  obtain ⟨j, hj, rfl⟩ := (ubWin_mem _ _ _).1 ha
  obtain ⟨hklt, hleaf, -⟩ := hwf.1 k w hk
  have hkv' : (BitVec.ofNat 27 k).toNat = k := by
    have : tfVpn.toNat < 2 ^ 27 := tfVpn.isLt
    simp; omega
  have hL : get? P.leaves (BitVec.ofNat 27 k).toNat = some w := by
    rw [hkv', UPt.leaves_get_um P k (by omega) (by rw [Xv6.trampVpn_toNat]; rw [Xv6.tfVpn_toNat] at hklt; omega)]
    exact hk
  obtain ⟨addr, v, hw, hvw⟩ := hrep.2.2.2.1 _ w hL
  have hent := PTree.walk_mem_entries 2 t _ addr v hw
  obtain ⟨l, d, hd, hda⟩ := hcov _ hent
  have hs := hsees _ hent l d hd hda
  obtain ⟨-, -, h2, h3, h4⟩ := pteAD_low hvw
  have hlv : uepLeafB v = true := by rw [uepLeafB_AD hvw]; exact uepLeafB_of_isLeaf hleaf
  unfold ukTextLeaf at htl
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at htl
  obtain ⟨⟨hU, hX⟩, hW⟩ := htl
  have htv : uepTextB v = true := by
    unfold uepTextB uepXB; rw [hlv, h2, h3, h4, hU, hX, hW]; rfl
  have hdv : uepTextB d.c = true ∧ ptePpn d.c = ptePpn v := by
    split at hs
    · rw [← hs]; exact ⟨htv, rfl⟩
    · obtain ⟨-, -, g2, g3, g4⟩ := pteAD_low hs
      refine ⟨?_, (pteAD_ptePpn hs).symm⟩
      unfold uepTextB uepXB
      rw [← uepLeafB_AD hs, ← g2, ← g3, ← g4]
      unfold uepTextB uepXB at htv
      exact htv
  have hm := (hf.2 l d hd).2.2.2.2 hdv.1 j hj
  rwa [uepLeafPA_pageAddr, hdv.2, pteAD_ptePpn hvw, ← (ub_data_valid P hwf k w hk).1] at hm

/-! ## §2 The joins -/

section join
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF]

/-- A quarter of a byte, any history. -/
abbrev qCell (a : PAddr) : IProp GF := iprop(∃ H : Hist, a ↦ₕ{DFrac.own Qp.quarter} H)

/-- The user tier's share of a byte and a quarter of it are the byte. -/
theorem ctxByte_joinQ (ξ : CtxId) (a : PAddr) (b : BitVec 8) :
    ctxByte (GF := GF) ξ a uCustQ b ∗ qCell a ⊢ ctxByte ξ a (DFrac.own 1) b := by
  iintro ⟨H1, %H, H2⟩
  icases ctxByte_cases ξ a uCustQ b $$ H1 with ⟨%e, %He, Hpt1, %hev, #Hkey⟩
  ihave %hag := pointsTo_agree $$ [Hpt1 H2]
  · iframe Hpt1 H2
  rw [← hag]
  have h := pointsTo_combine (GF := GF) (L := PAddr) (V := Hist) (H := MemF)
    (l := a) (dq₁ := DFrac.own Qp.threeQuarters) (dq₂ := DFrac.own Qp.quarter)
    (v₁ := e :: He) (v₂ := e :: He)
  rw [DFrac.op_own, qp_tq_add_q] at h
  icases h $$ [Hpt1 H2] with ⟨Hpt, _⟩
  · iframe Hpt1 H2
  unfold ctxByte
  iexists e, He
  iframe Hpt Hkey
  ipureintro; exact hev

/-- **The join of a labelled list**: every byte at the read-only label meets
a quarter of the cells `T`, the rest are whole already. -/
theorem uepClose_join (ξ : CtxId) (hf : PAddr → Bool) : ∀ (A : List (PAddr × BitVec 8)) (T : List PAddr),
    (A.map Prod.fst).Nodup → (∀ p ∈ A, hf p.1 = true → p.1 ∈ T) →
    ([∗list] a ∈ T, qCell (GF := GF) a) ∗ ubOwnAF ξ hf A ⊢ ubOwnA ξ A
  | [], _, _, _ => by
    iintro ⟨-, -⟩
    unfold ubOwnA
    simp only [Iris.Algebra.BigOpL.bigOpL_nil]; iempintro
  | p :: A, T, hnd, hcov => by
    rw [List.map_cons, List.nodup_cons] at hnd
    unfold ubOwnAF ubOwnA
    iintro ⟨HT, HA⟩
    icases BigSepL.bigSepL_cons.1 $$ HA with ⟨Hp, HA⟩
    iapply BigSepL.bigSepL_cons.2
    cases hp : hf p.1 with
    | false =>
      have e : ubFr hf p.1 = DFrac.own 1 := by simp [ubFr, hp]
      rw [e]
      iframe Hp
      iapply (show ubOwnA (GF := GF) ξ A ⊢ [∗list] y ∈ A, ctxByte ξ y.1 (DFrac.own 1) y.2 from .rfl)
      iapply uepClose_join ξ hf A T hnd.2 (fun q hq hq' => hcov q (List.mem_cons_of_mem _ hq) hq')
      iframe HT; unfold ubOwnAF; iexact HA
    | true =>
      have e : ubFr hf p.1 = uCustQ := by simp [ubFr, hp, dqRO]
      rw [e]
      have hpT := hcov p List.mem_cons_self hp
      icases (BigSepL.bigSepL_perm (Φ := fun a => qCell (GF := GF) a) (List.perm_cons_erase hpT)).1 $$ HT
        with HT
      icases BigSepL.bigSepL_cons.1 $$ HT with ⟨Hq, HT⟩
      isplitl [Hp Hq]
      · iapply ctxByte_joinQ ξ p.1 p.2; iframe Hp Hq
      have hcov' : ∀ q ∈ A, hf q.1 = true → q.1 ∈ T.erase p.1 := by
        intro q hq hq'
        have hne : q.1 ≠ p.1 := fun h => hnd.1 (h ▸ List.mem_map_of_mem hq)
        exact (List.mem_erase_of_ne hne).2 (hcov q (List.mem_cons_of_mem _ hq) hq')
      iapply (show ubOwnA (GF := GF) ξ A ⊢ [∗list] y ∈ A, ctxByte ξ y.1 (DFrac.own 1) y.2 from .rfl)
      iapply uepClose_join ξ hf A (T.erase p.1) hnd.2 hcov'
      iframe HT; unfold ubOwnAF; iexact HA

/-- The record's slot cells as quarters of their bytes. -/
theorem uslotCells_q (K : Nat) : ∀ sl : List (Nat × KSlot),
    ([∗list] p ∈ sl, uslotCell (GF := GF) K p) ⊢ [∗list] a ∈ sl.flatMap (fun p => ubWin p.2.addr 8), qCell a
  | [] => by
    iintro _
    simp only [List.flatMap_nil, Iris.Algebra.BigOpL.bigOpL_nil]; iempintro
  | p :: sl => by
    iintro H
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨⟨%Hs, Hp, -⟩, H⟩
    rw [List.flatMap_cons]
    iapply BigSepL.bigSepL_append.2
    isplitl [Hp]
    · unfold ubWin
      rw [BigSepL.bigSepL_map]
      iapply BigSepL.bigSepL_mono _ $$ Hp
      intro k j _
      iintro Hj
      iexists Hs j
      iexact Hj
    · iapply uslotCells_q K sl $$ H

/-- The record's text cells as quarters. -/
theorem utextCells_q (K : Nat) (T : List PAddr) :
    ([∗list] a ∈ T, ∃ (x : HEnt) (H : Hist),
      pointsTo (G := (MachGS.era (hlc := hlc) (GF := GF)).mem) a (DFrac.own Qp.quarter) (x :: H) ∗ ⌜x.t ≤ K⌝) ⊢
      [∗list] a ∈ T, qCell (GF := GF) a := by
  apply BigSepL.bigSepL_mono
  intro k a _
  iintro ⟨%x, %H, Ha, -⟩
  iexists x :: H
  iexact Ha

/-- **The record's slots and the writer's words agree**, word by word. -/
theorem uslotCells_seesL (K : Nat) (ξ : CtxId) (dq : DFrac) (sl : List (Nat × KSlot)) :
    ∀ E : List (BitVec 64 × BitVec 64),
    ([∗list] p ∈ sl, uslotCell (GF := GF) K p) ∗ ([∗list] x ∈ E, ctxBytes ξ x.1 8 dq x.2) ⊢
      ⌜∀ x ∈ E, uslotSees sl x.1 x.2⌝ ∗ ([∗list] p ∈ sl, uslotCell K p) ∗ ([∗list] x ∈ E, ctxBytes ξ x.1 8 dq x.2)
  | [] => by
    iintro ⟨H, HE⟩
    iframe H HE
    ipureintro; intro x hx; cases hx
  | x :: E => by
    iintro ⟨H, HE⟩
    icases BigSepL.bigSepL_cons.1 $$ HE with ⟨Hx, HE⟩
    icases uslotCells_sees K ξ x.1 dq x.2 sl $$ [H Hx] with ⟨%hx, H, Hx⟩
    · iframe H Hx
    icases uslotCells_seesL K ξ dq sl E $$ [H HE] with ⟨%hE, H, HE⟩
    · iframe H HE
    iframe H
    isplitr
    · ipureintro
      intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · exact hx
      · exact hE y hy
    iapply BigSepL.bigSepL_cons.2
    iframe

/-- The table's bytes, word by word. -/
theorem ubTree_ctxBytes (ξ : CtxId) (lvl : Nat) (t : PTree) (dq : DFrac) :
    ([∗list] p ∈ ubTreeBytes lvl t, ctxByte (GF := GF) ξ p.1 dq p.2) ⊣⊢
      [∗list] x ∈ t.entries lvl, ctxBytes ξ x.1 8 dq x.2 := by
  unfold ubTreeBytes
  rw [BigSepL.bigSepL_flatMap]
  constructor <;>
  · apply BigSepL.bigSepL_mono
    intro k x _
    unfold ubWordBytes ctxBytes
    rw [BigSepL.bigSepL_map]

/-! ## §3 The close -/

/-- **The text's quarters, given back** for the process's text pages. -/
def uTextQ (P : UPtd) : IProp GF :=
  iprop(∃ T : List PAddr, ⌜∀ a ∈ ukTextAddrs P.um, a ∈ T⌝ ∗ [∗list] a ∈ T, qCell (GF := GF) a)

set_option maxRecDepth 10000 in
/-- **The table, whole again** (at `uservec`'s `csrw satp`): the installed
user table at the user tier's share and the closed epoch's cells at the
user root make the installed table in full, and the record's text quarters
cover the process's text pages. -/
theorem uepClose_tree [CurCtx] (cpu : CPU) (P : UPtd) (e : UEp) (her : e.root = P.root) (hwf : uptWf P) :
    kmapStatic (GF := GF) ∗ uepCellsE (MachGS.era (hlc := hlc) (GF := GF)) cpu e ∗ uptSlot cpu P ⊢
      uptSlotF cpu P ∗ uTextQ P := by
  unfold uepCellsE uptSlot
  iintro ⟨#HS, ⟨%hf, -, Htext, Hslots⟩, %t, %⟨hb, hrep⟩, Ho, Htlb, -⟩
  ihave HT := ubTree_own_fwdQ 2 t hrep.2.2.1 uCustQ $$ HS Ho
  ihave HT := (ubTree_ctxBytes curCtx 2 t uCustQ).1 $$ HT
  icases uslotCells_seesL e.K curCtx uCustQ e.slots (t.entries 2) $$ [Hslots HT] with ⟨%hsees, Hslots, HT⟩
  · iframe Hslots HT
  have hpg : uepPageIn e.slots 2 (pteAddr t.base 0#9) := by
    have h := hf.1
    rw [her, ← hb] at h
    have hr : uepRootPA t.base = pteAddr t.base 0#9 := by rw [pteAddr_rootPA]; simp
    rw [hr] at h; exact h
  have hcov := uep_cover e hf 2 t hrep.1 hpg hsees
  have htc := uep_text_cover e hf P t hrep hwf hsees hcov
  ihave HT := (ubTree_ctxBytes curCtx 2 t uCustQ).2 $$ HT
  ihave HT := (ubOwnAF_of_const curCtx (fun _ => true) (ubTreeBytes 2 t) uCustQ (fun _ _ => rfl)).2 $$ HT
  ihave %hnd := ubOwnAF_nodup curCtx _ _ $$ HT
  ihave HQ := uslotCells_q e.K e.slots $$ Hslots
  have hcovB : ∀ p ∈ ubTreeBytes 2 t, (fun _ => true) p.1 = true →
      p.1 ∈ e.slots.flatMap (fun p => ubWin p.2.addr 8) := by
    intro p hp _
    unfold ubTreeBytes at hp
    obtain ⟨x, hx, hpx⟩ := List.mem_flatMap.1 hp
    unfold ubWordBytes at hpx
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hpx
    obtain ⟨l, d, hd, hda⟩ := hcov x hx
    exact List.mem_flatMap.2 ⟨(l, d), hd, (ubWin_mem _ _ _).2 ⟨j, List.mem_range.1 hj, by rw [hda]⟩⟩
  ihave HT := uepClose_join curCtx (fun _ => true) (ubTreeBytes 2 t) _ hnd hcovB $$ [HQ HT]
  · iframe HQ HT
  ihave HT := (show ubOwnA (GF := GF) curCtx (ubTreeBytes 2 t) ⊢
    [∗list] p ∈ ubTreeBytes 2 t, ctxByte curCtx p.1 (DFrac.own 1) p.2 from .rfl) $$ HT
  ihave HT := ubTree_own_bwdQ 2 t hrep.2.2.1 (DFrac.own 1) $$ HS HT
  isplitl [HT Htlb]
  · unfold uptSlotF
    iexists t
    iframe HT Htlb
    ipureintro; exact ⟨hb, hrep⟩
  · unfold uTextQ
    iexists e.text
    isplitr
    · ipureintro; exact htc
    iapply utextCells_q e.K e.text $$ Htext

/-- **The pages, whole again**: the user pages at the user tier's shares
and the record's text quarters are the pages in full. -/
theorem uepClose_pages [CurCtx] (P : UPtd) (hwf : uptWf P) (M : Nat → List (BitVec 8)) :
    kmapStatic (GF := GF) ∗ uTextQ P ∗ umPagesU P M ⊢ umPages P M := by
  unfold uTextQ
  iintro ⟨#HS, ⟨%T, %hT, HQ⟩, Hum⟩
  icases ubData_own_fwdU P hwf M $$ HS Hum with ⟨%hl, HD⟩
  ihave %hnd := ubOwnAF_nodup curCtx _ _ $$ HD
  have hcovD : ∀ p ∈ ubDataBytes P.um M, uRoOf P p.1 = true → p.1 ∈ T := by
    intro p hp hro
    have ha : p.1 ∈ ubDataAddrs P.um := by
      rw [← ubDataBytes_fst _ _ hl]; exact List.mem_map_of_mem hp
    rcases ub_data_split ha with h | h
    · unfold uRoOf at hro; simp [h] at hro
    · exact hT _ h
  ihave HD := uepClose_join curCtx (uRoOf P) (ubDataBytes P.um M) T hnd hcovD $$ [HQ HD]
  · iframe HQ HD
  iapply ubData_own_bwd P hwf M hl $$ HS HD

end join

end Xv6
