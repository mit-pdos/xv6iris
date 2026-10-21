/-
MachCSL: **the user epoch's record, read as a discipline** (W8 (f3-utext)
[OWN.89] (W-R), [R34.1]): the export's O1 (`uTextDiscAt`, the user code) out
of the interpretation's user-epoch record (`uepModelAt`).

A hart in user mode has an open epoch (`uepLink`) at the root its `satp`
names; the record's quarters of the table's slots fix the current words of
its pointer slots (frozen: their values as of the stamp) and of its leaves
(`A`/`D` variants of them), so a walk as of now from the root reaches only
the record's pages, and a user text leaf's page is the record's text; the
record's quarter of each text byte is headed at or below the stamp `K`,
which is at or below the hart's instruction view, and histories are newest
first (`histOk`).
-/
import MachCSL.UEpochArm

namespace MachCSL

open Iris Iris.BI Iris.ProofMode Std
open LeanRV64D

/-! ## Pure: the record bounds the walk -/

theorem uepTextB_setAD (c : BitVec 64) (a d : BitVec 1) : uepTextB (pteSetAD c a d) = uepTextB c := by
  have h1 : (pteSetAD c a d).getLsbD 2 = c.getLsbD 2 ∧ (pteSetAD c a d).getLsbD 3 = c.getLsbD 3 ∧
      (pteSetAD c a d).getLsbD 4 = c.getLsbD 4 := by
    simp only [pteSetAD, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange',
      BitVec.extractLsb, LeanRV64D.Functions._update_PTE_Flags_A, LeanRV64D.Functions._update_PTE_Flags_D]
    refine ⟨?_, ?_, ?_⟩ <;> bv_decide
  unfold uepTextB uepXB
  rw [uepLeafB_setAD, h1.1, h1.2.1, h1.2.2]

theorem uepLeafPA_setAD (c : BitVec 64) (a d : BitVec 1) : uepLeafPA (pteSetAD c a d) = uepLeafPA c := by
  simp only [uepLeafPA, pteSetAD, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange',
    BitVec.extractLsb, LeanRV64D.Functions._update_PTE_Flags_A, LeanRV64D.Functions._update_PTE_Flags_D]
  bv_decide

/-- The record's histories of a slot, at the heap, with its certificates agreeing with the landing
positions (route P, design D11). -/
def uslotHeapOkL (m : FlatMem) (lp : LandPos) (K : Nat) (d : KSlot) : Prop :=
  ∃ (Hs : Nat → Hist) (L : List (Nat × Nat)), (∀ j, j < 8 → m[d.addr + BitVec.ofNat 64 j]? = some (Hs j)) ∧
    lp 0 = some 0 ∧ (∀ q ∈ L, q.1 ≠ 0 → lp q.1 = some q.2) ∧ uslotHistOkL K d Hs L

/-- A slot of the record and the current word at its address: frozen, its
value; a leaf, a variant of it. -/
theorem uslot_nowL {m : FlatMem} {lp : LandPos} {K : Nat} {d : KSlot} (h : uslotHeapOkL m lp K d)
    {v : BitVec 64} (hv : curWordAt m d.addr v) : if d.frozen then v = d.c else uepAD d.c v := by
  obtain ⟨Hs, L, hget, -, -, hk⟩ := h
  refine uslot_headsL hk (fun j hj => ?_)
  have := hv j hj
  rw [hget j hj] at this
  exact this

theorem uepPageIn_slot {sl : List (Nat × KSlot)} {l : Nat} {p a : PAddr} (hp : uepPageIn sl l p)
    (ha : uSlotOf p a) : ∃ d : KSlot, (l, d) ∈ sl ∧ d.addr = a := by
  obtain ⟨i, hi, rfl⟩ := ha
  exact hp i hi

/-- Below a landed head, every entry of a co-ordered history is landed at or below it. -/
theorem landed_below_head {lp : LandPos} {log : List Agent} {x : HEnt} {H : Hist} {q : Nat}
    (hok : histOkP lp log (x :: H)) (hx : lp x.t = some q) : ∀ e ∈ H, e.landedLe lp q = true := by
  intro e he
  have hc := List.rel_of_pairwise_cons hok.1 he
  unfold coAbove at hc
  rw [hx] at hc
  unfold HEnt.landedLe
  cases hl : lp e.t with
  | none => rw [hl] at hc; exact hc.elim
  | some p' => rw [hl] at hc; simpa using hc

/-- **O1 at one hart, pure, over the landing positions** (route P): the walk from an open epoch's
root as of now reaches its user text leaves only at the record's text pages, whose entries are
landed at or below the stamp. -/
theorem uTextDisc_pureP (m : FlatMem) (lp : LandPos) (log : List Agent) (e : UEp) (hf : uepFacts e)
    (hslots : ∀ l d, (l, d) ∈ e.slots → uslotHeapOkL m lp e.K d)
    (htext : ∀ a ∈ e.text, ∃ (x : HEnt) (H : Hist), m[a]? = some (x :: H) ∧
      ∃ q, lp x.t = some q ∧ q ≤ e.K)
    (hord : ∀ (a : PAddr) (H : Hist), m[a]? = some H → histOkP lp log H)
    (a : PAddr) (v : BitVec 64) (hw : uSlotNow m e.root a v) (ht : uepTextB v = true) :
    ∀ j, j < 4096 → ∀ H : Hist, m[uepLeafPA v + BitVec.ofNat 64 j]? = some H → ∀ en ∈ H,
      en.landedLe lp e.K = true := by
  have hleafv : uepLeafB v = true := by
    unfold uepTextB uepXB at ht; simp only [Bool.and_eq_true] at ht; exact ht.1.1.1
  have hnoleaf : ∀ l d, (l, d) ∈ e.slots → l ≠ 0 → d.addr = a → curWordAt m a v → False := by
    intro l d hd hl hda hcw
    have hfd := hf.2 l d hd
    have hs := uslot_nowL (hslots l d hd) (hda ▸ hcw)
    rw [hfd.2.1 hl, if_pos rfl] at hs
    have := hfd.1
    rw [hfd.2.1 hl, ← hs, hleafv] at this
    exact absurd this (by decide)
  have hptr : ∀ l d (a' : PAddr) (v' : BitVec 64) (p : PAddr), (l, d) ∈ e.slots → l ≠ 0 → d.addr = a' →
      curWordAt m a' v' → ptPtrTo v' p → uepPageIn e.slots (l - 1) p := by
    intro l d a' v' p hd hl hda hcw hp
    have hfd := hf.2 l d hd
    have hs := uslot_nowL (hslots l d hd) (hda ▸ hcw)
    rw [hfd.2.1 hl, if_pos rfl] at hs
    rw [hs] at hp
    exact (hfd.2.2.2.1 p hp).2
  have hpg2 := hf.1
  have hleaf0 : ∀ d : KSlot, (0, d) ∈ e.slots → d.addr = a → curWordAt m a v →
      ∀ j, j < 4096 → uepLeafPA v + BitVec.ofNat 64 j ∈ e.text := by
    intro d hd hda hcw j hj
    have hs := uslot_nowL (hslots 0 d hd) (hda ▸ hcw)
    have hdv : uepTextB d.c = true ∧ uepLeafPA v = uepLeafPA d.c := by
      split at hs
      · rw [← hs]; exact ⟨ht, rfl⟩
      · obtain ⟨a', d', rfl⟩ := hs
        rw [uepTextB_setAD] at ht
        exact ⟨ht, uepLeafPA_setAD _ _ _⟩
    rw [hdv.2]
    exact (hf.2 0 d hd).2.2.2.2 hdv.1 j hj
  have hin : ∀ j, j < 4096 → uepLeafPA v + BitVec.ofNat 64 j ∈ e.text := by
    rcases hw with ⟨hs2, hcw⟩ | ⟨a2, v2, p1, hs2, hcw2, hp1, hrest⟩
    · obtain ⟨d, hd, hda⟩ := uepPageIn_slot hpg2 hs2
      exact (hnoleaf 2 d hd (by decide) hda hcw).elim
    · obtain ⟨d2, hd2, hda2⟩ := uepPageIn_slot hpg2 hs2
      have hpg1 := hptr 2 d2 a2 v2 p1 hd2 (by decide) hda2 hcw2 hp1
      rcases hrest with ⟨hs1, hcw⟩ | ⟨a1, v1, p0, hs1, hcw1, hp0, hs0, hcw⟩
      · obtain ⟨d, hd, hda⟩ := uepPageIn_slot hpg1 hs1
        exact (hnoleaf 1 d hd (by decide) hda hcw).elim
      · obtain ⟨d1, hd1, hda1⟩ := uepPageIn_slot hpg1 hs1
        have hpg0 := hptr 1 d1 a1 v1 p0 hd1 (by decide) hda1 hcw1 hp0
        obtain ⟨d0, hd0, hda0⟩ := uepPageIn_slot hpg0 hs0
        exact hleaf0 d0 hd0 hda0 hcw
  intro j hj H hH en hen
  obtain ⟨x, H0, hx, q, hq, hqK⟩ := htext _ (hin j hj)
  rw [hx] at hH
  obtain rfl := Option.some.inj hH
  have hok := hord _ _ hx
  rcases List.mem_cons.1 hen with rfl | hen'
  · unfold HEnt.landedLe; rw [hq]; simpa using hqK
  · have h1 := landed_below_head hok hq en hen'
    unfold HEnt.landedLe at h1 ⊢
    cases hl : lp en.t with
    | none => rw [hl] at h1; cases h1
    | some p' => rw [hl] at h1; simp at h1 ⊢; omega


/-! ## Pure: T4, the user tables after the stamp -/

/-- An `A`/`D` variant differs only in its low byte. -/
theorem uepAD_byte {c v : BitVec 64} (h : uepAD c v) (j : Nat) (h1 : 1 ≤ j) (h8 : j < 8) :
    nthByte (n := 8) v j = nthByte (n := 8) c j := by
  obtain ⟨a, d, rfl⟩ := h
  have : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  · simp only [nthByte, pteSetAD, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange',
      BitVec.extractLsb, LeanRV64D.Functions._update_PTE_Flags_A, LeanRV64D.Functions._update_PTE_Flags_D]
    bv_decide

/-- A word whose every byte is a byte of some `A`/`D` variant is one. -/
theorem uepAD_of_bytes {c w : BitVec 64}
    (h : ∀ j, j < 8 → ∃ v, uepAD c v ∧ nthByte (n := 8) w j = nthByte (n := 8) v j) : uepAD c w := by
  obtain ⟨v0, hv0, hw0⟩ := h 0 (by decide)
  have : w = v0 := by
    apply bv_eq_of_bytes (n := 8)
    intro j hj
    rcases Nat.eq_zero_or_pos j with rfl | hpos
    · exact hw0
    · obtain ⟨vj, hvj, hwj⟩ := h j hj
      rw [hwj, uepAD_byte hvj j hpos hj, uepAD_byte hv0 j hpos hj]
  rw [this]; exact hv0

theorem find?_of_weaker {p q : HEnt → Bool} : ∀ (l : List HEnt) (x : HEnt), l.find? p = some x → q x = true →
    (∀ y, q y = true → p y = true) → l.find? q = some x
  | [], _, h, _, _ => by cases h
  | y :: l, x, h, hq, hqp => by
    by_cases hy : p y = true
    · rw [List.find?_cons_of_pos hy] at h
      obtain rfl := Option.some.inj h
      exact List.find?_cons_of_pos hq
    · rw [List.find?_cons_of_neg hy] at h
      have hqy : ¬ q y = true := fun h' => hy (hqp y h')
      rw [List.find?_cons_of_neg hqy]
      exact find?_of_weaker l x h hq hqp

/-- **A slot of the record after the stamp, over the landing positions** (route P): written only by
harts, whole, with variants of its value as of any `T` past the stamp. -/
theorem uslot_discAfterP {m : FlatMem} {lp : LandPos} {log : List Agent} {K T : Nat} {d : KSlot}
    (hd : uslotHeapOkL m lp K d) (hord : ∀ (a : PAddr) (H : Hist), m[a]? = some H → histOkP lp log H)
    (hKT : K ≤ T) {c : BitVec 64} (hc : wordAsOfP m lp d.addr T c) : uSlotDiscAfterP m lp T d.addr c := by
  obtain ⟨Hs, L, hget, hlp0, hL, -, hent⟩ := hd
  -- the value as of `K` is landed at or below `K`
  have hxK : ∀ j, j < 8 → ∀ (P : Hist) (x : HEnt) (Q : Hist), Hs j = P ++ x :: Q →
      (x.t = 0 ∨ ∃ q, (x.t, q) ∈ L ∧ q ≤ K) → ∃ q, lp x.t = some q ∧ q ≤ K := by
    intro j hj P x Q _ hx
    rcases hx with h0 | ⟨q, hq, hqK⟩
    · exact ⟨0, by rw [h0]; exact hlp0, Nat.zero_le _⟩
    · by_cases h0 : x.t = 0
      · exact ⟨0, by rw [h0]; exact hlp0, Nat.zero_le _⟩
      · exact ⟨q, hL _ hq h0, hqK⟩
  have hdc : uepAD d.c c := by
    apply uepAD_of_bytes
    intro j hj
    have hcj := hc j hj
    rw [show (m.lview lp).entAsOf (d.addr + BitVec.ofNat 64 j) T = m.entAsOfP lp (d.addr + BitVec.ofNat 64 j) T
      from rfl, FlatMem.entAsOfP_eq, hget j hj] at hcj
    simp only [Option.bind_some] at hcj
    obtain ⟨P, x, Q, hPQ, hxv, hxc, hP⟩ := hent j hj
    obtain ⟨qx, hqx, hqxK⟩ := hxK j hj P x Q hPQ hxc
    have hxl : HEnt.landedLe lp T x = true := by
      unfold HEnt.landedLe; rw [hqx]; simp; omega
    rw [hPQ, List.find?_append] at hcj
    cases hfP : P.find? (HEnt.landedLe lp T) with
    | some y =>
      rw [hfP] at hcj
      simp only [Option.some_or, Option.bind_some] at hcj
      have hyv : y.v = nthByte (n := 8) c j := by
        unfold HEnt.atLanding at hcj
        cases hl : lp y.t with
        | none => rw [hl] at hcj; cases hcj
        | some q => rw [hl] at hcj; simpa using hcj
      obtain ⟨-, -, -, v, hv, hv', -⟩ := hP y (List.mem_of_find?_eq_some hfP)
      exact ⟨v, hv, by rw [← hyv, hv']⟩
    | none =>
      rw [hfP, Option.none_or, List.find?_cons, hxl] at hcj
      simp only [Option.bind_some] at hcj
      have hxv' : x.v = nthByte (n := 8) c j := by
        unfold HEnt.atLanding at hcj
        rw [hqx] at hcj; simpa using hcj
      exact ⟨d.c, uepAD_refl d.c, by rw [← hxv', hxv]⟩
  intro j H e hj hH he hTe
  rw [hget j hj] at hH
  obtain rfl := Option.some.inj hH
  obtain ⟨P, x, Q, hPQ, hxv, hxc, hP⟩ := hent j hj
  obtain ⟨qx, hqx, hqxK⟩ := hxK j hj P x Q hPQ hxc
  rw [hPQ] at he
  rcases List.mem_append.1 he with heP | hxQ
  · obtain ⟨-, -, htid, v, hv, hev, hall⟩ := hP e heP
    exact ⟨htid, v, pteAD_trans (pteAD_symm hdc) hv, hev, fun j' hj' => ⟨Hs j', hget j' hj', hall j' hj'⟩⟩
  · exfalso
    rcases List.mem_cons.1 hxQ with rfl | hQ
    · unfold HEnt.landedLe at hTe; rw [hqx] at hTe; simp at hTe; omega
    · have hok := hord _ _ (hget j hj)
      rw [hPQ] at hok
      have := List.rel_of_pairwise_cons (List.pairwise_append.1 hok.1).2.1 hQ
      unfold coAbove at this
      rw [hqx] at this
      unfold HEnt.landedLe at hTe
      cases hl : lp e.t with
      | none => rw [hl] at this; exact this
      | some p' => rw [hl] at this hTe; simp at hTe; omega

/-- A slot a walk reaches as of now from an open epoch's root is a slot of the
record. -/
theorem uSlotNow_recL (m : FlatMem) (lp : LandPos) (e : UEp) (hf : uepFacts e)
    (hslots : ∀ l d, (l, d) ∈ e.slots → uslotHeapOkL m lp e.K d) (a : PAddr) (v : BitVec 64)
    (hw : uSlotNow m e.root a v) : ∃ (l : Nat) (d : KSlot), (l, d) ∈ e.slots ∧ d.addr = a := by
  have hptr : ∀ l d (a' : PAddr) (v' : BitVec 64) (p : PAddr), (l, d) ∈ e.slots → l ≠ 0 → d.addr = a' →
      curWordAt m a' v' → ptPtrTo v' p → uepPageIn e.slots (l - 1) p := by
    intro l d a' v' p hd hl hda hcw hp
    have hfd := hf.2 l d hd
    have hs := uslot_nowL (hslots l d hd) (hda ▸ hcw)
    rw [hfd.2.1 hl, if_pos rfl] at hs
    rw [hs] at hp
    exact (hfd.2.2.2.1 p hp).2
  rcases hw with ⟨hs2, -⟩ | ⟨a2, v2, p1, hs2, hcw2, hp1, hrest⟩
  · obtain ⟨d, hd, hda⟩ := uepPageIn_slot hf.1 hs2
    exact ⟨2, d, hd, hda⟩
  · obtain ⟨d2, hd2, hda2⟩ := uepPageIn_slot hf.1 hs2
    have hpg1 := hptr 2 d2 a2 v2 p1 hd2 (by decide) hda2 hcw2 hp1
    rcases hrest with ⟨hs1, -⟩ | ⟨a1, v1, p0, hs1, hcw1, hp0, hs0, -⟩
    · obtain ⟨d, hd, hda⟩ := uepPageIn_slot hpg1 hs1
      exact ⟨1, d, hd, hda⟩
    · obtain ⟨d1, hd1, hda1⟩ := uepPageIn_slot hpg1 hs1
      have hpg0 := hptr 1 d1 a1 v1 p0 hd1 (by decide) hda1 hcw1 hp0
      obtain ⟨d0, hd0, hda0⟩ := uepPageIn_slot hpg0 hs0
      exact ⟨0, d0, hd0, hda0⟩

/-! ## The record, read off the interpretation -/

section iris
variable {hlc : HasLC} {GF : BundledGFunctors} [MachFixedGS hlc GF]

theorem histsAtE (E : EraGS) (m : FlatMem) (pa : PAddr) (dq : DFrac) (Hs : Nat → Hist) : ∀ n : Nat,
    genHeapInterp (G := E.mem) m ∗
      ([∗list] j ∈ List.range n, pointsTo (G := E.mem) (pa + BitVec.ofNat 64 j) dq (Hs j)) ⊢@{IProp GF}
      ⌜∀ j, j < n → m[pa + BitVec.ofNat 64 j]? = some (Hs j)⌝
  | 0 => by
    iintro ⟨_, _⟩
    ipureintro
    intro j hj
    omega
  | n + 1 => by
    rw [List.range_succ]
    iintro ⟨Hm, Hb⟩
    icases BigSepL.bigSepL_snoc.1 $$ Hb with ⟨Hb1, Hb2⟩
    ihave %H1 : ⌜∀ j, j < n → m[pa + BitVec.ofNat 64 j]? = some (Hs j)⌝ $$ [Hm Hb1]
    · iapply histsAtE E m pa dq Hs n $$ [Hm Hb1]
      iframe
    ihave %H2 : ⌜m[pa + BitVec.ofNat 64 n]? = some (Hs n)⌝ $$ [Hm Hb2]
    · letI : genHeapGS PAddr Hist GF MemF := E.mem
      icases genHeap_valid $$ [$Hm $Hb2] with >%_
      itrivial
    ipureintro
    intro j hj
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h | rfl
    · exact H1 j h
    · exact H2

/-- The record's landing certificates agree with the machine. -/
theorem landedListE_agree (E : EraGS) (σ : MState) : ∀ L : List (Nat × Nat),
    memModelAt E σ ∗ ([∗list] q ∈ L, landedAtE E q.1 q.2) ⊢@{IProp GF}
      ⌜∀ q ∈ L, q.1 ≠ 0 → σ.lp q.1 = some q.2⌝
  | [] => by
    iintro _
    ipureintro
    intro q hq; cases hq
  | q :: L => by
    iintro ⟨Hmm, Hl⟩
    icases BigSepL.bigSepL_cons.1 $$ Hl with ⟨#H0, Hs⟩
    ihave %hs := landedListE_agree E σ L $$ [Hmm Hs]
    · iframe Hmm Hs
    by_cases hq0 : q.1 = 0
    · ipureintro
      intro q' hq' hne
      rcases List.mem_cons.1 hq' with rfl | hq'
      · exact absurd hq0 hne
      · exact hs q' hq' hne
    · ihave %h0 := memModel_landedAt E σ q.1 q.2 hq0 $$ [Hmm H0]
      · iframe Hmm H0
      ipureintro
      intro q' hq' hne
      rcases List.mem_cons.1 hq' with rfl | hq'
      · exact h0
      · exact hs q' hq' hne

/-- The record's slot cells, at the heap, over the landing positions. -/
theorem uslotCellsE_heapL (E : EraGS) (σ : MState) (K : Nat) : ∀ sl : List (Nat × KSlot),
    genHeapInterp (G := E.mem) σ.mem ∗ memModelAt E σ ∗
      ([∗list] p ∈ sl, ∃ (Hs : Nat → Hist) (L : List (Nat × Nat)),
        ([∗list] j ∈ List.range 8, pointsTo (G := E.mem) (p.2.addr + BitVec.ofNat 64 j)
          (DFrac.own Qp.quarter) (Hs j)) ∗ ([∗list] q ∈ L, landedAtE E q.1 q.2) ∗ ⌜uslotHistOkL K p.2 Hs L⌝)
      ⊢@{IProp GF} ⌜∀ l d, (l, d) ∈ sl → uslotHeapOkL σ.mem σ.lp K d⌝
  | [] => by
    iintro _
    ipureintro
    intro l d h; cases h
  | p :: sl => by
    iintro ⟨Hm, Hmm, H⟩
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨⟨%Hs, %L, Hp, #HL, %hk⟩, H⟩
    ihave %h1 := histsAtE E σ.mem p.2.addr _ Hs 8 $$ [Hm Hp]
    · iframe
    ihave %hL := landedListE_agree E σ L $$ [Hmm HL]
    · iframe Hmm HL
    ihave %h2 := uslotCellsE_heapL E σ K sl $$ [Hm Hmm H]
    · iframe
    ipureintro
    intro l d hd
    rcases List.mem_cons.1 hd with rfl | hd
    · exact ⟨Hs, L, h1, rfl, hL, hk⟩
    · exact h2 l d hd

/-- The record's text cells, at the heap, over the landing positions. -/
theorem utextCellsE_heapL (E : EraGS) (σ : MState) (K : Nat) : ∀ T : List PAddr,
    genHeapInterp (G := E.mem) σ.mem ∗ memModelAt E σ ∗
      ([∗list] a ∈ T, ∃ (x : HEnt) (H : Hist), pointsTo (G := E.mem) a (DFrac.own Qp.quarter) (x :: H) ∗
        (⌜x.t = 0⌝ ∨ ∃ q : Nat, landedAtE E x.t q ∗ ⌜q ≤ K⌝)) ⊢@{IProp GF}
      ⌜∀ a ∈ T, ∃ (x : HEnt) (H : Hist), σ.mem[a]? = some (x :: H) ∧ ∃ q, σ.lp x.t = some q ∧ q ≤ K⌝
  | [] => by
    iintro _
    ipureintro
    intro a h; cases h
  | a :: T => by
    iintro ⟨Hm, Hmm, H⟩
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨⟨%x, %H0, Ha, Hx⟩, H⟩
    ihave %h1 : ⌜σ.mem[a]? = some (x :: H0)⌝ $$ [Hm Ha]
    · letI : genHeapGS PAddr Hist GF MemF := E.mem
      icases genHeap_valid $$ [$Hm $Ha] with >%_
      itrivial
    ihave %hx : ⌜∃ q, σ.lp x.t = some q ∧ q ≤ K⌝ $$ [Hmm Hx]
    · icases Hx with (%h0 | ⟨%q, #Hq, %hqK⟩)
      · ipureintro; exact ⟨0, by rw [h0]; rfl, Nat.zero_le _⟩
      · by_cases h0 : x.t = 0
        · ipureintro; exact ⟨0, by rw [h0]; rfl, Nat.zero_le _⟩
        · ihave %hl := memModel_landedAt E σ x.t q h0 $$ [Hmm Hq]
          · iframe Hmm Hq
          ipureintro; exact ⟨q, hl, hqK⟩
    ihave %h2 := utextCellsE_heapL E σ K T $$ [Hm Hmm H]
    · iframe
    ipureintro
    intro b hb
    rcases List.mem_cons.1 hb with rfl | hb
    · exact ⟨x, H0, h1, hx⟩
    · exact h2 b hb

/-- An instruction-view lower bound is at or below the view. -/
theorem memModelAt_iviewLb (E : EraGS) (σ : MState) (h : CPU) (K : Nat) :
    memModelAt E σ ∗ MonoNat.lb_own (E.iviewName h) (.ofNat K) ⊢@{IProp GF} ⌜K ≤ σ.itv h⌝ := by
  unfold memModelAt
  iintro ⟨⟨_, _, Hviews, _⟩, Hlb⟩
  icases BigSepL.bigSepL_lookup_acc_impl (Φ := fun _ c => hartViewsAt E σ c) (cpus_get? h) $$ Hviews
    with ⟨Hc, _⟩
  icases hartViewsAt_cases E σ h $$ Hc with ⟨_, Hv, _⟩
  ihave %Hv := MonoNat.auth_lb_own_valid $$ Hv Hlb
  ipureintro
  have := Hv.2
  simpa [MaxNat.le_toNat] using this

/-- **O1, out of the interpretation** (route P: the export's twin `uTextDiscAtP`): the heap, the
memory model and the user-epoch record give it. -/
theorem uepModel_textDiscP (E : EraGS) (σ : MState) :
    genHeapInterp (G := E.mem) σ.mem ∗ memModelAt E σ ∗ uepModelAt E σ ⊢@{IProp GF} ⌜uTextDiscAtP σ⌝ := by
  iintro ⟨Hm, Hmm, Huep⟩
  ihave %hmm := memModel_mmOk E σ $$ Hmm
  unfold uepModelAt
  icases Huep with ⟨%k, -, Hharts⟩
  unfold uTextDiscAtP
  iapply BI.pure_forall.2
  iintro %h
  icases (BigSepL.bigSepL_lookup_acc (Φ := fun _ (c : CPU) => uepHartAt (GF := GF) E σ k c)
    (cpus_get? h)).1 $$ Hharts with ⟨Hh, -⟩
  unfold uepHartAt
  icases Hh with ⟨%oe, %hl, Hc⟩
  by_cases hp : σ.regs h Register.cur_privilege = Privilege.User
  · cases oe with
    | none => exact absurd hp (hl.2 rfl).1
    | some e =>
    obtain ⟨hsat, -⟩ := hl.1 e rfl
    rw [uepCellsAt_some]
    unfold uepCellsE
    icases Hc with ⟨%hf, Hlb, Htext, Hslots⟩
    ihave %hK := memModelAt_iviewLb E σ h e.K $$ [Hmm Hlb]
    · iframe
    ihave %hsl := uslotCellsE_heapL E σ e.K e.slots $$ [Hm Hmm Hslots]
    · iframe
    ihave %htx := utextCellsE_heapL E σ e.K e.text $$ [Hm Hmm Htext]
    · iframe
    ipureintro
    intro r _ hr a v hw ht j hj H hH en hen
    rw [hsat] at hr
    obtain rfl := Option.some.inj hr
    have h1 := uTextDisc_pureP σ.mem σ.lp σ.log e hf hsl htx (fun a H h => mmOk_hist hmm a H h) a v hw ht j hj H hH en hen
    unfold HEnt.landedLe at h1 ⊢
    cases hle : σ.lp en.t with
    | none => rw [hle] at h1; cases h1
    | some p' => rw [hle] at h1; simp at h1 ⊢; omega
  · ipureintro
    intro r hp' _
    exact absurd hp' hp

/-- The kernel root the record knows is held, as of now, by a registered root
word. -/
theorem uepKsat_word (E : EraGS) (m : FlatMem) (k : Option (BitVec 44)) :
    genHeapInterp (G := E.mem) m ∗ uepKsatAt E k ⊢@{IProp GF}
      ⌜∀ rk, k = some rk → ∃ ra : PAddr, (⟨ra, .roots 1 8⟩ : RsvRegion) ∈ MachFixedGS.rsvStatic (hlc := hlc) (GF := GF) ∧
        curWordAt m ra (uepRootPA rk)⌝ := by
  cases k with
  | none =>
    iintro _
    ipureintro
    intro rk h; cases h
  | some rk =>
    unfold uepKsatAt
    iintro ⟨Hm, -, %ra, %S, %Hr, %⟨hin, hhd⟩, Hb⟩
    ihave %hg := histsAtE E m ra DFrac.discard Hr 8 $$ [Hm Hb]
    · iframe
    ipureintro
    intro rk' h
    obtain rfl := Option.some.inj h
    refine ⟨ra, hin, fun j hj => ?_⟩
    obtain ⟨e, H, he, hev, -⟩ := hhd j hj
    rw [hg j hj, he]
    simp [Hist.top, hev, uepRootPA]

/-- **T4, out of the interpretation** (route P: the export's twin `uPtDiscAtP`): the heap, the
memory model and the user-epoch record give it at the record's static list. -/
theorem uepModel_ptDiscP (E : EraGS) (σ : MState) :
    genHeapInterp (G := E.mem) σ.mem ∗ memModelAt E σ ∗ uepModelAt E σ ⊢@{IProp GF}
      ⌜uPtDiscAtP (MachFixedGS.rsvStatic (hlc := hlc) (GF := GF)) σ⌝ := by
  iintro ⟨Hm, Hmm, Huep⟩
  ihave %hmm := memModel_mmOk E σ $$ Hmm
  unfold uepModelAt
  icases Huep with ⟨%k, #Hk, Hharts⟩
  ihave %hkw := uepKsat_word E σ.mem k $$ [Hm]
  · iframe Hm; iexact Hk
  unfold uPtDiscAtP
  iapply BI.pure_forall.2
  iintro %h
  icases (BigSepL.bigSepL_lookup_acc (Φ := fun _ (c : CPU) => uepHartAt (GF := GF) E σ k c)
    (cpus_get? h)).1 $$ Hharts with ⟨Hh, -⟩
  unfold uepHartAt
  icases Hh with ⟨%oe, %hl, Hc⟩
  cases oe with
  | none =>
    ipureintro
    intro r hpM hr hnot
    rcases (hl.2 rfl).2 hpM with h0 | ⟨_, h0⟩
    · rw [hr] at h0; cases h0
    · rw [hr] at h0
      obtain ⟨ra, hin, hcw⟩ := hkw r h0.symm
      exact absurd hcw (hnot ra hin)
  | some e =>
    obtain ⟨hsat, -⟩ := hl.1 e rfl
    rw [uepCellsAt_some]
    unfold uepCellsE
    icases Hc with ⟨%hf, Hlb, -, Hslots⟩
    ihave %hK := memModelAt_iviewLb E σ h e.K $$ [Hmm Hlb]
    · iframe
    ihave %hsl := uslotCellsE_heapL E σ e.K e.slots $$ [Hm Hmm Hslots]
    · iframe
    ipureintro
    intro r _ hr _ a v c hw hc
    rw [hsat] at hr
    obtain rfl := Option.some.inj hr
    obtain ⟨l, d, hd, rfl⟩ := uSlotNow_recL σ.mem σ.lp e hf hsl a v hw
    exact uslot_discAfterP (hsl l d hd) (fun a H h => mmOk_hist hmm a H h) hK hc

end iris

end MachCSL
