/-
MachCSL: the shared kernel page table, as an invariant.

Every hart walks the same kernel table, and the hardware writes its A/D
bits back concurrently from all of them, so under weak memory a reader may
see any of the values ever written to an entry.  An entry is therefore a
word history (`wordCell`) whose every write is an A/D VARIANT of the
entry's canonical value (`pteVariant`): a leaf at any A/D, a pointer or an
empty entry unchanged.  All entries live in one invariant (`kptBody`) at a
floor the ambient context has passed, and the kernel MAPPING (vpn ↦ the
canonical leaf) is a ghost map whose persistent elements (`kmapAt`) are
what a client presents to a page-walk leaf.  Mirrors the prototype's
`tlb_inv_pt`/`kmap_at` (KptTree.v, KptShare.v), without the publication
bound: the walk reads through `readAU`, whose view is the context's.
-/
import MachCSL.PtTree
import MachCSL.WordHist
import MachCSL.WordPointsTo
import MachCSL.CtxLaws
import Iris.Instances.Lib.Invariants

set_option maxRecDepth 100000

namespace MachCSL

open Iris Iris.BI Iris.ProofMode Std
open LeanRV64D LeanRV64D.Functions

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF]

/-! ## Entries as value sets -/

/-- The values an entry of canonical value `c` may hold: a leaf at any
A/D, anything else exactly. -/
def pteVariant (c v : BitVec 64) : Prop :=
  v = c ∨ ∃ (ppn : BitVec 44) (perm : KPerm) (a d a' d' : BitVec 1), c = kLeaf ppn perm a d ∧ v = kLeaf ppn perm a' d'

theorem pteVariant_refl (c : BitVec 64) : pteVariant c c := Or.inl rfl

theorem pteVariant_kLeaf (ppn : BitVec 44) (perm : KPerm) (a d a' d' : BitVec 1) :
    pteVariant (kLeaf ppn perm a d) (kLeaf ppn perm a' d') :=
  Or.inr ⟨ppn, perm, a, d, a', d', rfl, rfl⟩

/-- A variant of a variant. -/
theorem pteVariant_trans {c v w : BitVec 64} (h1 : pteVariant c v) (h2 : pteVariant v w) : pteVariant c w := by
  rcases h1 with rfl | ⟨ppn, perm, a, d, a', d', rfl, rfl⟩
  · exact h2
  · rcases h2 with rfl | ⟨ppn₂, perm₂, a₂, d₂, a₂', d₂', h, rfl⟩
    · exact pteVariant_kLeaf ppn perm a d a' d'
    · obtain ⟨rfl, rfl⟩ := kLeaf_inj h
      exact pteVariant_kLeaf ppn perm a d a₂' d₂'

/-- The A/D write-back of a variant of a leaf is a variant of the leaf. -/
theorem pteVariant_setAD {c v : BitVec 64} (ppn : BitVec 44) (perm : KPerm) (a d : BitVec 1)
    (hc : c = kLeaf ppn perm a d) (hv : pteVariant c v) (a' d' : BitVec 1) :
    pteVariant c (pteSetAD v a' d') := by
  subst hc
  rcases hv with rfl | ⟨ppn₂, perm₂, a₂, d₂, a₂', d₂', h, rfl⟩
  · unfold kLeaf; rw [pteSetAD_pteSetAD]; exact pteVariant_kLeaf ppn perm a d a' d'
  · obtain ⟨rfl, rfl⟩ := kLeaf_inj h
    unfold kLeaf; rw [pteSetAD_pteSetAD]; exact pteVariant_kLeaf ppn perm a d a' d'

/-- The value at the point of a variant: the leaf's page and permission. -/
theorem pteVariant_of_kLeaf {v : BitVec 64} (ppn : BitVec 44) (perm : KPerm) (a d : BitVec 1)
    (hv : pteVariant (kLeaf ppn perm a d) v) : ∃ a' d', v = kLeaf ppn perm a' d' := by
  rcases hv with rfl | ⟨ppn₂, perm₂, a₂, d₂, a₂', d₂', h, rfl⟩
  · exact ⟨a, d, rfl⟩
  · obtain ⟨rfl, rfl⟩ := kLeaf_inj h
    exact ⟨a₂', d₂', rfl⟩

/-! ## The invariant -/

def kptN : Namespace := ndot nroot "xv6kpt"

/-- One entry of the shared table at `addr`, canonical value `c`, under
the word discipline since floor `lo`: every write is a variant. -/
def pteCell (addr c : BitVec 64) (lo : Nat) : IProp GF := iprop%
  ∃ (v0 : BitVec 64) (W : WordHist 8),
    wordCell addr 8 lo v0 W ∗ ⌜pteVariant c v0 ∧ ∀ e ∈ W, pteVariant c e.v⌝

instance pteCell_timeless (addr c : BitVec 64) (lo : Nat) : Timeless (pteCell (GF := GF) addr c lo) := by
  unfold pteCell; infer_instance

theorem pteCell_cases (addr c : BitVec 64) (lo : Nat) :
    pteCell (GF := GF) addr c lo ⊢ ∃ (v0 : BitVec 64) (W : WordHist 8),
      wordCell addr 8 lo v0 W ∗ ⌜pteVariant c v0 ∧ ∀ e ∈ W, pteVariant c e.v⌝ := by
  unfold pteCell; iintro H; iexact H

theorem pteCell_intro (addr c : BitVec 64) (lo : Nat) (v0 : BitVec 64) (W : WordHist 8)
    (hpin : pteVariant c v0 ∧ ∀ e ∈ W, pteVariant c e.v) :
    wordCell (GF := GF) addr 8 lo v0 W ⊢ pteCell addr c lo := by
  unfold pteCell; iintro H; iexists v0, W; iframe H; ipureintro; exact hpin

/-- All entries of the table `t`. -/
def kptBody (t : PTree) (lo : Nat) : IProp GF := iprop%
  [∗list] e ∈ t.entries 2, pteCell e.1 e.2 lo

instance kptBody_timeless (t : PTree) (lo : Nat) : Timeless (kptBody (GF := GF) t lo) := by
  unfold kptBody; infer_instance

/-- The kernel mapping's element: `vpn` maps to the page of the canonical
leaf `v` (persistent: the table is never unmapped). -/
def kmapAt (vpn : BitVec 27) (v : BitVec 64) : IProp GF := iprop%
  MachGS.kmapName (hlc := hlc) (GF := GF) ↪◯MAP[vpn.toNat]{.discard} v

instance kmapAt_persistent (vpn : BitVec 27) (v : BitVec 64) : Persistent (kmapAt (GF := GF) vpn v) := by
  unfold kmapAt; infer_instance

/-- A published (discarded) mapping authority is persistent. -/
instance kmap_auth_discard_persistent (γ : GName) (m : RegMapF (BitVec 64)) :
    Persistent (PROP := IProp GF) (γ ↪●MAP{.discard} m) := by
  unfold ghost_map_auth HeapView.Auth; infer_instance

/-- The pure facts of an installed table `t` with mapping `M`. -/
def kptFacts (t : PTree) (M : RegMapF (BitVec 64)) : Prop :=
  t.wf 2 ∧ t.pagesNodup 2 ∧
  (∀ e ∈ t.entries 2, inRam e.1 8 ∧ e.1.toNat % 8 = 0) ∧
  (∀ (vpn : BitVec 27) (v : BitVec 64), get? M vpn.toNat = some v →
    ∃ (addr : BitVec 64) (ppn : BitVec 44) (perm : KPerm), v = kLeaf ppn perm 0#1 0#1 ∧ t.maps vpn addr ppn perm)

/-- **The kernel page table is installed** (persistent): the table `t` is
well-formed with distinct pages and entries in RAM, the mapping `M` is
published (its auth discarded, so no element ever changes), and the
entries sit under the invariant at a floor the ambient context has
passed. -/
def kptOn [CurCtx] (t : PTree) (M : RegMapF (BitVec 64)) : IProp GF := iprop%
  ⌜kptFacts t M⌝ ∗ (MachGS.kmapName (hlc := hlc) (GF := GF) ↪●MAP{.discard} M) ∗
  ∃ lo : Nat, inv kptN (kptBody t lo) ∗ ctxFloor curCtx lo

instance kptOn_persistent [CurCtx] (t : PTree) (M : RegMapF (BitVec 64)) :
    Persistent (kptOn (GF := GF) t M) := by
  unfold kptOn; infer_instance

/-- A mapping element is in the published mapping. -/
theorem kptOn_facts [CurCtx] (t : PTree) (M : RegMapF (BitVec 64)) :
    kptOn (GF := GF) t M ⊢ ⌜kptFacts t M⌝ := by
  unfold kptOn
  iintro ⟨%h, _, _⟩
  ipureintro
  exact h

theorem kptOn_kmapAt [CurCtx] (t : PTree) (M : RegMapF (BitVec 64)) (vpn : BitVec 27) (v : BitVec 64) :
    kptOn (GF := GF) t M ∗ kmapAt vpn v ⊢
      ⌜∃ (addr : BitVec 64) (ppn : BitVec 44) (perm : KPerm), v = kLeaf ppn perm 0#1 0#1 ∧ t.maps vpn addr ppn perm⌝ := by
  unfold kptOn kmapAt
  iintro ⟨⟨%hf, Hauth, _⟩, Hel⟩
  icases ghost_map_lookup $$ Hauth Hel with %hget
  ipureintro
  exact hf.2.2.2 vpn v hget

/-! ## The accessors

What a page-walk leaf uses: the racy read of an entry (a value of its
variant set, at the reader's view), and the exclusive read/conditional
write pair of the A/D write-back (which pushes a variant). -/

/-- An entry of the table, from its membership. -/
theorem kptBody_acc (t : PTree) (lo : Nat) (addr c : BitVec 64) (hmem : (addr, c) ∈ t.entries 2) :
    kptBody (GF := GF) t lo ⊢ pteCell addr c lo ∗ (pteCell addr c lo -∗ kptBody t lo) := by
  unfold kptBody
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hmem
  iintro H
  icases BigSepL.bigSepL_lookup_acc (Φ := fun _ e => pteCell e.1 e.2 lo) hi $$ H with ⟨He, Hclose⟩
  iframe He
  iintro He
  ihave H := Hclose $$ %(addr, c) He
  have hset : (t.entries 2).set i (addr, c) = t.entries 2 := by
    have hl := (List.getElem?_eq_some_iff.mp hi).1
    have hv : (t.entries 2)[i] = (addr, c) := by
      have := (List.getElem?_eq_some_iff.mp hi).2; simpa using this
    rw [← hv]; exact @List.set_getElem_self _ (t.entries 2) i hl
  ihave H' := (show ([∗list] e ∈ (t.entries 2).set i (addr, c), pteCell (GF := GF) e.1 e.2 lo) ⊢
      [∗list] e ∈ t.entries 2, pteCell e.1 e.2 lo from by rw [hset]) $$ H
  iexact H'

/-- The racy read of entry `addr` (canonical `c`) by `cpu`: some variant. -/
theorem kpt_readAU [CurCtx] (cpu : CPU) (t : PTree) (M : RegMapF (BitVec 64)) (addr c : BitVec 64)
    (hmem : (addr, c) ∈ t.entries 2) :
    kptOn (GF := GF) t M ∗ ownCtx cpu curCtx ⊢
      ownCtx cpu curCtx ∗ ∃ K : Nat, viewLb cpu K ∗ readAU cpu addr 8 K (fun w => iprop(⌜pteVariant c w⌝)) := by
  unfold kptOn
  iintro ⟨⟨%hf, _, %lo, #Hinv, #Hfl⟩, Hctx⟩
  icases ownCtx_floor_view cpu curCtx lo $$ [Hctx Hfl] with ⟨Hctx, ⟨%K, #HK, %hloK⟩⟩
  · iframe Hctx; iexact Hfl
  iframe Hctx
  iexists K
  isplit
  · iexact HK
  unfold readAU
  iinv Hinv with Hbody Hclose
  icases Hbody with >Hbody
  icases kptBody_acc t lo addr c hmem $$ Hbody with ⟨Hcell, Hback⟩
  icases pteCell_cases addr c lo $$ Hcell with ⟨%v0, %W, Hw, %hpin⟩
  icases wordCell_cases addr 8 lo v0 W $$ Hw with ⟨%Hold, Hb, %htail⟩
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hmask
  iexists (fun _ => DFrac.own 1), W.hist Hold
  iframe Hb
  isplit
  · ipureintro; exact fun j hj => WordHist.hist_ne_nil W Hold htail j hj
  inext
  iintro %w %tvn %hKt %hrd Hb
  imod Hmask
  ihave Hw := wordCell_intro addr 8 lo v0 W Hold htail $$ Hb
  ihave Hcell := pteCell_intro addr c lo v0 W hpin $$ Hw
  ihave Hcl := Hclose $$ (Hback $$ Hcell)
  imod Hcl
  imodintro
  ipureintro
  rcases WordHist.read_cases W Hold (hartAgent cpu) tvn lo v0 w (by decide) htail (by omega) hrd with
    ⟨_, e, _, _, _, _, rfl⟩ | ⟨_, rfl⟩
  · exact hpin.2 e (by simp_all)
  · exact hpin.1

/-- The exclusive read of entry `addr`: the head of its history, a variant. -/
theorem kpt_exclReadAU [CurCtx] (t : PTree) (M : RegMapF (BitVec 64)) (addr c : BitVec 64)
    (hmem : (addr, c) ∈ t.entries 2) :
    kptOn (GF := GF) t M ⊢ exclReadAU addr 8 (fun w0 => iprop(⌜pteVariant c w0⌝)) := by
  unfold kptOn
  iintro ⟨%hf, _, %lo, #Hinv, #Hfl⟩
  unfold exclReadAU
  iinv Hinv with Hbody Hclose
  icases Hbody with >Hbody
  icases kptBody_acc t lo addr c hmem $$ Hbody with ⟨Hcell, Hback⟩
  icases pteCell_cases addr c lo $$ Hcell with ⟨%v0, %W, Hw, %hpin⟩
  icases wordCell_cases addr 8 lo v0 W $$ Hw with ⟨%Hold, Hb, %htail⟩
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hmask
  iexists (fun _ => DFrac.own 1), W.hist Hold
  iframe Hb
  isplit
  · ipureintro; exact fun j hj => WordHist.hist_ne_nil W Hold htail j hj
  inext
  iintro %w0 %hheads Hb
  imod Hmask
  ihave Hw := wordCell_intro addr 8 lo v0 W Hold htail $$ Hb
  ihave Hcell := pteCell_intro addr c lo v0 W hpin $$ Hw
  ihave Hcl := Hclose $$ (Hback $$ Hcell)
  imod Hcl
  imodintro
  ipureintro
  rw [WordHist.heads_eq W Hold v0 w0 htail hheads]
  unfold curVal
  cases W with
  | nil => exact hpin.1
  | cons e W => exact hpin.2 e (by simp)

/-- The conditional write of a variant `w'` to entry `addr` by `cpu`, after
an exclusive read that saw `w0`: the entry stays in its variant set. -/
theorem kpt_exclWriteAU [CurCtx] (cpu : CPU) (t : PTree) (M : RegMapF (BitVec 64)) (addr c : BitVec 64)
    (hmem : (addr, c) ∈ t.entries 2) (w0 w' : BitVec 64) (hw' : pteVariant c w') :
    kptOn (GF := GF) t M ⊢ exclWriteAU cpu addr 8 false w0 w' emp := by
  unfold kptOn
  iintro ⟨%hf, _, %lo, #Hinv, #Hfl⟩
  unfold exclWriteAU
  iinv Hinv with Hbody Hclose
  icases Hbody with >Hbody
  icases kptBody_acc t lo addr c hmem $$ Hbody with ⟨Hcell, Hback⟩
  icases pteCell_cases addr c lo $$ Hcell with ⟨%v0, %W, Hw, %hpin⟩
  icases wordCell_cases addr 8 lo v0 W $$ Hw with ⟨%Hold, Hb, %htail⟩
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hmask
  iexists W.hist Hold, 0
  iframe Hb
  isplit
  · iapply topLbAt_0
  inext
  iintro %t' %_ %_ _ Hb #_ #_
  imod Hmask
  ihave Hw := wordCell_push addr 8 lo v0 W Hold htail t' (hartAgent cpu) w' $$ Hb
  have hpin' : pteVariant c v0 ∧ ∀ e ∈ (⟨t', hartAgent cpu, w'⟩ :: W : WordHist 8), pteVariant c e.v := by
    refine ⟨hpin.1, fun e he => ?_⟩
    simp only [List.mem_cons] at he
    rcases he with rfl | he
    · exact hw'
    · exact hpin.2 e he
  ihave Hcell := pteCell_intro addr c lo v0 _ hpin' $$ Hw
  ihave Hcl := Hclose $$ (Hback $$ Hcell)
  imod Hcl
  imodintro
  iempintro

end MachCSL
