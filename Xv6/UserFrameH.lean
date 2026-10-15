/-
**The user tier's byte frame** (W8 (f3-utext) [OWN.89] (W-R)): the walker's
write-permission labels (`uRoOf`, `uPtOf`), and the frame `ufBF P D` over
the walker's map once the open epoch's custody holds half of the read-only
bytes -- the table's slots and the text pages at a HALF (`uRoOf`), the data
pages in full -- with the table's facts (`UbTreeIn`) that let an A/D
write-back locate its leaf in the epoch's record
(`MachCSL.swp_sail_mem_write_excl_upt`).
-/
import Xv6.UserBytes
import MachCSL.UByteFrameF
import MachCSL.UEpochArm

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Std MachCSL
open Iris.Std.PartialMap Iris.Std.FiniteMap
open Sail LeanRV64D LeanRV64D.Functions
open Sail.ConcurrencyInterfaceV1

/-! ## §4′ The walker's write-permission labels (W8 (f3-utext)) -/

/-- **The walker's write-permission sets at a user machine** (W8 (f3-utext)
[OWN.89]): a plain write may touch only the DATA pages (`ukDataAddrs`: user
leaves that are not text) -- every other byte (the table's pages, the TEXT
pages, `ukTextLeaf`: X set, W clear) is read-only; an A/D write-back may land
only on an 8-aligned byte on neither a data nor a text page (of the walker's
map, whose ownership `runRW` checks first: a slot of the table). -/
def uRoOf (P : UPtd) : PAddr → Bool := fun a => !decide (a ∈ ukDataAddrs P.um)

def uPtOf (P : UPtd) : PAddr → Bool := fun a =>
  (a.toNat % 8 == 0) && !decide (a ∈ ukDataAddrs P.um) && !decide (a ∈ ukTextAddrs P.um)

/-- A window of the data pages is writable. -/
theorem uRoOf_data (P : UPtd) {pa : PAddr} {n : Nat}
    (h : ∀ j, j < n → pa + BitVec.ofNat 64 j ∈ ukDataAddrs P.um) : ummRw (uRoOf P) pa n := by
  intro j hj; unfold uRoOf; simp [h j hj]

/-- A slot off the user pages may take an A/D write-back. -/
theorem uPtOf_slot (P : UPtd) {a : PAddr} (h8 : a.toNat % 8 = 0)
    (hnd : a ∉ ukDataAddrs P.um) (hnt : a ∉ ukTextAddrs P.um) : uPtOf P a = true := by
  unfold uPtOf; simp [h8, hnd, hnt]

/-- The data and the text pages are user pages. -/
theorem ukDataAddrs_sub {um : RegMapF (BitVec 64)} {a : PAddr} (h : a ∈ ukDataAddrs um) : a ∈ ubDataAddrs um := by
  obtain ⟨kv, hkv, ha⟩ := List.mem_flatMap.1 h
  refine List.mem_flatMap.2 ⟨kv, hkv, ?_⟩
  split at ha
  · cases ha
  · exact ha

theorem ukTextAddrs_sub {um : RegMapF (BitVec 64)} {a : PAddr} (h : a ∈ ukTextAddrs um) : a ∈ ubDataAddrs um := by
  obtain ⟨kv, hkv, ha⟩ := List.mem_flatMap.1 h
  refine List.mem_flatMap.2 ⟨kv, hkv, ?_⟩
  split at ha
  · exact ha
  · cases ha

/-- A table slot is 8-aligned. -/
theorem pteAddr_al8 (b : BitVec 44) (i : BitVec 9) : (pteAddr b i).toNat % 8 = 0 := by
  have h : BitVec.extractLsb' 0 3 (pteAddr b i) = 0#3 := by
    unfold pteAddr zero_extend Sail.BitVec.zeroExtend; bv_decide
  have h' := congrArg BitVec.toNat h
  simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_zero, BitVec.toNat_ofNat, Nat.reducePow] at h'
  omega


/-! ## The table's shape, for the A/D arm -/

/-- A child page is not its parent. -/
theorem ptree_kid_base_ne (lvl : Nat) (t : PTree) (hnd : t.pagesNodup (lvl + 1)) (i : BitVec 9) (c : PTree)
    (hk : t.kids i = some c) : c.base ≠ t.base := by
  unfold PTree.pagesNodup PTree.pages at hnd
  rw [List.nodup_cons] at hnd
  intro he
  apply hnd.1
  rw [← he]
  refine List.mem_flatMap.2 ⟨i, mem_allIdx i, ?_⟩
  rw [hk]
  cases lvl <;> simp [PTree.pages]

/-- **A leaf entry of a user-shaped table is a level-0 slot**, reached by a
walk whose two pointer entries name its pages. -/
theorem ptree_leaf_entry (t : PTree) (hwf : t.wfU 2) {a v : BitVec 64} (he : (a, v) ∈ t.entries 2)
    (hv : uepLeafB v = true) :
    ∃ (vpn : BitVec 27) (c1 c0 : PTree), t.kids (vpnIdx vpn 2) = some c1 ∧ c1.kids (vpnIdx vpn 1) = some c0 ∧
      t.ents (vpnIdx vpn 2) = kPtr c1.base ∧ c1.ents (vpnIdx vpn 1) = kPtr c0.base ∧
      a = pteAddr c0.base (vpnIdx vpn 0) ∧ t.walk 2 vpn = some (a, v) := by
  have hv0 : v ≠ 0#64 := by
    intro h; subst h; exact absurd hv (by decide)
  have hnp : ∀ b, v ≠ kPtr b := by
    intro b h; subst h; rw [uepLeafB_kPtr] at hv; exact absurd hv (by decide)
  simp only [PTree.entries, List.mem_append, List.mem_map, List.mem_flatMap] at he
  rcases he with ⟨i2, -, he⟩ | ⟨i2, -, he⟩
  · exfalso
    obtain ⟨-, rfl⟩ := Prod.mk.inj he
    have h2 := hwf i2
    cases hk : t.kids i2 with
    | none => rw [hk] at h2; exact hv0 h2
    | some c => rw [hk] at h2; exact hnp _ h2.1
  · cases hk2 : t.kids i2 with
    | none => rw [hk2] at he; cases he
    | some c1 =>
      rw [hk2] at he
      have h2 := hwf i2
      rw [hk2] at h2
      obtain ⟨he2, hwf1⟩ := h2
      simp only [PTree.entries, List.mem_append, List.mem_map, List.mem_flatMap] at he
      rcases he with ⟨i1, -, he⟩ | ⟨i1, -, he⟩
      · exfalso
        obtain ⟨-, rfl⟩ := Prod.mk.inj he
        have h1 := hwf1 i1
        cases hk : c1.kids i1 with
        | none => rw [hk] at h1; exact hv0 h1
        | some c => rw [hk] at h1; exact hnp _ h1.1
      · cases hk1 : c1.kids i1 with
        | none => rw [hk1] at he; cases he
        | some c0 =>
          rw [hk1] at he
          have h1 := hwf1 i1
          rw [hk1] at h1
          obtain ⟨he1, -⟩ := h1
          simp only [PTree.entries, List.mem_map] at he
          obtain ⟨i0, -, he⟩ := he
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
          refine ⟨i2 ++ i1 ++ i0, c1, c0, ?_, ?_, ?_, ?_, ?_, ?_⟩
          all_goals
            have e2 : vpnIdx (i2 ++ i1 ++ i0) 2 = i2 := by unfold vpnIdx; bv_decide
            have e1 : vpnIdx (i2 ++ i1 ++ i0) 1 = i1 := by unfold vpnIdx; bv_decide
            have e0 : vpnIdx (i2 ++ i1 ++ i0) 0 = i0 := by unfold vpnIdx; bv_decide
          · rw [e2]; exact hk2
          · rw [e1]; exact hk1
          · rw [e2]; exact he2
          · rw [e1]; exact he1
          · rw [e0]
          · simp only [PTree.walk, e2, e1, e0, hk2, hk1]
            rw [if_neg hv0]

/-- An aligned byte of the tree is an entry's address. -/
theorem ptree_entry_of_addr (t : PTree) {a : PAddr} (ha : a ∈ ubTreeAddrs 2 t) (h8 : a.toNat % 8 = 0) :
    ∃ v, (a, v) ∈ t.entries 2 := by
  rw [← ubTreeBytes_fst] at ha
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ha
  obtain ⟨e, he, hpe⟩ := List.mem_flatMap.1 hp
  unfold ubWordBytes at hpe
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hpe
  have hj' := List.mem_range.1 hj
  obtain ⟨b, -, i, hbi⟩ := Xv6.entries_page 2 t e he
  have hal := pteAddr_al8 b i
  have hj0 : j = 0 := by
    simp only at h8
    rw [hbi] at h8
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := j) (by omega)] at h8
    have := (pteAddr b i).isLt
    by_cases hlt : (pteAddr b i).toNat + j < 2 ^ 64
    · rw [Nat.mod_eq_of_lt hlt] at h8; omega
    · have : (pteAddr b i).toNat < 2 ^ 64 := (pteAddr b i).isLt
      omega
  subst hj0
  refine ⟨e.2, ?_⟩
  simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero]
  exact he

/-- The tree's bytes after a walk's leaf is written back in place. -/
theorem ubTree_setLeaf_bytes (t : PTree) (mm : BMap) (hnd : t.pagesNodup 2)
    (htb : ∀ p ∈ ubTreeBytes 2 t, mm p.1 = some p.2) (vpn : BitVec 27) (addr w v : BitVec 64)
    (hw : t.walk 2 vpn = some (addr, w)) (hv : v ≠ 0#64) :
    ∀ p ∈ ubTreeBytes 2 (t.setLeaf 2 vpn v), bmWrite mm addr 8 v p.1 = some p.2 := by
  have hwe := PTree.walk_mem_entries 2 t vpn addr w hw
  intro p hp
  obtain ⟨e, he, hpe⟩ := List.mem_flatMap.1 hp
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hpe
  have hj' := List.mem_range.1 hj
  have hslot : addr = pteAddr (t.slot 2 vpn).1 (t.slot 2 vpn).2 := by
    rw [PTree.walk_eq] at hw
    split at hw
    · exact absurd hw (by simp)
    · exact (Prod.mk.inj (Option.some.inj hw)).1.symm
  by_cases h1 : e.1 = addr
  · have hnew := PTree.walk_mem_entries 2 _ vpn addr v (PTree.walk_setLeaf_self 2 t vpn v hv addr w hw)
    have hnd' := PTree.entries_addr_nodup 2 _ (PTree.pagesNodup_setLeaf 2 t vpn v hnd)
    obtain rfl := ub_eq_of_fst _ hnd' e (addr, v) he hnew h1
    simp only
    rw [bmWrite_at mm addr 8 v (by decide) j hj']
  · have hold : e ∈ t.entries 2 := by
      rcases ub_entries_setLeaf vpn v 2 t e he with h' | h'
      · exact h'
      · exact absurd (by rw [h', ← hslot]) h1
    have hp' : (e.1 + BitVec.ofNat 64 j, nthByte (n := 8) e.2 j) ∈ ubTreeBytes 2 t :=
      List.mem_flatMap.2 ⟨e, hold, List.mem_map.2 ⟨j, hj, rfl⟩⟩
    simp only
    rw [bmWrite_other]
    · exact htb _ hp'
    intro hin
    obtain ⟨j₂, hj₂, hjj⟩ := (ubWin_mem _ _ _).1 hin
    obtain ⟨b, -, i, hbi⟩ := Xv6.entries_page 2 t e hold
    obtain ⟨b', -, i', hbi'⟩ := Xv6.entries_page 2 t (addr, w) hwe
    simp only at hbi'
    rw [hbi, hbi'] at hjj
    exact h1 (by rw [hbi, hbi']; exact ub_pteAddr_win b b' i i' j j₂ hj' hj₂ hjj)

/-- **The table's facts the user frame carries** (W8 (f3-utext)): a
user-shaped tree at the root, its bytes in the map, the map's domain the
tree and the user pages, the tree off the user pages. -/
def UbTreeIn (P : UPtd) (mm : BMap) : Prop :=
  ∃ t : PTree, t.base = P.root ∧ t.wfU 2 ∧ t.pagesNodup 2 ∧
    (∀ p ∈ ubTreeBytes 2 t, mm p.1 = some p.2) ∧
    (∀ a, (mm a).isSome = true → a ∈ ubTreeAddrs 2 t ∨ a ∈ ukDataAddrs P.um ∨ a ∈ ukTextAddrs P.um) ∧
    (∀ a ∈ ubTreeAddrs 2 t, a ∉ ukDataAddrs P.um ∧ a ∉ ukTextAddrs P.um)

/-- A write of data bytes keeps the table's facts. -/
theorem ubTreeIn_write_data {P : UPtd} {mm : BMap} (h : UbTreeIn P mm) {pa : PAddr} {n : Nat}
    (w : BitVec (8 * n)) (hn : n < 2 ^ 64) (ho : bmOwned mm pa n = true)
    (hfull : ∀ j, j < n → uRoOf P (pa + BitVec.ofNat 64 j) = false) : UbTreeIn P (bmWrite mm pa n w) := by
  obtain ⟨t, hb, hwf, hnd, htb, hcov, hdisj⟩ := h
  refine ⟨t, hb, hwf, hnd, fun p hp => ?_, fun a ha => ?_, hdisj⟩
  · rw [bmWrite_other]
    · exact htb p hp
    intro hin
    obtain ⟨j, hj, hpj⟩ := (ubWin_mem pa n p.1).1 hin
    have hpt : p.1 ∈ ubTreeAddrs 2 t := by
      rw [← ubTreeBytes_fst]; exact List.mem_map_of_mem hp
    have := hfull j hj
    rw [← hpj] at this
    unfold uRoOf at this
    simp only [Bool.not_eq_false', decide_eq_true_eq] at this
    exact (hdisj _ hpt).1 this
  · rw [bmWrite_isSome mm pa n w (by omega) ho a] at ha
    exact hcov a ha

/-- An A/D write-back of a walk's leaf keeps the table's facts. -/
theorem ubTreeIn_setLeaf {P : UPtd} {mm : BMap} {t : PTree} (hb : t.base = P.root) (hwf : t.wfU 2)
    (hnd : t.pagesNodup 2) (htb : ∀ p ∈ ubTreeBytes 2 t, mm p.1 = some p.2)
    (hcov : ∀ a, (mm a).isSome = true → a ∈ ubTreeAddrs 2 t ∨ a ∈ ukDataAddrs P.um ∨ a ∈ ukTextAddrs P.um)
    (hdisj : ∀ a ∈ ubTreeAddrs 2 t, a ∉ ukDataAddrs P.um ∧ a ∉ ukTextAddrs P.um)
    (vpn : BitVec 27) (addr w v : BitVec 64) (hw : t.walk 2 vpn = some (addr, w)) (hv : uepLeafB v = true)
    (ho : bmOwned mm addr 8 = true) : UbTreeIn P (bmWrite mm addr 8 v) := by
  have hv0 : v ≠ 0#64 := by intro h; subst h; exact absurd hv (by decide)
  have hvl : v.getLsbD 0 = true ∧ v &&& 0xE#64 ≠ 0#64 := by
    unfold uepLeafB at hv
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hv
    exact hv
  have ha : ubTreeAddrs 2 (t.setLeaf 2 vpn v) = ubTreeAddrs 2 t :=
    ubTreeAddrs_shape 2 t _ (ubSameShape_setLeaf 2 t vpn v)
  refine ⟨t.setLeaf 2 vpn v, by rw [PTree.base_setLeaf]; exact hb,
    PtRun.wfU_setLeaf_complete 2 t vpn v hvl hwf (UPtAlloc.complete_of_walk 2 t vpn hwf (by rw [hw]; simp)),
    PTree.pagesNodup_setLeaf 2 t vpn v hnd, ubTree_setLeaf_bytes t mm hnd htb vpn addr w v hw hv0,
    fun a h => ?_, by rw [ha]; exact hdisj⟩
  rw [bmWrite_isSome mm addr 8 v (by decide) ho a] at h
  rw [ha]
  exact hcov a h

section frame
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [CurCtx]

/-- The user frame's resource: the table's facts and the bytes, the
read-only ones at a half. -/
def ufBFB (P : UPtd) (D : List PAddr) (mm : BMap) : IProp GF :=
  iprop(⌜UbTreeIn P mm⌝ ∗ ubFrameFB curCtx D (uRoOf P) mm)

/-- Three disjoint windows split off a list that contains them. -/
theorem ub_perm_sub (D W : List PAddr) (hnd : D.Nodup) (hW : W.Nodup) (hsub : ∀ a ∈ W, a ∈ D) :
    D.Perm (W ++ D.filter (fun a => !decide (a ∈ W))) := by
  have h1 := List.filter_append_perm (fun a => decide (a ∈ W)) D
  refine List.Perm.trans h1.symm (List.Perm.append ?_ List.Perm.rfl)
  refine (List.perm_ext_iff_of_nodup (hnd.filter _) hW).2 ?_
  intro a
  simp only [List.mem_filter, decide_eq_true_eq]
  exact ⟨fun h => h.2, fun h => ⟨hsub a h, h⟩⟩

/-- On a window of half bytes, the frame's bytes are the all-half bytes. -/
theorem ubOwnF_halfWin (ξ : CtxId) (W : List PAddr) (hf : PAddr → Bool) (mm : BMap)
    (h : ∀ a ∈ W, hf a = true) : ubOwnF (GF := GF) ξ W hf mm ⊣⊢ ubOwnF ξ W (fun _ => true) mm := by
  unfold ubOwnF
  constructor <;>
  · apply BigSepL.bigSepL_mono
    intro k a hk
    simp only [ubFr, h a (List.mem_of_getElem? hk), if_true]
    exact .rfl

/-- Distinct entry addresses have disjoint windows. -/
theorem ub_win_disj {b b' : BitVec 44} {i i' : BitVec 9} (hne : pteAddr b i ≠ pteAddr b' i') :
    ∀ a ∈ ubWin (pteAddr b i) 8, a ∉ ubWin (pteAddr b' i') 8 := by
  intro a ha hb
  obtain ⟨j, hj, rfl⟩ := (ubWin_mem _ _ _).1 ha
  obtain ⟨j', hj', hjj⟩ := (ubWin_mem _ _ _).1 hb
  exact hne (ub_pteAddr_win b b' i i' j j' hj hj' hjj)

theorem ub_win8_nodup (a : PAddr) : (ubWin a 8).Nodup := ubWin_nodup a 8 (by decide)

/-- A window of the map at an entry address, read off the tree's bytes. -/
theorem ub_entry_read {t : PTree} {mm : BMap} (htb : ∀ p ∈ ubTreeBytes 2 t, mm p.1 = some p.2)
    {a v : BitVec 64} (he : (a, v) ∈ t.entries 2) : bmRead mm a 8 = some v :=
  ubWordBytes_read mm a v (fun p hp => htb p (List.mem_flatMap.2 ⟨(a, v), he, hp⟩))

/-- A byte of the map that a window read finds is owned. -/
theorem ub_read_isSome {mm : BMap} {a : PAddr} {n : Nat} {w : BitVec (8 * n)} (hr : bmRead mm a n = some w)
    {x : PAddr} (hx : x ∈ ubWin a n) : (mm x).isSome = true := by
  obtain ⟨j, hj, rfl⟩ := (ubWin_mem _ _ _).1 hx
  rw [bmRead_spec mm a n w hr j hj]; rfl

/-- A written window reads back. -/
theorem bmRead_bmWrite8 (mm : BMap) (pa : PAddr) (w : BitVec 64) : bmRead (bmWrite mm pa 8 w) pa 8 = some w :=
  bmRead_of_bytes _ pa 8 w (fun j hj => bmWrite_at mm pa 8 w (by decide) j hj)

/-- A window off a written one reads as before. -/
theorem bmRead_bmWrite_other (mm : BMap) (pa a : PAddr) (n : Nat) (w : BitVec (8 * n)) (v : BitVec 64)
    (hr : bmRead mm a 8 = some v) (hd : ∀ x ∈ ubWin a 8, x ∉ ubWin pa n) : bmRead (bmWrite mm pa n w) a 8 = some v :=
  bmRead_of_bytes _ a 8 v (fun j hj => by
    rw [bmWrite_other mm pa n w _ (hd _ ((ubWin_mem _ _ _).2 ⟨j, hj, rfl⟩))]
    exact bmRead_spec mm a 8 v hr j hj)

set_option maxHeartbeats 8000000 in
/-- **The user frame's A/D write-back** (W8 (f3-utext)): the leaf the write
lands on is a level-0 slot of the frame's tree; its two pointer slots and
the leaf, at a half each, go to the epoch's arm
(`MachCSL.swp_sail_mem_write_excl_upt`) with the hart's `satp` and user
privilege. -/
theorem ufBF_accPt (P : UPtd) (D : List PAddr) (cpu : CPU) (mm : BMap) {vasize : Nat}
    (req : Mem_write_request 8 vasize Arch.pa Arch.translation Arch.arch_ak) (w' : BitVec 64) (r : Option Resv)
    (s : BitVec 64) (dqs dqp : DFrac) (Φ : Result (Option Bool) Arch.abort → IProp GF)
    (hv : req.value = some w') (hk : akExcl req.access_kind = true) (ho : bmOwned mm req.pa 8 = true)
    (hpt : uPtOf P req.pa = true) (hs : satpTable s = some P.root)
    (hc : ∃ c, bmRead mm req.pa 8 = some c ∧ uepLeafB c = true ∧ pteADb c w' = true) :
    ownCtx cpu curCtx ∗ resvFragAny cpu r ∗ ufBFB (GF := GF) P D mm ∗ Register.satp ↦ᵣ[cpu]{dqs} s ∗
      Register.cur_privilege ↦ᵣ[cpu]{dqp} Privilege.User ∗
      ▷ (ownCtx cpu curCtx -∗ resvFrag cpu none false -∗ ufBFB P D (bmWrite mm req.pa 8 w') -∗
          Register.satp ↦ᵣ[cpu]{dqs} s -∗ Register.cur_privilege ↦ᵣ[cpu]{dqp} Privilege.User -∗
          Φ (.Ok (some true)))
    ⊢ swp cpu (ConcurrencyInterfaceV1.sail_mem_write req) Φ := by
  obtain ⟨c, hrc, hleaf, hadb⟩ := hc
  unfold ufBFB ubFrameFB
  iintro ⟨Hc, Hfrag, ⟨%htree, %⟨hnd, hdom⟩, HO⟩, Hs, Hp, HΦ⟩
  obtain ⟨t, hb, hwf, hnodup, htb, hcov, hdisj⟩ := htree
  have hpa_own : (mm req.pa).isSome = true := by
    have := (bmOwned_iff mm req.pa 8).1 ho 0 (by decide)
    simpa using this
  have hptF : req.pa.toNat % 8 = 0 ∧ req.pa ∉ ukDataAddrs P.um ∧ req.pa ∉ ukTextAddrs P.um := by
    unfold uPtOf at hpt
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', decide_eq_false_iff_not] at hpt
    exact ⟨hpt.1.1, hpt.1.2, hpt.2⟩
  have hpaT : req.pa ∈ ubTreeAddrs 2 t := by
    rcases hcov _ hpa_own with h | h | h
    · exact h
    · exact absurd h hptF.2.1
    · exact absurd h hptF.2.2
  obtain ⟨v0, hent⟩ := ptree_entry_of_addr t hpaT hptF.1
  have hrv := ub_entry_read htb hent
  rw [hrc] at hrv
  obtain rfl := Option.some.inj hrv
  obtain ⟨vpn, c1, c0, hk2, hk1, he2, he1, hpa, hwalk⟩ := ptree_leaf_entry t hwf hent hleaf
  have hm2 : (pteAddr t.base (vpnIdx vpn 2), kPtr c1.base) ∈ t.entries 2 := by
    simp only [PTree.entries, List.mem_append, List.mem_map]
    exact Or.inl ⟨vpnIdx vpn 2, mem_allIdx _, by rw [he2]⟩
  have hm1 : (pteAddr c1.base (vpnIdx vpn 1), kPtr c0.base) ∈ t.entries 2 := by
    simp only [PTree.entries, List.mem_append, List.mem_map, List.mem_flatMap]
    refine Or.inr ⟨vpnIdx vpn 2, mem_allIdx _, ?_⟩
    rw [hk2]
    simp only [PTree.entries, List.mem_append, List.mem_map]
    exact Or.inl ⟨vpnIdx vpn 1, mem_allIdx _, by rw [he1]⟩
  have hr2 := ub_entry_read htb hm2
  have hr1 := ub_entry_read htb hm1
  have hnl : ∀ b, kPtr b ≠ c := fun b h => by rw [← h, uepLeafB_kPtr] at hleaf; exact absurd hleaf (by decide)
  have hd20 : pteAddr t.base (vpnIdx vpn 2) ≠ req.pa := fun h => by
    rw [h, hrc] at hr2; exact hnl _ (Option.some.inj hr2).symm
  have hd10 : pteAddr c1.base (vpnIdx vpn 1) ≠ req.pa := fun h => by
    rw [h, hrc] at hr1; exact hnl _ (Option.some.inj hr1).symm
  have hd21 : pteAddr t.base (vpnIdx vpn 2) ≠ pteAddr c1.base (vpnIdx vpn 1) := fun h =>
    (ptree_kid_base_ne 1 t hnodup (vpnIdx vpn 2) c1 hk2) (pteAddr_inj h).1.symm
  have hpa' : req.pa = pteAddr c0.base (vpnIdx vpn 0) := hpa
  have hx20 := ub_win_disj (hpa' ▸ hd20)
  have hx10 := ub_win_disj (hpa' ▸ hd10)
  have hx21 := ub_win_disj hd21
  have hro : ∀ x (v : BitVec 64), (x, v) ∈ t.entries 2 → ∀ a ∈ ubWin x 8, uRoOf P a = true := by
    intro x v hx a ha
    have := (hdisj a (ukm_entry_win hx a ha)).1
    unfold uRoOf; simp [this]
  have hinD : ∀ x (v : BitVec 64), (x, v) ∈ t.entries 2 → ∀ a ∈ ubWin x 8, a ∈ D := fun x v hx a ha =>
    (hdom a).1 (ub_read_isSome (ub_entry_read htb hx) ha)
  let W2 := ubWin (pteAddr t.base (vpnIdx vpn 2)) 8
  let W1 := ubWin (pteAddr c1.base (vpnIdx vpn 1)) 8
  let W0 := ubWin req.pa 8
  have hd2 : ∀ x ∈ W2, x ∉ ubWin req.pa 8 := fun x hx => by rw [hpa']; exact hx20 x hx
  have hd1 : ∀ x ∈ W1, x ∉ ubWin req.pa 8 := fun x hx => by rw [hpa']; exact hx10 x hx
  have hWnd : (W2 ++ W1 ++ W0).Nodup := by
    refine List.nodup_append.2 ⟨List.nodup_append.2 ⟨ub_win8_nodup _, ub_win8_nodup _, ?_⟩, ub_win8_nodup _, ?_⟩
    · intro a ha b hb e; subst e; exact hx21 a ha hb
    · intro a ha b hb e
      subst e
      rcases List.mem_append.1 ha with ha | ha
      · exact hd2 a ha hb
      · exact hd1 a ha hb
  have hWsub : ∀ a ∈ W2 ++ W1 ++ W0, a ∈ D := by
    intro a ha
    rcases List.mem_append.1 ha with ha | ha
    · rcases List.mem_append.1 ha with ha | ha
      · exact hinD _ _ hm2 a ha
      · exact hinD _ _ hm1 a ha
    · exact hinD _ _ hent a ha
  have hp := ub_perm_sub D (W2 ++ W1 ++ W0) hnd hWnd hWsub
  icases (ubOwnF_perm curCtx _ _ _ mm hp).1 $$ HO with HO
  icases (ubOwnF_app curCtx _ _ _ mm).1 $$ HO with ⟨HW, Hrest⟩
  icases (ubOwnF_app curCtx _ _ _ mm).1 $$ HW with ⟨HW, H0⟩
  icases (ubOwnF_app curCtx _ _ _ mm).1 $$ HW with ⟨H2, H1⟩
  ihave H2 := (ubOwnF_halfWin curCtx W2 _ mm (hro _ _ hm2)).1 $$ H2
  ihave H2 := (ubOwnF_win_half curCtx _ 8 mm (kPtr c1.base) hr2).1 $$ H2
  ihave H1 := (ubOwnF_halfWin curCtx W1 _ mm (hro _ _ hm1)).1 $$ H1
  ihave H1 := (ubOwnF_win_half curCtx _ 8 mm (kPtr c0.base) hr1).1 $$ H1
  ihave H0 := (ubOwnF_halfWin curCtx W0 _ mm (hro _ _ hent)).1 $$ H0
  ihave H0 := (ubOwnF_win_half curCtx _ 8 mm c hrc).1 $$ H0
  have hpath : uptPathOk P.root (pteAddr t.base (vpnIdx vpn 2)) (kPtr c1.base) (pteAddr c1.base (vpnIdx vpn 1))
      (kPtr c0.base) req.pa := by
    refine ⟨⟨(vpnIdx vpn 2).toNat, (vpnIdx vpn 2).isLt, by rw [pteAddr_rootPA, hb]⟩, uepRootPA c1.base,
      uepRootPA c0.base, kPtr_ptPtrTo _, ⟨(vpnIdx vpn 1).toNat, (vpnIdx vpn 1).isLt, pteAddr_rootPA _ _⟩,
      kPtr_ptPtrTo _, ⟨(vpnIdx vpn 0).toNat, (vpnIdx vpn 0).isLt, by rw [hpa', pteAddr_rootPA]⟩⟩
  have had : uepAD c w' := ⟨_, _, (beq_iff_eq.1 hadb).symm⟩
  iapply (swp_sail_mem_write_excl_upt cpu req curCtx r c w' hv hk hleaf had P.root s hs Privilege.User dqs dqp
    dqRO dqRO _ _ _ _ hpath Φ)
  iframe Hc Hfrag H0 H2 H1 Hs Hp
  isplitr
  · unfold uptOpenWit; ileft; ipureintro; rfl
  inext
  iintro Hc Hfrag H0 H2 H1 Hs Hp
  iapply HΦ $$ Hc Hfrag [H0 H2 H1 Hrest] Hs Hp
  have hw'l : uepLeafB w' = true := by rw [uepLeafB_AD had]; exact hleaf
  isplitr
  · ipureintro
    exact ubTreeIn_setLeaf hb hwf hnodup htb hcov hdisj vpn req.pa c w' hwalk hw'l ho
  isplitr
  · ipureintro
    refine ⟨hnd, fun a => ?_⟩
    rw [bmWrite_isSome mm req.pa 8 w' (by decide) ho a]
    exact hdom a
  iapply (ubOwnF_perm curCtx _ _ _ _ hp).2
  iapply (ubOwnF_app curCtx _ _ _ _).2
  isplitl [H0 H2 H1]
  · iapply (ubOwnF_app curCtx _ _ _ _).2
    isplitl [H2 H1]
    · iapply (ubOwnF_app curCtx _ _ _ _).2
      isplitl [H2]
      · iapply (ubOwnF_halfWin curCtx W2 _ _ (hro _ _ hm2)).2
        iapply (ubOwnF_win_half curCtx _ 8 _ (kPtr c1.base)
          (bmRead_bmWrite_other mm req.pa _ 8 w' _ hr2 hd2)).2 $$ H2
      · iapply (ubOwnF_halfWin curCtx W1 _ _ (hro _ _ hm1)).2
        iapply (ubOwnF_win_half curCtx _ 8 _ (kPtr c0.base)
          (bmRead_bmWrite_other mm req.pa _ 8 w' _ hr1 hd1)).2 $$ H1
    · iapply (ubOwnF_halfWin curCtx W0 _ _ (hro _ _ hent)).2
      iapply (ubOwnF_win_half curCtx _ 8 _ w' (bmRead_bmWrite8 mm req.pa w')).2 $$ H0
  · iapply ubOwnF_congr curCtx _ _ mm _ ?_ $$ Hrest
    intro a ha
    simp only [List.mem_filter, Bool.not_eq_true', decide_eq_false_iff_not] at ha
    exact bmWrite_other mm req.pa 8 w' a (fun h => ha.2 (List.mem_append_right _ h))

/-- **The user tier's byte frame** at table `P` over the addresses `D`
(W8 (f3-utext)): the read-only bytes (table, text) at a half, the data in
full; reads at a half, writes of data in full, A/D write-backs through the
open epoch's arm. -/
def ufBF (P : UPtd) (D : List PAddr) : UByteFrame GF curCtx where
  B := ufBFB P D
  ro := uRoOf P
  pt := uPtOf P
  satpOk v := satpTable v = some P.root
  accR := fun mm pa n hn ho => by
    unfold ufBFB
    iintro ⟨%ht, HB⟩
    icases ubFrameFB_accR curCtx D _ mm pa n hn ho $$ HB with ⟨%dq, %w, %hw, Hb, Hc⟩
    iexists dq, w
    iframe Hb
    isplitr
    · ipureintro; exact hw
    iintro Hb
    isplitr
    · ipureintro; exact ht
    iapply Hc $$ Hb
  acc := fun mm pa n hn ho hrw => by
    have hfull : ∀ j, j < n → uRoOf P (pa + BitVec.ofNat 64 j) = false := by
      intro j hj
      have := List.all_eq_true.1 hrw j (List.mem_range.2 hj)
      simpa using this
    unfold ufBFB
    iintro ⟨%ht, HB⟩
    icases ubFrameFB_acc curCtx D _ mm pa n hn ho hfull $$ HB with ⟨%w, %hw, Hb, Hc⟩
    iexists w
    iframe Hb
    isplitr
    · ipureintro; exact hw
    iintro %w' Hb
    isplitr
    · ipureintro; exact ubTreeIn_write_data ht w' hn ho hfull
    iapply Hc $$ %w' Hb
  accPt := fun cpu mm {_} req w' r s dqs dqp Φ hv hk ho hpt hs hc =>
    ufBF_accPt P D cpu mm req w' r s dqs dqp Φ hv hk ho hpt hs hc

theorem ufBF_B (P : UPtd) (D : List PAddr) (mm : BMap) : (ufBF (GF := GF) P D).B mm = ufBFB P D mm := rfl

theorem ufBF_ro (P : UPtd) (D : List PAddr) : (ufBF (GF := GF) P D).ro = uRoOf P := rfl
theorem ufBF_pt (P : UPtd) (D : List PAddr) : (ufBF (GF := GF) P D).pt = uPtOf P := rfl
theorem ufBF_satpOk (P : UPtd) (D : List PAddr) (v : BitVec 64) :
    (ufBF (GF := GF) P D).satpOk v = (satpTable v = some P.root) := rfl

end frame

/-! ## The user tier's address space as labelled bytes (the USER restatement) -/

section conv
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF]

/-- One entry word at any share, physically. -/
theorem ubWord_ownQ [CurCtx] (b : BitVec 44) (hb : pageValid (pageAddr b)) (i : BitVec 9) (dq : DFrac)
    (w : BitVec 64) :
    kmapStatic (GF := GF) ⊢ (wordPointsTo (pteAddr b i) 8 dq w -∗
        [∗list] p ∈ ubWordBytes (pteAddr b i) w, ctxByte curCtx p.1 dq p.2) ∧
      (([∗list] p ∈ ubWordBytes (pteAddr b i) w, ctxByte curCtx p.1 dq p.2) -∗
        wordPointsTo (pteAddr b i) 8 dq w) := by
  have e : iprop([∗list] p ∈ ubWordBytes (pteAddr b i) w, ctxByte (GF := GF) curCtx p.1 dq p.2) =
      bytesPointsTo (pteAddr b i) 8 dq w := by
    unfold ubWordBytes bytesPointsTo ctxBytes
    rw [BigSepL.bigSepL_map]
  rw [e]
  exact uptCell_phys b hb i dq w

/-- The tree's words at any share as its bytes. -/
theorem ubTree_own_fwdQ [CurCtx] (lvl : Nat) (t : PTree) (hv : ∀ b ∈ t.pages lvl, pageValid (pageAddr b))
    (dq : DFrac) :
    kmapStatic (GF := GF) ⊢ ptreeOwn lvl dq t -∗ [∗list] p ∈ ubTreeBytes lvl t, ctxByte curCtx p.1 dq p.2 := by
  iintro #HS H
  ihave H := (ptreeOwn_entries dq lvl t).1 $$ H
  unfold ubTreeBytes
  rw [BigSepL.bigSepL_flatMap]
  iapply (ub_sepL_wand kmapStatic (t.entries lvl) _ _ ?_) $$ HS H
  intro e he
  obtain ⟨b, hb, i, hi⟩ := Xv6.entries_page lvl t e he
  obtain ⟨a, w⟩ := e
  simp only at hi
  subst hi
  exact (ubWord_ownQ b (hv b hb) i dq w).trans and_elim_l

/-- ...and back. -/
theorem ubTree_own_bwdQ [CurCtx] (lvl : Nat) (t : PTree) (hv : ∀ b ∈ t.pages lvl, pageValid (pageAddr b))
    (dq : DFrac) :
    kmapStatic (GF := GF) ⊢ ([∗list] p ∈ ubTreeBytes lvl t, ctxByte curCtx p.1 dq p.2) -∗ ptreeOwn lvl dq t := by
  iintro #HS H
  iapply (ptreeOwn_entries dq lvl t).2
  unfold ubTreeBytes
  rw [BigSepL.bigSepL_flatMap]
  iapply (ub_sepL_wand kmapStatic (t.entries lvl) _ _ ?_) $$ HS H
  intro e he
  obtain ⟨b, hb, i, hi⟩ := Xv6.entries_page lvl t e he
  obtain ⟨a, w⟩ := e
  simp only at hi
  subst hi
  exact (ubWord_ownQ b (hv b hb) i dq w).trans and_elim_r

/-- One byte of a user page at any share, physically. -/
theorem ubByte_ownQ [CurCtx] (b : BitVec 44) (hb : pageValid (pageAddr b)) (off : Nat) (hoff : off < 4096)
    (dq : DFrac) (x : BitVec 8) :
    kmapStatic (GF := GF) ⊢ (wordPointsTo (pageAddr b + BitVec.ofNat 64 off) 1 dq x -∗
        ctxByte curCtx (pageAddr b + BitVec.ofNat 64 off) dq x) ∧
      (ctxByte curCtx (pageAddr b + BitVec.ofNat 64 off) dq x -∗
        wordPointsTo (pageAddr b + BitVec.ofNat 64 off) 1 dq x) := by
  have hcl := pageValid_kmapClass b hb off hoff
  have hram := ub_inRam_page b hb off 1 (by omega)
  iintro #HS
  ihave #Hid := kmapStatic_rw (pageAddr b + BitVec.ofNat 64 off) hcl $$ HS
  isplit
  · iintro Hw
    ihave Hp := wordPointsTo_phys _ 1 dq x $$ Hid Hw
    icases pwordPointsTo_cases _ _ _ _ $$ Hp with ⟨_, Hb⟩
    iapply (ub_ctxBytes_one curCtx _ dq x).1 $$ Hb
  · iintro Hb
    ihave Hb := (ub_ctxBytes_one curCtx _ dq x).2 $$ Hb
    ihave Hp := pwordPointsTo_intro _ 1 dq x hram (Nat.mod_one _) $$ Hb
    iapply pwordPointsTo_kernel _ 1 dq x $$ Hid Hp

/-- One user page's buffer at any share, physically (both ways). -/
theorem ubPage_ownQ [CurCtx] (b : BitVec 44) (hb : pageValid (pageAddr b)) (bs : List (BitVec 8))
    (hl : bs.length = 4096) (dq : DFrac) :
    kmapStatic (GF := GF) ⊢ (byteBuf (pageAddr b) dq bs -∗
        [∗list] p ∈ ubPageBytes (pageAddr b) bs, ctxByte curCtx p.1 dq p.2) ∧
      (([∗list] p ∈ ubPageBytes (pageAddr b) bs, ctxByte curCtx p.1 dq p.2) -∗ byteBuf (pageAddr b) dq bs) := by
  have e1 : byteBuf (GF := GF) (pageAddr b) dq bs ⊣⊢
      [∗list] j ∈ List.range bs.length,
        wordPointsTo (pageAddr b + BitVec.ofNat 64 j) 1 dq (bs[j]?.getD 0#8) := by
    unfold byteBuf
    exact ub_sepL_idx (fun j x => wordPointsTo (pageAddr b + BitVec.ofNat 64 j) 1 dq x) bs
  have e2 : iprop([∗list] p ∈ ubPageBytes (pageAddr b) bs, ctxByte (GF := GF) curCtx p.1 dq p.2) =
      [∗list] j ∈ List.range bs.length,
        ctxByte curCtx (pageAddr b + BitVec.ofNat 64 j) dq (bs[j]?.getD 0#8) := by
    unfold ubPageBytes
    rw [BigSepL.bigSepL_map]
  rw [e2]
  have hper : ∀ j ∈ List.range bs.length, kmapStatic (GF := GF) ⊢
      (wordPointsTo (pageAddr b + BitVec.ofNat 64 j) 1 dq (bs[j]?.getD 0#8) -∗
        ctxByte curCtx (pageAddr b + BitVec.ofNat 64 j) dq (bs[j]?.getD 0#8)) ∧
      (ctxByte curCtx (pageAddr b + BitVec.ofNat 64 j) dq (bs[j]?.getD 0#8) -∗
        wordPointsTo (pageAddr b + BitVec.ofNat 64 j) 1 dq (bs[j]?.getD 0#8)) :=
    fun j hj => ubByte_ownQ b hb j (by rw [← hl]; exact List.mem_range.1 hj) dq _
  iintro #HS
  isplit
  · iintro H
    ihave H := e1.1 $$ H
    iapply (ub_sepL_wand kmapStatic _ _ _ (fun j hj => (hper j hj).trans and_elim_l)) $$ HS H
  · iintro H
    iapply e1.2
    iapply (ub_sepL_wand kmapStatic _ _ _ (fun j hj => (hper j hj).trans and_elim_r)) $$ HS H

end conv

/-- Two bytes of pages at offsets below a page are on the same page only if
the pages are equal. -/
theorem um_page_eq {b b' : BitVec 44} {j j' : Nat} (hj : j < 4096) (hj' : j' < 4096)
    (h : pageAddr b + BitVec.ofNat 64 j = pageAddr b' + BitVec.ofNat 64 j') : b = b' := by
  have hx : BitVec.ofNat 64 j < 4096#64 := by rw [BitVec.lt_def]; simp only [BitVec.toNat_ofNat]; omega
  have hx' : BitVec.ofNat 64 j' < 4096#64 := by rw [BitVec.lt_def]; simp only [BitVec.toNat_ofNat]; omega
  revert h hx hx'
  generalize BitVec.ofNat 64 j = x
  generalize BitVec.ofNat 64 j' = x'
  unfold pageAddr pteAddr zero_extend Sail.BitVec.zeroExtend
  intro h hx hx'
  bv_decide

/-- **A text page's byte is off the data pages** (distinct leaves map
distinct pages, `uptWf`). -/
theorem ub_text_notData (P : UPtd) (hwf : uptWf P) (k : Nat) (w : BitVec 64) (hk : get? P.um k = some w)
    (ht : ukTextLeaf w = true) (j : Nat) (hj : j < 4096) : pte2pa w + BitVec.ofNat 64 j ∉ ukDataAddrs P.um := by
  intro hin
  obtain ⟨kv, hkv, ha⟩ := List.mem_flatMap.1 hin
  split at ha
  · cases ha
  · rename_i hnt
    obtain ⟨j', hj', he⟩ := (ubWin_mem _ _ _).1 ha
    have hk' : get? P.um kv.1 = some kv.2 := toList_get.1 hkv
    obtain ⟨hpa, -⟩ := ub_data_valid P hwf k w hk
    obtain ⟨hpa', -⟩ := ub_data_valid P hwf kv.1 kv.2 hk'
    rw [hpa, hpa'] at he
    have hb := um_page_eq hj hj' he
    have hkk := hwf.2.1 k w kv.1 kv.2 hk hk' hb
    rw [← hkk, hk] at hk'
    obtain rfl := Option.some.inj hk'
    exact hnt ht

/-- The label of a user page's byte is the page's share. -/
theorem ub_page_label (P : UPtd) (hwf : uptWf P) (k : Nat) (w : BitVec 64) (hk : get? P.um k = some w)
    (j : Nat) (hj : j < 4096) : ubFr (uRoOf P) (pte2pa w + BitVec.ofNat 64 j) = umPgFr w := by
  unfold ubFr umPgFr uRoOf
  cases ht : ukTextLeaf w with
  | true =>
    have := ub_text_notData P hwf k w hk ht j hj
    simp [this]
  | false =>
    have := ukm_data_mem P.um k w hk ht j hj
    simp [this]

section conv2
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF]

/-- **The user pages as the user tier holds them, as labelled bytes.** -/
theorem ubData_own_fwdU [CurCtx] (P : UPtd) (hwf : uptWf P) (M : Nat → List (BitVec 8)) :
    kmapStatic (GF := GF) ⊢ umPagesU P M -∗
      ⌜∀ kv ∈ toList P.um, (M kv.1).length = 4096⌝ ∗ ubOwnAF curCtx (uRoOf P) (ubDataBytes P.um M) := by
  iintro #HS H
  unfold umPagesU
  ihave H := BigSepM.bigSepM_toList.1 $$ H
  unfold ubDataBytes
  rw [ubOwnAF_flatMap]
  ihave H := BigSepL.bigSepL_sep_eqv.1 $$ H
  icases H with ⟨Hl, H⟩
  ihave %hl : ⌜∀ kv ∈ toList P.um, (M kv.1).length = 4096⌝ $$ [Hl]
  · ihave %h := (BigSepL.bigSepL_pure (φ := fun _ (kv : Nat × BitVec 64) => (M kv.1).length = 4096)).1 $$ Hl
    ipureintro
    intro kv hkv
    obtain ⟨k, hk⟩ := List.getElem?_of_mem hkv
    exact h k kv hk
  isplit
  · ipureintro; exact hl
  iapply (ub_sepL_wand kmapStatic _ _ _ ?_) $$ HS H
  intro kv hkv
  have hk : get? P.um kv.1 = some kv.2 := toList_get.1 hkv
  obtain ⟨he, hv⟩ := ub_data_valid P hwf kv.1 kv.2 hk
  have hc : ∀ p ∈ ubPageBytes (pte2pa kv.2) (M kv.1), ubFr (uRoOf P) p.1 = umPgFr kv.2 := by
    intro p hp
    unfold ubPageBytes at hp
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hp
    rw [List.mem_range, hl kv hkv] at hj
    exact ub_page_label P hwf kv.1 kv.2 hk j hj
  rw [he]
  rw [he] at hc
  iintro #HS H
  ihave H := ((ubPage_ownQ (ptePpn kv.2) hv (M kv.1) (hl kv hkv) (umPgFr kv.2)).trans and_elim_l) $$ HS H
  iapply (ubOwnAF_of_const curCtx (uRoOf P) _ _ hc).2 $$ H

/-- ...and back. -/
theorem ubData_own_bwdU [CurCtx] (P : UPtd) (hwf : uptWf P) (M : Nat → List (BitVec 8))
    (hl : ∀ kv ∈ toList P.um, (M kv.1).length = 4096) :
    kmapStatic (GF := GF) ⊢ ubOwnAF curCtx (uRoOf P) (ubDataBytes P.um M) -∗ umPagesU P M := by
  iintro #HS H
  unfold umPagesU
  iapply BigSepM.bigSepM_toList.2
  unfold ubDataBytes
  rw [ubOwnAF_flatMap]
  iapply BigSepL.bigSepL_sep_eqv.2
  isplitr
  · iapply (BigSepL.bigSepL_pure (φ := fun _ (kv : Nat × BitVec 64) => (M kv.1).length = 4096)).2
    ipureintro
    intro k kv hk
    exact hl kv (List.mem_of_getElem? hk)
  iapply (ub_sepL_wand kmapStatic _ _ _ ?_) $$ HS H
  intro kv hkv
  have hk : get? P.um kv.1 = some kv.2 := toList_get.1 hkv
  obtain ⟨he, hv⟩ := ub_data_valid P hwf kv.1 kv.2 hk
  have hc : ∀ p ∈ ubPageBytes (pte2pa kv.2) (M kv.1), ubFr (uRoOf P) p.1 = umPgFr kv.2 := by
    intro p hp
    unfold ubPageBytes at hp
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hp
    rw [List.mem_range, hl kv hkv] at hj
    exact ub_page_label P hwf kv.1 kv.2 hk j hj
  rw [he]
  rw [he] at hc
  iintro #HS H
  ihave H := (ubOwnAF_of_const curCtx (uRoOf P) _ _ hc).1 $$ H
  iapply ((ubPage_ownQ (ptePpn kv.2) hv (M kv.1) (hl kv hkv) (umPgFr kv.2)).trans and_elim_r) $$ HS H

end conv2

end Xv6
