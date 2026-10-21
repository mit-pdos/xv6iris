/-
**A user table is not the kernel's** (W8 (f3-utext) [OWN.89] (W-R), F-REGS):
the root a process's table installs at `userret` is not the kernel table's,
by ownership -- the process owns its root page's entries outright
(`ptreeOwn`), while the installed kernel table's root-page entries are
frozen, every one a discarded cell (`MachCSL.KptInv.kptPtrs`: the root page
holds only pointers and empty entries).  Two cells at one address, one of
them exclusive, cannot coexist (`pointsTo_ne`).

What the user-epoch record's `satp` steps and the user-mode entry need
(`MachCSL.satpStep_open`/`_close`, `MachCSL.uenterWit`): the user root named
by `satp` is not the kernel root (`MachCSL.uepLink`).
-/
import Xv6.TransPt
import Xv6.SpecUserret
import Xv6.UserretDefs
import MachCSL.UEpochSatp

namespace Xv6

open Iris Iris.BI Iris.ProofMode MachCSL
open LeanRV64D

section
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF]

theorem allIdx_get0 : allIdx[0]? = some 0#9 := by
  simp [allIdx]

/-- The kernel table's root page holds no leaf (level 2 of a `wf` tree:
pointers and empty entries). -/
theorem kpt_root_nonleaf (tk : PTree) (hwf : tk.wf 2) (i : BitVec 9) : pteLeafB (tk.ents i) = false := by
  have h := hwf i
  cases hk : tk.kids i with
  | some c =>
    rw [hk] at h
    rw [h.1]
    exact pteLeafB_kPtr _
  | none =>
    rw [hk] at h
    rw [h]
    decide

/-- The first entry of the root page is the first of the table's entries. -/
theorem entries_get0 (t : PTree) : (t.entries 2)[0]? = some (pteAddr t.base 0#9, t.ents 0#9) := by
  simp only [PTree.entries, List.getElem?_append, List.length_map]
  rw [if_pos (by simp [allIdx])]
  simp [allIdx]

/-- **The user table's root is not the kernel table's**: the user root page's
first entry owned outright, the kernel root page's frozen. -/
theorem ptreeOwn_kptOn_ne [CurCtx] (t tk : PTree) (M : RegMapF (BitVec 64)) (hpv : pageValid (pageAddr t.base)) :
    kmapStatic (GF := GF) ∗ kptOn tk M ∗ ptreeOwn 2 (DFrac.own 1) t ⊢ ⌜t.base ≠ tk.base⌝ := by
  iintro ⟨#HS, #Hk, Ho⟩
  rw [ptreeOwn_succ]
  icases Ho with ⟨Hn, -⟩
  unfold nodeOwn
  ihave Hw := BigSepL.bigSepL_lookup (Φ := fun _ i => wordPointsTo (GF := GF) (pteAddr t.base i) 8 (DFrac.own 1)
    (t.ents i)) allIdx_get0 $$ Hn
  icases uptCell_phys t.base hpv 0#9 (DFrac.own 1) (t.ents 0#9) $$ HS with ⟨Hc2, -⟩
  ihave Hb := Hc2 $$ Hw
  unfold bytesPointsTo ctxBytes
  ihave Hb0 := BigSepL.bigSepL_lookup (Φ := fun _ j => ctxByte (GF := GF) curCtx (pteAddr t.base 0#9 + BitVec.ofNat 64 j)
    (DFrac.own 1) (nthByte (n := 8) (t.ents 0#9) j)) (i := 0) (x := 0) (by simp) $$ Hb
  unfold ctxByte
  icases Hb0 with ⟨%e, %H, Hp, -⟩
  -- the kernel's frozen first root entry
  unfold kptOn kptCore
  icases Hk with ⟨%⟨hf, -⟩, _, _, %fl, %fr, ⟨%S, _, _, _, _, #Hptrs, _, _, _⟩, _⟩
  ihave #Hc := kptPtrs_acc tk fl 0 (pteAddr tk.base 0#9) (tk.ents 0#9) (entries_get0 tk)
    (kpt_root_nonleaf tk hf.1 0#9) $$ Hptrs
  unfold ptrCell histBytes
  icases Hc with ⟨%Hs, #Hc, -⟩
  ihave #Hc0 := BigSepL.bigSepL_lookup (Φ := fun _ j => iprop((pteAddr tk.base 0#9 + BitVec.ofNat 64 j) ↦ₕ{DFrac.discard} Hs j))
    (i := 0) (x := 0) (by simp) $$ Hc
  ihave %hne := pointsTo_ne $$ Hp Hc0
  ipureintro
  intro he
  apply hne
  rw [he]

/-- `ptreeOwn_kptOn_ne` at the parked process table (`uptFrame`). -/
theorem uptFrame_kptOn_ne [CurCtx] (P : UPtd) (tk : PTree) (M : RegMapF (BitVec 64)) :
    kmapStatic (GF := GF) ∗ kptOn tk M ∗ uptFrame P ⊢ ⌜P.root ≠ tk.base⌝ := by
  unfold uptFrame
  iintro ⟨#HS, #Hk, %t, %⟨hb, hrep⟩, Ho⟩
  have hpv : pageValid (pageAddr t.base) := hrep.2.2.1 t.base (by simp [PTree.pages])
  ihave %h := ptreeOwn_kptOn_ne t tk M hpv $$ [HS Hk Ho]
  · iframe Ho; iframe HS Hk
  ipureintro
  rw [← hb]; exact h

/-- At the installed user table (`uptSlot`): the open epoch's witness names
the kernel root and says the user root is another. -/
theorem uptSlot_kptOn_ne [CurCtx] (cpu : CPU) (P : UPtd) (tk : PTree) (M : RegMapF (BitVec 64)) :
    kmapStatic (GF := GF) ∗ kptOn tk M ∗ uptSlot cpu P ⊢ ⌜P.root ≠ tk.base⌝ := by
  unfold uptSlot uptOpenWit
  iintro ⟨#HS, #Hk, %t, %⟨hb, hrep⟩, Ho, -, Hw⟩
  icases Hw with (%hu | ⟨%kr, #Hr, %⟨hne, -⟩⟩)
  · cases hu
  icases kptOn_root tk M $$ Hk with ⟨#Hr', -⟩
  ihave %he := ghost_var_agree _ kr _ tk.base _ $$ Hr Hr'
  ipureintro
  rw [← he]; exact hne

/-- ... and at userret's state under the user table (`urSt`). -/
theorem urSt_kptOn_ne [CurCtx] (cpu : CPU) (c : MConf) (P : UPtd) (pc : BitVec 64) (R : RegMap) (tk : PTree)
    (M : RegMapF (BitVec 64)) :
    kmapStatic (GF := GF) ∗ kptOn tk M ∗ urSt cpu c P pc R ⊢ ⌜P.root ≠ tk.base⌝ := by
  unfold urSt
  iintro ⟨#HS, #Hk, ⟨-, -, -, Hs, -⟩⟩
  iapply uptSlot_kptOn_ne cpu P tk M
  iframe Hs; iframe HS Hk

/-- The installed kernel table's root ghost, at its root. -/
theorem kptOnAt_rootName [CurCtx] (root : BitVec 44) :
    kptOnAt (GF := GF) root ⊢ MachGS.kptRootName (hlc := hlc) (GF := GF) ↪VAR{.discard} root := by
  unfold kptOnAt
  iintro ⟨%tk, %M, #Hk, %hb⟩
  icases kptOn_root tk M $$ Hk with ⟨#Hr, -⟩
  rw [hb] at *
  iexact Hr

/-- `uptFrame_kptOn_ne` at the installed kernel table's root. -/
theorem uptFrame_kptOnAt_ne [CurCtx] (P : UPtd) (root : BitVec 44) :
    kmapStatic (GF := GF) ∗ kptOnAt root ∗ uptFrame P ⊢ ⌜P.root ≠ root⌝ := by
  unfold kptOnAt
  iintro ⟨#HS, ⟨%tk, %M, #Hk, %hb⟩, Hf⟩
  ihave %h := uptFrame_kptOn_ne P tk M $$ [HS Hk Hf]
  · iframe Hf; iframe HS Hk
  ipureintro
  rw [← hb]; exact h

end

end Xv6
