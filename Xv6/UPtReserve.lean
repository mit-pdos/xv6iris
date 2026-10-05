/-
The table's credits for one user mapping, reserved BEFORE the walk (NI M3
quotas Q-1): a mapping's supply is the walk's (`missingOn`), which a caller
(`uvmalloc`, `vmfault`, `uvmcopy`'s child) only learns once `mappages`
returns; `ptRest_reserveUser` takes the `missingOn + 1` credits up front
and leaves a wand that rebuilds the table's rest at whatever supply the
walk consumed (of the reserved length).
-/
import Xv6.UPtLemmas
import Xv6.PtRunLemmas

namespace Xv6.UPt

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Std MachCSL
open Iris.Std Iris.Std.PartialMap Iris.Std.LawfulPartialMap

section
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [WchG GF]

/-- The page count of a fill by a supply at least as long as the missing
path. -/
theorem fill_pages_len (t : PTree) (vpn : BitVec 27) (fr : List (BitVec 44))
    (h : t.missingOn 2 vpn ≤ fr.length) :
    ((t.fill 2 vpn fr).1.pages 2).length = (t.pages 2).length + t.missingOn 2 vpn := by
  rw [(PtRun.pages_fill_perm 2 t vpn fr).length_eq, List.length_append, List.length_take]
  omega

/-- The rest of a table only counts: two trees of one page count and two
leaf maps of one user count share it. -/
theorem ptRest_retarget (t t' : PTree) (L L' : RegMapF (BitVec 64))
    (hp : (t'.pages 2).length = (t.pages 2).length) (hl : uLeafCnt L' = uLeafCnt L)
    (hs' : t'.shapeQ) (hreg' : uLeafRegion L') :
    ptRest (GF := GF) t L ⊢ ptRest t' L' := by
  unfold ptRest
  iintro ⟨-, Hc⟩
  isplitl []
  · ipureintro; exact ⟨hs', hreg'⟩
  iapply pageCredit_congr _ _ (by rw [hp, hl]) $$ Hc

/-- **RESERVING A USER MAPPING**: the walk's `missingOn` interior pages and
the data page, taken before the walk; the wand rebuilds the rest once the
walk's supply (of that length) and the leaf are known (the tree's leaf
word and the map's may differ in their `A`/`D` bits: only the keys count). -/
theorem ptRest_reserveUser (t : PTree) (L : RegMapF (BitVec 64)) (vpn : BitVec 27)
    (hq : vpn.toNat < uQpages) (hn : get? L vpn.toNat = none) :
    ptRest (GF := GF) t L ⊢
      pageCredit (t.missingOn 2 vpn + 1) ∗
      (∀ (fresh : List (BitVec 44)) (v w : BitVec 64), ⌜fresh.length = t.missingOn 2 vpn⌝ -∗
        ptRest ((t.fill 2 vpn fresh).1.setLeaf 2 vpn v) (insert L vpn.toNat w)) := by
  iintro H
  icases (ptRest_unfold t L).1 $$ H with ⟨%⟨hs, hreg⟩, Hc⟩
  have hp0 := fill_pages_len t vpn (List.replicate (t.missingOn 2 vpn) 0#44)
    (by rw [List.length_replicate]; exact Nat.le_refl _)
  ihave H := ptRest_take t ((t.fill 2 vpn (List.replicate (t.missingOn 2 vpn) 0#44)).1.setLeaf 2 vpn 0#64)
    L (insert L vpn.toNat 0#64) (t.missingOn 2 vpn) 1
    (by rw [PTree.pages_setLeaf]; exact hp0)
    (uLeafCnt_insert_new L vpn.toNat 0#64 hq hn)
    (PTree.shapeQ_setLeaf _ vpn _ (PTree.shapeQ_fill t vpn _ (Or.inl hq) hs))
    (uLeafRegion_insert L vpn.toNat _ hreg (Or.inl hq)) $$ [Hc]
  · iapply (ptRest_unfold t L).2
    iframe Hc
    ipureintro; exact ⟨hs, hreg⟩
  icases H with ⟨Hc, Hr⟩
  iframe Hc
  iintro %fresh %v %w %hlen
  have hp1 := fill_pages_len t vpn fresh (by omega)
  iapply ptRest_retarget _ _ _ _ ?_ ?_
    (PTree.shapeQ_setLeaf _ vpn _ (PTree.shapeQ_fill t vpn _ (Or.inl hq) hs))
    (uLeafRegion_insert L vpn.toNat _ hreg (Or.inl hq)) $$ Hr
  · rw [PTree.pages_setLeaf, PTree.pages_setLeaf, hp0, hp1]
  · rw [uLeafCnt_insert_new L vpn.toNat _ hq hn, uLeafCnt_insert_new L vpn.toNat _ hq hn]

end

end Xv6.UPt
