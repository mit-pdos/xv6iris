/-
Weak: **allocproc route P, row P-W6 on the S-R walk — `IssueCo` and its census, R-WALK VARIANTS**
(F-PW6-1 (a), [OWN.149]; [OWN.150] S-R walk; `PROGRESS-PW6.md` design check: P-W6 realizes the R-walk members
`SbKillR.certSupplyOfWalkR` uses).  Lean-only, no Rocq twin.  A PRIMED TWIN: nothing registered imports this
file.

**Spec first.**  As in `Weak/SbIssueCo.lean`: RVWMO does not order two harts' plain stores to one byte by issue;
MachCSL-P lands them in issue order (`SbRealP.landBlockedForeign`), so a realization of the walk needs, at every
landing, that no FOREIGN store issued EARLIER on a common byte is still pending (`SbRealP.ForeignBelowLanded`).

The S-R walk (`SbOrdR.enbR`, `SbOrdR.PInvR`) steps the same machine (`SbWalk.nextI`) with a different gate: its
landing `SbOrdR.landR` lands GF's NEXT WRITE (the S-P prefix), which gives the per-byte co prefix
(`SbOrdR.coPfx`) that `SbOrd.landG` asked for explicitly.  So:
* **`SbIssueCoR.noForeignBelowR`**: the walk half of `ForeignBelowLanded` at an enabled S-R landing, from the
  SAME named input `SbIssueCo.IssueCo` (stated over walk positions, gate-independent);
* **`SbIssueCoR.issueCoOfCustodyR`**: `IssueCo` from the SAME named census `SbIssueCoCensus.WwCustody` along a
  valid S-R walk with `PInvR` (through its base view `SbOrdR.PInvR.toB`) and `CtrLanded` at every state.

Spec: FAITHFUL (proof organisation; the named inputs are the P-walk's, unchanged).  Lean-only helpers
`SbIssueCoR.*`.
-/
import Weak.SbIssueCoCensus
import Weak.SbHoldR

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Lbl SbWalk SbAgree SbReplay SbOrd SbIssueCo

namespace SbIssueCoR

/-- **THE WALK HALF OF `ForeignBelowLanded`, S-R walk**: at an enabled S-R landing (`landR`) of row `i`'s
pending store `p`, no pending store `q` of another row `j`, issued BEFORE `p` (items `k1 < k2`), writes a byte
`p` writes. -/
theorem noForeignBelowR {N : Nat} {img : Image} {X : Geid → Prop} {dev : List Geid} (pol : SbPol)
    (G : Gexec) (c : CandW) (hco : IssueCo G c) (hnd : G.gxGmo.Nodup)
    (hP : SbOrdR.PInvR N img G X dev (SbWalk.cur c)) (i k : Nat) (hg : SbOrdR.landR pol G (SbWalk.cur c) i k)
    (p : Nat × SbEnt) (hp : ((SbWalk.cur c).pend i)[k]? = some p)
    (j : Nat) (q : Nat × SbEnt) (hq : q ∈ (SbWalk.cur c).pend j) (hji : j ≠ i)
    (k1 k2 : Nat) (h12 : k1 < k2) (hk2 : k2 ≤ c.its.length)
    (he1 : SbIssueCo.evAt c k1 = some (j, q.1)) (he2 : SbIssueCo.evAt c k2 = some (i, p.1))
    (l1 l2 : Lbl) (hl1 : gxLbl G (j, q.1) = some l1) (hl2 : gxLbl G (i, p.1) = some l2)
    (hs1 : isSt l1 = true) (hs2 : isSt l2 = true) (a : Int) (hw1 : wrsB l1 a = true)
    (hw2 : wrsB l2 a = true) : False := by
  have hqG : (j, q.1) ∉ (SbWalk.cur c).gmo := hP.inv.pendGmo j q hq
  have hq2 : (j, q.1) ∉ (stAt c k2).gmo := fun h =>
    hqG ((gmoMonoAt c k2 c.its.length hk2).subset h)
  have hlt := hco k1 k2 _ _ l1 l2 a h12 he1 he2 hji hl1 hl2 hs1 hs2 hw1 hw2 hq2
  obtain ⟨p', hp', -, hS⟩ := hg
  rw [hp, Option.some.injEq] at hp'
  subst hp'
  have hgw : gwrB G a (i, p.1) = true := by unfold gwrB; rw [hl2]; exact hw2
  have hpre := SbOrdR.coPfx hP.pf hP.inv (i, p.1) a hS hgw
  have hpm : p ∈ (SbWalk.cur c).pend i := List.mem_of_getElem? hp
  have hsW : (i, p.1) ∉ wrAtW (SbWalk.cur c) a := fun h => hP.inv.pendGmo i p hpm (List.mem_filter.1 h).1
  have hxG : (j, q.1) ∈ wrAtG G a :=
    List.mem_filter.2 ⟨hlt.1, by simp only [gwrB, hl1]; exact hw1⟩
  have hin := landedBelowTop G (SbWalk.cur c) a _ _ hnd hpre hsW hxG hlt.2.2
  exact hqG (List.mem_filter.1 hin).1

/-- **`IssueCo` FROM THE WRITE-WRITE CUSTODY CENSUS, S-R walk**: along a valid epoch walk with the S-R walk
invariant and `CtrLanded` at every state, `WwCustody` gives `IssueCo` (its premise is never met). -/
theorem issueCoOfCustodyR {N : Nat} {X : Geid → Prop} {dev : List Geid} (G : Gexec) (c : CandW)
    (Ctr : Geid → Prop) (hv : validW SbPol.epoch c)
    (hP : ∀ k, k ≤ c.its.length → SbOrdR.PInvR N c.img G X dev (stAt c k)) (hc : CatH G)
    (hC : ∀ k, k ≤ c.its.length → SbVirtio.CtrLanded G Ctr (stAt c k))
    (hW : SbIssueCoCensus.WwCustody G dev Ctr) : IssueCo G c := by
  intro k1 k2 e1 e2 l1 l2 a h12 he1 he2 hne hl1 hl2 hs1 hs2 hw1 hw2 hnot
  exfalso
  obtain ⟨hk1, hd1⟩ := SbIssueCoCensus.evAtHd c k1 e1 he1
  obtain ⟨hk2, hd2⟩ := SbIssueCoCensus.evAtHd c k2 e2 he2
  have hh1 := SbBlocked.histStAt c hv k1
  have hh2 := SbBlocked.histStAt c hv k2
  rcases hW e1 e2 l1 l2 a hne hl1 hl2 hs1 hs2 hw1 hw2 with h | h
  · rw [hd2] at h
    have hB := (hP k2 (Nat.le_of_lt hk2)).toB
    have hL := (SbVirtio.hvSoundB hB hc hh2.1 hh2.2 (hC k2 (Nat.le_of_lt hk2)) e2.1 true e1 h).2 rfl
    exact hnot (SbBlocked.landedGmoB hB e1 hL (SbIssueCoCensus.gisWOfSt G e1 l1 hl1 hs1))
  · rw [hd1] at h
    have hB := (hP k1 (Nat.le_of_lt hk1)).toB
    have hL := (SbVirtio.hvSoundB hB hc hh1.1 hh1.2 (hC k1 (Nat.le_of_lt hk1)) e1.1 true e2 h).2 rfl
    have hr : e2.2 < ((stAt c k1).rows e2.1).length := hL.1
    have hmono := SbIssueCoCensus.rowsMonoAt c e2.1 k1 k2 (Nat.le_of_lt h12)
    have he22 : e2.2 = ((stAt c k2).rows e2.1).length := congrArg Prod.snd hd2
    omega

#print axioms Weak.SbIssueCoR.noForeignBelowR
#print axioms Weak.SbIssueCoR.issueCoOfCustodyR

end SbIssueCoR

end Weak
