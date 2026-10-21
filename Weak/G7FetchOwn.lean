/-
Weak: **row 6h — W11-F A11, the E2/E3 "early" half of G7's fetch arm split by WRITER** (rulings
[OWN.137] Q-6H-1 = (a), [OWN.138] Q-6H-2 = (r1); `PROGRESS-w2-6h.md`).  Lean-only, no Rocq twin.

Under route P the early half (`fetchReplayOk`, `Weak/G7Fetch.lean`) has no replay state: it is asked
at the CLASS graph's cut, and the `SbCand` member agrees with GF only per byte (`SbAgree.agreeX`), so
no buffered run realizes GF's cross-address gmo (finding F-6h-1).  It is equivalent to a pure graph
fact — no write to a fetched byte co-after its source lies gmo-before the fetching hart's next own
write — and that fact is FALSE for a user RWX page (F-6h-2: a user self-store after the fetch may
land gmo-before the hart's next own store).  This file splits the fact by writer:

  §1  **`fetchEarlyForeign`** — the FOREIGN-writer half, the NAMED premise (REVISIT [OWN.137]); TRUE of
      xv6 (every writer other than the fetching hart reaches a user text byte only through a lock
      hand-off from a release po-after the slot).
  §2  the OWN-HART arm ([OWN.138]), by program order and the trusted item `gzFetch`:
      * **`G7FetchOwn.ownLateE3`** — an E3 edge into an own write at/after the slot: CS-chained by
        (Z2) (E1′), exactly as `g7E1Chained`;
      * **`G7FetchOwn.ownFencedNone`** — an own write PO-BEFORE a fence.i site before the slot is
        never co-after the fetch's source ((Z3): it is its own contributor).
      The remaining own cases — an E2 edge into an own write at/after the slot, and an own write
      po-before the slot with no fence.i between — are NOT dischargeable by program order (finding
      F-6h-3, `PROGRESS-w2-6h.md` §5): RVWMO orders neither a contributor before a later own event
      nor an own store before the hart's own later fetch.  They occur only through a user RWX page.
  §3  the bridge **`G7FetchOwn.fetchReplayOkOf`**: the old interface from the two halves.

Spec (FIRST): RVWMO / riscv.cat have no fetch events; Zifencei orders this hart's later fetches
after stores visible to it at `fence.i` and leaves a self-store race on a writable+executable page
to the program; the arms add no trusted text (`gzFetch` (Z2)/(Z3) as stated).  FAITHFUL.
Lean-only helpers are `G7FetchOwn.*`.
-/
import Weak.CapFetchProv

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std

/-! # 1. The foreign-writer early half (NAMED, [OWN.137]) -/

/-- **THE EARLY HALF, FOREIGN WRITERS (NAMED PREMISE, [OWN.137]; REVISIT [OWN.137]).**  For every
fetched byte of hart `i`'s fetch item at slot `k`, every write `w′` to it co-after the byte's source
by an agent OTHER than hart `i` is gmo-after hart `i`'s next own write (`gfcut < gwix w′`).

*Truth reason (xv6):* a user text byte (`U ∧ X ∧ ¬W`) is written by another agent only after the
fetching process's epoch has ended — `exit`/`exec` → `freeproc`/`uvmfree`/`kfree` junk, `kalloc`,
`uvmcopy`, `loadseg` — through a lock hand-off (`p->lock`, `wait_lock`, `kmem.lock`) whose release
on hart `i` is po-after the slot, so at or after `gnxw` (`fence rw,w`), and whose acquire is
po-before `w′` (ppo + rfe ⊆ gmo); a write co-after the source and gmo-before the fetch is excluded by
(Z3): it precedes the hand-off's release, whose store hart `i`'s acquire reads before `userret`'s
`fence.i` (a contributor); DMA never targets a user page; kernel text is never written.
**REVISIT [OWN.137]** — named until plan row A2 (G7 O2, [OWN.101]) lands: A2's lock-hand-off
argument (every E2/E3 target is gmo-after hart `i`'s release po-after the slot) discharges it,
+0.3–0.8k on top of A2.  Under route P it has no replay proof (F-6h-1, `PROGRESS-w2-6h.md`). -/
def fetchEarlyForeign (G : Gexec) (i k : Nat) (base : Int) (tvs : List (Nat × BitVec 8)) : Prop :=
  ∀ (j t : Nat) (v : BitVec 8), tvs[j]? = some (t, v) →
    ∀ (w' : Geid) (v' : BitVec 8), gwritesByte G w' (base + (j : Int)) v' → t < gwix G w' →
      w'.1 ≠ i → gfcut G i k < gwix G w'

/-- The own-writer early half: every own write to a fetched byte co-after its source is gmo-after
the hart's next own write.  (NOT a premise of this file: FALSE in general for a user RWX page,
F-6h-2; recorded for the bridge §3.) -/
def G7FetchOwn.ownEarlyNone (G : Gexec) (i k : Nat) (base : Int) (tvs : List (Nat × BitVec 8)) :
    Prop :=
  ∀ (j t : Nat) (v : BitVec 8), tvs[j]? = some (t, v) →
    ∀ (w' : Geid) (v' : BitVec 8), gwritesByte G w' (base + (j : Int)) v' → t < gwix G w' →
      w'.1 = i → gfcut G i k < gwix G w'

/-! # 2. The own-hart arm ([OWN.138]) -/

/-- **E3 INTO AN OWN PO-LATER WRITE — CS-chained by (Z2)**: the edge's source is another fetched
byte's source, the segment runs on hart `i` from at/after the slot, so (E1′) puts the source
gmo-before its exit. -/
theorem G7FetchOwn.ownLateE3 (GD : Gdexec) (ad : List (Geid × Geid)) (X : Geid → Geid → Prop)
    (C : Geid → Prop) (i k : Nat) (base : Int) (tvs : List (Nat × BitVec 8)) (prev : Geid)
    (s : Seg) (hc : CatLin.rvwmoCatAD GD ad) (hz : gzFetch GD.gdG C i k base tvs)
    (hx : ∃ (l tl : Nat) (vl : BitVec 8), tvs[l]? = some (tl, vl) ∧ gwriteAt GD.gdG tl = some prev)
    (hy : s.sgEntry.1 = i) (hk : k ≤ s.sgEntry.2) (hrun : CatLin.segRunC GD s)
    (hm : gmem GD.gdG s.sgExit) : CatLin.CertC GD.gdG X prev s := by
  obtain ⟨l, tl, vl, hl, hw⟩ := hx
  obtain ⟨h1, h2⟩ := G7Fetch.rtcSameLex GD ad hc _ _ hrun
  have hi : s.sgExit.1 = i := h1.symm.trans hy
  have hex : s.sgExit = (i, s.sgExit.2) := Prod.ext hi rfl
  refine .CSchained ?_
  rw [hex]
  rw [hex] at hm
  exact (hz l tl vl hl).2.1 prev s.sgExit.2 hw (by omega) hm

/-- **AN OWN WRITE BEFORE A FENCE.I IS NEVER CO-AFTER THE SOURCE** ((Z3)): an own write po-before a
fence.i site before the slot is a contributor, and (Z3) would put it gmo-before itself. -/
theorem G7FetchOwn.ownFencedNone (G : Gexec) (fi : Nat → Prop) (i k : Nat) (base : Int)
    (tvs : List (Nat × BitVec 8)) (j t : Nat) (v : BitVec 8) (w' : Geid) (v' : BitVec 8) (f : Nat)
    (hz : gzFetch G (gzContrib G fi i k) i k base tvs) (hj : tvs[j]? = some (t, v))
    (hw : gwritesByte G w' (base + (j : Int)) v') (ht : t < gwix G w') (hi : w'.1 = i)
    (hf : f < k) (hfi : fi f) (hwf : w'.2 < f) : False := by
  have hcon : gzContrib G fi i k w' :=
    ⟨f, hf, hfi, .inl ⟨hi, hwf, WeakRvwmoGraph.gwritesByteGisW G w' _ v' hw⟩⟩
  exact gmoLtIrrefl G w' (((hz j t v hj).2.2 w' v' hw ht).1 w' hcon)

/-! # 3. The bridge to G7's interface -/

/-- **`fetchReplayOk` from the two halves** (its replay disjunct vacuous: no early write at all). -/
theorem G7FetchOwn.fetchReplayOkOf (G : Gexec) (i k : Nat) (base : Int)
    (tvs : List (Nat × BitVec 8)) (hf : fetchEarlyForeign G i k base tvs)
    (ho : G7FetchOwn.ownEarlyNone G i k base tvs) : fetchReplayOk G i k base tvs := by
  intro j t v hj
  refine .inr fun w' v' hw ht hcut => ?_
  exfalso
  by_cases h : w'.1 = i
  · have := ho j t v hj w' v' hw ht h
    omega
  · have := hf j t v hj w' v' hw ht h
    omega

end Weak
