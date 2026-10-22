/-
Weak: **allocproc route P, row P-W6 — `IssueCo` DISCHARGED by the write-write custody census**
(F-PW6-1 (a), [OWN.149]; `weakmach/proposal-A7.md` §3.4 (ii); `PROGRESS-PW6.md` CP-PW6-5).  Lean-only, no
Rocq twin.  A PRIMED TWIN: nothing registered imports this file.

**Spec first.**  RVWMO orders two harts' plain stores to one byte only through the program's
synchronisation (ppo, fences, rf); xv6 synchronises every such pair (design §2.1, R45 A13): a shared byte
is written under a lock (the previous holder's stores precede its `fence rw,w` release, the next holder's
`amoswap.aq` reads that release or a later one), by one designated hart (`started`, PTEs by their owner),
or across the boot hand-off (hart 0's initialisation stores precede its draining `fence` and the
`started := 1` store; the other harts read `started = 1` before their first store).  The walk's free issue
order meets MachCSL's issue-order landing (`SbRealP.landBlockedForeign`) only if such a pair is issued
"backwards" while the earlier store is still pending — `SbIssueCo.IssueCo` forbids exactly that.

**`SbIssueCoCensus.WwCustody` (NAMED census, GF-level, the write-write twin of `SbBlocked.NonCensusSrc`)**:
for two plain stores of DIFFERENT rows writing a common byte, one is LANDED by the extended chain
`SbVirtio.Hv` rooted at the other (program order, fabric order, a realized AMO's source, the release
epoch, the draining fence, co below a landed write, a realized counter read's source).  FAITHFUL (true of
xv6 by the lock / custody / boot discipline above: the lock hand-off is `Hv.root`/`po` + `Hv.amo` +
`Hv.epoch`, the boot hand-off is the `started` read through `Hv.ctr` + `Hv.po` + `Hv.drain`); WEAKER
while named.  The realized-prefix input is the EXISTING `SbVirtio.CtrLanded`, at a read set `Ctr` that
must contain the `started` reads (a new instance, not a new kind of input).

**`SbIssueCoCensus.issueCoOfCustody`**: along a valid epoch walk with `PInv` at every state and
`CtrLanded` at every state, `WwCustody` gives `IssueCo` — in fact its premise never holds:
* if the earlier-issued store `e1` is `Hv`-landed from the later one `e2`, it has LANDED by `e2`'s issue
  (`SbVirtio.hvSound` at `e2`'s state) — not pending;
* if `e2` is `Hv`-landed from `e1`, it was REALIZED at `e1`'s issue (`hvSound` at `e1`'s state) — but it is
  issued later.

**Why the census and not the kill's linearization K** (A7 [B6.s1]): `IssueCo` from K needs a walk that
issues each store at its K position — a different issue gate in `SbOrd` (excluded now), and K exists only
in the COMPLETENESS role: the walk is also the kill's instrument (`SbKill.cycleKillCoreP` walks a GF ASSUMED
to have a racy cycle, so no K exists there).  The census serves both roles, needs no `SbOrd` edit, and
reuses the proved chain soundness (`hvSound`) and the already-named `CtrLanded` — it is the cheaper
faithful route.

Lean-only helpers `SbIssueCoCensus.*`.
-/
import Weak.SbIssueCo
import Weak.SbVirtio

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Lbl SbWalk SbAgree SbReplay SbOrd SbIssueCo

namespace SbIssueCoCensus

/-- **`WwCustody` (NAMED census)**: two different rows' plain stores on a common byte are ordered by the
extended custody chain, one way or the other. -/
def WwCustody (G : Gexec) (dev : List Geid) (Ctr : Geid → Prop) : Prop :=
  ∀ (e1 e2 : Geid) (l1 l2 : Lbl) (a : Int), e1.1 ≠ e2.1 →
    gxLbl G e1 = some l1 → gxLbl G e2 = some l2 → isSt l1 = true → isSt l2 = true →
    wrsB l1 a = true → wrsB l2 a = true →
    SbVirtio.Hv G dev Ctr e2 true e1 ∨ SbVirtio.Hv G dev Ctr e1 true e2

/-- The event an item steps is its row's head at the state before it. -/
theorem evAtHd (c : CandW) (k : Nat) (e : Geid) (h : SbIssueCo.evAt c k = some e) :
    k < c.its.length ∧ e = hd (stAt c k) e.1 := by
  unfold SbIssueCo.evAt at h
  cases hk : c.its[k]? with
  | none => rw [hk] at h; cases h
  | some it =>
    rw [hk] at h
    cases it with
    | land i j => cases h
    | ev s =>
      simp only [Option.some.injEq] at h
      subst h
      exact ⟨lookup_lt_Some hk, rfl⟩

/-- One item only appends to a row. -/
theorem rowsStep (w : WS) (it : Item) (x : Nat) : (w.rows x).length ≤ ((nextI w it).rows x).length := by
  cases it with
  | ev s =>
    show (w.rows x).length ≤ (upd w.rows s.esAg (w.rows s.esAg ++ [s.esLb]) x).length
    by_cases hx : x = s.esAg
    · subst hx; rw [updEq]; simp
    · rw [updNe _ _ _ _ hx]; exact Nat.le_refl _
  | land i k =>
    cases hp : (w.pend i)[k]? <;> simp [nextI, hp]

/-- Rows only grow along the walk. -/
theorem rowsMonoAt (c : CandW) (x k : Nat) : ∀ k', k ≤ k' →
    ((stAt c k).rows x).length ≤ ((stAt c k').rows x).length := by
  intro k' hk
  induction k' with
  | zero =>
    have : k = 0 := by omega
    subst this; exact Nat.le_refl _
  | succ k' ih =>
    rcases Nat.eq_or_lt_of_le hk with h | h
    · rw [h]; exact Nat.le_refl _
    · have h1 := ih (by omega)
      cases hi : c.its[k']? with
      | none =>
        have : stAt c (k' + 1) = stAt c k' := by
          show (match c.its[k']? with
            | some it => nextI (stAt c k') it
            | none => stAt c k') = _
          rw [hi]
        rw [this]; exact h1
      | some it =>
        rw [stAtSucc c k' it hi]
        exact Nat.le_trans h1 (rowsStep _ it x)

theorem gisWOfSt (G : Gexec) (e : Geid) (l : Lbl) (hl : gxLbl G e = some l) (hs : isSt l = true) :
    gisW G e = true := by
  unfold gisW; rw [hl]
  cases l <;> simp_all [isSt, lbIsW]

/-- **`IssueCo` FROM THE WRITE-WRITE CUSTODY CENSUS**: along a valid epoch walk with the walk invariant and
`CtrLanded` at every state, `WwCustody` gives `IssueCo` (its premise is never met). -/
theorem issueCoOfCustody {N : Nat} {X : Geid → Prop} {dev : List Geid} (G : Gexec) (c : CandW)
    (Ctr : Geid → Prop) (hv : validW SbPol.epoch c)
    (hP : ∀ k, k ≤ c.its.length → PInv N c.img G X dev (stAt c k)) (hc : CatH G)
    (hC : ∀ k, k ≤ c.its.length → SbVirtio.CtrLanded G Ctr (stAt c k))
    (hW : WwCustody G dev Ctr) : IssueCo G c := by
  intro k1 k2 e1 e2 l1 l2 a h12 he1 he2 hne hl1 hl2 hs1 hs2 hw1 hw2 hnot
  exfalso
  obtain ⟨hk1, hd1⟩ := evAtHd c k1 e1 he1
  obtain ⟨hk2, hd2⟩ := evAtHd c k2 e2 he2
  have hh1 := SbBlocked.histStAt c hv k1
  have hh2 := SbBlocked.histStAt c hv k2
  rcases hW e1 e2 l1 l2 a hne hl1 hl2 hs1 hs2 hw1 hw2 with h | h
  · -- `e1` landed by `e2`'s issue: not pending
    rw [hd2] at h
    have hL := (SbVirtio.hvSound (hP k2 (Nat.le_of_lt hk2)) hc hh2.1 hh2.2 (hC k2 (Nat.le_of_lt hk2))
      e2.1 true e1 h).2 rfl
    exact hnot (SbBlocked.landedGmo (hP k2 (Nat.le_of_lt hk2)) e1 hL (gisWOfSt G e1 l1 hl1 hs1))
  · -- `e2` realized at `e1`'s issue: but it is issued later
    rw [hd1] at h
    have hL := (SbVirtio.hvSound (hP k1 (Nat.le_of_lt hk1)) hc hh1.1 hh1.2 (hC k1 (Nat.le_of_lt hk1))
      e1.1 true e2 h).2 rfl
    have hr : e2.2 < ((stAt c k1).rows e2.1).length := hL.1
    have hmono := rowsMonoAt c e2.1 k1 k2 (Nat.le_of_lt h12)
    have he22 : e2.2 = ((stAt c k2).rows e2.1).length := congrArg Prod.snd hd2
    omega

#print axioms Weak.SbIssueCoCensus.issueCoOfCustody

end SbIssueCoCensus

end Weak
