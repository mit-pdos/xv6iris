/-
Weak: **the S-R `DomAt` lift, increment I-4 — `SbWalkR`, THE S-R WALK RUNS TO COMPLETION and its MEMBER**
(ruling [OWN.150]; `PROGRESS-DomAt.md` §0.2).  Lean-only, no Rocq twin.  A leaf: nothing registered
imports this file.

  §1  gated S-R candidates (`gatedWR`: every item enabled at its state by the S-R gate) and the per-state
      named interfaces `StateIfcR` — row H3′ `HeadOrdW` and the min-rule exempt value `ExValMin` (the
      `holding+0x12` class only: the two `ip->ref` reads are NOT exempt under S-R, so `IrefTop`/`IrefGF`
      — MachCSL Q5/Q6 — have no consumer here).
  §2  **`walkRunR`**: from the empty walk, given the global hypotheses (`SbOrd.WalkHyp`), the census
      `NoAqLd` and the per-state interfaces at every reachable gated candidate, a FINISHED gated S-R walk.
  §3  **`memberOfRunR` / `memberOfCatR`**: its member is a well-formed graph whose writes are the landed
      log, whose AMOs read the latest bytes, which AGREES with GF (`agreeX`), with `agreeW4`, `agreeW3` at
      every lock set, and value agreement given `ExValGF`.

Spec: FAITHFUL (proof organisation).  Lean-only helpers `SbOrdR.*`.
-/
import Weak.SbProgR

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Lbl

namespace SbOrdR

open SbWalk SbAgree SbReplay SbOrd SpikeSP SbDom

/-! # 1. Gated candidates and the per-state interfaces -/

/-- **A GATED S-R CANDIDATE**: every item was ENABLED by the S-R gate at the walk state before it. -/
def gatedWR (G : Gexec) (X : Geid → Prop) (dev : List Geid) (c : CandW) : Prop :=
  ∀ (k : Nat) (it : Item), c.its[k]? = some it → enbR SbPol.epoch G X dev (stAt c k) (itemTgt it)

theorem gatedNilR (G : Gexec) (X : Geid → Prop) (dev : List Geid) (img : Image) :
    gatedWR G X dev ⟨img, []⟩ := fun _ _ h => by simp at h

theorem gatedSnocR (G : Gexec) (X : Geid → Prop) (dev : List Geid) (c : CandW) (it : Item)
    (hg : gatedWR G X dev c) (he : enbR SbPol.epoch G X dev (cur c) (itemTgt it)) :
    gatedWR G X dev (snocC c it) := by
  intro k it' hk
  change (c.its ++ [it])[k]? = some it' at hk
  by_cases hlt : k < c.its.length
  · rw [List.getElem?_append_left hlt] at hk
    rw [stAtSnoc c it k (Nat.le_of_lt hlt)]
    exact hg k it' hk
  · have hk' : k = c.its.length := by
      have := (List.getElem?_eq_some_iff.1 hk).1
      simp only [List.length_append, List.length_singleton] at this
      omega
    subst hk'
    rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self] at hk
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
    subst hk
    rw [stAtSnoc c it _ (Nat.le_refl _)]
    exact he

/-- **WHAT THE S-R WALK NEEDS AT EVERY REACHABLE CANDIDATE (NAMED)**: row H3′ and the min-rule exempt
value. -/
structure StateIfcR (G : Gexec) (X : Geid → Prop) (dev : List Geid) (c : CandW) : Prop where
  head : HeadOrdW G X dev (cur c)
  exv : ExValMin G X (cur c)

/-! # 2. The run -/

/-- **`walkRunR` — THE S-R WALK RUNS TO COMPLETION.** -/
theorem walkRunR (GF : Gfexec) (N : Nat) (img : Image) (X : Geid → Prop)
    (hW : WalkHyp GF N img X) (hNA : NoAqLd GF.gfGd.gdG)
    (hS : ∀ c, validW SbPol.epoch c → gatedWR GF.gfGd.gdG X GF.gfDev c → c.img = img →
      PInvR N img GF.gfGd.gdG X GF.gfDev (cur c) → StateIfcR GF.gfGd.gdG X GF.gfDev c) :
    ∃ c, c.img = img ∧ validW SbPol.epoch c ∧ PInvR N img GF.gfGd.gdG X GF.gfDev (cur c) ∧
      (∀ x, x < N → ((cur c).rows x).length = (GF.gfGd.gdG.gxProg.getD x []).length) ∧
      drained (cur c) ∧ gatedWR GF.gfGd.gdG X GF.gfDev c := by
  suffices H : ∀ n c, validW SbPol.epoch c → gatedWR GF.gfGd.gdG X GF.gfDev c → c.img = img →
      PInvR N img GF.gfGd.gdG X GF.gfDev (cur c) → work N GF.gfGd.gdG (cur c) ≤ n →
      ∃ c', c'.img = img ∧ validW SbPol.epoch c' ∧ PInvR N img GF.gfGd.gdG X GF.gfDev (cur c') ∧
        (∀ x, x < N → ((cur c').rows x).length = (GF.gfGd.gdG.gxProg.getD x []).length) ∧
        drained (cur c') ∧ gatedWR GF.gfGd.gdG X GF.gfDev c' by
    exact H _ ⟨img, []⟩ (fun k it h => by simp at h) (gatedNilR _ X _ img) rfl
      (pinvInitR N img _ hW.cat.wf X _) (Nat.le_refl _)
  intro n
  induction n with
  | zero =>
    intro c hv hg hc hP hw
    by_cases hfin : (∀ x, x < N → ((cur c).rows x).length = (GF.gfGd.gdG.gxProg.getD x []).length) ∧
        drained (cur c)
    · exact ⟨c, hc, hv, hP, hfin.1, hfin.2, hg⟩
    · exfalso
      obtain ⟨T, hT, he⟩ := noStuckR GF N img X (cur c) hW.cat hW.io hW.wio hW.imgF hNA hW.len hP
        hW.devSt hW.devFab hW.hart (hS c hv hg hc hP).head (nonFinal hP hfin)
      subst hc
      obtain ⟨it, -, -, hlt, -⟩ := walkStepR GF N X c hW hv hP (hS c hv hg rfl hP).exv T hT he
      omega
  | succ n ih =>
    intro c hv hg hc hP hw
    by_cases hfin : (∀ x, x < N → ((cur c).rows x).length = (GF.gfGd.gdG.gxProg.getD x []).length) ∧
        drained (cur c)
    · exact ⟨c, hc, hv, hP, hfin.1, hfin.2, hg⟩
    · obtain ⟨T, hT, he⟩ := noStuckR GF N img X (cur c) hW.cat hW.io hW.wio hW.imgF hNA hW.len hP
        hW.devSt hW.devFab hW.hart (hS c hv hg hc hP).head (nonFinal hP hfin)
      subst hc
      obtain ⟨it, hv', hP', hlt, hit⟩ := walkStepR GF N X c hW hv hP (hS c hv hg rfl hP).exv T hT he
      exact ih (snocC c it) hv' (gatedSnocR _ X _ c it hg (by rw [hit]; exact he)) rfl hP'
        (by omega)
where
  nonFinal {G : Gexec} {dev : List Geid} {w : WS} (hP : PInvR N img G X dev w)
      (hfin : ¬ ((∀ x, x < N → (w.rows x).length = (G.gxProg.getD x []).length) ∧ drained w)) :
      (∃ x, x < N ∧ (w.rows x).length < (G.gxProg.getD x []).length) ∨ (∃ i, w.pend i ≠ []) := by
    by_cases h1 : ∀ x, x < N → (w.rows x).length = (G.gxProg.getD x []).length
    · have h2 : ¬ drained w := fun h => hfin ⟨h1, h⟩
      obtain ⟨i, hi⟩ : ∃ i, w.pend i ≠ [] :=
        Classical.byContradiction (fun hn => h2 (fun i => Classical.byContradiction (fun h => hn ⟨i, h⟩)))
      exact .inr ⟨i, hi⟩
    · obtain ⟨x, hx, hne⟩ : ∃ x, x < N ∧ (w.rows x).length ≠ (G.gxProg.getD x []).length :=
        Classical.byContradiction (fun hn => h1 (fun x hx =>
          Classical.byContradiction (fun h => hn ⟨x, hx, h⟩)))
      exact .inl ⟨x, hx, by have := hP.len x; omega⟩

/-! # 3. The member -/

/-- **THE FINISHED S-R WALK'S MEMBER.** -/
theorem memberOfRunR (pol : SbPol) (N : Nat) (G : Gexec) (X : Geid → Prop) (dev : List Geid) (c : CandW)
    (hv : validW pol c) (hwf : gwf G) (himg : G.gxImg = c.img) (hN : G.gxProg.length = N)
    (hP : PInvR N c.img G X dev (cur c))
    (hfin : ∀ x, x < N → ((cur c).rows x).length = (G.gxProg.getD x []).length)
    (hdr : drained (cur c)) :
    gwf (memberP N c) ∧ logOf (memberP N c) (logP c) ∧
    CertZ18.rmwLatest (memberP N c) (logP c) ∧ agreeX G (memberP N c) X ∧
    CertZ24.agreeW4 G (memberP N c) (fun _ => False) ∧
    (∀ L, CertZ18.agreeW3 G (memberP N c) L) ∧
    (ExValGF G X → valEqX G (memberP N c) X) := by
  have hR : RmwInv c.img (cur c) := rmwInvStAt pol c hv _
  have hagr := agreeXOfPfx N c.img G X (cur c) hP.inv hP.ag hdr hwf himg hN hfin hP.pf
  exact ⟨memberGwf N _ _ hP.inv hP.ag hdr, memberLogOf N _ _ hP.inv hP.ag,
    memberRmwLatest N _ _ hP.inv hR hP.ag hdr, hagr, agreeW4OfX _ _ X hagr,
    fun L => agreeW3OfX _ _ X L hagr, fun hG => valEqXOfAgree _ _ X hagr hG (memberExOk N _ X _ hP.ex)⟩

/-- **A COMPLETED S-R MEMBER FOR EVERY CAT-CONSISTENT GF** (modulo the census `NoAqLd` and the per-state
interfaces `StateIfcR`, asked only at gated candidates). -/
theorem memberOfCatR (GF : Gfexec) (N : Nat) (img : Image) (X : Geid → Prop)
    (hW : WalkHyp GF N img X) (hNA : NoAqLd GF.gfGd.gdG)
    (hS : ∀ c, validW SbPol.epoch c → gatedWR GF.gfGd.gdG X GF.gfDev c → c.img = img →
      PInvR N img GF.gfGd.gdG X GF.gfDev (cur c) → StateIfcR GF.gfGd.gdG X GF.gfDev c) :
    ∃ c, c.img = img ∧ validW SbPol.epoch c ∧ drained (cur c) ∧
      gwf (memberP N c) ∧ logOf (memberP N c) (logP c) ∧
      CertZ18.rmwLatest (memberP N c) (logP c) ∧ agreeX GF.gfGd.gdG (memberP N c) X ∧
      CertZ24.agreeW4 GF.gfGd.gdG (memberP N c) (fun _ => False) ∧
      (∀ L, CertZ18.agreeW3 GF.gfGd.gdG (memberP N c) L) ∧
      (ExValGF GF.gfGd.gdG X → valEqX GF.gfGd.gdG (memberP N c) X) := by
  obtain ⟨c, hc, hv, hP, hfin, hdr, -⟩ := walkRunR GF N img X hW hNA hS
  subst hc
  exact ⟨c, rfl, hv, hdr, memberOfRunR SbPol.epoch N _ X _ c hv hW.cat.wf hW.imgEq hW.len hP hfin hdr⟩

end SbOrdR

end Weak
