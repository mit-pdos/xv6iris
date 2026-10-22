/-
Weak: **the S-R `DomAt` lift, increment I-8 — `SbLockstepR`, row 6m UNDER S-R: the S-R walk CARRIES ITS
PROGRAMS** (ruling [OWN.150]; `Weak/SbProg.lean`'s construction re-hosted on `SbOrdR.PInvR`).  Lean-only, no
Rocq twin.  A leaf: nothing registered imports this file.

`SbProg` threads the program layer (`SbWalk.ok`'s `progOk`, every row's program state LOCKSTEP or
`TR`-tainted w.r.t. its emission) through the top-read gated walk; its invariant `SbProg.PrgInv`, the
fabric count `devCnt`, the landing step, the start and the lockstep machinery never look at the walk
invariant, so they are REUSED; what changes is the walk underneath (`SbOrdR.enbR`, `PInvR`, `noStuckR`,
`walkStepR`).  Under S-R a non-exempt member label is GF's VERBATIM, so the lockstep re-timing
(`SilSiteStep.setTs`) is the identity on it; the only exempt read left is `holding+0x12` ([OWN.124]).

  §1  `ReachR` (reachable S-R states), the named inputs re-stated over them: **`SailXR`** (the Sail meaning
      of the taint, O-P-W2-a — now ONE pc, `holding+0x12`, REVISIT [OWN.124]) and **`FetchProgR`** (fetch
      progress, F-6m-1, against `enbR`).
  §2  `emBlkAtR`, **`evStepR`** (lockstep off the exempt read, `SailXR` otherwise).
  §3  **`walkRunProgR`**, **`memberOfCatProgR`**.

Spec: FAITHFUL (proof organisation).  Named inputs: `SailXR`, `FetchProgR` (as `SbProg`'s, FAITHFUL,
WEAKER while named), `NoAqLd` (image census) and `StateIfcR`.  Lean-only helpers `SbOrdR.*`.
-/
import Weak.SbWalkR
import Weak.SbProg

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open TsoShadow
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D
open Lbl SbWalk SbAgree SbReplay SbOrd SbProg

namespace SbOrdR

/-! # 1. Reachable S-R states and the named inputs -/

/-- The reachable states of the S-R walk. -/
structure ReachR (GF : Gfexec) (N : Nat) (img : Image) (X : Geid → Prop) (S : St) : Prop where
  imgEq : S.c.img = img
  valid : validW SbPol.epoch S.c
  gated : gatedWR GF.gfGd.gdG X GF.gfDev S.c
  pinv : PInvR N img GF.gfGd.gdG X GF.gfDev (cur S.c)

/-- **`SailXR` — THE SAIL MEANING OF THE TAINT (NAMED; O-P-W2-a; REVISIT [OWN.124])**: `SbProg.SailX` over
the reachable S-R states. -/
def SailXR (GF : Gfexec) (N : Nat) (img : Image) (X : Geid → Prop) (d0 : Efab)
    (fab : Nat → Efab) (D : Nat → CertZ7.EmData) (TR : CertZ9.HRel) : Prop :=
  ∀ (S : St) (x : Nat) (pC : Pexv6) (l lb : Lbl),
    ReachR GF N img X S → PrgInv d0 fab GF.gfDev N D TR S → x < N →
    (S.pst S.c.its.length)[x]? = some pC →
    gxLbl GF.gfGd.gdG (hd (cur S.c) x) = some l →
    lblRelX (X (hd (cur S.c) x)) l lb →
    (X (hd (cur S.c) x) → exValL x l ∧ exValL x lb) →
    SbCand.stepE (cur S.c).σ x lb (SbCand.nextE (cur S.c).σ x lb) →
    (TR x ((cur S.c).rows x).length ((D x).f ((cur S.c).rows x).length) pC ∨
      (pC = (D x).f ((cur S.c).rows x).length ∧ X (hd (cur S.c) x))) →
    fetchOk (cur S.c) ((D x).g ((cur S.c).rows x).length) →
    hd (cur S.c) x ∉ GF.gfDev ∧
    ∃ pC', evData (cur S.c) x lb pC (S.dv S.c.its.length) pC' (S.dv S.c.its.length) ∧
      SilSiteStep.relS TR x (((cur S.c).rows x).length + 1)
        ((D x).f (((cur S.c).rows x).length + 1)) pC'

/-- **`FetchProgR` — FETCH PROGRESS (NAMED; finding F-6m-1)**: `SbProg.FetchProg` against the S-R gate. -/
def FetchProgR (GF : Gfexec) (N : Nat) (img : Image) (X : Geid → Prop) (d0 : Efab)
    (fab : Nat → Efab) (D : Nat → CertZ7.EmData) (TR : CertZ9.HRel) : Prop :=
  ∀ (S : St) (x : Nat), ReachR GF N img X S → PrgInv d0 fab GF.gfDev N D TR S →
    validT N GF.gfGd.gdG (cur S.c) (.hd x) →
    enbR SbPol.epoch GF.gfGd.gdG X GF.gfDev (cur S.c) (.hd x) → ¬ fetchReady D (cur S.c) x →
    ∃ T, validT N GF.gfGd.gdG (cur S.c) T ∧ enbR SbPol.epoch GF.gfGd.gdG X GF.gfDev (cur S.c) T ∧
      ∀ y, T = .hd y → fetchReady D (cur S.c) y

/-! # 2. The event step -/

/-- **THE EMISSION'S BLOCK AT THE WALK FABRIC** (`SbProg.emBlkAt` over `PInvR`). -/
theorem emBlkAtR (boot : Nat → Pexv6) (fab : Nat → Efab) (GF : Gfexec) (D : Nat → CertZ7.EmData)
    (hD : CertZ7.emDataOk boot fab GF D) (hnd : GF.gfDev.Nodup) (N : Nat) (img : Image)
    (X : Geid → Prop) (w : WS) (hP : PInvR N img GF.gfGd.gdG X GF.gfDev w) (x : Nat) (l : Lbl)
    (hl : gxLbl GF.gfGd.gdG (hd w x) = some l) (hfo : fabOk GF.gfDev w (hd w x)) (lb : Lbl) :
    SilSiteStep.emBlk D GF.gfGd.gdG.gxProg x (w.rows x).length l (fab (devCnt GF.gfDev w))
      (fab (devCnt GF.gfDev (nextI w (.ev ⟨x, lb⟩)))) := by
  unfold gxLbl hd at hl
  cases hr : GF.gfGd.gdG.gxProg[x]? with
  | none => rw [hr] at hl; cases hl
  | some row =>
    rw [hr] at hl
    simp only [Option.bind_some] at hl
    have hgd := getDOf _ x row hr
    have hn : (w.rows x).length < row.length := lookup_lt_Some hl
    obtain ⟨em, -, hiff, hpin, -, -, hblk⟩ := hD x row hr
    unfold SilSiteStep.emBlk
    rw [hgd]
    by_cases hin : (x, (w.rows x).length) ∈ GF.gfDev
    · obtain ⟨m, hm⟩ := List.mem_iff_getElem?.1 hin
      obtain ⟨h1, h2⟩ := devCntEvIn GF.gfDev w ⟨x, lb⟩ m hnd hm (hfo hin) hP.dvP
      obtain ⟨hdi, hdo⟩ := hpin _ m hm
      rw [h1, h2, ← hdi, ← hdo]
      rcases hblk _ l hl with ⟨hfu, hb, -⟩ | ⟨hb, -⟩
      · exact .inl ⟨hfu, hb⟩
      · exact .inr hb
    · have htq : (D x).tq (w.rows x).length = false := by
        cases h : (D x).tq (w.rows x).length with
        | false => rfl
        | true => exact absurd ((hiff _ hn).2 (.inr (.inr h))) hin
      rw [devCntEvOut GF.gfDev w ⟨x, lb⟩ hin]
      rcases hblk _ l hl with ⟨hfu, -, hq⟩ | ⟨-, hq⟩
      · exact .inl ⟨hfu, hq htq _⟩
      · exact .inr (hq htq _)

/-- **THE S-R EVENT STEP** — lockstep (`SbReplay.lockBlk`) off the exempt read, `SailXR` at tainted states
and the exempt read: the program invariant extends along an appended event of row `x`. -/
theorem evStepR (GF : Gfexec) (N : Nat) (img : Image) (X : Geid → Prop) (boot : Nat → Pexv6)
    (d0 : Efab) (fab : Nat → Efab) (D : Nat → CertZ7.EmData) (TR : CertZ9.HRel)
    (hD : CertZ7.emDataOk boot fab GF D) (hnd : GF.gfDev.Nodup) (hexG : ExValGF GF.gfGd.gdG X)
    (hsail : SailXR GF N img X d0 fab D TR)
    (S : St) (hR : ReachR GF N img X S) (hI : PrgInv d0 fab GF.gfDev N D TR S) (x : Nat) (hx : x < N)
    (s : Estep) (hs : s.esAg = x)
    (hv' : validW SbPol.epoch (snocC S.c (.ev s)))
    (hP' : PInvR N img GF.gfGd.gdG X GF.gfDev (cur (snocC S.c (.ev s))))
    (he : enbR SbPol.epoch GF.gfGd.gdG X GF.gfDev (cur S.c) (.hd x))
    (hfr : fetchReady D (cur S.c) x) :
    ∃ pC' d', PrgInv d0 fab GF.gfDev N D TR (snocE S s pC' d') := by
  subst hs
  obtain ⟨-, l, hl, hfo, -⟩ := id he
  obtain ⟨pC, hpC, hrel⟩ := hI.rel s.esAg hx
  have hrowsN : (cur (snocC S.c (.ev s))).rows s.esAg = (cur S.c).rows s.esAg ++ [s.esLb] := by
    rw [curSnoc, rowsEvEq, if_pos rfl]
  have hlbAt : ((cur (snocC S.c (.ev s))).rows s.esAg)[((cur S.c).rows s.esAg).length]? = some s.esLb := by
    rw [hrowsN]; simp
  obtain ⟨l0, hl0, hrx⟩ := hP'.pf.1 s.esAg ((cur S.c).rows s.esAg).length s.esLb hlbAt
  have hl0' : gxLbl GF.gfGd.gdG (hd (cur S.c) s.esAg) = some l0 := hl0
  rw [hl] at hl0'
  cases hl0'
  have hexl : X (hd (cur S.c) s.esAg) → exValL s.esAg s.esLb :=
    fun hX => hP'.ex s.esAg ((cur S.c).rows s.esAg).length s.esLb hlbAt hX
  have hstep : SbCand.stepE (cur S.c).σ s.esAg s.esLb (SbCand.nextE (cur S.c).σ s.esAg s.esLb) :=
    okIOfSnoc S.c _ hv'
  have hfin : ∀ (pC' : Pexv6) (d' : Efab),
      evData (cur S.c) s.esAg s.esLb pC (S.dv S.c.its.length) pC' d' →
      SilSiteStep.relS TR s.esAg (((cur S.c).rows s.esAg).length + 1)
        ((D s.esAg).f (((cur S.c).rows s.esAg).length + 1)) pC' →
      d' = fab (devCnt GF.gfDev (nextI (cur S.c) (.ev s))) →
      PrgInv d0 fab GF.gfDev N D TR (snocE S s pC' d') := by
    intro pC' d' hev hrel' hd'
    have hcur : cur (snocE S s pC' d').c = nextI (cur S.c) (.ev s) := curSnoc S.c (.ev s)
    have hlen' : (snocE S s pC' d').c.its.length = S.c.its.length + 1 := by simp [snocE, snocC]
    have hn' : ¬ S.c.its.length + 1 ≤ S.c.its.length := by omega
    refine ⟨okSnocE SbPol.epoch d0 S s pC pC' d' hI.ok hpC (okIOfSnoc S.c _ hv') hev, fun y hy => ?_, ?_⟩
    · rw [hlen', hcur]
      dsimp only [snocE]
      rw [if_neg hn', rowsEvEq]
      by_cases hys : y = s.esAg
      · subst hys
        rw [if_pos rfl, List.length_append, List.length_singleton]
        exact ⟨pC', List.getElem?_set_self (lookup_lt_Some hpC), hrel'⟩
      · rw [if_neg hys]
        obtain ⟨q, hq, hqr⟩ := hI.rel y hy
        exact ⟨q, by rw [List.getElem?_set_ne (Ne.symm hys)]; exact hq, hqr⟩
    · rw [hlen', hcur]
      dsimp only [snocE]
      rw [if_neg hn', hd']
  by_cases hlock : pC = (D s.esAg).f ((cur S.c).rows s.esAg).length ∧ ¬ X (hd (cur S.c) s.esAg)
  · -- LOCKSTEP
    obtain ⟨hpe, hnX⟩ := hlock
    have hre : lblReidx l s.esLb := by
      rcases hrx with ⟨-, h⟩ | ⟨h, -⟩
      · exact h
      · exact absurd h hnX
    have hblk := emBlkAtR boot fab GF D hD hnd N img X (cur S.c) hR.pinv s.esAg l hl hfo s.esLb
    have hr := relpAgree SbPol.epoch S.c GF.gfGd.gdG X s.esAg hR.valid hR.pinv.pf
    have hev := lockBlk (cur S.c) s.esAg D GF.gfGd.gdG.gxProg ((cur S.c).rows s.esAg).length l _ _
      (tsOfL s.esLb) hr hblk hfr (tsOfLLoad l _ hre) (tsOfLRmw l _ hre)
    rw [setTsOfReidx l _ hre, ← hpe, ← hI.fab] at hev
    have hdv : devCnt GF.gfDev (nextI (cur S.c) (.ev ⟨s.esAg, s.esLb⟩)) =
        devCnt GF.gfDev (nextI (cur S.c) (.ev s)) := rfl
    exact ⟨_, _, hfin _ _ hev (.inl rfl) (by rw [hdv])⟩
  · -- TAINTED, or LOCKSTEP at the exempt read
    have harm : TR s.esAg ((cur S.c).rows s.esAg).length ((D s.esAg).f ((cur S.c).rows s.esAg).length) pC ∨
        (pC = (D s.esAg).f ((cur S.c).rows s.esAg).length ∧ X (hd (cur S.c) s.esAg)) := by
      rcases hrel with h | h
      · exact .inr ⟨h, Classical.byContradiction (fun hn' => hlock ⟨h, hn'⟩)⟩
      · exact .inl h
    obtain ⟨hout, pC', hev, hrel'⟩ := hsail S s.esAg pC l s.esLb hR hI hx hpC hl hrx
      (fun hX => ⟨hexG _ l hX hl, hexl hX⟩) hstep harm hfr
    refine ⟨pC', _, hfin pC' _ hev hrel' ?_⟩
    rw [hI.fab, devCntEvOut GF.gfDev (cur S.c) s hout]

/-! # 3. The program-carrying S-R walk -/

theorem nonFinalR {N : Nat} {img : Image} {G : Gexec} {X : Geid → Prop} {dev : List Geid} {w : WS}
    (hP : PInvR N img G X dev w)
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

/-- **`walkRunProgR` — THE S-R WALK RUNS TO COMPLETION CARRYING ITS PROGRAMS.** -/
theorem walkRunProgR (GF : Gfexec) (N : Nat) (img : Image) (X : Geid → Prop)
    (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (D : Nat → CertZ7.EmData) (TR : CertZ9.HRel)
    (hW : WalkHyp GF N img X) (hNA : NoAqLd GF.gfGd.gdG)
    (hS : ∀ c, validW SbPol.epoch c → gatedWR GF.gfGd.gdG X GF.gfDev c → c.img = img →
      PInvR N img GF.gfGd.gdG X GF.gfDev (cur c) → StateIfcR GF.gfGd.gdG X GF.gfDev c)
    (hD : CertZ7.emDataOk boot fab GF D) (hf0 : fab 0 = d0) (hnd : GF.gfDev.Nodup)
    (hexG : ExValGF GF.gfGd.gdG X)
    (hsail : SailXR GF N img X d0 fab D TR) (hfp : FetchProgR GF N img X d0 fab D TR) :
    ∃ S, ReachR GF N img X S ∧ PrgInv d0 fab GF.gfDev N D TR S ∧
      (∀ x, x < N → ((cur S.c).rows x).length = (GF.gfGd.gdG.gxProg.getD x []).length) ∧
      drained (cur S.c) := by
  suffices H : ∀ k S, ReachR GF N img X S → PrgInv d0 fab GF.gfDev N D TR S →
      work N GF.gfGd.gdG (cur S.c) ≤ k →
      ∃ S', ReachR GF N img X S' ∧ PrgInv d0 fab GF.gfDev N D TR S' ∧
        (∀ x, x < N → ((cur S'.c).rows x).length = (GF.gfGd.gdG.gxProg.getD x []).length) ∧
        drained (cur S'.c) by
    exact H _ (start boot d0 N img)
      ⟨rfl, fun k it h => by simp [start] at h, gatedNilR _ X _ img, pinvInitR N img _ hW.cat.wf X _⟩
      (prgStart boot d0 fab GF D TR N img hD hW.len hf0) (Nat.le_refl _)
  intro k
  induction k with
  | zero =>
    intro S hR hI hw
    by_cases hfin : (∀ x, x < N → ((cur S.c).rows x).length = (GF.gfGd.gdG.gxProg.getD x []).length) ∧
        drained (cur S.c)
    · exact ⟨S, hR, hI, hfin.1, hfin.2⟩
    · exfalso
      have hSI := hS S.c hR.valid hR.gated hR.imgEq hR.pinv
      obtain ⟨T, hT, he⟩ := noStuckR GF N img X (cur S.c) hW.cat hW.io hW.wio hW.imgF hNA hW.len hR.pinv
        hW.devSt hW.devFab hW.hart hSI.head (nonFinalR hR.pinv hfin)
      have hW' : WalkHyp GF N S.c.img X := hR.imgEq ▸ hW
      have hP' : PInvR N S.c.img GF.gfGd.gdG X GF.gfDev (cur S.c) := hR.imgEq ▸ hR.pinv
      obtain ⟨it, -, -, hlt, -⟩ := walkStepR GF N X S.c hW' hR.valid hP' hSI.exv T hT he
      omega
  | succ k ih =>
    intro S hR hI hw
    by_cases hfin : (∀ x, x < N → ((cur S.c).rows x).length = (GF.gfGd.gdG.gxProg.getD x []).length) ∧
        drained (cur S.c)
    · exact ⟨S, hR, hI, hfin.1, hfin.2⟩
    · have hSI := hS S.c hR.valid hR.gated hR.imgEq hR.pinv
      obtain ⟨T0, hT0, he0⟩ := noStuckR GF N img X (cur S.c) hW.cat hW.io hW.wio hW.imgF hNA hW.len
        hR.pinv hW.devSt hW.devFab hW.hart hSI.head (nonFinalR hR.pinv hfin)
      obtain ⟨T, hT, he, hfr⟩ : ∃ T, validT N GF.gfGd.gdG (cur S.c) T ∧
          enbR SbPol.epoch GF.gfGd.gdG X GF.gfDev (cur S.c) T ∧
          ∀ y, T = .hd y → fetchReady D (cur S.c) y := by
        cases T0 with
        | ld i j => exact ⟨_, hT0, he0, fun y h => by cases h⟩
        | hd x =>
          by_cases hx : fetchReady D (cur S.c) x
          · exact ⟨_, hT0, he0, fun y h => by cases h; exact hx⟩
          · exact hfp S x hR hI hT0 he0 hx
      have hW' : WalkHyp GF N S.c.img X := hR.imgEq ▸ hW
      have hP0 : PInvR N S.c.img GF.gfGd.gdG X GF.gfDev (cur S.c) := hR.imgEq ▸ hR.pinv
      have hEx : ExValMin GF.gfGd.gdG X (cur S.c) := hSI.exv
      obtain ⟨it, hv', hP', hlt, hit⟩ := walkStepR GF N X S.c hW' hR.valid hP0 hEx T hT he
      have hP'' : PInvR N img GF.gfGd.gdG X GF.gfDev (cur (snocC S.c it)) := hR.imgEq ▸ hP'
      have hg' : gatedWR GF.gfGd.gdG X GF.gfDev (snocC S.c it) :=
        gatedSnocR _ X _ S.c it hR.gated (by rw [hit]; exact he)
      cases it with
      | land i j =>
        have hR' : ReachR GF N img X (snocL S i j) := ⟨hR.imgEq, hv', hg', hP''⟩
        exact ih (snocL S i j) hR' (landStep d0 fab GF.gfDev N D TR S hI i j hv') (by
          show work N GF.gfGd.gdG (cur (snocC S.c (.land i j))) ≤ k; omega)
      | ev s =>
        have hsx : T = .hd s.esAg := hit.symm
        subst hsx
        obtain ⟨hx, -⟩ := hT
        obtain ⟨pC', d', hI'⟩ := evStepR GF N img X boot d0 fab D TR hD hnd hexG hsail S hR hI
          s.esAg hx s rfl hv' hP'' he (hfr _ rfl)
        have hR' : ReachR GF N img X (snocE S s pC' d') := ⟨hR.imgEq, hv', hg', hP''⟩
        exact ih (snocE S s pC' d') hR' hI' (by
          show work N GF.gfGd.gdG (cur (snocC S.c (.ev s))) ≤ k; omega)

/-- **A COMPLETED, PROGRAM-CARRYING S-R MEMBER** (`walkRunProgR` + `memberOfRunR`). -/
theorem memberOfCatProgR (GF : Gfexec) (N : Nat) (img : Image) (X : Geid → Prop)
    (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (D : Nat → CertZ7.EmData) (TR : CertZ9.HRel)
    (hW : WalkHyp GF N img X) (hNA : NoAqLd GF.gfGd.gdG)
    (hS : ∀ c, validW SbPol.epoch c → gatedWR GF.gfGd.gdG X GF.gfDev c → c.img = img →
      PInvR N img GF.gfGd.gdG X GF.gfDev (cur c) → StateIfcR GF.gfGd.gdG X GF.gfDev c)
    (hD : CertZ7.emDataOk boot fab GF D) (hf0 : fab 0 = d0) (hnd : GF.gfDev.Nodup)
    (hexG : ExValGF GF.gfGd.gdG X)
    (hsail : SailXR GF N img X d0 fab D TR) (hfp : FetchProgR GF N img X d0 fab D TR) :
    ∃ S, S.c.img = img ∧ validW SbPol.epoch S.c ∧ drained (cur S.c) ∧
      PrgInv d0 fab GF.gfDev N D TR S ∧
      gwf (memberP N S.c) ∧ logOf (memberP N S.c) (logP S.c) ∧
      CertZ18.rmwLatest (memberP N S.c) (logP S.c) ∧ agreeX GF.gfGd.gdG (memberP N S.c) X ∧
      CertZ24.agreeW4 GF.gfGd.gdG (memberP N S.c) (fun _ => False) ∧
      (∀ L, CertZ18.agreeW3 GF.gfGd.gdG (memberP N S.c) L) ∧
      valEqX GF.gfGd.gdG (memberP N S.c) X := by
  obtain ⟨S, hR, hI, hfin, hdr⟩ :=
    walkRunProgR GF N img X boot d0 fab D TR hW hNA hS hD hf0 hnd hexG hsail hfp
  have hP0 : PInvR N S.c.img GF.gfGd.gdG X GF.gfDev (cur S.c) := hR.imgEq ▸ hR.pinv
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := memberOfRunR SbPol.epoch N GF.gfGd.gdG X GF.gfDev S.c hR.valid
    hW.cat.wf (hW.imgEq.trans hR.imgEq.symm) hW.len hP0 hfin hdr
  exact ⟨S, hR.imgEq, hR.valid, hdr, hI, h1, h2, h3, h4, h5, h6, h7 hexG⟩

end SbOrdR

end Weak
