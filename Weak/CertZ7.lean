/-
Weak: **W10-3 [OWN.94] (N2′), increment 2 — the zero-cut walk supply FROM A SCHEDULER over the
bundle's emissions** (`PROGRESS-W10N2p.md`).  Lean-only, no Rocq twin.

`CatLin.walkSupplyCZ` (`Weak/CertZ3.lean`) asks for a walk invariant, its start, the walk policy
and the final lock co.  `CertZ6.walkPolOfSched` builds the policy from a scheduler over the harts'
emission blocks.  This file closes the gap to the bundle:

  §1  the per-hart emission datum `CertZ7.EmData` and its fit to the bundle `CertZ7.emDataOk`
      (an emission of the row from the boot state, its fabric membership/pins, its Zifencei slot,
      and the extracted blocks); **`CertZ7.emDataOfConf`**: the Zifencei bundle with (P2) gives one;
  §2  the SCHEDULER SUPPLY **`CatLin.schedSupplyCZ`** — THE NAMED PREMISE now left at the zero cut
      (for every fitting emission datum: an extra invariant `X` holding at the start, the scheduler
      `CertZ6.schedZ`, and the lock-co agreement of a finished walk) — and
      **`CatLin.walkSupplyOfSched`** (`walkSupplyCZ` from it, the hart count ≤ `N` and (P2) for the
      whole graph); **`CatLin.cycleKillOfSchedCZRC`** — the kill W11-F consumes.

Spec: (P2) for the whole graph is the plan's D19 scope restriction (`GraphFetchBlocks` §1: a dangling
LR is outside the theorem; the kernel has no LR/SC), EQUAL to M2's clause (i); the hart count is a
bundle fact.  FAITHFUL; nothing assumed of `GF`'s gmo.  Lean-only helpers file-qualified
(`CertZ7.*`).
-/
import Weak.CertZ6

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open TsoShadow

/-! # 1. The emission datum -/

/-- A hart's emission datum: program states, leading stars, realizing labels, fabric endpoints,
contact bits. -/
structure CertZ7.EmData where
  f : Nat → Pexv6
  g : Nat → List Wlabel
  r : Nat → Wlabel
  dvi : Nat → Efab
  dvo : Nat → Efab
  tq : Nat → Bool

/-- The datum FITS the bundle at hart `x`'s row: an emission of the row from the boot state, with
the bundle's fabric membership and pins and its Zifencei slot, and the datum's blocks. -/
def CertZ7.emDataOk (boot : Nat → Pexv6) (fab : Nat → Efab) (GF : Gfexec)
    (D : Nat → CertZ7.EmData) : Prop :=
  ∀ (x : Nat) (row : List Lbl), GF.gfGd.gdG.gxProg[x]? = some row →
    ∃ em : Hemission,
      hartConff x row (boot x) (D x).dvi (D x).dvo (D x).tq em ∧
      (∀ k : Nat, k < row.length →
        ((x, k) ∈ GF.gfDev ↔ (gisIo GF.gfGd.gdG (x, k) = true ∨ (D x).dvi k ≠ (D x).dvo k ∨
          (D x).tq k = true))) ∧
      (∀ (k n : Nat), GF.gfDev[n]? = some (x, k) → (D x).dvi k = fab n ∧ (D x).dvo k = fab (n + 1)) ∧
      (emZifencei GF.gfGd.gdG x em ∧ GraphFetch.emFetchIn GF.gfGd x em) ∧
      (D x).f 0 = boot x ∧
      CertZ6.emBlocks row (D x).f (D x).g (D x).r (D x).dvi (D x).dvo (D x).tq

/-- **A FITTING DATUM EXISTS** for every graph carrying the bundle, under (P2). -/
theorem CertZ7.emDataOfConf (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (GF : Gfexec) :
    GraphFabConf.gfexecConfZF boot d0 fab GF → GraphFetchBlocks.emPremOk boot GF.gfGd.gdG →
    ∃ D : Nat → CertZ7.EmData, CertZ7.emDataOk boot fab GF D := by
  rintro ⟨-, -, -, hrows⟩ hp2
  have h : ∀ x, ∃ d : CertZ7.EmData, ∀ row, GF.gfGd.gdG.gxProg[x]? = some row →
      ∃ em : Hemission,
        hartConff x row (boot x) d.dvi d.dvo d.tq em ∧
        (∀ k : Nat, k < row.length →
          ((x, k) ∈ GF.gfDev ↔ (gisIo GF.gfGd.gdG (x, k) = true ∨ d.dvi k ≠ d.dvo k ∨
            d.tq k = true))) ∧
        (∀ (k n : Nat), GF.gfDev[n]? = some (x, k) → d.dvi k = fab n ∧ d.dvo k = fab (n + 1)) ∧
        (emZifencei GF.gfGd.gdG x em ∧ GraphFetch.emFetchIn GF.gfGd x em) ∧
        d.f 0 = boot x ∧ CertZ6.emBlocks row d.f d.g d.r d.dvi d.dvo d.tq := by
    intro x
    cases hx : GF.gfGd.gdG.gxProg[x]? with
    | none =>
      exact ⟨⟨fun _ => boot x, fun _ => [], fun _ => .LSilent, fun _ => d0, fun _ => d0,
        fun _ => false⟩, fun row h => by cases h⟩
    | some row =>
      obtain ⟨em, dvi, dvo, tq, hem, hiff, hpin, hfi, -⟩ := hrows x row hx
      obtain ⟨f, g, r, hf0, hblk⟩ :=
        CertZ6.emBlocksOfHart x row (boot x) dvi dvo tq em hem (hp2 x row em dvi dvo tq hx hem)
      refine ⟨⟨f, g, r, dvi, dvo, tq⟩, fun row' h => ?_⟩
      rw [Option.some.injEq] at h
      subst h
      exact ⟨em, hem, hiff, hpin, hfi, hf0, hblk⟩
  exact ⟨fun x => Classical.choose (h x), fun x row hx => Classical.choose_spec (h x) row hx⟩

/-! # 2. The scheduler supply -/

theorem CertZ7.getDSome (rows : List (List Lbl)) (x : Nat) :
    x < rows.length → rows[x]? = some (rows.getD x []) := by
  intro hx
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hx, Option.getD_some]


namespace CatLin

/-- **THE SCHEDULER SUPPLY — THE NAMED PREMISE AT THE ZERO CUT (W10-3b order + device order + lock co,
W10-4 values / poison)**: on every cyclic class graph with the residue facts, for every emission
datum fitting the bundle, an extra invariant `X` holding at the empty start, the scheduler
(`CertZ6.schedZ`: an enabled hart whose reads/fetches agree in value with the latest bytes), and,
at a finished lockstep walk, the lock-co agreement of its member with `GF`. -/
def schedSupplyCZ (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image) (N : Nat)
    (P : Int → Int → Prop) : Prop :=
  ∀ (GF : Gfexec) (ad : List (Geid × Geid)) (z : Geid) (ss : List Seg),
    GF.gfGd.gdG.gxImg = im → rvwmoCatAD GF.gfGd ad → GraphFabConf.gfexecConfZF boot d0 fab GF →
    ioResidueGmo GF → gdiskRead14 GF.gfGd.gdG →
    ss ≠ [] → rawChainC GF.gfGd (ioCross GF) z z ss →
    ∀ D : Nat → CertZ7.EmData, CertZ7.emDataOk boot fab GF D →
    ∃ X : CertZ2.WInv,
      (∀ itvOf fiOf, CertZ.cstOkZW d0 (wlkStart boot d0 N GF.gfGd.gdG) itvOf fiOf →
        X (wlkStart boot d0 N GF.gfGd.gdG) itvOf fiOf (fun _ => 0)) ∧
      CertZ6.schedZ d0 GF.gfGd.gdG.gxProg (fun x => (D x).f) (fun x => (D x).g)
        (fun x => (D x).dvi) (fun x => (D x).dvo) (fun x => (D x).tq) X ∧
      (∀ Sf itvOf fiOf cntF,
        CertZ6.lockInv GF.gfGd.gdG.gxProg (fun x => (D x).f) X Sf itvOf fiOf cntF →
        CertZ.cstOkZW d0 Sf itvOf fiOf →
        (∀ x, x < GF.gfGd.gdG.gxProg.length →
          (GF.gfGd.gdG.gxProg.getD x []).length ≤ cntF x) →
        GraphFetchN2.lockCoAgree GF.gfGd.gdG
          (CertZ3.member GF.gfGd.gdG.gxProg.length Sf.cstC) (GraphFetchN2.lockBytes P))

/-- **`walkSupplyOfSched`** — the zero-cut walk supply from the scheduler supply, the hart count
and (P2) for the whole graph: the lockstep invariant from the boot states, the policy by
`CertZ6.walkPolOfSched`, the shapes by `gwf`. -/
theorem walkSupplyOfSched (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image)
    (N : Nat) (P : Int → Int → Prop) :
    (∀ (GF : Gfexec) (ad : List (Geid × Geid)), GF.gfGd.gdG.gxImg = im → rvwmoCatAD GF.gfGd ad →
      GraphFabConf.gfexecConfZF boot d0 fab GF →
      GF.gfGd.gdG.gxProg.length ≤ N ∧ GraphFetchBlocks.emPremOk boot GF.gfGd.gdG) →
    schedSupplyCZ boot d0 fab im N P → walkSupplyCZ boot d0 fab im N P := by
  intro hpre hsup GF ad z ss him hc hconf hres hdr hne hch
  obtain ⟨hN, hp2⟩ := hpre GF ad him hc hconf
  obtain ⟨D, hD⟩ := CertZ7.emDataOfConf boot d0 fab GF hconf hp2
  obtain ⟨X, hX0, hsch, hco⟩ := hsup GF ad z ss him hc hconf hres hdr hne hch D hD
  have hblk : ∀ x, x < GF.gfGd.gdG.gxProg.length →
      CertZ6.emBlocks (GF.gfGd.gdG.gxProg.getD x []) (D x).f (D x).g (D x).r (D x).dvi
        (D x).dvo (D x).tq := by
    intro x hx
    obtain ⟨_, _, _, _, _, _, hb⟩ := hD x _ (CertZ7.getDSome _ x hx)
    exact hb
  have hshape : ∀ (x n : Nat) (lb : Lbl), (GF.gfGd.gdG.gxProg.getD x [])[n]? = some lb →
      CertZ4.lblShape lb := by
    intro x n lb hlb
    have hx : x < GF.gfGd.gdG.gxProg.length := by
      refine Nat.lt_of_not_le (fun hge => ?_)
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge, Option.getD_none] at hlb
      cases hlb
    have hl : gxLbl GF.gfGd.gdG (x, n) = some lb := by
      unfold gxLbl
      rw [CertZ7.getDSome _ x hx]
      exact hlb
    have := gwfLblShape GF.gfGd.gdG (x, n) lb hc.1 hl
    cases lb <;> exact this
  refine ⟨CertZ6.lockInv GF.gfGd.gdG.gxProg (fun x => (D x).f) X, fun itvOf fiOf hok => ?_,
    CertZ6.walkPolOfSched d0 _ _ _ (fun x => (D x).r) _ _ _ X hshape hblk hsch,
    fun Sf itvOf fiOf cntF hinv hok hdone => hco Sf itvOf fiOf cntF hinv hok hdone⟩
  refine ⟨fun x hx => ⟨Nat.zero_le _, ?_, ?_⟩, fun s hs => by simp [wlkStart] at hs,
    hX0 itvOf fiOf hok⟩
  · obtain ⟨_, _, _, _, _, hf0, _⟩ := hD x _ (CertZ7.getDSome _ x hx)
    show ((List.range' 0 N).map boot)[x]? = some ((D x).f 0)
    rw [hf0, List.getElem?_map, lookup_seq_lt (by omega), Nat.zero_add]
    rfl
  · show List.Forall₂ lblReidxW ((GF.gfGd.gdG.gxProg.getD x []).take 0) (CertZ2.hartTr [] x)
    simp [CertZ2.hartTr]

section glue

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode
open Language.Notation PrimStep
open LeanRV64D

/-- **`cycleKillOfSchedCZRC`** — WHAT W11-F CONSUMES AT THE ZERO CUT (N2′, after W10-2/W10-3 inc. 1–2):
the class kill from the WP package, the fetch-view premise, the hart count and (P2), the SCHEDULER
SUPPLY (`schedSupplyCZ`), the two xv6 facts and the L2′ claim at the member. -/
theorem cycleKillOfSchedCZRC (hlc : HasLC) (GF0 : BundledGFunctors) [MachGpreS hlc GF0]
    [WeakGpreS GF0] (gen : Nat) (σ0 : WGState) (D : CPU → List Register) (hD : ∀ c, (D c).Nodup)
    (Nm : Int → Int → Namespace) (P : Int → Int → Prop)
    (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (N : Nat) :
    freshEra gen σ0 →
    (List.range' 0 N).map boot = epsInit σ0 →
    d0 = efInit σ0.wgdev →
    wpPackage hlc GF0 gen σ0 D →
    (∀ a base, P a base → wpPackageProt hlc GF0 gen σ0 D (Nm a base) a base) →
    (∀ ρ, rtc epfRun (epInit gen, σ0) ρ → efetchItvOk ρ.1 ρ.2) →
    (∀ (GF : Gfexec) (ad : List (Geid × Geid)), GF.gfGd.gdG.gxImg = imgZ σ0.wgimg →
      rvwmoCatAD GF.gfGd ad → GraphFabConf.gfexecConfZF boot d0 fab GF →
      GF.gfGd.gdG.gxProg.length ≤ N ∧ GraphFetchBlocks.emPremOk boot GF.gfGd.gdG) →
    schedSupplyCZ boot d0 fab (imgZ σ0.wgimg) N P →
    acqAqCZ boot d0 fab (imgZ σ0.wgimg) P →
    relCoversCZ boot d0 fab (imgZ σ0.wgimg) P →
    l2ClaimCZR boot d0 fab (imgZ σ0.wgimg) P (badRun gen σ0) →
    cycleKillCZC boot d0 fab (imgZ σ0.wgimg) :=
  fun hfr hb1 hb2 hwp hwpp hcov hpre hsup hAQ hRC hl2 =>
    cycleKillOfWalkSupCZRC hlc GF0 gen σ0 D hD Nm P boot d0 fab N hfr hb1 hb2 hwp hwpp hcov
      (walkSupplyOfSched boot d0 fab _ N P hpre hsup) hAQ hRC hl2

end glue

end CatLin

end Weak
