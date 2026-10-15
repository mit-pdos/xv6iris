/-
Weak: **W10 [OWN.94] (N2′), decision (A), step 4c — the walk supply with skips from the order, and the
kill** (`PROGRESS-W10N2p.md`).  Lean-only, no Rocq twin.

  §1  **`CatLin.stepSupplyCZ4`** — the per-step datum RELATIVIZED to walk-invariant states with skips
      (`CertZ29.hartStepRI4`), given the walk order (W10-4's per-pc obligation, named);
  §2  **`CatLin.walkSupplyOfOrdStep4`** (`lockDiscCZ3 → gfDevWIoCZ → stepSupplyCZ4 → walkSupplyCZ4`: the
      order `CertZ23.ordOfDisc`, the policy `CertZ29.walkPolOfOrdR4`, the final padded lock co
      `CertZ30.lockCoOfOrd4`; fabric members are kept by NF3a);
  §3  **`CatLin.cycleKillOfOrdStepCZRC4`** — the zero-cut kill up to failed acquires.

Spec: FAITHFUL (proof organisation; the named premises' truth in `PROGRESS-W10N2p.md`).
-/
import Weak.CertZ30

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open TsoShadow

namespace CatLin

/-- **THE STEP SUPPLY AT WALK-INVARIANT STATES, WITH SKIPS (named, W10-4 per pc).** -/
def stepSupplyCZ4 (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image)
    (P : Int → Int → Prop) : Prop :=
  ∀ (GF : Gfexec) (ad : List (Geid × Geid)) (z : Geid) (ss : List Seg),
    GF.gfGd.gdG.gxImg = im → rvwmoCatAD GF.gfGd ad → GraphFabConf.gfexecConfZF boot d0 fab GF →
    ioResidueGmo GF → gdiskRead14 GF.gfGd.gdG →
    ss ≠ [] → rawChainC GF.gfGd (ioCross GF) z z ss →
    ∀ D : Nat → CertZ7.EmData, CertZ7.emDataOk boot fab GF D →
    ∀ L : List Geid, CertZ8.walkOrd GF.gfGd.gdG.gxProg GF.gfDev L →
      CertZ23.ordCoSP GF.gfGd.gdG L (GraphFetchN2.lockBytes P) →
    ∃ Rel : CertZ9.HRel,
      (∀ x, x < GF.gfGd.gdG.gxProg.length → Rel x 0 (boot x) (boot x)) ∧
      CertZ29.hartStepRI4 d0 GF.gfGd.gdG.gxProg (GraphFetchN2.lockBytes P) L Rel

/-- Fabric members are no failed acquires (NF3a: no lock-byte write is a fabric member). -/
theorem devKeep (GF : Gfexec) (Lb : Int → Prop) :
    CertZ23.lockDisc3 GF Lb →
    ∀ e, e ∈ GF.gfDev → CertZ29.keepEv GF.gfGd.gdG.gxProg Lb e = true := by
  intro hld e he
  obtain ⟨-, -, -, -, hNF3a, -⟩ := hld
  unfold CertZ29.keepEv
  cases hl : (GF.gfGd.gdG.gxProg.getD e.1 [])[e.2]? with
  | none => rfl
  | some l =>
    dsimp only
    rw [CertZ26.keepBTrue]
    intro hf
    have hx : e.1 < GF.gfGd.gdG.gxProg.length := by
      refine Nat.lt_of_not_le (fun hge => ?_)
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge, Option.getD_none] at hl
      cases hl
    have hlG : gxLbl GF.gfGd.gdG e = some l := by
      unfold gxLbl; rw [CertZ7.getDSome _ e.1 hx]; exact hl
    obtain ⟨b, hb, ⟨v, hw, -⟩, -⟩ := (CertZ24.failIff _ Lb e l hlG).1 hf
    exact hNF3a e ⟨b, v, hb, hw⟩ he

/-- **`walkSupplyOfOrdStep4` — THE WALK SUPPLY WITH SKIPS FROM THE ORDER AND THE STEP SUPPLY.** -/
theorem walkSupplyOfOrdStep4 (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image)
    (N : Nat) (P : Int → Int → Prop) :
    (∀ (GF : Gfexec) (ad : List (Geid × Geid)), GF.gfGd.gdG.gxImg = im → rvwmoCatAD GF.gfGd ad →
      GraphFabConf.gfexecConfZF boot d0 fab GF →
      GF.gfGd.gdG.gxProg.length ≤ N ∧ GraphFetchBlocks.emPremOk boot GF.gfGd.gdG) →
    lockDiscCZ3 boot d0 fab im P → gfDevWIoCZ boot d0 fab im → stepSupplyCZ4 boot d0 fab im P →
    walkSupplyCZ4 boot d0 fab im N P := by
  intro hpre hdisc hwio hstep GF ad z ss him hc hconf hres hdr hne hch
  obtain ⟨hN, hp2⟩ := hpre GF ad him hc hconf
  obtain ⟨D, hD⟩ := CertZ7.emDataOfConf boot d0 fab GF hconf hp2
  have hld := hdisc GF ad him hc hconf
  have hdevL : ∀ e, e ∈ GF.gfDev → (gxLbl GF.gfGd.gdG e).isSome := by
    intro e he
    obtain ⟨n, hn⟩ := List.mem_iff_getElem?.1 he
    obtain ⟨i, k⟩ := e
    obtain ⟨row, hrow, hk⟩ := hconf.2.2.1 n i k hn
    unfold gxLbl
    simp only [hrow, Option.bind_some]
    exact lookup_lt_is_Some_2 hk
  obtain ⟨L, hL, hco⟩ := CertZ23.ordOfDisc GF ad _ hc hres (hwio GF ad him hc hconf) hld hdevL
  obtain ⟨Rel, hR0, hsR⟩ := hstep GF ad z ss him hc hconf hres hdr hne hch D hD L hL hco
  have hsub : ∀ e, e ∈ GF.gfDev → e ∈ L := by
    intro e he
    obtain ⟨n, hn⟩ := List.mem_iff_getElem?.1 he
    obtain ⟨i, k⟩ := e
    obtain ⟨row, hrow, hk⟩ := hconf.2.2.1 n i k hn
    have hi : i < GF.gfGd.gdG.gxProg.length := lookup_lt_Some hrow
    refine (hL.2.1 _).2 ⟨hi, ?_⟩
    rw [List.getD_eq_getElem?_getD, hrow, Option.getD_some]
    exact hk
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
  refine ⟨CertZ29.lockInvR4 GF.gfGd.gdG.gxProg _ (fun x => (D x).f) Rel
      (CertZ29.prefInv4 GF.gfGd.gdG.gxProg _ L GF.gfDev fab), fun itvOf fiOf _ => ?_,
    CertZ29.walkPolOfOrdR4 boot d0 fab GF D L _ Rel hD hconf.2.1 hL hsub hshape
      (devKeep GF _ hld) hsR, ?_⟩
  · refine ⟨fun x hx => ⟨Nat.zero_le _, ⟨boot x, ?_, ?_⟩, ?_⟩, fun s hs => by simp [wlkStart] at hs,
      ⟨0, Nat.zero_le _, fun x => by simp, ?_, by simp [wlkStart]⟩⟩
    · show ((List.range' 0 N).map boot)[x]? = some (boot x)
      rw [List.getElem?_map, lookup_seq_lt (by omega), Nat.zero_add]
      rfl
    · obtain ⟨_, _, _, _, _, hf0, _⟩ := hD x _ (CertZ7.getDSome _ x hx)
      show Rel x 0 ((D x).f 0) (boot x)
      rw [hf0]
      exact hR0 x hx
    · show List.Forall₂ lblReidxW (((GF.gfGd.gdG.gxProg.getD x []).take 0).filter _)
        (CertZ2.hartTr [] x)
      simp [CertZ2.hartTr]
    · show d0 = fab _
      simp only [List.take_zero, List.filter_nil, List.length_nil]
      exact hconf.1.symm
  · intro Sf itvOf fiOf cntF hinv hok hdone
    obtain ⟨hper, hagt, ⟨k, hkL, hcnt, -, hags⟩⟩ := hinv
    have hk : k = L.length := by
      refine Nat.le_antisymm hkL (Nat.le_of_not_lt (fun hlt => ?_))
      obtain ⟨⟨x, a⟩, hx⟩ : ∃ e, L[k]? = some e := ⟨L[k], List.getElem?_eq_getElem hlt⟩
      have hev := (hL.2.1 _).1 (List.mem_of_getElem? hx)
      have hca := CertZ8.ordCount _ _ L k x a hL hx
      rw [← hcnt x] at hca
      have := hdone x hev.1
      have := hev.2
      dsimp only at this
      omega
    rw [hk, List.take_length] at hags
    have hyp : CertZ27.hyp GF.gfGd.gdG.gxProg.length GF.gfGd.gdG.gxProg
        (GraphFetchN2.lockBytes P) Sf.cstC := by
      refine ⟨rfl, hok.1, hagt, fun x hx => ?_⟩
      obtain ⟨hle, -, hf⟩ := hper x hx
      rw [List.take_of_length_le (Nat.le_antisymm hle (hdone x hx) ▸ Nat.le_refl _)] at hf
      exact hf
    exact CertZ30.lockCoOfOrd4 _ GF.gfDev L Sf.cstC _ hc.1 hL hco hags hyp
      (CertZ30.keepOfSp GF _ hld)

section glue

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode
open Language.Notation PrimStep
open LeanRV64D

/-- **`cycleKillOfOrdStepCZRC4`** — THE ZERO-CUT KILL UP TO FAILED ACQUIRES: WP package, `regZeroRun`,
fetch view, (harts ≤ N ∧ P2), the lock discipline (successful ops) and `gfDevWIo` for the ORDER, the
relativized STEP supply with skips, the two xv6 lock facts and the L2′ claim at the padded member. -/
theorem cycleKillOfOrdStepCZRC4 (hlc : HasLC) (GF0 : BundledGFunctors) [MachGpreS hlc GF0]
    [WeakGpreS GF0] (gen : Nat) (σ0 : WGState) (D : CPU → List Register) (hD : ∀ c, (D c).Nodup)
    (P : Int → Int → Prop)
    (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (N : Nat) :
    freshEra gen σ0 →
    (List.range' 0 N).map boot = epsInit σ0 →
    d0 = efInit σ0.wgdev →
    wpPackage hlc GF0 gen σ0 D →
    regZeroRun gen σ0 P →
    (∀ ρ, rtc epfRun (epInit gen, σ0) ρ → efetchItvOk ρ.1 ρ.2) →
    (∀ (GF : Gfexec) (ad : List (Geid × Geid)), GF.gfGd.gdG.gxImg = imgZ σ0.wgimg →
      rvwmoCatAD GF.gfGd ad → GraphFabConf.gfexecConfZF boot d0 fab GF →
      GF.gfGd.gdG.gxProg.length ≤ N ∧ GraphFetchBlocks.emPremOk boot GF.gfGd.gdG) →
    lockDiscCZ3 boot d0 fab (imgZ σ0.wgimg) P →
    gfDevWIoCZ boot d0 fab (imgZ σ0.wgimg) →
    stepSupplyCZ4 boot d0 fab (imgZ σ0.wgimg) P →
    acqAqCZ4 boot d0 fab (imgZ σ0.wgimg) P →
    relCoversCZ4 boot d0 fab (imgZ σ0.wgimg) P →
    l2ClaimCZR4 boot d0 fab (imgZ σ0.wgimg) P (badRun gen σ0) →
    cycleKillCZC boot d0 fab (imgZ σ0.wgimg) :=
  fun hfr hb1 hb2 hwp hrz hcov hpre hdisc hwio hstep hAQ hRC hl2 =>
    cycleKillOfL2CZRC4 hlc GF0 gen σ0 D hD P boot d0 fab N hfr hb1 hb2 hwp hrz hcov
      (cutSupplyOfCycleCZC boot d0 fab _)
      (certSupplyCZROfWalk4 boot d0 fab _ N P
        (walkSupplyOfOrdStep4 boot d0 fab _ N P hpre hdisc hwio hstep))
      hAQ hRC hl2

end glue

end CatLin

end Weak
