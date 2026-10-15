/-
Weak: **W10 F1 [OWN.94] (N2′), decision (A), step 3c — the cert supply from the walk with skips**
(`PROGRESS-W10N2p.md`).  Lean-only, no Rocq twin.

`CatLin.walkSupplyCZ4` (the walk with skip steps, `CertZ26.walkPolZ4`, whose finished state's PADDED member
agrees with `GF` on successful-protocol lock co) and **`CatLin.certSupplyCZROfWalk4`**
(`walkSupplyCZ4 → certSupplyCZR4`: the free walk with skips, the padded member `CertZ27.pad` — well-formed,
its log the run's, program write order, RMW atomicity, the padded label agreement).

Spec: FAITHFUL (proof organisation).
-/
import Weak.CertZ27

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open TsoShadow

namespace CatLin

/-- The walk supply with skip steps; its final clause is the PADDED member's lock co. -/
def walkSupplyCZ4 (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image) (N : Nat)
    (P : Int → Int → Prop) : Prop :=
  ∀ (GF : Gfexec) (ad : List (Geid × Geid)) (z : Geid) (ss : List Seg),
    GF.gfGd.gdG.gxImg = im → rvwmoCatAD GF.gfGd ad → GraphFabConf.gfexecConfZF boot d0 fab GF →
    ioResidueGmo GF → gdiskRead14 GF.gfGd.gdG →
    ss ≠ [] → rawChainC GF.gfGd (ioCross GF) z z ss →
    ∃ Inv : CertZ2.WInv,
      (∀ itvOf fiOf, CertZ.cstOkZW d0 (wlkStart boot d0 N GF.gfGd.gdG) itvOf fiOf →
        Inv (wlkStart boot d0 N GF.gfGd.gdG) itvOf fiOf (fun _ => 0)) ∧
      CertZ26.walkPolZ4 d0 GF.gfGd.gdG.gxProg (GraphFetchN2.lockBytes P) Inv ∧
      (∀ Sf itvOf fiOf cntF, Inv Sf itvOf fiOf cntF → CertZ.cstOkZW d0 Sf itvOf fiOf →
        (∀ x, x < GF.gfGd.gdG.gxProg.length →
          (GF.gfGd.gdG.gxProg.getD x []).length ≤ cntF x) →
        CertZ18.lockCoSP GF.gfGd.gdG
          (CertZ27.pad GF.gfGd.gdG.gxProg.length GF.gfGd.gdG.gxProg (GraphFetchN2.lockBytes P)
            Sf.cstC)
          (GraphFetchN2.lockBytes P))

/-- **(G-3) AT THE PADDED MEMBER FROM THE FREE WALK WITH SKIPS.** -/
theorem certSupplyCZROfWalk4 (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image)
    (N : Nat) (P : Int → Int → Prop) :
    walkSupplyCZ4 boot d0 fab im N P → certSupplyCZR4 boot d0 fab im N P := by
  intro hws GF ad _ z ss him hc hconf hres hdr _ _ _ _ _ hne hch
  obtain ⟨Inv, hI0, hpol, hco⟩ := hws GF ad z ss him hc hconf hres hdr hne hch
  have hstart := wlkStartInvZ boot d0 N GF.gfGd.gdG
  obtain ⟨itv0, fi0, hok0⟩ := CertZ.cstOkZWOf d0 _ hstart.1
  obtain ⟨_, Sf, itvF, fiF, cntF, tradd, hrun, hokF, hinvF, hdone, -, htr, hf2, hagt, himg,
    hpst⟩ := CertZ26.walkRunZ4 d0 GF.gfGd.gdG.gxProg _ Inv hpol _ (wlkStart boot d0 N GF.gfGd.gdG)
      itv0 fi0 (fun _ => 0) (Nat.le_refl _) hok0 (hI0 itv0 fi0 hok0)
  have htr' : Sf.cstC.cdTr = tradd := by rw [htr]; rfl
  have hagS : ∀ s, s ∈ Sf.cstC.cdTr → s.esAg < GF.gfGd.gdG.gxProg.length := by
    rw [htr']; exact hagt
  have hcons := hokF.1
  have hyp : CertZ27.hyp GF.gfGd.gdG.gxProg.length GF.gfGd.gdG.gxProg (GraphFetchN2.lockBytes P)
      Sf.cstC := by
    refine ⟨rfl, hcons, hagS, fun x hx => ?_⟩
    have hfx := hf2 x
    rw [List.drop_zero, Nat.sub_zero, List.take_of_length_le (hdone x hx)] at hfx
    rw [htr']
    exact hfx
  have hlogM : logOf (CertZ3.member GF.gfGd.gdG.gxProg.length Sf.cstC)
      (cdLog Sf.cstC Sf.cstC.cdTr.length) :=
    logOfOfPfx _ _ (CertZ3.memberLogPfx GF.gfGd.gdG.gxProg.length Sf.cstC hcons hagS)
  refine ⟨Sf.cstC, Sf.cstPst, Sf.cstDv,
    CertZ27.pad GF.gfGd.gdG.gxProg.length GF.gfGd.gdG.gxProg (GraphFetchN2.lockBytes P) Sf.cstC,
    fun t => t,
    runDataZOfCyc boot d0 N GF.gfGd.gdG Sf (CertZ.cstOkZOfW _ _ _ _ hokF) (by rw [himg]; rfl)
      (by rw [hpst]; rfl),
    CertZ27.padLogOf _ _ _ _ _ hyp hlogM, CertZ27.padGwf _ _ _ _ hyp,
    ⟨show Sf.cstC.cdImg = _ by rw [himg]; rfl, CertZ27.padLblAgree GF.gfGd.gdG _ Sf.cstC hyp,
      hco Sf itvF fiF cntF hinvF hokF hdone⟩,
    CertZ27.padGwrowGmo _ _ _ _ hyp (CertZ3.memberGwrowGmo _ _ hagS),
    CertZ27.padRmwLatest _ _ _ _ _ hyp (CertZ20.memberRmwLatest _ _ hcons hagS)⟩

end CatLin

end Weak
