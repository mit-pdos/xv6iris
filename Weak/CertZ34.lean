/-
Weak: **W10-4 [OWN.94] (N2′), decision (A), step 5a — the LAGGED relation for the failed-iteration lag**
(`PROGRESS-W10N2p.md`).  Lean-only, no Rocq twin.

After skipped failed acquires the certified hart lags behind its emission: it is still where the
emission was before the spin loop's first failed iteration.  **`CertZ34.relLag TT`**: the certified state
is `relT TT`-related (lockstep or tainted) to an emission state at an EARLIER slot `m0`, every slot from
`m0` on being a failed acquire (`m0 = m`: no lag, the ordinary relation).

**`CertZ34.siteStepLag`** — the per-pc datum at walk-invariant states for this relation: with no lag the
ordinary site facts (`CertZ13.siteFacts`) and the wRelp agreement; with a lag the SPIN-LOOP fact (from the
lagging certified state, a step realizing the slot's label — the loop head's `amoswap.w.aq` reading the
free value — that re-converges with the emission after it).  **`CertZ34.hartStepOfSiteLag`**
(`siteStepLag → hartStepRI4 (relLag TT)`, the skip clause FREE: a failed slot only extends the lag),
`CatLin.siteSupplyLag` → `CatLin.stepSupplyCZ4`, and the kill `CatLin.cycleKillOfOrdSiteLagCZRC4`.

Spec: the datum is per pc (W10-4); its lag clause is the failed-iteration fact in re-converging form;
FAITHFUL.  Lean-only helpers file-qualified (`CertZ34.*`).
-/
import Weak.CertZ33

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open TsoShadow

/-- The failed slots `[m0, m)` of hart `x`'s row. -/
def CertZ34.failRun (rows : List (List Lbl)) (Lb : Int → Prop) (x m0 m : Nat) : Prop :=
  ∀ j, m0 ≤ j → j < m → ∃ lb, (rows.getD x [])[j]? = some lb ∧ CertZ24.lblFail Lb lb

/-- **THE LAGGED RELATION.** -/
def CertZ34.relLag (rows : List (List Lbl)) (Lb : Int → Prop) (TT : Nat → Nat → List Nat) :
    CertZ9.HRel :=
  fun x m pE pC => ∃ (m0 : Nat) (pE0 : Pexv6), m0 ≤ m ∧ CertZ13.relT TT x m0 pE0 pC ∧
    CertZ34.failRun rows Lb x m0 m ∧ (m0 = m → pE0 = pE)

/-- **THE SITE DATUM FOR THE LAGGED RELATION** (W10-4 per pc, named).

WARNING (`PROGRESS-W10N2p.md`): its LAG clause is FALSE as stated — after skipped failed iterations the
emission has retired more instructions, so its `minstret` / `mcycle` differ from the certified hart's,
and `relT` (via `dregAgree`) compares every register without an `eregNum` EXACTLY.  The reduction
(`hartStepOfSiteLag`) is sound; the relation must agree MODULO the counters.  Do not consume. -/
def CertZ34.siteStepLag (d0 : Efab) (rows : List (List Lbl)) (Lb : Int → Prop) (L : List Geid)
    (TT : Nat → Nat → List Nat) : Prop :=
  ∀ (St : CycState) (itvOf : Nat → Nat → Nat) (fiOf : Nat → Nat → Bool) (x n : Nat) (lb : Lbl)
    (ws : Wstate) (ls : List Wlabel) (l : Wlabel) (pE pE' pC : Pexv6) (d' : Efab) (k : Nat),
    CertZ.cstOkZW d0 St itvOf fiOf →
    (St.cstPst (cdEnd St.cstC))[x]? = some pC → CertZ4.lblShape lb →
    ((lbFused l ∧ GraphFetchBlocks.blkOne (St.cstDv (cdEnd St.cstC)) d' ws lb ls l pE pE') ∨
      GraphFetchBlocks.blkPair (St.cstDv (cdEnd St.cstC)) d' ws lb ls l pE pE') →
    St.cstC.cdTr.map Estep.esAg = ((L.take k).filter (CertZ29.keepEv rows Lb)).map Prod.fst →
    L[k]? = some (x, n) →
    (∀ y, y < rows.length →
      List.Forall₂ lblReidxW
        (((rows.getD y []).take (((L.take k).filter (fun e => decide (e.1 = y))).length)).filter
          (CertZ26.keepB Lb))
        (CertZ2.hartTr St.cstC.cdTr y)) →
    (rows.getD x [])[n]? = some lb → ¬ CertZ24.lblFail Lb lb →
    -- no lag: the ordinary site facts
    (CertZ13.relT TT x n pE pC →
      ((candLastSt St.cstC).msWs x).wRelp = ws.wRelp ∧ CertZ13.siteFacts TT St x n lb ls l pE pC) ∧
    -- a lag: the spin-loop fact
    (∀ (m0 : Nat) (pE0 : Pexv6), m0 < n → CertZ13.relT TT x m0 pE0 pC →
      CertZ34.failRun rows Lb x m0 n →
      ∃ (lb' : Lbl) (pa : Pexv6) (da : Efab) (ls' : List Wlabel) (pC' : Pexv6),
        lblReidxW lb lb' ∧ CertZ2.stepOkZ St itvOf x lb' pC pa da ls' pC' d' ∧
        CertZ13.relT TT x (n + 1) pE' pC')

/-- **`hartStepOfSiteLag`**: the lagged datum gives the relativized per-step datum (skips free). -/
theorem CertZ34.hartStepOfSiteLag (d0 : Efab) (rows : List (List Lbl)) (Lb : Int → Prop)
    (L : List Geid) (TT : Nat → Nat → List Nat) :
    CertZ34.siteStepLag d0 rows Lb L TT →
    CertZ29.hartStepRI4 d0 rows Lb L (CertZ34.relLag rows Lb TT) := by
  intro hsite St itvOf fiOf x n lb ws ls l pE pE' pC d' k hok hp hrel hsh hblk hags hk hper hlb
  obtain ⟨m0, pE0, hm0, hrel0, hrun, hpe⟩ := hrel
  refine ⟨fun hf => ⟨m0, pE0, by omega, hrel0, fun j hj1 hj2 => ?_, fun h => by omega⟩, fun hf => ?_⟩
  · rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj2) with hlt | heq
    · exact hrun j hj1 hlt
    · subst heq; exact ⟨lb, hlb, hf⟩
  · obtain ⟨hnolag, hlag⟩ := hsite St itvOf fiOf x n lb ws ls l pE pE' pC d' k hok hp hsh hblk hags
      hk hper hlb hf
    rcases Nat.lt_or_eq_of_le hm0 with hlt | heq
    · obtain ⟨lb', pa, da, ls', pC', hre, hok', hrel'⟩ := hlag m0 pE0 hlt hrel0 hrun
      exact ⟨lb', pa, da, ls', pC', hre, hok', n + 1, pE', Nat.le_refl _, hrel',
        fun j h1 h2 => by omega, fun _ => rfl⟩
    · have hpe0 := hpe heq
      subst heq hpe0
      obtain ⟨hr, hfacts⟩ := hnolag hrel0
      obtain ⟨lb', pa, da, ls', pC', hre, hok', hrel'⟩ :=
        CertZ33.stepOfSiteFacts d0 TT St itvOf fiOf x m0 lb ws ls l pE0 pE' pC d' hok hp hrel0 hr
          hsh hblk hfacts
      exact ⟨lb', pa, da, ls', pC', hre, hok', m0 + 1, pE', Nat.le_refl _, hrel',
        fun j h1 h2 => by omega, fun _ => rfl⟩

namespace CatLin

/-- **THE SITE SUPPLY FOR THE LAGGED RELATION** (named, W10-4 per pc). -/
def siteSupplyLag (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image)
    (P : Int → Int → Prop) : Prop :=
  ∀ (GF : Gfexec) (ad : List (Geid × Geid)) (z : Geid) (ss : List Seg),
    GF.gfGd.gdG.gxImg = im → rvwmoCatAD GF.gfGd ad → GraphFabConf.gfexecConfZF boot d0 fab GF →
    ioResidueGmo GF → gdiskRead14 GF.gfGd.gdG →
    ss ≠ [] → rawChainC GF.gfGd (ioCross GF) z z ss →
    ∀ D : Nat → CertZ7.EmData, CertZ7.emDataOk boot fab GF D →
    ∀ L : List Geid, CertZ8.walkOrd GF.gfGd.gdG.gxProg GF.gfDev L →
      CertZ23.ordCoSP GF.gfGd.gdG L (GraphFetchN2.lockBytes P) →
    ∃ TT : Nat → Nat → List Nat,
      CertZ34.siteStepLag d0 GF.gfGd.gdG.gxProg (GraphFetchN2.lockBytes P) L TT

theorem stepSupplyOfSiteLag (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image)
    (P : Int → Int → Prop) :
    siteSupplyLag boot d0 fab im P → stepSupplyCZ4 boot d0 fab im P := by
  intro hs GF ad z ss him hc hconf hres hdr hne hch D hD L hL hco
  obtain ⟨TT, hTT⟩ := hs GF ad z ss him hc hconf hres hdr hne hch D hD L hL hco
  exact ⟨CertZ34.relLag GF.gfGd.gdG.gxProg (GraphFetchN2.lockBytes P) TT,
    fun x _ => ⟨0, boot x, Nat.le_refl _, .inl rfl, fun j h1 h2 => by omega, fun _ => rfl⟩,
    CertZ34.hartStepOfSiteLag d0 _ _ L TT hTT⟩

section glue

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode
open Language.Notation PrimStep
open LeanRV64D

/-- WARNING: `siteSupplyLag` is false as stated (instruction counters, see `CertZ34.siteStepLag`); do not
consume.

**`cycleKillOfOrdSiteLagCZRC4`** — the zero-cut kill up to failed acquires from the LAGGED site
supply. -/
theorem cycleKillOfOrdSiteLagCZRC4 (hlc : HasLC) (GF0 : BundledGFunctors) [MachGpreS hlc GF0]
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
    siteSupplyLag boot d0 fab (imgZ σ0.wgimg) P →
    acqAqCZ4 boot d0 fab (imgZ σ0.wgimg) P →
    relCoversCZ4 boot d0 fab (imgZ σ0.wgimg) P →
    l2ClaimCZR4 boot d0 fab (imgZ σ0.wgimg) P (badRun gen σ0) →
    cycleKillCZC boot d0 fab (imgZ σ0.wgimg) :=
  fun hfr hb1 hb2 hwp hrz hcov hpre hdisc hwio hsite hAQ hRC hl2 =>
    cycleKillOfOrdStepCZRC4 hlc GF0 gen σ0 D hD P boot d0 fab N hfr hb1 hb2 hwp hrz hcov hpre hdisc
      hwio (stepSupplyOfSiteLag boot d0 fab _ P hsite) hAQ hRC hl2

end glue

end CatLin

end Weak
