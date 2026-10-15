/-
Weak: **W10-4 [OWN.94] (N2′), decision (A), step 4e — the site facts at walk-invariant states WITH SKIPS**
(`PROGRESS-W10N2p.md`).  Lean-only, no Rocq twin.

  §1  **`CertZ33.stepOfSiteFacts`** — `CertZ13.hartStepOfSite`'s body POINTWISE (the realized step from
      the site facts at one state, no universal site datum);
  §2  **`CertZ33.readAgreeOfDrf4`** — at a walk-invariant state with skips, a protected plain load meets
      the value conjunct of `CertZ13.siteFacts` (`CertZ11.readAgree`) by `CertZ32.readAgreeDrf4`;
  §3  **`CertZ33.siteStepI4`** (the site datum at walk-invariant states with skips: site facts and the
      wRelp agreement at realized slots, the relation kept at skipped slots), `CertZ33.hartStepOfSiteI4`
      (`siteStepI4 → hartStepRI4` at `relT`), and `CatLin.siteSupplyCZ4` → `CatLin.stepSupplyCZ4`.

Spec: FAITHFUL (proof organisation; the site datum's truth in `PROGRESS-W10N2p.md`).
-/
import Weak.CertZ32

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open TsoShadow
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D
open Wlabel

local notation "Ofence" => Option (Bool × Bool × Bool × Bool)

/-! # 1. The realized step, pointwise -/

/-- **THE REALIZED STEP FROM THE SITE FACTS, POINTWISE** (`CertZ13.hartStepOfSite`'s body at one
state: lockstep with agreement, lockstep with poison, or tainted). -/
theorem CertZ33.stepOfSiteFacts (d0 : Efab) (TT : Nat → Nat → List Nat) (St : CycState)
    (itvOf : Nat → Nat → Nat) (fiOf : Nat → Nat → Bool) (x n : Nat) (lb : Lbl) (ws : Wstate)
    (ls : List Wlabel) (l : Wlabel) (pE pE' pC : Pexv6) (d' : Efab) :
    CertZ.cstOkZW d0 St itvOf fiOf →
    (St.cstPst (cdEnd St.cstC))[x]? = some pC → CertZ13.relT TT x n pE pC →
    ((candLastSt St.cstC).msWs x).wRelp = ws.wRelp → CertZ4.lblShape lb →
    ((lbFused l ∧ GraphFetchBlocks.blkOne (St.cstDv (cdEnd St.cstC)) d' ws lb ls l pE pE') ∨
      GraphFetchBlocks.blkPair (St.cstDv (cdEnd St.cstC)) d' ws lb ls l pE pE') →
    CertZ13.siteFacts TT St x n lb ls l pE pC →
    ∃ (lb' : Lbl) (pa : Pexv6) (da : Efab) (ls' : List Wlabel) (pC' : Pexv6),
      lblReidxW lb lb' ∧ CertZ2.stepOkZ St itvOf x lb' pC pa da ls' pC' d' ∧
      CertZ13.relT TT x (n + 1) pE' pC' := by
  intro hok hp hrel hr hsh hblk hfacts
  obtain ⟨hft, hfag, hTT, hval, hunt⟩ := hfacts
  have hitv := CertZ5.itvBound d0 St itvOf fiOf hok (cdEnd St.cstC) (Nat.le_refl _) x
  obtain ⟨hmok, hld⟩ := CertZ4.machLblOk St.cstC x lb hok.1 hsh hft
  rcases hrel with rfl | ⟨cpu, m1, rs1, fn1, ib1, m2, rs2, fn2, ib2, rfl, rfl, hcs⟩
  · -- LOCKSTEP
    rcases hval with ⟨hvl, hvr⟩ | ⟨⟨base, ts, vs, hlbE⟩, hpois⟩
    · obtain ⟨pa, da, hre', hs'⟩ := CertZ9.lockstepStep d0 St itvOf fiOf x lb ws ls l pE pE' d' hok
        hr hsh hblk hft hvl hvr hfag
      exact ⟨_, pa, da, _, pE', hre', hs', .inl rfl⟩
    · rcases hblk with ⟨hfu, pa, da, hrun, hre, hst⟩ | ⟨pa, da, pm, dm, ls2, pm2, dm2, l2, -, hpr, -⟩
      · obtain ⟨cpu, ma, rsa, fna, iba, rfl, htail⟩ := hpois pa da hrun
        obtain ⟨m', rs', fn', ib', rfl⟩ := pstepEvPhart cpu ma rsa fna iba da l pE' d' hst
        obtain ⟨l', mC, rsC, fnC, ibC, hfu', hre', hst', hreidx, hcs'⟩ :=
          CertZ11.realizeT St.cstC [] (TT x (n + 1)) cpu ma rsa rsa fna iba da ws
            ((candLastSt St.cstC).msWs x) lb l m' rs' fn' ib' d' (List.nil_subset _) hr hfu hre hst
            (fun _ _ _ _ k hk hin => by simp at hin) (dregAgreeRefl _ _)
            (.inr ⟨base, ts, vs, hlbE, htail⟩)
        exact ⟨_, _, da, _, _, hreidx, ⟨hmok, hld,
          CertZ5.admRunGRet St.cstC true _ _ ls _ da hrun hfag, CertZ5.starCut St.cstC _ x ls hitv hfag,
          .inl ⟨l', hfu', hre', hst'⟩⟩, .inr ⟨cpu, m', rs', fn', ib', mC, rsC, fnC, ibC, rfl, rfl, hcs'⟩⟩
      · obtain ⟨aq, rl, base', tvs, data, asrc1, asrc2, vsrc2, -, -, -, -, hlb'⟩ := hpr
        rw [hlbE] at hlb'
        cases hlb'
  · -- TAINTED
    obtain ⟨hbu, hnld⟩ := hunt cpu m1 rs1 fn1 ib1 m2 rs2 fn2 ib2 rfl rfl hcs
    have hTT' := hTT
    rcases hblk with ⟨hfu, pa, da, hrunG, hre, hst⟩ |
        ⟨pa, da, pm, dm, ls2, pm2, dm2, l2, hrunG, hpr, hst1, hrun2, hst2⟩
    · -- a fused block
      have hrun := CertZ10.admRunOfG true _ _ ls pa da hrunG
      obtain ⟨ma, rsa, fna, iba, rfl⟩ := admRunPhart true _ pa _ ls da hrun cpu m1 rs1 fn1 ib1 rfl
      obtain ⟨m', rs', fn', ib', rfl⟩ := pstepEvPhart cpu ma rsa fna iba da l pE' d' hst
      obtain ⟨hsu, hrest⟩ := hbu ma rsa fna iba da hrun
      obtain ⟨hstu, -⟩ := hrest m' rs' fn' ib' d' hst
      obtain ⟨lsC, rsa2, hrunC, hag, hfsub⟩ := CertZ13.certStar (TT x n) cpu _ m1 rs1 fn1 ib1 m2 rs2
        fn2 ib2 ls ma rsa fna iba da l _ d' hcs hrun hsu (hlblRealizesNotadm _ ws lb l true hre)
        hnld hst
      have hval' : CertZ11.readAgree St.cstC lb ∨
          (∃ base ts vs, lb = .LLoad false base ts vs ∧ CertZ11.loadTail (TT x (n + 1)) cpu ma) := by
        rcases hval with h | ⟨⟨base, ts, vs, hlbE⟩, hpois⟩
        · exact .inl h
        · obtain ⟨cpu', ma', rsa', fna', iba', heq, htail⟩ := hpois _ da hrunG
          simp only [Pexv6.PHart.injEq] at heq
          obtain ⟨rfl, rfl, -, -, -⟩ := heq
          exact .inr ⟨base, ts, vs, hlbE, htail⟩
      obtain ⟨l', mC, rsC, fnC, ibC, hfu', hre', hst', hreidx, hcs'⟩ :=
        CertZ11.realizeT St.cstC (TT x n) (TT x (n + 1)) cpu ma rsa rsa2 fna iba da ws
          ((candLastSt St.cstC).msWs x) lb l m' rs' fn' ib' d' hTT' hr hfu hre hst hstu hag hval'
      have hfagC := CertZ13.fetchAgreeSub St.cstC ls lsC hfag hfsub
      exact ⟨_, _, da, _, _, hreidx, ⟨hmok, hld,
        CertZ5.admRunGRet St.cstC true _ _ lsC _ da (CertZ10.admRunGOf true _ _ lsC _ da hrunC)
          hfagC, CertZ5.starCut St.cstC _ x lsC hitv hfagC, .inl ⟨l', hfu', hre', hst'⟩⟩,
        .inr ⟨cpu, m', rs', fn', ib', mC, rsC, fnC, ibC, rfl, rfl, hcs'⟩⟩
    · -- the exclusive pair
      have hrun := CertZ10.admRunOfG true _ _ ls pa da hrunG
      obtain ⟨ma, rsa, fna, iba, rfl⟩ := admRunPhart true _ pa _ ls da hrun cpu m1 rs1 fn1 ib1 rfl
      obtain ⟨hsu, hrest⟩ := hbu ma rsa fna iba da hrun
      have hna : ¬ lbAdmin true l := by
        obtain ⟨_, _, _, _, _, _, _, _, rfl, -⟩ := hpr
        simp [lbAdmin]
      obtain ⟨lsC, rsa2, hrunC, hag, hfsub⟩ := CertZ13.certStar (TT x n) cpu _ m1 rs1 fn1 ib1 m2 rs2
        fn2 ib2 ls ma rsa fna iba da l pm dm hcs hrun hsu hna hnld hst1
      have hvr : ∀ aq rl base ts rvs wvs kc, lb = .LRmw aq rl base ts rvs wvs kc →
          lrdVs St.cstC base ts.length = rvs := by
        rcases hval with ⟨-, h⟩ | ⟨⟨base, ts, vs, hlbE⟩, -⟩
        · exact h
        · obtain ⟨_, _, _, _, _, _, _, _, -, -, -, -, hlb'⟩ := hpr
          rw [hlbE] at hlb'
          cases hlb'
      obtain ⟨l1', pmC, pm2C, m', rs', rs2', fn', ib', rfl, hpair', hst1', hrun2', hst2', hag3⟩ :=
        CertZ12.pairT St.cstC (TT x n) cpu ma rsa rsa2 fna iba da ws ((candLastSt St.cstC).msWs x) lb
          l l2 pm dm ls2 pm2 dm2 pE' d' hr hpr hst1 hrun2 hst2
          (fun mm rsm fnm ibm hpm => (hrest mm rsm fnm ibm dm (hpm ▸ hst1)).1)
          (fun mm rsm fnm ibm mm2 rsm2 fnm2 ibm2 hpm hpm2 => by
            subst hpm hpm2
            obtain ⟨m'', rs'', fn'', ib'', rfl⟩ := pstepEvPhart cpu mm2 rsm2 fnm2 ibm2 dm2 l2 pE' d'
              hst2
            exact ((hrest mm rsm fnm ibm dm hst1).2 ls2 mm2 rsm2 fnm2 ibm2 dm2 l2 m'' rs'' fn'' ib''
              d' hrun2 hst2).1)
          (fun mm2 rsm2 fnm2 ibm2 m'' rs'' fn'' ib'' hpm2 hpE => by
            subst hpm2 hpE
            obtain ⟨mm, rsm, fnm, ibm, rfl⟩ := pstepEvPhart cpu ma rsa fna iba da l pm dm hst1
            exact ((hrest mm rsm fnm ibm dm hst1).2 ls2 mm2 rsm2 fnm2 ibm2 dm2 l2 m'' rs'' fn'' ib''
              d' hrun2 hst2).2)
          hag hvr
      have hfagC := CertZ13.fetchAgreeSub St.cstC ls lsC hfag hfsub
      have hreidx : lblReidxW lb (CertZ4.machLbl St.cstC lb) :=
        CertZ4.machLblReidx St.cstC lb (fun aq base ts vs he => by
          obtain ⟨_, _, _, _, _, _, _, _, -, -, -, -, hlb'⟩ := hpr
          rw [he] at hlb'
          cases hlb') hvr
      exact ⟨_, _, da, _, _, hreidx, ⟨hmok, hld,
        CertZ5.admRunGRet St.cstC true _ _ lsC _ da (CertZ10.admRunGOf true _ _ lsC _ da hrunC)
          hfagC, CertZ5.starCut St.cstC _ x lsC hitv hfagC,
          .inr ⟨pmC, dm, ls2, pm2C, dm2, l1', l2, hpair', hst1', hrun2', hst2'⟩⟩,
        .inr ⟨cpu, m', rs', fn', ib', _, rs2', fn', ib', rfl, rfl,
          .inl ⟨rfl, rfl, rfl, dregAgreeTaintMono _ _ _ _ hTT' hag3⟩⟩⟩

/-! # 2. Race-free reads give the value conjunct -/

/-- A protected plain load at a walk-invariant state with skips agrees in value. -/
theorem CertZ33.readAgreeOfDrf4 (G : Gexec) (dev L : List Geid) (c : Cand) (Lb : Int → Prop)
    (k : Nat) (r : Geid) (aq : Bool) (base : Int) (ts : List Nat) (vs : List (BitVec 8)) :
    gwf G → gppoCat6Gmo G → gloadValue G → CertZ8.walkOrd G.gxProg dev L →
    c.cdImg = G.gxImg →
    c.cdTr.map Estep.esAg = ((L.take k).filter (CertZ29.keepEv G.gxProg Lb)).map Prod.fst →
    (∀ y, y < G.gxProg.length →
      List.Forall₂ lblReidxW
        (((G.gxProg.getD y []).take (((L.take k).filter (fun e => decide (e.1 = y))).length)).filter
          (CertZ26.keepB Lb))
        (CertZ2.hartTr c.cdTr y)) →
    L[k]? = some r → gxLbl G r = some (.LLoad aq base ts vs) → vs.length = ts.length →
    (∀ j, j < ts.length → ∃ (b : Int) (A : Geid) (oR : Option Geid),
      CertZ21.drfFacts G b (accAddr base j) ∧ CertZ21.ordFacts G b L ∧ CertZ21.secOf G b r A oR ∧
      ∀ e v', gwritesByte G e (accAddr base j) v' → CertZ29.keepEv G.gxProg Lb e = true) →
    CertZ11.readAgree c (.LLoad aq base ts vs) := by
  intro hwf h6 hlv hord hci hags hper hk hl hvl hprot
  refine ⟨fun aq' base' ts' vs' he => ?_, fun _ _ _ _ _ _ _ he => by cases he⟩
  cases he
  exact CertZ32.readAgreeDrf4 G dev L c Lb k r aq base ts vs hwf h6 hlv hord hci hags hper hk hl hvl
    hprot

/-! # 3. The site datum at walk-invariant states with skips -/

/-- **THE SITE DATUM AT WALK-INVARIANT STATES, WITH SKIPS** (W10-4 per pc, named).

WARNING (`PROGRESS-W10N2p.md`): its skip clause asks the relation `relT` (lockstep or one-instruction
`csync`) to hold after a FIRST failed iteration, where the certified hart is still before the spin loop
(several instructions behind) — likely FALSE there.  Not consumed by the recommended kill
(`CatLin.cycleKillOfOrdStepCZRC4`, whose `stepSupplyCZ4` lets the relation be richer); its realized-slot
half (`stepOfSiteFacts`, `readAgreeOfDrf4`) is what a `stepSupplyCZ4` proof reuses. -/
def CertZ33.siteStepI4 (d0 : Efab) (rows : List (List Lbl)) (Lb : Int → Prop) (L : List Geid)
    (TT : Nat → Nat → List Nat) : Prop :=
  ∀ (St : CycState) (itvOf : Nat → Nat → Nat) (fiOf : Nat → Nat → Bool) (x n : Nat) (lb : Lbl)
    (ws : Wstate) (ls : List Wlabel) (l : Wlabel) (pE pE' pC : Pexv6) (d' : Efab) (k : Nat),
    CertZ.cstOkZW d0 St itvOf fiOf →
    (St.cstPst (cdEnd St.cstC))[x]? = some pC → CertZ13.relT TT x n pE pC → CertZ4.lblShape lb →
    ((lbFused l ∧ GraphFetchBlocks.blkOne (St.cstDv (cdEnd St.cstC)) d' ws lb ls l pE pE') ∨
      GraphFetchBlocks.blkPair (St.cstDv (cdEnd St.cstC)) d' ws lb ls l pE pE') →
    St.cstC.cdTr.map Estep.esAg = ((L.take k).filter (CertZ29.keepEv rows Lb)).map Prod.fst →
    L[k]? = some (x, n) →
    (∀ y, y < rows.length →
      List.Forall₂ lblReidxW
        (((rows.getD y []).take (((L.take k).filter (fun e => decide (e.1 = y))).length)).filter
          (CertZ26.keepB Lb))
        (CertZ2.hartTr St.cstC.cdTr y)) →
    (rows.getD x [])[n]? = some lb →
    (CertZ24.lblFail Lb lb → CertZ13.relT TT x (n + 1) pE' pC) ∧
    (¬ CertZ24.lblFail Lb lb →
      ((candLastSt St.cstC).msWs x).wRelp = ws.wRelp ∧ CertZ13.siteFacts TT St x n lb ls l pE pC)

theorem CertZ33.hartStepOfSiteI4 (d0 : Efab) (rows : List (List Lbl)) (Lb : Int → Prop)
    (L : List Geid) (TT : Nat → Nat → List Nat) :
    CertZ33.siteStepI4 d0 rows Lb L TT → CertZ29.hartStepRI4 d0 rows Lb L (CertZ13.relT TT) := by
  intro hsite St itvOf fiOf x n lb ws ls l pE pE' pC d' k hok hp hrel hsh hblk hags hk hper hlb
  obtain ⟨hskip, hreal⟩ := hsite St itvOf fiOf x n lb ws ls l pE pE' pC d' k hok hp hrel hsh hblk
    hags hk hper hlb
  refine ⟨hskip, fun hf => ?_⟩
  obtain ⟨hr, hfacts⟩ := hreal hf
  exact CertZ33.stepOfSiteFacts d0 TT St itvOf fiOf x n lb ws ls l pE pE' pC d' hok hp hrel hr hsh
    hblk hfacts

namespace CatLin

/-- **THE SITE SUPPLY AT WALK-INVARIANT STATES, WITH SKIPS** (named, W10-4 per pc). -/
def siteSupplyCZ4 (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image)
    (P : Int → Int → Prop) : Prop :=
  ∀ (GF : Gfexec) (ad : List (Geid × Geid)) (z : Geid) (ss : List Seg),
    GF.gfGd.gdG.gxImg = im → rvwmoCatAD GF.gfGd ad → GraphFabConf.gfexecConfZF boot d0 fab GF →
    ioResidueGmo GF → gdiskRead14 GF.gfGd.gdG →
    ss ≠ [] → rawChainC GF.gfGd (ioCross GF) z z ss →
    ∀ D : Nat → CertZ7.EmData, CertZ7.emDataOk boot fab GF D →
    ∀ L : List Geid, CertZ8.walkOrd GF.gfGd.gdG.gxProg GF.gfDev L →
      CertZ23.ordCoSP GF.gfGd.gdG L (GraphFetchN2.lockBytes P) →
    ∃ TT : Nat → Nat → List Nat,
      CertZ33.siteStepI4 d0 GF.gfGd.gdG.gxProg (GraphFetchN2.lockBytes P) L TT

theorem stepSupplyOfSite4 (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image)
    (P : Int → Int → Prop) :
    siteSupplyCZ4 boot d0 fab im P → stepSupplyCZ4 boot d0 fab im P := by
  intro hs GF ad z ss him hc hconf hres hdr hne hch D hD L hL hco
  obtain ⟨TT, hTT⟩ := hs GF ad z ss him hc hconf hres hdr hne hch D hD L hL hco
  exact ⟨CertZ13.relT TT, fun _ _ => .inl rfl,
    CertZ33.hartStepOfSiteI4 d0 _ _ L TT hTT⟩

section glue

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode
open Language.Notation PrimStep

/-- WARNING: `siteSupplyCZ4`'s skip clause at `relT` is likely false (see `CertZ33.siteStepI4`); do not
consume — use `cycleKillOfOrdStepCZRC4`.

**`cycleKillOfOrdSiteCZRC4`** — the zero-cut kill up to failed acquires from the SITE supply at
walk-invariant states (`siteSupplyCZ4 → stepSupplyCZ4`). -/
theorem cycleKillOfOrdSiteCZRC4 (hlc : HasLC) (GF0 : BundledGFunctors) [MachGpreS hlc GF0]
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
    siteSupplyCZ4 boot d0 fab (imgZ σ0.wgimg) P →
    acqAqCZ4 boot d0 fab (imgZ σ0.wgimg) P →
    relCoversCZ4 boot d0 fab (imgZ σ0.wgimg) P →
    l2ClaimCZR4 boot d0 fab (imgZ σ0.wgimg) P (badRun gen σ0) →
    cycleKillCZC boot d0 fab (imgZ σ0.wgimg) :=
  fun hfr hb1 hb2 hwp hrz hcov hpre hdisc hwio hsite hAQ hRC hl2 =>
    cycleKillOfOrdStepCZRC4 hlc GF0 gen σ0 D hD P boot d0 fab N hfr hb1 hb2 hwp hrz hcov hpre hdisc
      hwio (stepSupplyOfSite4 boot d0 fab _ P hsite) hAQ hRC hl2

end glue

end CatLin

end Weak
