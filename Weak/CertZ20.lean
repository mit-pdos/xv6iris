/-
Weak: **W10 F1 [OWN.94] (N2′), decision (i), increment 3 — the PRODUCER side at successful-protocol
lock co** (`PROGRESS-W10N2p.md`).  Lean-only, no Rocq twin.

  §1  **`CertZ20.memberRmwLatest`** — the walk's member satisfies `CertZ18.rmwLatest`: its RMWs are the
      candidate's, which the promise-free machine realizes (`srvwmoRealizable`), and the machine's RMW
      step requires its read timestamps latest (`rmwLatest`) with the candidate's values
      (`candValues`), at the log prefix `cdLog c k` = the member's first `gwix − 1` messages;
  §2  `CatLin.certSupplyCZROfWalk3` (`walkSupplyCZ2 → certSupplyCZR3`: successful-protocol co is a
      restriction of protocol co) and **`CatLin.cycleKillOfOrdSiteCZRC3`** — the zero-cut kill at
      successful-protocol lock co, from the unchanged named `orderSupplyCZ2` (decision (i)), the site
      supply, the two xv6 lock facts, the L2′ claim, and the named run fact `regZeroRun`.

Spec: FAITHFUL (proof organisation; the member fact is a theorem).
-/
import Weak.CertZ19

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open TsoShadow

/-! # 1. The member's RMW atomicity -/

/-- The machine's RMW step requires its read timestamps latest. -/
theorem CertZ20.mstepRmwLatest (σ σ' : Mstate) (i : Nat) (l : Lbl) (base : Int) (ts : List Nat)
    (vs : List (BitVec 8)) :
    mstep σ i l σ' → lbIsW l = true → lbRd l = some (base, ts, vs) →
    rmwLatest σ.msImg σ.msLog base ts := by
  intro hst hW hrd
  cases hst with
  | MStepRmw aq rl b0 ts0 rvs wvs kc _ _ _ hrl =>
    simp only [lbRd, Option.some.injEq, Prod.mk.injEq] at hrd
    obtain ⟨rfl, rfl, rfl⟩ := hrd
    exact hrl
  | _ => simp_all [lbIsW, lbRd]

/-- **THE WALK'S MEMBER READS THE LATEST BYTES AT ITS RMWs.** -/
theorem CertZ20.memberRmwLatest (n : Nat) (c : Cand) :
    srvwmoConsistent c → (∀ s, s ∈ c.cdTr → s.esAg < n) →
    CertZ18.rmwLatest (CertZ3.member n c) (cdLog c c.cdTr.length) := by
  intro hcons hag e a t v ⟨l, hl, hW⟩ ⟨l0, base, ts, vs, j, hl0, hrd, ht, hv, ha⟩
  rw [hl, Option.some.injEq] at hl0
  subst hl0
  obtain ⟨hwf, htrE, -⟩ := srvwmoRealizable c hcons
  rw [CertZ3.memberLbl n c e hag] at hl
  obtain ⟨k, s, hk, hce, hsl⟩ := CertZ3.cgLblInv c e l hl
  subst hsl
  have hkE : (candExec c).exTr[k]? = some s := by rw [htrE]; exact hk
  have hkl : k < c.cdTr.length := lookup_lt_Some hk
  -- the member's prefix before `e` is `cdLog c k`
  have hix : gwix (CertZ3.member n c) e - 1 = (cdLog c k).length := by
    rw [CertZ3.memberGwix n c e hag, ← hce, cgWix (candExec c) k s hwf hkE hW, evTsAt,
      candElog c k (Nat.le_of_lt hkl), Nat.add_sub_cancel]
  have hpfx : (cdLog c c.cdTr.length).take (gwix (CertZ3.member n c) e - 1) = cdLog c k := by
    obtain ⟨rest, hrest⟩ := cdLogSplit c k c.cdTr.length (Nat.le_of_lt hkl)
    rw [hix, hrest, List.take_left]
  have himg : (CertZ3.member n c).gxImg = c.cdImg := rfl
  rw [hpfx, himg]
  -- the machine's RMW step: latest timestamps
  have hstep := execStepAt (candExec c) k s hwf hkE
  have hlat : latest c.cdImg (cdLog c k) (accAddr base j) t := by
    have hm : (stt (candExec c) k).msImg = c.cdImg := candEimg c k (Nat.le_of_lt hkl)
    have hlg : (stt (candExec c) k).msLog = cdLog c k := candElog c k (Nat.le_of_lt hkl)
    have := CertZ20.mstepRmwLatest _ _ _ _ base ts vs hstep hW hrd j t ht
    rw [hm, hlg] at this
    exact this
  rw [← ha]
  exact ⟨hlat, hcons.2.1 k s base ts vs hk hrd j t v ht hv⟩

/-! # 2. The supply and the kill -/

namespace CatLin

/-- (G-3) at a successful-protocol member from the free walk (`certSupplyCZROfWalk2` + the member's
RMW atomicity). -/
theorem certSupplyCZROfWalk3 (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image)
    (N : Nat) (P : Int → Int → Prop) :
    walkSupplyCZ2 boot d0 fab im N P → certSupplyCZR3 boot d0 fab im N P := by
  intro hws GF ad _ z ss him hc hconf hres hdr _ _ _ _ _ hne hch
  obtain ⟨Inv, hI0, hpol, hco⟩ := hws GF ad z ss him hc hconf hres hdr hne hch
  have hstart := wlkStartInvZ boot d0 N GF.gfGd.gdG
  obtain ⟨itv0, fi0, hok0⟩ := CertZ.cstOkZWOf d0 _ hstart.1
  obtain ⟨_, Sf, itvF, fiF, cntF, tradd, hrun, hokF, hinvF, hdone, -, htr, hf2, hagt, himg,
    hpst⟩ := CertZ2.walkRunZ d0 GF.gfGd.gdG.gxProg Inv hpol _ (wlkStart boot d0 N GF.gfGd.gdG) itv0 fi0 (fun _ => 0)
      (Nat.le_refl _) hok0 (hI0 itv0 fi0 hok0)
  have htr' : Sf.cstC.cdTr = tradd := by rw [htr]; rfl
  have hagS : ∀ s, s ∈ Sf.cstC.cdTr → s.esAg < GF.gfGd.gdG.gxProg.length := by
    rw [htr']; exact hagt
  have hcons := hokF.1
  refine ⟨Sf.cstC, Sf.cstPst, Sf.cstDv, CertZ3.member GF.gfGd.gdG.gxProg.length Sf.cstC, fun t => t,
    runDataZOfCyc boot d0 N GF.gfGd.gdG Sf (CertZ.cstOkZOfW _ _ _ _ hokF) (by rw [himg]; rfl)
      (by rw [hpst]; rfl),
    ?_, CertZ3.memberGwf _ _ hcons hagS,
    ⟨show Sf.cstC.cdImg = _ by rw [himg]; rfl, ?_,
      CertZ18.lockCoSPOfNP _ _ _ (hco Sf itvF fiF cntF hinvF hokF hdone)⟩,
    CertZ3.memberGwrowGmo _ _ hagS, CertZ20.memberRmwLatest _ _ hcons hagS⟩
  · have := CertZ3.memberLogPfx GF.gfGd.gdG.gxProg.length Sf.cstC hcons hagS
    exact logOfOfPfx _ _ this
  · show List.Forall₂ _ GF.gfGd.gdG.gxProg ((List.range' 0 GF.gfGd.gdG.gxProg.length).map _)
    refine CertZ3.forall₂Range _ _ GF.gfGd.gdG.gxProg 0 (fun x row hx => ?_)
    rw [Nat.zero_add, htr']
    have hfx := hf2 x
    have hlen : (GF.gfGd.gdG.gxProg.getD x []).length ≤ cntF x := hdone x (lookup_lt_Some hx)
    rw [List.getD_eq_getElem?_getD, hx, Option.getD_some] at hfx hlen
    rw [List.drop_zero, Nat.sub_zero, List.take_of_length_le hlen] at hfx
    have hre : List.Forall₂ (fun l l' => lblReidxW (lblRen (fun t => t) l) l') row
        (CertZ2.hartTr tradd x) := by
      refine List.Forall₂.imp (fun {l l'} h => ?_) hfx
      rw [lblRenId]; exact h
    exact hre

section glue

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode
open Language.Notation PrimStep
open LeanRV64D

/-- WARNING (2026-10-14): VACUOUS as stated — `orderSupplyCZ2` (failed-acquire cycles) and
`siteSupplyCZ` (all walk states) are false on xv6 graphs; see `PROGRESS-W10N2p.md`.  Do not consume.

**`cycleKillOfOrdSiteCZRC3`** — WHAT W11-F CONSUMES AT THE ZERO CUT, AT SUCCESSFUL-PROTOCOL LOCK CO
(decision (i)): the WP package, the registration fact `regZeroRun`, the fetch-view premise, the hart
count and (P2), the ORDER supply (`orderSupplyCZ2`, named), the SITE supply, the two xv6 lock facts and
the L2′ claim at the successful-protocol member. -/
theorem cycleKillOfOrdSiteCZRC3 (hlc : HasLC) (GF0 : BundledGFunctors) [MachGpreS hlc GF0]
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
    orderSupplyCZ2 boot d0 fab (imgZ σ0.wgimg) P →
    siteSupplyCZ boot d0 fab (imgZ σ0.wgimg) →
    acqAqCZ3 boot d0 fab (imgZ σ0.wgimg) P →
    relCoversCZ3 boot d0 fab (imgZ σ0.wgimg) P →
    l2ClaimCZR3 boot d0 fab (imgZ σ0.wgimg) P (badRun gen σ0) →
    cycleKillCZC boot d0 fab (imgZ σ0.wgimg) :=
  fun hfr hb1 hb2 hwp hrz hcov hpre hord hsite hAQ hRC hl2 =>
    cycleKillOfL2CZRC3 hlc GF0 gen σ0 D hD P boot d0 fab N hfr hb1 hb2 hwp hrz hcov
      (cutSupplyOfCycleCZC boot d0 fab _)
      (certSupplyCZROfWalk3 boot d0 fab _ N P
        (walkSupplyOfOrdStep2 boot d0 fab _ N P hpre hord (stepSupplyOfSite boot d0 fab _ hsite)))
      hAQ hRC hl2

end glue

end CatLin

end Weak
