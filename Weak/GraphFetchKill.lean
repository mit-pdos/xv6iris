/-
Weak: **W5d-G G6-3 (= W11 (iii)), layer L4 — the kill glue at the UNPINNED shaped supply** (plan
`notes/weak-allocproc-plan.md` rev 51, §C top "W5d-G G6 — LAUNCH PLAN [rev 50]", paragraph "G6-3 =
W11 (iii)", layer L4: "L4 is ALSO W11 (v)'s restatement surface: G6-3 lands the Z-twins, W11-F
consumes them").  Lean-only, no Rocq twin.

`CatLin.cycleKillOfL2C` (`CatLinChain.lean:256`) proves the pinned cat kill `cycleKillC` from the
cut / certification supplies, the L2′ claim, the WP package and `runErased`.  Its Zifencei twin
here proves `CatLin.cycleKillCZ` (`Weak/GraphFetchLinInd.lean`, the GUARDED `racyDIO` kill):

  §1  the classification over `ioCross`-entered segments (`CatLin.l2ClaimAtCZ`, the `l2ClaimAtC`
      twin at the I/O cross order; `CatLin.rawChainChainCZ`: a classified raw chain IS a
      `chainC … (ioCross GF)`, killed by `cycleKillIOC`);
  §2  the supplies `CatLin.cutSupplyCZ` (a cut whose hull CARRIES the Zifencei bundle and (P2) —
      the burden the guarded induction hypothesis puts on the kill, `GraphFetchLinInd` deviation 1)
      and `CatLin.certSupplyCZ` (from the acyclic hull, a `RunDataZ` whose log is the graph's);
  §3  **`CatLin.cycleKillOfL2CZ`** — the glue: the cycle as `ioCross` segments, the cut, the
      guarded IH, the certified run datum, `runErasedZ` (M2's replay), the exports `protRegOfRun` /
      `noBadRun`, the classification, the kill; **`CatLin.t2linOfL2CZ`** — T2-LIN at the Zifencei
      bundle from the same premises (`t2linOfL2'''C`'s twin, the certification supply named).

**Deviations from the pinned glue.**  (1) `certSupplyCZ` receives the hull's ACYCLICITY rather
than a pinned `RunData` of it: the unpinned hull run (`hullRunZ`) has the guards `trDevOrdered`/
`candDiskLat` (`GraphFetchRun` deviation 3), which only the certifier can discharge.  (2) The
quiescent consumers `cycleKillOfL2''` (`Glue2`) and `cycleKillOfL2''''`/`t2linOfL2'''` (`Walk3`) have
NO Zifencei twin: they are stated over the quiescent pinned bundle `gdexecQconf`, and there is no
quiescent Zifencei bundle (`GraphFetchLinInd` deviation 4); the walk (`walkPolicy`/`segsRun`) has its
Zifencei threaded state in `GraphFetchRun` §3, its policy is W11-F's.  (3) The WP package, the fetch-view
premise `efetchItvOk` and the L2′ claim are KEPT as premises (W11-F replaces them by the W8-sourced
facts and `l2ClaimAtB`; plan §C W11-F).  (4) The image tie: the kill obligations carry the image
(`GraphFetchLinInd`, `cycleKill*Z … im`).

Spec: proof organisation; FAITHFUL, no trusted text.  Lean-only helpers file-qualified.
-/
import Weak.GraphFetchRun
import Weak.CatLinChain

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open TsoShadow

/-- (P2) at every row of a graph (`GraphFetchBlocks` §1; (P1) retired by [OWN.86]). -/
def GraphFetchBlocks.emPremOk (boot : Nat → Pexv6) (G : Gexec) : Prop :=
  ∀ (i : Nat) (row : List Lbl) (em : Hemission) (dvi dvo : Nat → Efab) (tq : Nat → Bool),
    G.gxProg[i]? = some row → hartConff i row (boot i) dvi dvo tq em →
    GraphFetchBlocks.emNoDangle em

namespace CatLin

/-! # 1. The classification at the I/O cross order -/

/-- THE L2′ CLAIM at `ioCross` (`l2ClaimAtC`'s twin): each `ioCross`-entered segment of a cycle
is PINNED, CS-chained, or `Bad`. -/
def l2ClaimAtCZ (GF : Gfexec) (ad : List (Geid × Geid)) (P : Int → Int → Prop) (Bad : Prop) :
    Prop :=
  ∀ (log : List Wmsg) (z : Geid) (ss : List Seg),
    rvwmoCatAD GF.gfGd ad →
    logOf GF.gfGd.gdG log →
    protReg P log →
    ss ≠ [] → rawChainC GF.gfGd (ioCross GF) z z ss →
    ∀ (prev : Geid) (s : Seg),
      s ∈ ss → ioCross GF prev s.sgEntry → segRunC GF.gfGd s →
      segPinC GF.gfGd ad s ∨ csHyps GF.gfGd P log prev s ∨ Bad

def l2ClaimCZ (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image)
    (P : Int → Int → Prop) (Bad : Prop) : Prop :=
  ∀ GF ad, GF.gfGd.gdG.gxImg = im → GraphFabConf.gfexecConfZF boot d0 fab GF →
    l2ClaimAtCZ GF ad P Bad

/-- A classified `ioCross` raw chain IS a `chainC` at `ioCross` (`rawChainChainC`'s twin). -/
theorem rawChainChainCZ (GF : Gfexec) (ad : List (Geid × Geid)) (P : Int → Int → Prop)
    (log : List Wmsg) (Bad : Prop) (ss : List Seg) :
    rvwmoCatAD GF.gfGd ad → ioResidueGmo GF → gdiskRead14 GF.gfGd.gdG →
    logOf GF.gfGd.gdG log → protReg P log → ¬ Bad →
    (∀ prev s, s ∈ ss → ioCross GF prev s.sgEntry → segRunC GF.gfGd s →
       segPinC GF.gfGd ad s ∨ csHyps GF.gfGd P log prev s ∨ Bad) →
    ∀ (x y : Geid) (ss' : List Seg),
      ss' ⊆ ss → rawChainC GF.gfGd (ioCross GF) x y ss' →
      chainC GF.gfGd.gdG (ioCross GF) x y ss' := by
  intro hc hres hdr hlog hpr hnB hcl x y ss'
  have hX : ∀ x y, ioCross GF x y → gmoLt GF.gfGd.gdG x y :=
    ioCrossGmo GF hc.1 hc.2.2.1 hres hdr
  induction ss' generalizing x with
  | nil => intro _ hch; exact hch
  | cons s ss' ih =>
    intro hsub hch
    obtain ⟨hx, hrun, hrest⟩ := hch
    have hs : s ∈ ss := hsub (by simp)
    have hsub' : ss' ⊆ ss := by
      intro t ht
      exact hsub (List.mem_cons_of_mem s ht)
    show CertC GF.gfGd.gdG (ioCross GF) x s ∧ chainC GF.gfGd.gdG (ioCross GF) s.sgExit y ss'
    refine ⟨?_, ih _ hsub' hrest⟩
    rcases hcl x s hs hx hrun with hp | hcs | hb
    · exact segPinCCert GF.gfGd ad _ x s hc hx hp
    · exact csHypsCertC GF.gfGd ad _ P log x s hc hX hlog hpr hcs hx
    · exact absurd hb hnB

/-! # 2. The supplies -/

/-- (G-2) at the Zifencei bundle: a cut, `gfDev`-closed, whose hull carries the bundle and
(P2) — what the guarded induction hypothesis asks for. -/
def cutSupplyCZ (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image) : Prop :=
  ∀ (GF : Gfexec) (ad : List (Geid × Geid)) (z : Geid) (ss : List Seg),
    GF.gfGd.gdG.gxImg = im → rvwmoCatAD GF.gfGd ad → GraphFabConf.gfexecConfZF boot d0 fab GF →
    ss ≠ [] → rawChainC GF.gfGd (ioCross GF) z z ss →
    ∃ cs, cutOk GF.gfGd.gdG cs ∧ dclosed cs GF.gfDev ∧
      GraphFabConf.gfexecConfZF boot d0 fab (gfHull GF cs) ∧
      GraphFetchBlocks.emPremOk boot (gfHull GF cs).gfGd.gdG

/-- (G-3) at the Zifencei bundle: from the cut's acyclic hull, a run datum (M2's conjunct) whose
log is the graph's. -/
def certSupplyCZ (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image) (N : Nat) :
    Prop :=
  ∀ (GF : Gfexec) (ad : List (Geid × Geid)) (cs : List Nat) (z : Geid) (ss : List Seg),
    GF.gfGd.gdG.gxImg = im → rvwmoCatAD GF.gfGd ad → GraphFabConf.gfexecConfZF boot d0 fab GF →
    cutOk GF.gfGd.gdG cs → GraphFabConf.gfexecConfZF boot d0 fab (gfHull GF cs) →
    (∀ x, ¬ tc (racyDIO (gfHull GF cs)) x x) →
    ss ≠ [] → rawChainC GF.gfGd (ioCross GF) z z ss →
    ∃ (c : Cand) (pst : Nat → List Pexv6) (dv : Nat → Efab),
      RunDataZ boot d0 N GF.gfGd.gdG c pst dv ∧
      logOf GF.gfGd.gdG (cdLog c c.cdTr.length)

/-- The `cutOk` cut with `gfDev`-closure is a `properCutF`. -/
theorem GraphFetchKill.properCutFOfCut (GF : Gfexec) (cs : List Nat) :
    cutOk GF.gfGd.gdG cs → dclosed cs GF.gfDev → properCutF GF cs :=
  fun hc hd => ⟨cutOkProper _ _ hc, hd⟩

/-! # 3. THE GLUE -/

section glue

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode
open Language.Notation PrimStep
open LeanRV64D

/-- **`cycleKillOfL2CZ`** (`cycleKillOfL2C`'s twin): the guarded Zifencei cat kill from the
supplies, the classification at `ioCross`, the WP package and the fetch-view premise — through
M2's replay (`runErasedZ`). -/
theorem cycleKillOfL2CZ (hlc : HasLC) (GF0 : BundledGFunctors) [MachGpreS hlc GF0]
    [WeakGpreS GF0] (gen : Nat) (σ0 : WGState) (D : CPU → List Register) (hD : ∀ c, (D c).Nodup)
    (Nm : Int → Int → Namespace) (P : Int → Int → Prop)
    (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (N : Nat) :
    freshEra gen σ0 →
    (List.range' 0 N).map boot = epsInit σ0 →
    d0 = efInit σ0.wgdev →
    wpPackage hlc GF0 gen σ0 D →
    (∀ a base, P a base → wpPackageProt hlc GF0 gen σ0 D (Nm a base) a base) →
    (∀ ρ, rtc epfRun (epInit gen, σ0) ρ → efetchItvOk ρ.1 ρ.2) →
    cutSupplyCZ boot d0 fab (imgZ σ0.wgimg) →
    certSupplyCZ boot d0 fab (imgZ σ0.wgimg) N →
    l2ClaimCZ boot d0 fab (imgZ σ0.wgimg) P (badRun gen σ0) →
    cycleKillCZ boot d0 fab (imgZ σ0.wgimg) := by
  intro hfr hb1 hb2 hwp hwpp hcov hcut hcert hl2
  intro GF ad him hc hconf hres hdr hIH x hcyc
  -- (1) the cycle, as `ioCross`-entered segments
  obtain ⟨z, ss, hne, hch⟩ := cycleSegmentsIO GF ad x hc hcyc
  -- (2) the cut, its hull's bundle, and the guarded induction hypothesis
  obtain ⟨cs, hcutok, hdc, hconfH, -⟩ := hcut GF ad z ss him hc hconf hne hch
  have hacyH := hIH cs (GraphFetchKill.properCutFOfCut GF cs hcutok hdc) hconfH
  -- (3) the certified run datum
  obtain ⟨c, pst, dv, hrd, hlog⟩ := hcert GF ad cs z ss him hc hconf hcutok hconfH hacyH hne hch
  -- (4) the erased run (M2's replay), and the exports at its log
  obtain ⟨t2, σ2, hrtc, hlgeq⟩ :=
    runErasedZ gen σ0 boot d0 N GF.gfGd.gdG c pst dv hfr hcov hb1 hb2 him hrd
  have hpr : protReg P (cdLog c c.cdTr.length) := by
    rw [← hlgeq]
    exact protRegOfRun hlc GF0 gen σ0 D hD Nm P t2 σ2 hfr hwpp hrtc
  -- (5) the classification, and the kill at `ioCross`
  have hnB : ¬ badRun gen σ0 := noBadRun hlc GF0 gen σ0 D hD hfr hwp
  exact cycleKillIOC GF ad z ss hc hres hdr hne
    (rawChainChainCZ GF ad P (cdLog c c.cdTr.length) (badRun gen σ0) ss hc hres hdr hlog hpr hnB
      (hl2 GF ad him hconf (cdLog c c.cdTr.length) z ss hc hlog hpr hne hch) z z ss
      (fun _ h => h) hch)

/-- **`t2linOfL2CZ`** (`t2linOfL2'''C`'s twin, the certification supply named): T2-LIN at the
Zifencei bundle — every booted cat graph carrying it, with the I/O residue facts, is
`racyDIO`-acyclic. -/
theorem t2linOfL2CZ (hlc : HasLC) (GF0 : BundledGFunctors) [MachGpreS hlc GF0] [WeakGpreS GF0]
    (gen : Nat) (σ0 : WGState) (D : CPU → List Register) (hD : ∀ c, (D c).Nodup)
    (Nm : Int → Int → Namespace) (P : Int → Int → Prop)
    (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (N : Nat) :
    freshEra gen σ0 →
    (List.range' 0 N).map boot = epsInit σ0 →
    d0 = efInit σ0.wgdev →
    wpPackage hlc GF0 gen σ0 D →
    (∀ a base, P a base → wpPackageProt hlc GF0 gen σ0 D (Nm a base) a base) →
    (∀ ρ, rtc epfRun (epInit gen, σ0) ρ → efetchItvOk ρ.1 ρ.2) →
    cutSupplyCZ boot d0 fab (imgZ σ0.wgimg) →
    certSupplyCZ boot d0 fab (imgZ σ0.wgimg) N →
    l2ClaimCZ boot d0 fab (imgZ σ0.wgimg) P (badRun gen σ0) →
    ∀ (GF : Gfexec) (ad : List (Geid × Geid)),
      GF.gfGd.gdG.gxImg = imgZ σ0.wgimg →
      rvwmoCatAD GF.gfGd ad → GraphFabConf.gfexecConfZF boot d0 fab GF →
      ioResidueGmo GF → gdiskRead14 GF.gfGd.gdG →
      ∀ x, ¬ tc (racyDIO GF) x x :=
  fun hfr hb1 hb2 hwp hwpp hcov hcut hcert hl2 =>
    t2linOfCycleKillCZ boot d0 fab _
      (cycleKillOfL2CZ hlc GF0 gen σ0 D hD Nm P boot d0 fab N hfr hb1 hb2 hwp hwpp hcov hcut hcert
        hl2)

end glue

end CatLin

end Weak
