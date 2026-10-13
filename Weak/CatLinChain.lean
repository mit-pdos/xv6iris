/-
Weak: **W12 (4)–(5) — the T2-LIN chain and the capstone over riscv.cat (TAGGED)** (plan
`notes/weak-allocproc-plan.md` §C W12 (4)–(5); D25 (a) [OWN.5], D33 (a) [OWN.13]).

Lean-only, no Rocq twin.  The RVWMO⁻ chain (`WeakRvwmoLinInd` §3, `WeakRvwmoGlue` §6,
`WeakRvwmoGlue2` §2–§4, `WeakRvwmoWalk` §4.2, `WeakRvwmoWalk3`, `WeakRvwmoCapstone` §2) restated
with the hypothesis `CatLin.rvwmoCatAD GD ad`; every statement is the RVWMO⁻ one with that
hypothesis, `rawChainC`/`segRunC`/`gcrossE`/`segPinC` in place of `rawChain`/`segRun`/`gcross`/
`segPin`, and the chain's sub-results reused unchanged where they never read ppo (`hullRun`,
`topoSupply` — both now take `rvwmoCoreD`, W12 (1) — `runErased`, `protRegOfRun`, `noBadRun`).

  §1  T2-LIN over cat: `cycleKillC`, `t2linAuxC` (the induction steps through `hullCatAD`),
      `t2linOfCycleKillC`, `t2linSupplyC`.
  §2  The glue: `csHypsCertC`, `l2ClaimAtC` (`segPinC ∨ csHyps ∨ Bad` on `gcrossE`-entered
      segments), `l2ClaimC`, `rawChainChainC`, `cutSupplyC` (+ its unconditional discharge
      `cutSupplyOfCycleC`), `certSupplyC`, `walkSupplyC`, `walkPolicyC`, `certSupplyOfWalkC`,
      `walkSupplyOfPolicyC`, `cycleKillOfL2C`, `t2linOfL2'''C`.
  §3  The TAGGED conformance text `gdexecQconfT` (`gdexecQconf` with the TAGGED edges
      `rowDepsT ⊆ GT.gtDeps` in place of `rowDeps ⊆ gdDeps`) and `gdexecQconfTForget` (it
      implies `gdexecQconf (forget GT)`, by `AxDeps.rowDepsSubT` and the target-is-a-store fact
      `hartConfRowDepsWf`); the capstone `xv6RvwmoSafeModuloT` — STATED, premises W11's, NOT
      registered (plan: "its premises are W11's").

**Trusted-surface note (`gdexecQconfT`, §A(6)).**  It is new statement text: each hart's row is
the hart's emission from its boot program (`hartConf`), quiescent (`emDevfree`), fetching from
the image (`emFetchImg`), and EVERY tagged dependency edge the tagger `rowDepsT` emits for that
emission is an edge of `GT.gtDeps` with its tag.  It is reviewed against `rowDepsT`'s correction
(5) (`AxDeps.lean` header: `dtAdr` fed only from an access's own `asrc`).  It covers I/O items
only as far as today's `rowDepsT` does (W13 (F-dep) extends the tagger; the plan names that
item as the one that makes the text cover I/O sources).

**Spec reliance on `AxDeps.gtdepsWf`'s RAM-endpoint shape** (pending ruling on W13 (F-dep)): only
through `CatLin.catADOfCatT` (`catTForgetAxioms`, `gtAdSubForget`); `gdexecQconfTForget` relies
on `forgetDeps` keeping exactly the WRITE-targeted edges (`elemOfForgetDeps`).
-/
import Weak.CatLinHull
import Weak.WeakRvwmoWalk3

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Lbl

namespace CatLin

/-! # 1. T2-LIN over cat -/

def cycleKillC (boot : Nat → Pexv6) (d0 : Efab) (im : Image) (nh : Nat) : Prop :=
  ∀ (GD : Gdexec) (ad : List (Geid × Geid)),
    rvwmoCatAD GD ad →
    gdexecQconf boot d0 im nh GD →
    (∀ cs, properCut GD.gdG cs → ∀ x, ¬ tc (racyD (gdHull GD cs)) x x) →
    ∀ x, tc (racyD GD) x x → False

theorem t2linAuxC (boot : Nat → Pexv6) (d0 : Efab) (im : Image) (nh : Nat) :
    cycleKillC boot d0 im nh →
    ∀ (n : Nat) (GD : Gdexec) (ad : List (Geid × Geid)),
      (gevs' GD.gdG).length ≤ n →
      rvwmoCatAD GD ad →
      gdexecQconf boot d0 im nh GD →
      ∀ x, ¬ tc (racyD GD) x x := by
  intro hk n
  induction n with
  | zero =>
    intro GD ad hlen hc hq x hcyc
    refine hk GD ad hc hq ?_ x hcyc
    intro cs hpc y _
    have := hullEventsLt GD.gdG cs hpc
    omega
  | succ n ih =>
    intro GD ad hlen hc hq x hcyc
    refine hk GD ad hc hq ?_ x hcyc
    intro cs hpc
    refine ih (gdHull GD cs) (adCut cs ad) ?_ (hullCatAD GD ad cs hc hpc.1)
      (gdexecQconfHull boot d0 im nh GD cs hq)
    have := hullEventsLt GD.gdG cs hpc
    change (gevs' (gxHull GD.gdG cs)).length ≤ n
    omega

theorem t2linOfCycleKillC (boot : Nat → Pexv6) (d0 : Efab) (im : Image) (nh : Nat) :
    cycleKillC boot d0 im nh →
    ∀ (GD : Gdexec) (ad : List (Geid × Geid)),
      rvwmoCatAD GD ad →
      gdexecQconf boot d0 im nh GD →
      ∀ x, ¬ tc (racyD GD) x x :=
  fun hk GD ad => t2linAuxC boot d0 im nh hk (gevs' GD.gdG).length GD ad (Nat.le_refl _)

/-- THE COROLLARY: the whole cat graph is realized (at the pinned LTS). -/
theorem t2linSupplyC (boot : Nat → Pexv6) (d0 : Efab) (im : Image) (nh : Nat)
    (GD : Gdexec) (ad : List (Geid × Geid)) (N : Nat) :
    cycleKillC boot d0 im nh →
    rvwmoCatAD GD ad →
    gdexecQconf boot d0 im nh GD →
    GD.gdG.gxProg.length ≤ N →
    ∃ (c : Cand) (pst : Nat → List Pexv6),
      srvwmoConsistent c ∧
      c.cdImg = GD.gdG.gxImg ∧
      pst 0 = (List.range' 0 N).map boot ∧
      execProgOk' (pstepPin c.cdImg pstepEv) pclsEv pst (fun _ => d0) (candExec c) := by
  intro hk hc hq hN
  obtain ⟨c, hsr, himg, pst, hpst0, hprg⟩ := topoSupply boot d0 GD N (catADCore GD ad hc)
    (fun x y => racyDDec GD x y) (t2linOfCycleKillC boot d0 im nh hk GD ad hc hq) im nh hq hN
  exact ⟨c, pst, hsr, himg, hpst0, hprg⟩

/-! # 2. THE GLUE over cat -/

/-- A CS-chained segment IS a `CSchained` certificate, for any gmo-forward cross order. -/
theorem csHypsCertC (GD : Gdexec) (ad : List (Geid × Geid)) (X : Geid → Geid → Prop)
    (P : Int → Int → Prop) (log : List Wmsg) (prev : Geid) (s : Seg) :
    rvwmoCatAD GD ad → (∀ x y, X x y → gmoLt GD.gdG x y) →
    logOf GD.gdG log → protReg P log →
    csHyps GD P log prev s → X prev s.sgEntry →
    CertC GD.gdG X prev s := by
  rintro hc hX hlog hpr
    ⟨b, a, ACQ, REL, hP, hlwb, hwa, hcl, hlew, hnob, hacq, hrow, haq, hleA, hcs, hpoe, hfen,
      hpox, hmx, hhart, hside⟩ hx
  obtain ⟨n0, r0, h, hprot, -, halt⟩ := hpr a b hP
  obtain ⟨hr0, hn0A⟩ := hside n0 r0 hprot
  exact .CSchained (csChainedC GD ad log b a n0 r0 h prev s.sgEntry s.sgExit ACQ REL hc hlog
    hlwb halt hrow hprot hwa hcl hr0 hlew hnob hacq haq hn0A hleA hcs hpoe hfen (hX _ _ hx) hpox
    hmx hhart)

/-- THE L2′ CLAIM over cat: each `gcrossE`-entered segment is PINNED (a same-hart chain of
ordered steps), CS-chained, or `Bad`. -/
def l2ClaimAtC (GD : Gdexec) (ad : List (Geid × Geid)) (P : Int → Int → Prop) (Bad : Prop) :
    Prop :=
  ∀ (log : List Wmsg) (z : Geid) (ss : List Seg),
    rvwmoCatAD GD ad →
    logOf GD.gdG log →
    protReg P log →
    ss ≠ [] → rawChainC GD (gcrossE GD.gdG) z z ss →
    ∀ (prev : Geid) (s : Seg),
      s ∈ ss → gcrossE GD.gdG prev s.sgEntry → segRunC GD s →
      segPinC GD ad s ∨ csHyps GD P log prev s ∨ Bad

def l2ClaimC (boot : Nat → Pexv6) (d0 : Efab) (im : Image) (nh : Nat)
    (P : Int → Int → Prop) (Bad : Prop) : Prop :=
  ∀ GD ad, gdexecQconf boot d0 im nh GD → l2ClaimAtC GD ad P Bad

/-- A classified raw chain IS a `chainC` (cross order `gcrossE`). -/
theorem rawChainChainC (GD : Gdexec) (ad : List (Geid × Geid)) (P : Int → Int → Prop)
    (log : List Wmsg) (Bad : Prop) (ss : List Seg) :
    rvwmoCatAD GD ad → logOf GD.gdG log → protReg P log →
    ¬ Bad →
    (∀ prev s, s ∈ ss → gcrossE GD.gdG prev s.sgEntry → segRunC GD s →
       segPinC GD ad s ∨ csHyps GD P log prev s ∨ Bad) →
    ∀ (x y : Geid) (ss' : List Seg),
      ss' ⊆ ss → rawChainC GD (gcrossE GD.gdG) x y ss' →
      chainC GD.gdG (gcrossE GD.gdG) x y ss' := by
  intro hc hlog hpr hnB hcl x y ss'
  have hX : ∀ x y, gcrossE GD.gdG x y → gmoLt GD.gdG x y :=
    fun x y => gcrossEGmo GD.gdG x y hc.1 hc.2.2.1
  induction ss' generalizing x with
  | nil => intro _ hch; exact hch
  | cons s ss' ih =>
    intro hsub hch
    obtain ⟨hx, hrun, hrest⟩ := hch
    have hs : s ∈ ss := hsub (by simp)
    have hsub' : ss' ⊆ ss := by
      intro t ht
      exact hsub (List.mem_cons_of_mem s ht)
    show CertC GD.gdG (gcrossE GD.gdG) x s ∧ chainC GD.gdG (gcrossE GD.gdG) s.sgExit y ss'
    refine ⟨?_, ih _ hsub' hrest⟩
    rcases hcl x s hs hx hrun with hp | hcs | hb
    · exact segPinCCert GD ad _ x s hc hx hp
    · exact csHypsCertC GD ad _ P log x s hc hX hlog hpr hcs hx
    · exact absurd hb hnB

def cutSupplyC (boot : Nat → Pexv6) (d0 : Efab) (im : Image) (nh : Nat) : Prop :=
  ∀ (GD : Gdexec) (ad : List (Geid × Geid)) (z : Geid) (ss : List Seg),
    rvwmoCatAD GD ad → gdexecQconf boot d0 im nh GD →
    ss ≠ [] → rawChainC GD (gcrossE GD.gdG) z z ss →
    ∃ cs, cutOk GD.gdG cs

/-- `cycleHasEvent` over cat: the first entry is a gmo member, hence a labelled event. -/
theorem cycleHasEventC (GD : Gdexec) (ad : List (Geid × Geid)) (z : Geid) (ss : List Seg) :
    rvwmoCatAD GD ad →
    ss ≠ [] → rawChainC GD (gcrossE GD.gdG) z z ss →
    ∃ i, i < GD.gdG.gxProg.length ∧ 0 < nrow GD.gdG i := by
  intro hc hne hch
  cases ss with
  | nil => exact absurd rfl hne
  | cons s ss =>
    obtain ⟨hx, -, -⟩ := hch
    obtain ⟨-, hin, -⟩ := gcrossEGmo GD.gdG z s.sgEntry hc.1 hc.2.2.1 hx
    obtain ⟨l, hl, -⟩ := (hc.1.2.1 s.sgEntry).1 hin
    obtain ⟨h1, h2⟩ := glblNrow GD.gdG s.sgEntry l hl
    exact ⟨s.sgEntry.1, h1, by omega⟩

/-- (G-2) over cat, UNCONDITIONALLY (the zero cut). -/
theorem cutSupplyOfCycleC (boot : Nat → Pexv6) (d0 : Efab) (im : Image) (nh : Nat) :
    cutSupplyC boot d0 im nh := by
  intro GD ad z ss hc _ hne hch
  obtain ⟨i, hi, hn⟩ := cycleHasEventC GD ad z ss hc hne hch
  exact ⟨zcut GD.gdG, zcutCutOk GD.gdG i hi hn⟩

def certSupplyC (boot : Nat → Pexv6) (d0 : Efab) (im : Image) (nh : Nat) (N : Nat) : Prop :=
  ∀ (GD : Gdexec) (ad : List (Geid × Geid)) (cs : List Nat) (c0 : Cand)
    (pst0 : Nat → List Pexv6) (z : Geid) (ss : List Seg),
    rvwmoCatAD GD ad → gdexecQconf boot d0 im nh GD →
    cutOk GD.gdG cs →
    RunData boot d0 N GD.gdG c0 pst0 (fun _ => d0) →
    ss ≠ [] → rawChainC GD (gcrossE GD.gdG) z z ss →
    ∃ (c : Cand) (pst : Nat → List Pexv6) (dv : Nat → Efab),
      RunData boot d0 N GD.gdG c pst dv ∧
      logOf GD.gdG (cdLog c c.cdTr.length)

def walkSupplyC (boot : Nat → Pexv6) (d0 : Efab) (im : Image) (nh : Nat) (N : Nat) : Prop :=
  ∀ (GD : Gdexec) (ad : List (Geid × Geid)) (cs : List Nat) (c0 : Cand)
    (pst0 : Nat → List Pexv6) (z : Geid) (ss : List Seg),
    rvwmoCatAD GD ad → gdexecQconf boot d0 im nh GD →
    cutOk GD.gdG cs →
    RunData boot d0 N GD.gdG c0 pst0 (fun _ => d0) →
    ss ≠ [] → rawChainC GD (gcrossE GD.gdG) z z ss →
    ∃ (l : List Segout) (S0 Sf : CycState),
      segsRun d0 l S0 Sf ∧
      Sf.cstC.cdImg = GD.gdG.gxImg ∧
      Sf.cstPst 0 = (List.range' 0 N).map boot ∧
      Sf.cstDv 0 = d0 ∧
      logOf GD.gdG (cdLog Sf.cstC Sf.cstC.cdTr.length)

/-- (R-2) over cat: the certification walk's per-state policy, on every cat graph. -/
def walkPolicyC (boot : Nat → Pexv6) (d0 : Efab) (im : Image) (nh : Nat) (N : Nat) : Prop :=
  ∀ (GD : Gdexec) (ad : List (Geid × Geid)),
    rvwmoCatAD GD ad → gdexecQconf boot d0 im nh GD → walkPolicy boot d0 N GD.gdG

theorem certSupplyOfWalkC (boot : Nat → Pexv6) (d0 : Efab) (im : Image) (nh : Nat) (N : Nat) :
    walkSupplyC boot d0 im nh N → certSupplyC boot d0 im nh N := by
  intro hw GD ad cs c0 pst0 z ss hc hq hcut hrd0 hne hch
  obtain ⟨l, S0, Sf, hrun, himg, hpst, hdv, hlog⟩ :=
    hw GD ad cs c0 pst0 z ss hc hq hcut hrd0 hne hch
  exact ⟨Sf.cstC, Sf.cstPst, Sf.cstDv,
    runDataOfCyc boot d0 N GD.gdG Sf (segsRunOk d0 l S0 Sf hrun) himg hpst hdv, hlog⟩

theorem walkSupplyOfPolicyC (boot : Nat → Pexv6) (d0 : Efab) (im : Image) (nh : Nat)
    (N : Nat) :
    walkPolicyC boot d0 im nh N → walkSupplyC boot d0 im nh N := by
  intro hpol GD ad _ _ _ _ _ hc hq _ _ _ _
  obtain ⟨l, Sf, hrun, _, himg, hpst, hdv, hlog⟩ :=
    wlkRun boot d0 N GD.gdG (walkPolicySteps boot d0 N GD.gdG (hpol GD ad hc hq))
      (gwrites GD.gdG).length 0 (wlkStart boot d0 N GD.gdG) (wlkStartInv boot d0 N GD.gdG)
      (Nat.zero_add _)
  exact ⟨l, wlkStart boot d0 N GD.gdG, Sf, hrun, himg, hpst, hdv, logOfOfPfx _ _ hlog⟩

section glue

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode
open Language.Notation PrimStep
open LeanRV64D

/-- `cycleKillOfL2` over cat. -/
theorem cycleKillOfL2C (hlc : HasLC) (GF : BundledGFunctors) [MachGpreS hlc GF] [WeakGpreS GF]
    (gen : Nat) (σ0 : WGState) (D : CPU → List Register) (hD : ∀ c, (D c).Nodup)
    (Nm : Int → Int → Namespace) (P : Int → Int → Prop)
    (boot : Nat → Pexv6) (d0 : Efab) (im : Image) (nh : Nat) (N : Nat) :
    freshEra gen σ0 →
    bootTie boot d0 im nh N σ0 →
    wpPackage hlc GF gen σ0 D →
    (∀ a base, P a base → wpPackageProt hlc GF gen σ0 D (Nm a base) a base) →
    (∀ ρ, rtc epfRun (epInit gen, σ0) ρ → efetchItvOk ρ.1 ρ.2) →
    cutSupplyC boot d0 im nh →
    certSupplyC boot d0 im nh N →
    l2ClaimC boot d0 im nh P (badRun gen σ0) →
    cycleKillC boot d0 im nh := by
  rintro hfr ⟨hb1, hb2, hb3⟩ hwp hwpp hcov hcut hcert hl2
  intro GD ad hc hq hIH x hcyc
  -- (1) the cycle, as segments entered by rfe ∪ co ∪ fr
  obtain ⟨z, ss, hne, hch⟩ := cycleSegmentsC GD ad x hc hcyc
  -- (2) the cut, and the realized causal past (the core suffices: W12 (1))
  obtain ⟨cs, hcutok⟩ := hcut GD ad z ss hc hq hne hch
  obtain ⟨himg, hN⟩ := hb3 GD hq
  obtain ⟨c0, pst0, -, hrd0, -⟩ :=
    hullRun boot d0 im nh GD cs N (catADCore GD ad hc) hq hcutok
      (hIH cs (cutOkProper _ _ hcutok)) hN
  -- (3) the certified configuration
  obtain ⟨c, pst, dv, hrd, hlog⟩ := hcert GD ad cs c0 pst0 z ss hc hq hcutok hrd0 hne hch
  -- (4) the erased run, and the exports at its log
  obtain ⟨t2, σ2, hrtc, hlgeq⟩ :=
    runErased gen σ0 boot d0 N GD.gdG c pst dv hfr hcov hb1 hb2 himg hrd
  have hpr : protReg P (cdLog c c.cdTr.length) := by
    rw [← hlgeq]
    exact protRegOfRun hlc GF gen σ0 D hD Nm P t2 σ2 hfr hwpp hrtc
  -- (5) the per-site classification, and the kill (gwf + load value only)
  have hnB : ¬ badRun gen σ0 := noBadRun hlc GF gen σ0 D hD hfr hwp
  exact cycleKillArmsC GD.gdG z ss hc.1 hc.2.2.1 hne
    (rawChainChainC GD ad P (cdLog c c.cdTr.length) (badRun gen σ0) ss hc hlog hpr hnB
      (hl2 GD ad hq (cdLog c c.cdTr.length) z ss hc hlog hpr hne hch) z z ss
      (fun _ h => h) hch)

/-- `t2linOfL2'''` over cat: T2-LIN at the canonical premises, (R-2) as the walk's policy. -/
theorem t2linOfL2'''C (hlc : HasLC) (GF : BundledGFunctors) [MachGpreS hlc GF] [WeakGpreS GF]
    (gen : Nat) (σ0 : WGState) (D : CPU → List Register) (hD : ∀ c, (D c).Nodup)
    (Nm : Int → Int → Namespace) (P : Int → Int → Prop)
    (boot : Nat → Pexv6) (d0 : Efab) (N : Nat) :
    freshEra gen σ0 →
    (List.range' 0 N).map boot = epsInit σ0 →
    d0 = efInit σ0.wgdev →
    l2ClaimC boot d0 (imgZ σ0.wgimg) N P (badRun gen σ0) →
    walkPolicyC boot d0 (imgZ σ0.wgimg) N N →
    wpPackage hlc GF gen σ0 D →
    (∀ a base, P a base → wpPackageProt hlc GF gen σ0 D (Nm a base) a base) →
    (∀ ρ, rtc epfRun (epInit gen, σ0) ρ → efetchItvOk ρ.1 ρ.2) →
    ∀ (GD : Gdexec) (ad : List (Geid × Geid)),
      rvwmoCatAD GD ad →
      gdexecQconf boot d0 (imgZ σ0.wgimg) N GD →
      ∀ x, ¬ tc (racyD GD) x x :=
  fun hfr hb1 hb2 hl2 hpol hwp hwpp hcov =>
    t2linOfCycleKillC boot d0 _ N
      (cycleKillOfL2C hlc GF gen σ0 D hD Nm P boot d0 (imgZ σ0.wgimg) N N hfr
        (bootTieOfQconf boot d0 N σ0 hb1 hb2) hwp hwpp hcov (cutSupplyOfCycleC boot d0 _ N)
        (certSupplyOfWalkC boot d0 _ N N (walkSupplyOfPolicyC boot d0 _ N N hpol)) hl2)

end glue

/-! # 3. THE TAGGED CONFORMANCE TEXT AND THE CAPSTONE -/

/-- **The tagged conformance bundle** (new trusted-SURFACE text; header).  `gdexecQconf` with the
dependency clause TAGGED: every edge `rowDepsT` emits for a hart's emission is in `GT.gtDeps`
with its tag. -/
def gdexecQconfT (boot : Nat → Pexv6) (d0 : Efab) (im : Image) (nh : Nat) (GT : GdexecT) :
    Prop :=
  GT.gtG.gxImg = im ∧
  GT.gtG.gxProg.length ≤ nh ∧
  (∀ i row, GT.gtG.gxProg[i]? = some row →
    ∃ em, hartConf i row (boot i) (fun _ => d0) em ∧
          emDevfree em ∧
          emFetchImg im em ∧
          (∀ e, e ∈ rowDepsT em.emItems → (((i, e.1.1), (i, e.1.2)), e.2) ∈ GT.gtDeps))

/-- The tagged bundle gives the untagged one on the projection (`rowDepsSubT`: every tree edge is
a tagged edge; `hartConfRowDepsWf`: its target is a store, so `forget` keeps it). -/
theorem gdexecQconfTForget (boot : Nat → Pexv6) (d0 : Efab) (im : Image) (nh : Nat)
    (GT : GdexecT) :
    gdexecQconfT boot d0 im nh GT → gdexecQconf boot d0 im nh (forget GT) := by
  rintro ⟨himg, hnh, hrows⟩
  refine ⟨himg, hnh, fun i row hrow => ?_⟩
  obtain ⟨em, hcf, hdf, hfi, hdeps⟩ := hrows i row hrow
  refine ⟨em, hcf, hdf, hfi, fun jk hjk => ?_⟩
  obtain ⟨tg, htg, -⟩ := rowDepsSubT em.emItems jk.1 jk.2 hjk
  obtain ⟨-, -, lb, hlb, hw⟩ := hartConfRowDepsWf i row (boot i) (fun _ => d0) em jk hcf hjk
  refine (elemOfForgetDeps GT.gtG GT.gtDeps (i, jk.1) (i, jk.2)).2 ⟨tg, hdeps _ htg, ?_⟩
  have hrow' : GT.gtG.gxProg[i]? = some row := hrow
  simp [gisW, gxLbl, hrow', hlb, hw]

section capstone

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode
open Language.Notation PrimStep
open LeanRV64D

/-- The workhorse over cat (`xv6RvwmoSafeModuloGen` with `rvwmoCatAD`), at an arbitrary boot tie. -/
theorem xv6RvwmoSafeModuloGenC (hlc : HasLC) (GF : BundledGFunctors) [MachGpreS hlc GF]
    [WeakGpreS GF]
    (gen : Nat) (σ0 : WGState) (D : CPU → List Register) (hD : ∀ c, (D c).Nodup)
    (Nm : Int → Int → Namespace) (P : Int → Int → Prop)
    (boot : Nat → Pexv6) (d0 : Efab) (N : Nat) :
    freshEra gen σ0 →
    (List.range' 0 N).map boot = epsInit σ0 →
    d0 = efInit σ0.wgdev →
    wpPackage hlc GF gen σ0 D →
    (∀ a base, P a base → wpPackageProt hlc GF gen σ0 D (Nm a base) a base) →
    (∀ ρ, rtc epfRun (epInit gen, σ0) ρ → efetchItvOk ρ.1 ρ.2) →
    l2ClaimC boot d0 (imgZ σ0.wgimg) N P (badRun gen σ0) →
    walkPolicyC boot d0 (imgZ σ0.wgimg) N N →
    ∀ (GD : Gdexec) (ad : List (Geid × Geid)),
      rvwmoCatAD GD ad →
      gdexecQconf boot d0 (imgZ σ0.wgimg) N GD →
      (∀ x, ¬ tc (racyD GD) x x) ∧
      (∃ (c : Cand) (pst : Nat → List Pexv6) (P' : Epool) (σ' : WGState),
        srvwmoConsistent c ∧
        c.cdImg = imgZ σ0.wgimg ∧
        pst 0 = epsInit σ0 ∧
        execProgOk' pstepEv pclsEv pst (fun _ => d0) (candExec c) ∧
        rtc epfRun (epInit gen, σ0) (P', σ') ∧
        σ'.wglog = cdLog c c.cdTr.length ∧
        (ecfgOf P' σ').pcAgs.map Wpagent.paSt = pst c.cdTr.length) ∧
      (∀ ρ, rtc epfRun (epInit gen, σ0) ρ → ¬ violationHart clsOf pubOf nDisk (ecfgOf ρ.1 ρ.2)) ∧
      (∀ (t2 : List EExpr) (σ2 : WGState) (e2 : EExpr),
        (epowerFork gen, σ0) -·->ₜₚ* (t2, σ2) → e2 ∈ t2 → Reducible (e2, σ2)) := by
  intro hfr hb1 hb2 hwp hwpp hcov hl2 hpol GD ad hc hq
  obtain ⟨hgen, hpow, hgen0, hlog, hws⟩ := hfr
  have hfr' : freshEra gen σ0 := ⟨hgen, hpow, hgen0, hlog, hws⟩
  have hk := cycleKillOfL2C hlc GF gen σ0 D hD Nm P boot d0 (imgZ σ0.wgimg) N N hfr'
    (bootTieOfQconf boot d0 N σ0 hb1 hb2) hwp hwpp hcov (cutSupplyOfCycleC boot d0 _ N)
    (certSupplyOfWalkC boot d0 _ N N (walkSupplyOfPolicyC boot d0 _ N N hpol)) hl2
  have hacy : ∀ x, ¬ tc (racyD GD) x x := t2linOfCycleKillC boot d0 _ N hk GD ad hc hq
  have hN := gdexecQconfNharts _ _ _ _ _ hq
  obtain ⟨c, pst, hsr, himg, hpst0, hprog⟩ := t2linSupplyC boot d0 _ N GD ad N hk hc hq hN
  have himg' : c.cdImg = imgZ σ0.wgimg := by rw [himg, gdexecQconfImg _ _ _ _ _ hq]
  have hpst0' : pst 0 = epsInit σ0 := by rw [hpst0, hb1]
  rw [himg'] at hprog
  obtain ⟨hreal, hvf, hred⟩ :=
    xv6SrvwmoSafe (hlc := hlc) (GF := GF) gen σ0 D hD c pst (fun _ => d0) hgen hpow hgen0 hlog
      hws hwp hcov hsr himg' hpst0' hb2 hprog
  obtain ⟨P', σ', hr, hlg, hpg⟩ := hreal
  exact ⟨hacy, ⟨c, pst, P', σ', hsr, himg', hpst0',
    WeakRvwmoCapstone.execProgOkPinSub _ _ _ _ _ _ hprog, hr, hlg, hpg⟩, hvf, hred⟩

/-- **W12 (5) THE CAPSTONE, TAGGED** — quantified over riscv.cat RVWMO-consistent tagged
executions (`AxDeps.rvwmoCatConsistentT`, D33 (a)) conforming to xv6's emission
(`gdexecQconfT`), at the canonical boot tie.  STATED: its premises — the L2′ claim and the walk's
policy, over cat graphs — are W11's; NOT registered. -/
theorem xv6RvwmoSafeModuloT (hlc : HasLC) (GF : BundledGFunctors) [MachGpreS hlc GF]
    [WeakGpreS GF]
    (gen : Nat) (σ0 : WGState) (D : CPU → List Register) (hD : ∀ c, (D c).Nodup)
    (Nm : Int → Int → Namespace) (P : Int → Int → Prop) :
    freshEra gen σ0 →
    wpPackage hlc GF gen σ0 D →
    (∀ a base, P a base → wpPackageProt hlc GF gen σ0 D (Nm a base) a base) →
    (∀ ρ, rtc epfRun (epInit gen, σ0) ρ → efetchItvOk ρ.1 ρ.2) →
    -- (R-1) over cat
    l2ClaimC (xboot σ0) (efInit σ0.wgdev) (imgZ σ0.wgimg) (xN σ0) P (badRun gen σ0) →
    -- (R-2) over cat, as the walk's per-state policy
    walkPolicyC (xboot σ0) (efInit σ0.wgdev) (imgZ σ0.wgimg) (xN σ0) (xN σ0) →
    ∀ GT : GdexecT,
      rvwmoCatConsistentT GT →
      gdexecQconfT (xboot σ0) (efInit σ0.wgdev) (imgZ σ0.wgimg) (xN σ0) GT →
      (∀ x, ¬ tc (racyD (forget GT)) x x) ∧
      (∃ (c : Cand) (pst : Nat → List Pexv6) (P' : Epool) (σ' : WGState),
        srvwmoConsistent c ∧
        c.cdImg = imgZ σ0.wgimg ∧
        pst 0 = epsInit σ0 ∧
        execProgOk' pstepEv pclsEv pst (fun _ => efInit σ0.wgdev) (candExec c) ∧
        rtc epfRun (epInit gen, σ0) (P', σ') ∧
        σ'.wglog = cdLog c c.cdTr.length ∧
        (ecfgOf P' σ').pcAgs.map Wpagent.paSt = pst c.cdTr.length) ∧
      (∀ ρ, rtc epfRun (epInit gen, σ0) ρ → ¬ violationHart clsOf pubOf nDisk (ecfgOf ρ.1 ρ.2)) ∧
      (∀ (t2 : List EExpr) (σ2 : WGState) (e2 : EExpr),
        (epowerFork gen, σ0) -·->ₜₚ* (t2, σ2) → e2 ∈ t2 → Reducible (e2, σ2)) :=
  fun hfr hwp hwpp hcov hl2 hpol GT hcT hqT =>
    xv6RvwmoSafeModuloGenC hlc GF gen σ0 D hD Nm P (xboot σ0) (efInit σ0.wgdev) (xN σ0) hfr
      (xbootSeq σ0) rfl hwp hwpp hcov hl2 hpol (forget GT) (gtAd GT.gtG GT.gtDeps)
      (catADOfCatT GT hcT) (gdexecQconfTForget _ _ _ _ GT hqT)

end capstone

end CatLin

end Weak
