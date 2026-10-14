/-
Weak: **W10-4 [OWN.94] (N2′), increment 5 — the site datum's step, LOCKSTEP OR TAINTED: `hartStepR` from
per-site facts** (`PROGRESS-W10N2p.md`).  Lean-only, no Rocq twin.

`CertZ9.hartStepR` (the walk's per-step obligation) is discharged here for the relation
**`CertZ13.relT TT`** — a hart is in LOCKSTEP (certified state = emission state) or TAINTED
(`csync (TT x n)`: the same node, or both in one instruction's silent tail, registers agreeing off the
per-slot taint bound `TT x n`) — from the PER-SITE FACTS **`CertZ13.siteFacts`**:

  * the read footprint exists and every fetch's VALUES are the latest bytes (text custody);
  * the taint bound grows along the row;
  * the read VALUES agree with the latest bytes, OR the row label is a PLAIN load whose node is a
    POISON site (`CertZ11.loadTail` off the next bound) — an RMW always agrees (no poisoned arm);
  * when tainted: the block reads no register of the bound (`CertZ13.blockUntainted`: star, realizing
    step, the pair's pieces), and in the silent-tail arm the realizing label is not `LDev`.

**`CertZ13.siteStep`** packages them per step and **`CertZ13.hartStepOfSite`** proves `hartStepR`
(lockstep with agreement: `CertZ9.lockstepStep`; lockstep with poison: `CertZ11.realizeT` at the
empty taint; tainted: the certified star by the mirror (`clockstep`) or `CertZ10.syncStar` (tail),
then `CertZ11.realizeT` / `CertZ12.pairT`).

Spec: the site facts are facts of the program at each site and of the walk's values (W10-4, per pc;
the [OWN.63/64] value arguments at a poisoned branch read enter as the taint bound and the untainted
clauses); FAITHFUL.  Lean-only helpers file-qualified (`CertZ13.*`).
-/
import Weak.CertZ12

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open TsoShadow
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D
open Wlabel

local notation "Ofence" => Option (Bool × Bool × Bool × Bool)

/-! # 1. The relation and the site facts -/

/-- **LOCKSTEP OR TAINTED.** -/
def CertZ13.relT (TT : Nat → Nat → List Nat) : CertZ9.HRel :=
  fun x n pE pC => pE = pC ∨
    ∃ (cpu : CPU) (m1 : SailM Unit) (rs1 : RegFile) (fn1 : Ofence) (ib1 : Ibch) (m2 : SailM Unit)
      (rs2 : RegFile) (fn2 : Ofence) (ib2 : Ibch),
      pE = .PHart cpu m1 rs1 fn1 ib1 ∧ pC = .PHart cpu m2 rs2 fn2 ib2 ∧
      csync (TT x n) m1 rs1 fn1 ib1 m2 rs2 fn2 ib2

/-- The emission's block reads no register of `T`: its star, its realizing step, and (a pair) the
`LInstr`-free star and the exclusive write. -/
def CertZ13.blockUntainted (T : List Nat) (cpu : CPU) (d : Efab) (ls : List Wlabel) (l : Wlabel)
    (m1 : SailM Unit) (rs1 : RegFile) (fn1 : Ofence) (ib1 : Ibch) : Prop :=
  ∀ (ma : SailM Unit) (rsa : RegFile) (fna : Ofence) (iba : Ibch) (da : Efab),
    admRun true (.PHart cpu m1 rs1 fn1 ib1) d ls (.PHart cpu ma rsa fna iba) da →
    CertZ10.starUntainted T cpu ls m1 rs1 fn1 ib1 d ma rsa fna iba da ∧
    ∀ (mT : SailM Unit) (rsT : RegFile) (fnT : Ofence) (ibT : Ibch) (dT : Efab),
      pstepEv (.PHart cpu ma rsa fna iba) da l (.PHart cpu mT rsT fnT ibT) dT →
      CertZ11.stepUntainted T cpu l ma rsa fna iba da mT rsT fnT ibT dT ∧
      ∀ (ls2 : List Wlabel) (mm2 : SailM Unit) (rsm2 : RegFile) (fnm2 : Ofence) (ibm2 : Ibch)
        (dm2 : Efab) (l2 : Wlabel) (mE : SailM Unit) (rsE : RegFile) (fnE : Ofence) (ibE : Ibch)
        (dE : Efab),
        admRunG pstepEv false (.PHart cpu mT rsT fnT ibT) dT ls2
          (.PHart cpu mm2 rsm2 fnm2 ibm2) dm2 →
        pstepEv (.PHart cpu mm2 rsm2 fnm2 ibm2) dm2 l2 (.PHart cpu mE rsE fnE ibE) dE →
        CertZ12.runUntainted T cpu ls2 mT rsT fnT ibT dT mm2 rsm2 fnm2 ibm2 dm2 ∧
        CertZ11.stepUntainted T cpu l2 mm2 rsm2 fnm2 ibm2 dm2 mE rsE fnE ibE dE

/-- **THE PER-SITE FACTS** at one step. -/
def CertZ13.siteFacts (TT : Nat → Nat → List Nat) (St : CycState) (x n : Nat) (lb : Lbl)
    (ls : List Wlabel) (l : Wlabel) (pE pC : Pexv6) : Prop :=
  CertZ4.readFoot St.cstC lb ∧ CertZ5.fetchAgree St.cstC ls ∧ TT x n ⊆ TT x (n + 1) ∧
  (CertZ11.readAgree St.cstC lb ∨
    ((∃ base ts vs, lb = .LLoad false base ts vs) ∧
      ∀ (pa : Pexv6) (da : Efab), admRunG pstepEv true pE (St.cstDv (cdEnd St.cstC)) ls pa da →
        ∃ (cpu : CPU) (ma : SailM Unit) (rsa : RegFile) (fna : Ofence) (iba : Ibch),
          pa = .PHart cpu ma rsa fna iba ∧ CertZ11.loadTail (TT x (n + 1)) cpu ma)) ∧
  (∀ (cpu : CPU) (m1 : SailM Unit) (rs1 : RegFile) (fn1 : Ofence) (ib1 : Ibch) (m2 : SailM Unit)
      (rs2 : RegFile) (fn2 : Ofence) (ib2 : Ibch),
    pE = .PHart cpu m1 rs1 fn1 ib1 → pC = .PHart cpu m2 rs2 fn2 ib2 →
    csync (TT x n) m1 rs1 fn1 ib1 m2 rs2 fn2 ib2 →
    CertZ13.blockUntainted (TT x n) cpu (St.cstDv (cdEnd St.cstC)) ls l m1 rs1 fn1 ib1 ∧
    (¬ clockstep (TT x n) m1 rs1 fn1 ib1 m2 rs2 fn2 ib2 →
      ∀ kd ba bs sa sv, l ≠ LDev kd ba bs sa sv))

/-- **THE PER-STEP SITE DATUM** (W10-4's per-pc obligation, named): at every step of the walk, the
per-site facts. -/
def CertZ13.siteStep (d0 : Efab) (TT : Nat → Nat → List Nat) : Prop :=
  ∀ (St : CycState) (itvOf : Nat → Nat → Nat) (fiOf : Nat → Nat → Bool) (x n : Nat) (lb : Lbl)
    (ws : Wstate) (ls : List Wlabel) (l : Wlabel) (pE pE' pC : Pexv6) (d' : Efab),
    CertZ.cstOkZW d0 St itvOf fiOf →
    (St.cstPst (cdEnd St.cstC))[x]? = some pC → CertZ13.relT TT x n pE pC →
    CertZ4.lblShape lb →
    ((lbFused l ∧ GraphFetchBlocks.blkOne (St.cstDv (cdEnd St.cstC)) d' ws lb ls l pE pE') ∨
      GraphFetchBlocks.blkPair (St.cstDv (cdEnd St.cstC)) d' ws lb ls l pE pE') →
    CertZ13.siteFacts TT St x n lb ls l pE pC

/-! # 2. The certified star from `csync` -/

/-- The certified star from `csync`-related states: the mirror (same node) or the re-convergence
(silent tail; then the realizing label is not `LDev`). -/
theorem CertZ13.certStar (T : List Nat) (cpu : CPU) (d : Efab)
    (m1 : SailM Unit) (rs1 : RegFile) (fn1 : Ofence) (ib1 : Ibch)
    (m2 : SailM Unit) (rs2 : RegFile) (fn2 : Ofence) (ib2 : Ibch)
    (ls : List Wlabel) (ma : SailM Unit) (rsa : RegFile) (fna : Ofence) (iba : Ibch) (da : Efab)
    (l : Wlabel) (p' : Pexv6) (d' : Efab) :
    csync T m1 rs1 fn1 ib1 m2 rs2 fn2 ib2 →
    admRun true (.PHart cpu m1 rs1 fn1 ib1) d ls (.PHart cpu ma rsa fna iba) da →
    CertZ10.starUntainted T cpu ls m1 rs1 fn1 ib1 d ma rsa fna iba da →
    ¬ lbAdmin true l →
    (¬ clockstep T m1 rs1 fn1 ib1 m2 rs2 fn2 ib2 → ∀ kd ba bs sa sv, l ≠ LDev kd ba bs sa sv) →
    pstepEv (.PHart cpu ma rsa fna iba) da l p' d' →
    ∃ (ls2 : List Wlabel) (rsa2 : RegFile),
      admRun true (.PHart cpu m2 rs2 fn2 ib2) d ls2 (.PHart cpu ma rsa2 fna iba) da ∧
      dregAgree (fun n => n ∉ T) rsa rsa2 ∧
      ∀ base tvs, LIFetch base tvs ∈ ls2 → tvs = [] ∨ LIFetch base tvs ∈ ls := by
  intro hcs hadm hunt hna hld hst
  by_cases hck : clockstep T m1 rs1 fn1 ib1 m2 rs2 fn2 ib2
  · obtain ⟨hm, hfn, hib, hag⟩ := hck
    rw [hm, hfn, hib]
    obtain ⟨rds, wrs, ann, hrun⟩ := pevrunPhrun ls _ d _ da (admRunPevrun true _ d ls _ da hadm)
      cpu m1 rs1 fn1 ib1 ma rsa fna iba rfl rfl
    obtain ⟨rsa2, hrun2, hag2⟩ :=
      phrunDagree _ cpu ls rds wrs ann m1 rs1 fn1 ib1 d ma rsa fna iba da hrun (hunt _ _ _ hrun) rs2
        hag
    exact ⟨ls, rsa2, CertZ10.admRunOfPhrun true cpu ls rds wrs ann m1 rs2 fn1 ib1 d ma rsa2 fna iba
      da hrun2 (admRunAdmin true _ d ls _ da hadm), hag2, fun _ _ h => .inr h⟩
  · exact CertZ10.syncStar T cpu d m1 rs1 fn1 ib1 m2 rs2 fn2 ib2 ls ma rsa fna iba da l p' d' hcs
      hadm hunt hna (hld hck) hst

theorem CertZ13.fetchAgreeSub (c : Cand) (ls ls2 : List Wlabel) :
    CertZ5.fetchAgree c ls →
    (∀ base tvs, LIFetch base tvs ∈ ls2 → tvs = [] ∨ LIFetch base tvs ∈ ls) →
    CertZ5.fetchAgree c ls2 := by
  intro hf hsub base tvs hm
  rcases hsub base tvs hm with rfl | h
  · exact ⟨by simp [witTvs, lrdTs, lrdVs], fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  · exact hf base tvs h

/-! # 3. `hartStepR` from the site datum -/

/-- **`CertZ13.hartStepOfSite` — THE WALK'S STEP, LOCKSTEP OR TAINTED, FROM THE SITE DATUM.** -/
theorem CertZ13.hartStepOfSite (d0 : Efab) (TT : Nat → Nat → List Nat) :
    CertZ13.siteStep d0 TT → CertZ9.hartStepR d0 (CertZ13.relT TT) := by
  intro hsite St itvOf fiOf x n lb ws ls l pE pE' pC d' hok hp hrel hr hsh hblk
  obtain ⟨hft, hfag, hTT, hval, hunt⟩ := hsite St itvOf fiOf x n lb ws ls l pE pE' pC d' hok hp
    hrel hsh hblk
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

/-! # 4. The site supply and the kill -/

namespace CatLin

/-- **THE SITE SUPPLY — W10-4's NAMED PREMISE (per pc)**: on every cyclic class graph with the residue
facts and every fitting emission datum, a per-slot taint bound with the per-step site datum. -/
def siteSupplyCZ (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image) : Prop :=
  ∀ (GF : Gfexec) (ad : List (Geid × Geid)) (z : Geid) (ss : List Seg),
    GF.gfGd.gdG.gxImg = im → rvwmoCatAD GF.gfGd ad → GraphFabConf.gfexecConfZF boot d0 fab GF →
    ioResidueGmo GF → gdiskRead14 GF.gfGd.gdG →
    ss ≠ [] → rawChainC GF.gfGd (ioCross GF) z z ss →
    ∀ D : Nat → CertZ7.EmData, CertZ7.emDataOk boot fab GF D →
    ∃ TT : Nat → Nat → List Nat, CertZ13.siteStep d0 TT

/-- The step supply from the site supply (the walk starts in lockstep). -/
theorem stepSupplyOfSite (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image) :
    siteSupplyCZ boot d0 fab im → stepSupplyCZ boot d0 fab im := by
  intro hs GF ad z ss him hc hconf hres hdr hne hch D hD
  obtain ⟨TT, hTT⟩ := hs GF ad z ss him hc hconf hres hdr hne hch D hD
  exact ⟨CertZ13.relT TT, fun _ _ => .inl rfl, CertZ13.hartStepOfSite d0 TT hTT⟩

section glue

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode
open Language.Notation PrimStep

/-- **`cycleKillOfOrdSiteCZRC`** — WHAT W11-F CONSUMES AT THE ZERO CUT (N2′, after W10-4 inc. 5): the class
kill from the WP package, the fetch-view premise, the hart count and (P2), the ORDER supply, the SITE
supply (per pc: lockstep or tainted, poisoned loads, untainted blocks, value agreement), the two xv6
lock facts and the L2′ claim at the member. -/
theorem cycleKillOfOrdSiteCZRC (hlc : HasLC) (GF0 : BundledGFunctors) [MachGpreS hlc GF0]
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
    orderSupplyCZ boot d0 fab (imgZ σ0.wgimg) P →
    siteSupplyCZ boot d0 fab (imgZ σ0.wgimg) →
    acqAqCZ boot d0 fab (imgZ σ0.wgimg) P →
    relCoversCZ boot d0 fab (imgZ σ0.wgimg) P →
    l2ClaimCZR boot d0 fab (imgZ σ0.wgimg) P (badRun gen σ0) →
    cycleKillCZC boot d0 fab (imgZ σ0.wgimg) :=
  fun hfr hb1 hb2 hwp hwpp hcov hpre hord hsite hAQ hRC hl2 =>
    cycleKillOfOrdStepCZRC hlc GF0 gen σ0 D hD Nm P boot d0 fab N hfr hb1 hb2 hwp hwpp hcov hpre
      hord (stepSupplyOfSite boot d0 fab _ hsite) hAQ hRC hl2

end glue

end CatLin

end Weak
