/-
Weak: **the footprint-certificate → demonic `wpd` story at a DATA event** (feasibility spike): a
plain RAM load, with the read's annotation deposit discharged at the REAL owned-read protocol.

Rocq: `iris/AxLdspWpd.v` @ xxvzwolszwmp.

## The Rocq header, in substance

§1 (generic) `wpdLoadStep` — the data-read twin of `AxCjrWpd.wpdFetchStep`.  At a plain RAM
`memRead` node whose row item `k` is a (non-RMW) read, the node's `wpd` follows from (i) a flow
resource `F` delivering, for every graph and every graph value `v` at `(i, k)`, the
`wpEvStep`-shaped deposit `loadFlow GD i k (Rv GD v)` (caller-chosen `Rv`), (ii) a continuation
`C` for EVERY read value `v` of the right length (the read is demonic), both carried across the
PLIC wire by Löb (clause (c)).  Clause (b) is EMPTY at a data load; clause (d) is refuted by the
row item at `k`.
§2 (the key part) `ldspFlowOwned` — `F` at the REAL protocol (`obStInterp ≡ protInv γ`,
`annotInterp ≡ AxAnnot.annotInterp`) for an OWNED read whose token arrives as the SPILL's
annotation (the thread holds only the fragment `annotOwn eSd Rsd`), pulled into the reload's flow
as `flowIn` via `annotDetach` (the spill must be in `lobp GD (i, k)`).  The deposit at the reload
is `⌜v = Vs⌝`, derived inside the flow from the token and the coverage wand `protInvPrefixCovMem`
opens from the live invariant.  `wpdLdspOwned` is §1 ∘ §2.
§2b (generic) `wpdCldspFromFetch` — fetch → pre-load `gstep` run (`HrunPre`, a premise) → the
load → a ∀-value post-load `epure` certificate (`Hpost`) → `.pure ()`; via `wpdRunTo` and
`wpdLoadThenRet`.
§3 `wpdLdspOwnedGa2` — §2 at `axGA2` with `obStInterp := protInv γ`: `Hob_eq`/`Hann_eq`/`Htok`/
`Hloc` discharge by conversion; only pure facts about `GD0` remain.

FINDINGS (Rocq's, unchanged): (F1) the continuation must be proved for EVERY `v` (the ownership
fact reaches only the annotation); (F2) the reload's token is the spill's annotation, so the
reload's flow pulls it as `flowIn` (`eSd ∈ lobp GD (i, k)`); (F3) that conjunct and `Hpref`
clash with `AxTierA2.tierAAdequacyAnn`'s `Hlobp_sub`/`Hs_pol_sub` (not machine-checked).

## Deviations from Rocq

1. O2 STAGE C (no `AStepFetch`, no `ax_text`; `AxCjrWpd` deviation 1).
   - `Hntext : ¬ ax_text (pa_z pa)` ↦ `Hnf : (classify req.access_kind).akIfetch = false` in
     `wpdLoadStep`, `wpdLdspOwned`, `wpdLoadThenRet`, `wpdCldspFromFetch` (the load), and
     `HT : ¬ T pa` ↦ `Hnf` in `wpdLdspOwnedGa2` (`axGA2` has no text parameter `T`).  Rocq
     refuted clause (b)'s `AStepFetch` by `Hntext`; in Lean the only way a RAM read node can take
     a non-read step is as the admin `LIFetch`, which `Hnf` excludes (`rdLabel false …` is a
     `LLoad`).
   - `wpdCldspFromFetch`: the fetch is a pinned admin step at `k` (Rocq: a row read at `k`), so
     the pre-load run and the load sit at `k` and the final `.pure ()` at `k + 1` (Rocq: `S k`,
     `S (S k)`); `Hlatf` ↦ `Hfef : akIfetch = true`; `Hgd` states `AxCjrWpd.fetchImgOk` (Q8;
     Rocq `fetch_gd_ok`); `Hflow`/`Hlocf` are dropped (no fetch deposit, no `k ↦ S k`); `Hrow`
     and the flow `F` are at `k` (Rocq `S k`).
2. THE PINS (`AxRunClose` deviation 1): `regs_agree seip_reg` ↦ `regsAgree AxRunClose.pinReg`;
   `wpdLoadThenRet`/`wpdCldspFromFetch` take `Hseip : sig_seip ∉ D` AND `Hmeip : sig_meip ∉ D`.
3. TYPES (as `AxCjrWpd` deviation 3): `RiscvLang.mstate` ↦ `ExecSt` (`sregs` ↦ `regs`),
   `gset register` ↦ `List Register`, `Interface.ReadReq.t n` ↦ `Mem_read_request n va …` (new
   bound `va`/`vaf`), `inl (w, None)` ↦ `.Ok (w, none)`, `Interface.Ret tt` ↦ `.pure ()`,
   `S k` ↦ `k + 1`; `WPd … @ MaybeStuck; i {{ Φ }}` ↦ `wpd .MaybeStuck i s Φ`; `invGS_gen
   HasNoLc Σ` ↦ `[InvGS_gen hlc GF]`; `A -∗ B` ↦ `⊢ A -∗ B`; `e ↦ₐ P` ↦ `AxAnnot.annotOwn e P`;
   graph vocabulary as `AxEpilogue` deviation 4.  `GF : BundledGFunctors.{0,0,0}` in §2/§3
   (`AxannotGS`).
4. §2's section context `γ`, `Hob_eq`, `Hann_eq` are explicit arguments of `ldspFlowOwned` and
   `wpdLdspOwned`.  §3's `Local Instance ldsp_ga2` ↦ the reducible def `ldspGa2 (GF := GF) GD0 γ`
   (`axGA2 GD0 Unit Unit (fun _ GD _ s => protInv γ GD s) ()`, as `AxTierA2` deviation 3),
   passed explicitly; `wpdLdspOwnedGa2`'s `wpd` is at that instance.

No `noSfAnn` premise is needed: the pre-load segment is a `gstep` premise (as Rocq) and the
post-load certificate goes through `epureGstepRtc`, which reads sfence-freedom off `epure`.

**Rocq → Lean name map.**  `load_flow` `loadFlow`, `load_row_ok` `loadRowOk`, `wpd_load_step`
`wpdLoadStep`, `ldsp_own_ok` `ldspOwnOk`, `ldsp_flow_owned` `ldspFlowOwned`, `wpd_ldsp_owned`
`wpdLdspOwned`, `wpd_run_to` `wpdRunTo`, `wpd_load_then_ret` `wpdLoadThenRet`,
`wpd_cldsp_from_fetch` `wpdCldspFromFetch`, `ldsp_ga2` `ldspGa2`, `wpd_ldsp_owned_ga2`
`wpdLdspOwnedGa2`.  None is in the duplicated-name table.  Lean-only (file-qualified):
`AxLdspWpd.loadStepInv`, `AxLdspWpd.annotEq`.

**Dropped:** nothing (Rocq 11 definitions/lemmas; Lean 11 + 2 Lean-only).  **Not ported:** the
`Print Assumptions` block (the lint's axiom check covers it).
-/
import Weak.AxCjrWpd
import Weak.AxEpilogue
import Weak.AxTierA2

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D
open Wlabel

/-! # 1. GENERIC: the data-load node -/

/-- (Lean-only) The program steps of a non-fetch, non-exclusive RAM read node: a plain `LLoad`. -/
theorem AxLdspWpd.loadStepInv (cpu : CPU) (n va : Nat)
    (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit) (rs : RegFile)
    (ib : Ibch) (d : Efab) (l : Wlabel) (p' : Pexv6) (d' : Efab) :
    devAddr req.pa = false → (classify req.access_kind).akLatest = false →
    (classify req.access_kind).akIfetch = false →
    pstepProg (.PHart cpu (.impure (.ok (.memRead n va req)) KK) rs none ib) d l p' d' →
    ∃ tvs : List (Nat × BitVec 8), tvs.length = n ∧
      l = LLoad (classify req.access_kind).akSync false (paZ req.pa) tvs [] ∧
      p' = .PHart cpu (KK (.Ok (wordOfBytes n (tvs.map Prod.snd), none))) rs none ib := by
  intro hdev hlat hnf h
  obtain ⟨tvs, hlen, hl, hp⟩ := fetchNodePstep cpu n va req KK rs ib d l p' d' hdev hlat h
  refine ⟨tvs, hlen, ?_, hp⟩
  rw [hl, hnf]
  rfl

section load
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [axG : AxirisG GF] [Axpol]

/-- The load's annotation deposit at `(i, k)`, with the deposited proposition `R` NAMED. -/
def loadFlow (GD : Gdexec) (i : Agent) (k : Nat) (R : IProp GF) : IProp GF :=
  iprop(∀ na, naAtProgress GD i k na ∗ AxirisG.annotInterp na -∗ |==> ▷ |==>
    ∃ (naUsed naUnused : Mea GF) (ls' : AxirisG.logTsT GF),
      naSplittingWf (Axpol.lobp GD (i, k)) na naUsed naUnused ∗
      flowEqDyn GD (i, k) (Axpol.sPol GD (i, k)) naUsed R ∗
      AxirisG.annotInterp (PartialMap.union (PartialMap.union {[(i, k) := R]} naUnused) na) ∗
      AxirisG.localInterp GD i (k + 1) ls')

/-- The pure row fact: row item `k` is a plain (non-RMW) read. -/
def loadRowOk (GD : Gdexec) (i : Agent) (k : Nat) : Prop :=
  ∃ lb, (AxOpsem.grow GD i)[k]? = some lb ∧ aidentAdvRd (aident lb) = 1

theorem wpdLoadStep (Φ : Athread → IProp GF) (i : Agent) (cpu : CPU) (n va : Nat)
    (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit) (ib : Ibch) (k : Nat)
    (rs0 : RegFile) (Rv : Gdexec → List (BitVec 8) → IProp GF)
    (Hdev : devAddr req.pa = false) (Hlat : (classify req.access_kind).akLatest = false)
    (Hn : 0 < n) (Hnf : (classify req.access_kind).akIfetch = false)
    (Hrow : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜loadRowOk GD i k⌝) :
    ⊢ ∀ rs, ⌜regsAgree AxRunClose.pinReg rs0 rs⌝ -∗
      (∀ (GD : Gdexec) (ls : AxirisG.logTsT GF) (v : List (BitVec 8)),
         ⌜rvwmoCatConsistent GD⌝ -∗ □ AxirisG.gconstInterp GD -∗ AxirisG.localInterp GD i k ls -∗
         ⌜graphValue GD (i, k) = some v⌝ -∗ loadFlow GD i k (Rv GD v)) -∗
      (∀ (v : List (BitVec 8)) (rs' : RegFile), ⌜v.length = n⌝ -∗
         ⌜regsAgree AxRunClose.pinReg rs0 rs'⌝ -∗
         wpd .MaybeStuck i ⟨.PHart cpu (KK (.Ok (wordOfBytes n v, none))) rs' none ib, k + 1⟩ Φ) -∗
      wpd .MaybeStuck i ⟨.PHart cpu (.impure (.ok (.memRead n va req)) KK) rs none ib, k⟩ Φ := by
  unfold loadFlow
  iloeb as IH
  iintro %rs %HP F C
  iapply (AxWpD.wpdMUnfoldStep rvwmoCatConsistent .MaybeStuck i _ Φ).2
  isplit
  · iapply (progressOblMaybestuck (GF := GF) i _).2
    itrivial
  unfold wpdMPreStepDef
  iintro %GD %ls ⟨%Hc, #Hg, Hloc⟩
  ihave Hok := (Hrow GD Hc) $$ Hg
  icases Hok with %Hok
  obtain ⟨lb0, Hlb0, Hadv0⟩ := Hok
  isplit
  · -- (a) THE DATA READ, demonic
    iintro %id %K %Hst
    obtain ⟨lb, Hlb, Hid, -, HK⟩ := Hst
    simp only at Hlb
    rw [Hlb0, Option.some.injEq] at Hlb
    subst Hlb Hid
    simp only [Hadv0, ↓reduceIte]
    iintro %v %Hv %Hlenv
    obtain ⟨l, d, d', -, Hrv, Hps, Hk'⟩ := HK v Hlenv
    obtain ⟨tvs, Htl, rfl, Hp'⟩ :=
      AxLdspWpd.loadStepInv cpu n va req KK rs ib d l _ d' Hdev Hlat Hnf Hps
    simp only [wlRvals] at Hrv
    subst Hrv
    rw [Hadv0] at Hk'
    have hKv : K (tvs.map Prod.snd) =
        ⟨.PHart cpu (KK (.Ok (wordOfBytes n (tvs.map Prod.snd), none))) rs none ib, k + 1⟩ := by
      cases hK : K (tvs.map Prod.snd) with
      | AThread p' k' =>
        rw [hK] at Hp' Hk'
        simp only at Hp' Hk'
        rw [Hp', Hk']
    rw [hKv]
    unfold wpEvStep
    iintro %na Hpg
    ihave Hf := F $$ %GD %ls %(tvs.map Prod.snd) %Hc Hg Hloc %Hv
    imod Hf $$ %na Hpg with Hf
    imodintro
    inext
    imod Hf with ⟨%nu, %nuu, %ls', Hs, Hfe, Hna, Hl⟩
    imodintro
    iexists (), Rv GD (tvs.map Prod.snd), nu, nuu, ls'
    isplitr
    · ipureintro
      trivial
    iframe Hs Hna Hl
    isplitl [Hfe]
    · iapply (flowEqDynMono GD (i, k) _ nu (Rv GD (tvs.map Prod.snd))
        iprop(Rv GD (tvs.map Prod.snd) ∗ ⌜graphValue GD (i, k) = some (tvs.map Prod.snd)⌝))
      · inext
        iintro HR
        iframe HR
        ipureintro
        exact Hv
      · iexact Hfe
    · iapply C $$ %(tvs.map Prod.snd) %rs
      · ipureintro
        rw [List.length_map]
        exact Htl
      · ipureintro
        exact HP
  isplit
  · -- (b) no program step exists at a data-load node
    iintro %l %s' %Hst %Hpin
    have hfalse : False := by
      obtain ⟨d, d', hps⟩ := astepProgPstep _ _ _ _ Hst
      obtain ⟨tvs, -, hl, -⟩ :=
        AxLdspWpd.loadStepInv cpu n va req KK rs ib d l _ d' Hdev Hlat Hnf hps
      subst hl
      cases Hst with
      | AStepAdmin _ _ _ _ _ _ hadm _ => exact hadm
      | AStepWrite _ _ _ _ _ _ _ _ hwr _ _ _ => simp [wlWr] at hwr
      | AStepFence _ _ _ _ _ _ _ _ hf _ _ => simp [wlFence] at hf
    exact hfalse.elim
  isplit
  · -- (c) the PLIC wire: back to the load node, Löb
    iintro %s' %Hw
    obtain ⟨hk, hp⟩ := awireAeqv _ _ Hw
    obtain ⟨p', k'⟩ := s'
    simp only at hk hp
    subst hk
    match p', hp with
    | .PHart c m' rs' fn' ib', hp =>
      obtain ⟨rfl, rfl, rfl, rfl, hag⟩ := hp
      unfold wpSkipStep
      iintro %na Hna
      imodintro
      inext
      imodintro
      iexists ls
      iframe Hna Hloc
      iapply IH $$ %rs' %(regsAgreeTrans _ _ _ _ HP (regsAgreeSym _ _ _ hag)) F C
  · -- (d) row end: the load item sits at `k`
    iintro %Heq
    have h1 := lookup_lt_Some Hlb0
    simp only at Heq
    omega

end load

/-! # 2. THE KEY PART: the flow resource at the REAL owned-read protocol -/

/-- (Lean-only) The annotation map after the detach and the reload's allocation. -/
theorem AxLdspWpd.annotEq {GF : BundledGFunctors} (na : Mea GF) (e e' : Geid) (R P : IProp GF) :
    insert (insert na e R) e' P =
      PartialMap.union (PartialMap.union {[e' := P]} {[e := R]}) na := by
  rw [insertUnionSingletonL (M := GMapF Geid), insertUnionSingletonL (M := GMapF Geid)]
  exact mapUnionAssoc (M := GMapF Geid)

section ldspOwn
variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF] [axG : AxirisG GF]
  [Axpol] [AxlogG GF Hent] [AxannotGS GF]

/-- The per-graph PURE facts the owned reload needs (policy, geometry, the token's own
well-formedness). -/
def ldspOwnOk (GD : Gdexec) (i : Agent) (k : Nat) (eSd : Geid) (a : Int)
    (Hs : List (List Hent)) : Prop :=
  eSd ∈ Axpol.lobp GD (i, k) ∧ eSd ∈ eidsBefore GD i k ∧
  (i, k) ∈ GD.gdG.gxGmo ∧ gisW GD.gdG (i, k) = false ∧
  (LawfulSet.ofList (gmoPrefix GD.gdG (i, k)) : GSet Geid) ⊆ Axpol.sPol GD (i, k) ∧
  (∃ aq ts0 vs0, gxLbl GD.gdG (i, k) = some (.LLoad aq a ts0 vs0) ∧
    ts0.length = 8 ∧ vs0.length = 8) ∧
  (∀ (j : Nat) (H : List Hent), Hs[j]? = some H →
    ∀ p, p ∈ H → gwritesByte GD.gdG p.1 (a + (j : Int)) p.2) ∧
  (∀ (j : Nat) (H : List Hent), Hs[j]? = some H → chainWith (gmoLt GD.gdG) (H.map Prod.fst)) ∧
  (∀ (j : Nat) (H : List Hent), Hs[j]? = some H →
    ∀ w v, gwritesByte GD.gdG w (a + (j : Int)) v → WeakRvwmoGraph.gpo GD.gdG w (i, k) →
      w ∈ H.map Prod.fst) ∧
  WeakRvwmoGraph.gpo GD.gdG eSd (i, k)

theorem ldspFlowOwned (γ : GName)
    (Hob_eq : ∀ (GD : Gdexec) (σ : AxirisG.obSt GF) (s : GSet Geid),
      AxirisG.obStInterp GD σ s ⊣⊢ protInv γ GD s)
    (Hann_eq : ∀ m : Mea GF, AxirisG.annotInterp m ⊣⊢ AxAnnot.annotInterp m)
    (i : Agent) (k : Nat) (eSd : Geid) (Rsd : IProp GF) (a : Int) (Hs : List (List Hent))
    (Vs : List (BitVec 8)) (Hlen8 : Vs.length = 8) (Hlens : Hs.length = 8)
    (HlastSpill : ∀ (j : Nat) (H : List Hent), Hs[j]? = some H →
      ∃ v, H.getLast? = some (eSd, v) ∧ Vs[j]? = some v)
    (Hok : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜ldspOwnOk GD i k eSd a Hs⌝)
    (Htok : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢
        Rsd -∗ tokn γ GD a Hs ({[eSd := (1 : Qp)]} : GMapF Geid Qp))
    (Hloc : ∀ GD ls, rvwmoCatConsistent GD →
      AxirisG.localInterp (GF := GF) GD i k ls ⊢ |==> ∃ ls', AxirisG.localInterp GD i (k + 1) ls') :
    AxAnnot.annotOwn eSd Rsd ⊢
      ∀ (GD : Gdexec) (ls : AxirisG.logTsT GF) (v : List (BitVec 8)),
        ⌜rvwmoCatConsistent GD⌝ -∗ □ AxirisG.gconstInterp GD -∗ AxirisG.localInterp GD i k ls -∗
        ⌜graphValue GD (i, k) = some v⌝ -∗ loadFlow GD i k iprop(⌜v = Vs⌝) := by
  iintro Hfrag %GD %ls %v %Hc #Hg Hloc %Hgv
  ihave %Hok' := (Hok GD Hc) $$ Hg
  obtain ⟨Hlob, Hbef, Hrgmo, Hnw, Hpref, ⟨aq, ts0, vs0, Hlbl, Hts, Hvs⟩, Hwr, Hch, Hown, Hpo⟩ :=
    Hok'
  ihave Htok := (Htok GD Hc) $$ Hg
  unfold loadFlow naAtProgress
  iintro %na ⟨%Hprog, Hannot⟩
  ihave Hloc := (Hloc GD ls Hc) $$ Hloc
  imod Hloc with ⟨%ls', Hloc⟩
  have Hsd2 : eSd.2 < k := ((elemOfEidsBefore GD i k eSd).1 Hbef).2.1
  have Hin : eSd ∈ (FiniteMap.dom_set na : GSet Geid) := by
    rw [← Hprog] at Hbef
    exact (elemOfFilter.1 Hbef).2
  obtain ⟨P', HP'⟩ := Option.isSome_iff_exists.1 (elemOfDom.1 Hin)
  ihave Hannot := (Hann_eq na).1 $$ Hannot
  have Hdet : ⊢ AxAnnot.annotInterp na -∗ AxAnnot.annotOwn eSd Rsd ==∗
      ∃ R, AxAnnot.annotInterp (insert na eSd R) ∗ iprop(▷ □ (P' -∗ Rsd ∗ R)) := by
    have h := annotDetach na eSd Rsd
    rw [HP'] at h
    exact h
  imod Hdet $$ Hannot Hfrag with ⟨%R, Hannot', Hwand⟩
  have Hnin : (i, k) ∉ (FiniteMap.dom_set (insert na eSd R) : GSet Geid) := by
    rw [domInsert, elemOfUnion, elemOfSingleton]
    rintro (Heq | Hik)
    · rw [← Heq] at Hsd2
      exact Nat.lt_irrefl _ Hsd2
    · have Hf : (i, k) ∈ FiniteSet.filter (fun e : Geid => decide (e.1 = i))
          (FiniteMap.dom_set na : GSet Geid) := elemOfFilter.2 ⟨by simp, Hik⟩
      rw [Hprog, elemOfEidsBefore] at Hf
      exact Nat.lt_irrefl _ Hf.2.1
  imod (annotAlloc (insert na eSd R) (i, k) iprop(⌜v = Vs⌝) Hnin) $$ Hannot' with ⟨Hannot'', -⟩
  imodintro
  inext
  imodintro
  iexists {[eSd := Rsd]}, {[eSd := R]}, ls'
  isplitl [Hwand]
  · unfold naSplittingWf
    isplitr
    · ipureintro
      rw [domSingleton]
      exact singletonSubseteqL.2 Hlob
    · iapply (BigSepM2.bigSepM2_singleton _ eSd Rsd R).2
      simp only [HP', AxWp.fromOption]
      inext
      iexact Hwand
  isplitl [Htok]
  · unfold flowEqDyn
    iintro %σ %sOb %Hsub %Hnin' Hob Hin
    ihave Hin := (BigSepM.bigSepM_singleton (M := GMapF Geid)).1 $$ Hin
    ihave Htoks := Htok $$ Hin
    ihave Hob := (Hob_eq GD σ sOb).1 $$ Hob
    icases Hob with #Hob
    ihave Hcovall : ∀ (j : Nat) (w : Geid) (v' : BitVec 8),
        ⌜gwritesByte GD.gdG w (a + (j : Int)) v'⌝ -∗ ⌜gmoLt GD.gdG w (i, k)⌝ -∗
        ∃ H' : List Hent, ⌜w ∈ H'.map Prod.fst⌝ ∗ histSnap (GF := GF) γ (a + (j : Int)) H' $$ []
    · iintro %j %w %v' %hwb %hmo
      ihave Hspec := protInvPrefixCovMem γ GD sOb (i, k) (a + (j : Int)) Hc.1 Hrgmo
        (subseteqTrans Hpref Hsub) $$ Hob
      ihave Hs2 := Hspec $$ %w %v' %hwb %hmo
      iexact Hs2
    have Hcase := epiHcaseDerived GD Hc (i, k) eSd a Vs Hs Hwr Hch Hown HlastSpill Hpo
    ihave %Hgv' := epiReloadValueOwn γ GD Hc eSd (i, k) a Vs Hlen8 Hs Hlens _ HlastSpill
      aq ts0 vs0 Hlbl Hts Hvs Hwr Hch Hown Hcase $$ Hcovall Htoks
    iapply fupd_mask_intro LawfulSet.empty_subset
    iintro Hclose
    inext
    imod Hclose
    imodintro
    iexists σ
    isplitl []
    · iapply (Hob_eq GD σ (({(i, k)} : GSet Geid) ∪ sOb)).2
      iapply protInvReadStep γ GD sOb (i, k) Hnin' Hnw
      iexact Hob
    · ipureintro
      rw [Hgv] at Hgv'
      exact Option.some.inj Hgv'
  isplitl [Hannot'']
  · iapply (Hann_eq _).2
    rw [← AxLdspWpd.annotEq]
    iexact Hannot''
  · iexact Hloc

/-- §1 ∘ §2: the reload node's `wpd` at the real protocol, from the spill's annotation fragment
and a ∀-value continuation. -/
theorem wpdLdspOwned (γ : GName)
    (Hob_eq : ∀ (GD : Gdexec) (σ : AxirisG.obSt GF) (s : GSet Geid),
      AxirisG.obStInterp GD σ s ⊣⊢ protInv γ GD s)
    (Hann_eq : ∀ m : Mea GF, AxirisG.annotInterp m ⊣⊢ AxAnnot.annotInterp m)
    (Φ : Athread → IProp GF) (i : Agent) (cpu : CPU) (va : Nat)
    (req : Mem_read_request 8 va Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (BitVec (8 * 8) × Option Bool) Arch.abort → SailM Unit) (ib : Ibch) (k : Nat)
    (rs0 : RegFile) (eSd : Geid) (Rsd : IProp GF) (Hs : List (List Hent)) (Vs : List (BitVec 8))
    (Hdev : devAddr req.pa = false) (Hlat : (classify req.access_kind).akLatest = false)
    (Hnf : (classify req.access_kind).akIfetch = false)
    (Hrow : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜loadRowOk GD i k⌝)
    (Hlen8 : Vs.length = 8) (Hlens : Hs.length = 8)
    (HlastSpill : ∀ (j : Nat) (H : List Hent), Hs[j]? = some H →
      ∃ v, H.getLast? = some (eSd, v) ∧ Vs[j]? = some v)
    (Hok : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜ldspOwnOk GD i k eSd (paZ req.pa) Hs⌝)
    (Htok : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢
        Rsd -∗ tokn γ GD (paZ req.pa) Hs ({[eSd := (1 : Qp)]} : GMapF Geid Qp))
    (Hloc : ∀ GD ls, rvwmoCatConsistent GD →
      AxirisG.localInterp (GF := GF) GD i k ls ⊢ |==> ∃ ls', AxirisG.localInterp GD i (k + 1) ls') :
    ⊢ AxAnnot.annotOwn eSd Rsd -∗
      (∀ (v : List (BitVec 8)) (rs' : RegFile), ⌜v.length = 8⌝ -∗
         ⌜regsAgree AxRunClose.pinReg rs0 rs'⌝ -∗
         wpd .MaybeStuck i ⟨.PHart cpu (KK (.Ok (wordOfBytes 8 v, none))) rs' none ib, k + 1⟩ Φ) -∗
      wpd .MaybeStuck i ⟨.PHart cpu (.impure (.ok (.memRead 8 va req)) KK) rs0 none ib, k⟩ Φ := by
  iintro Hfrag C
  iapply (wpdLoadStep Φ i cpu 8 va req KK ib k rs0 (fun _ v => iprop(⌜v = Vs⌝)) Hdev Hlat
    (by omega) Hnf Hrow) $$ %rs0 %(regsAgreeRefl _ rs0) [Hfrag] C
  iapply (ldspFlowOwned γ Hob_eq Hann_eq i k eSd Rsd _ Hs Vs Hlen8 Hlens HlastSpill Hok Htok Hloc)
  iexact Hfrag

end ldspOwn

/-! # 2b. GENERIC COMPOSITION: fetch, admin run, the load, admin run, `.pure ()` -/

section compose
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [axG : AxirisG GF] [Axpol]

/-- A closed `gstep` run from `s0` to `q`, entered at any `s' ≈ s0`. -/
theorem wpdRunTo (Φ : Athread → IProp GF) (i : Agent) (s0 q : Athread) (Hrun : rtc gstep s0 q) :
    ⊢ ∀ s', ⌜aeqv s' s0⌝ -∗
      ((∀ s2, ⌜Qat q s2⌝ -∗ wpd .MaybeStuck i s2 Φ) ∧
       (∀ (GD : Gdexec) s1, ⌜Pbefore q s1⌝ -∗ ⌜s1.atK = (AxOpsem.grow GD i).length⌝ -∗
          postLifting Φ i s1)) -∗
      wpd .MaybeStuck i s' Φ := by
  iintro %s' %Heq R
  iapply (AxCjrWpd.wpdOfRunFrom i q s0 s' Φ Hrun Heq) $$ R

/-- The load node entered at any `s2 ≈` it, then the post-load segment given as a ∀-value
`epure` certificate. -/
theorem wpdLoadThenRet (Φ : Athread → IProp GF) (i : Agent) (cpu : CPU) (va : Nat)
    (req : Mem_read_request 8 va Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (BitVec (8 * 8) × Option Bool) Arch.abort → SailM Unit) (ib : Ibch) (k : Nat)
    (sLd : ExecSt) (D : List Register) (Rv : Gdexec → List (BitVec 8) → IProp GF)
    (Hdev : devAddr req.pa = false) (Hlat : (classify req.access_kind).akLatest = false)
    (Hnf : (classify req.access_kind).akIfetch = false)
    (Hrow : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜loadRowOk GD i k⌝)
    (Hseip : Register.sig_seip ∉ D) (Hmeip : Register.sig_meip ∉ D)
    (Hpost : ∀ v : List (BitVec 8), v.length = 8 → ∃ sEnd : ExecSt,
      epure D (KK (.Ok (wordOfBytes 8 v, none))) sLd = some ((), sEnd)) :
    ⊢ ∀ s2, ⌜Qat ⟨.PHart cpu (.impure (.ok (.memRead 8 va req)) KK) sLd.regs none ib, k⟩ s2⌝ -∗
      (∀ (GD : Gdexec) (ls : AxirisG.logTsT GF) (v : List (BitVec 8)),
         ⌜rvwmoCatConsistent GD⌝ -∗ □ AxirisG.gconstInterp GD -∗ AxirisG.localInterp GD i k ls -∗
         ⌜graphValue GD (i, k) = some v⌝ -∗ loadFlow GD i k (Rv GD v)) -∗
      ((∀ (v : List (BitVec 8)) (sEnd : ExecSt) (ib' : Ibch) (s' : Athread),
          ⌜epure D (KK (.Ok (wordOfBytes 8 v, none))) sLd = some ((), sEnd)⌝ -∗
          ⌜Qat ⟨.PHart cpu (.pure ()) sEnd.regs none ib', k + 1⟩ s'⌝ -∗
          wpd .MaybeStuck i s' Φ) ∧
       (∀ (v : List (BitVec 8)) (sEnd : ExecSt) (ib' : Ibch) (GD : Gdexec) (s1 : Athread),
          ⌜epure D (KK (.Ok (wordOfBytes 8 v, none))) sLd = some ((), sEnd)⌝ -∗
          ⌜Pbefore ⟨.PHart cpu (.pure ()) sEnd.regs none ib', k + 1⟩ s1⌝ -∗
          ⌜s1.atK = (AxOpsem.grow GD i).length⌝ -∗ postLifting Φ i s1)) -∗
      wpd .MaybeStuck i s2 Φ := by
  iintro %s2 %Hq F R
  obtain ⟨p2, k2⟩ := s2
  obtain ⟨hk, hp⟩ := Hq
  simp only at hk hp
  subst k2
  match p2, hp with
  | .PHart c2 m2 rs2 fn2 ib2, hp =>
    obtain ⟨hc, hm, hf, hi, hag⟩ := hp
    subst c2 m2 fn2 ib2
    iapply (wpdLoadStep Φ i cpu 8 va req KK ib k sLd.regs Rv Hdev Hlat (by omega) Hnf Hrow) $$
      %rs2 %(regsAgreeSym _ _ _ hag) F
    iintro %v %rs' %Hlv %hag'
    obtain ⟨sEnd, Hep⟩ := Hpost v Hlv
    obtain ⟨ib', Hrun⟩ := epureGstepRtc D Hseip Hmeip _ _ _ _ Hep cpu ib (k + 1)
    iapply (wpdRunTo Φ i _ _ Hrun) $$
      %⟨.PHart cpu (KK (.Ok (wordOfBytes 8 v, none))) rs' none ib, k + 1⟩
      %⟨rfl, rfl, rfl, rfl, rfl, regsAgreeSym _ _ _ hag'⟩
    isplit
    · icases R with ⟨R, -⟩
      iintro %s3 %Hq3
      iapply R $$ %v %sEnd %ib' %s3 %Hep %Hq3
    · icases R with ⟨-, R⟩
      iintro %GD %s1 %Hb %Hend
      iapply R $$ %v %sEnd %ib' %GD %s1 %Hep %Hb %Hend

/-- c.ldsp from its FETCH node: the pinned 2-byte fetch (at `k`) → the pre-load admin run
`HrunPre` → the data load (row item `k`) → the ∀-value post-load `epure` certificate `Hpost` →
`.pure ()` (at `k + 1`). -/
theorem wpdCldspFromFetch (Φ : Athread → IProp GF) (i : Agent) (cpu : CPU) (vaf : Nat)
    (reqf : Mem_read_request 2 vaf Arch.pa Arch.translation Arch.arch_ak)
    (KKf : Result (BitVec (8 * 2) × Option Bool) Arch.abort → SailM Unit) (ib : Ibch) (k : Nat)
    (h : BitVec 16) (s2 : ExecSt) (va : Nat)
    (req : Mem_read_request 8 va Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (BitVec (8 * 8) × Option Bool) Arch.abort → SailM Unit) (ibLd : Ibch)
    (sLd : ExecSt) (D : List Register) (Rv : Gdexec → List (BitVec 8) → IProp GF)
    -- the fetch
    (Hdevf : devAddr reqf.pa = false) (Hfef : (classify reqf.access_kind).akIfetch = true)
    (Hgd : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢
        ⌜AxCjrWpd.fetchImgOk GD i k (paZ reqf.pa) (WeakInterpProj.wbytes 2 h)⌝)
    -- the pre-load admin segment
    (HrunPre : rtc gstep
      ⟨.PHart cpu (KKf (.Ok (wordOfBytes 2 (WeakInterpProj.wbytes 2 h), none))) s2.regs none ib, k⟩
      ⟨.PHart cpu (.impure (.ok (.memRead 8 va req)) KK) sLd.regs none ibLd, k⟩)
    -- the load
    (Hdev : devAddr req.pa = false) (Hlat : (classify req.access_kind).akLatest = false)
    (Hnf : (classify req.access_kind).akIfetch = false)
    (Hrow : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜loadRowOk GD i k⌝)
    -- the post-load certificate
    (Hseip : Register.sig_seip ∉ D) (Hmeip : Register.sig_meip ∉ D)
    (Hpost : ∀ v : List (BitVec 8), v.length = 8 → ∃ sEnd : ExecSt,
      epure D (KK (.Ok (wordOfBytes 8 v, none))) sLd = some ((), sEnd)) :
    ⊢ (∀ (GD : Gdexec) (ls : AxirisG.logTsT GF) (v : List (BitVec 8)),
         ⌜rvwmoCatConsistent GD⌝ -∗ □ AxirisG.gconstInterp GD -∗ AxirisG.localInterp GD i k ls -∗
         ⌜graphValue GD (i, k) = some v⌝ -∗ loadFlow GD i k (Rv GD v)) -∗
      (((∀ (v : List (BitVec 8)) (sEnd : ExecSt) (ib' : Ibch) (s' : Athread),
           ⌜epure D (KK (.Ok (wordOfBytes 8 v, none))) sLd = some ((), sEnd)⌝ -∗
           ⌜Qat ⟨.PHart cpu (.pure ()) sEnd.regs none ib', k + 1⟩ s'⌝ -∗
           wpd .MaybeStuck i s' Φ) ∧
        (∀ (v : List (BitVec 8)) (sEnd : ExecSt) (ib' : Ibch) (GD : Gdexec) (s1 : Athread),
           ⌜epure D (KK (.Ok (wordOfBytes 8 v, none))) sLd = some ((), sEnd)⌝ -∗
           ⌜Pbefore ⟨.PHart cpu (.pure ()) sEnd.regs none ib', k + 1⟩ s1⌝ -∗
           ⌜s1.atK = (AxOpsem.grow GD i).length⌝ -∗ postLifting Φ i s1)) ∧
       (∀ (GD : Gdexec) (s1 : Athread),
          ⌜Pbefore ⟨.PHart cpu (.impure (.ok (.memRead 8 va req)) KK) sLd.regs none ibLd, k⟩ s1⌝ -∗
          ⌜s1.atK = (AxOpsem.grow GD i).length⌝ -∗ postLifting Φ i s1)) -∗
      wpd .MaybeStuck i ⟨.PHart cpu (.impure (.ok (.memRead 2 vaf reqf)) KKf) s2.regs none ib, k⟩
        Φ := by
  iintro F R
  iapply (wpdFetchStep Φ i cpu 2 vaf reqf KKf ib k (WeakInterpProj.wbytes 2 h) s2.regs Hdevf Hfef
    (wbytesLength 2 h) Hgd) $$ %s2.regs %(regsAgreeRefl _ s2.regs)
  iintro %rs' %hag
  iapply (wpdRunTo Φ i _ _ HrunPre) $$
    %⟨.PHart cpu (KKf (.Ok (wordOfBytes 2 (WeakInterpProj.wbytes 2 h), none))) rs' none ib, k⟩
    %⟨rfl, rfl, rfl, rfl, rfl, regsAgreeSym _ _ _ hag⟩
  isplit
  · icases R with ⟨R, -⟩
    iintro %s3 %Hq3
    iapply (wpdLoadThenRet Φ i cpu va req KK ibLd k sLd D Rv Hdev Hlat Hnf Hrow Hseip Hmeip
      Hpost) $$ %s3 %Hq3 F R
  · icases R with ⟨-, R⟩
    iexact R

end compose

/-! # 3. SATISFIABILITY AT THE ADEQUACY INSTANCE `axGA2` -/

section ga2
variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF] [AxannotGS GF]
  [AxlogG GF Hent] [Axpol]

/-- Rocq `Local Instance ldsp_ga2`: `axGA2` at the graph `GD0` with `obStInterp := protInv γ`. -/
@[reducible] def ldspGa2 (GD0 : Gdexec) (γ : GName) : AxirisG GF :=
  axGA2 GD0 Unit Unit (fun _ GD _ s => protInv γ GD s) ()

theorem wpdLdspOwnedGa2 (GD0 : Gdexec) (γ : GName) (Φ : Athread → IProp GF) (i : Agent)
    (cpu : CPU) (va : Nat) (req : Mem_read_request 8 va Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (BitVec (8 * 8) × Option Bool) Arch.abort → SailM Unit) (ib : Ibch) (k : Nat)
    (rs0 : RegFile) (eSd : Geid) (Hs : List (List Hent)) (Vs : List (BitVec 8))
    (Hdev : devAddr req.pa = false) (Hlat : (classify req.access_kind).akLatest = false)
    (Hnf : (classify req.access_kind).akIfetch = false)
    (Hrow0 : loadRowOk GD0 i k)
    (Hlen8 : Vs.length = 8) (Hlens : Hs.length = 8)
    (HlastSpill : ∀ (j : Nat) (H : List Hent), Hs[j]? = some H →
      ∃ v, H.getLast? = some (eSd, v) ∧ Vs[j]? = some v)
    (Hok0 : ldspOwnOk GD0 i k eSd (paZ req.pa) Hs) :
    ⊢ AxAnnot.annotOwn eSd
        iprop(tokn γ GD0 (paZ req.pa) Hs ({[eSd := (1 : Qp)]} : GMapF Geid Qp) ∗
          [∗list] j ↦ H' ∈ Hs, histSnap (GF := GF) γ (paZ req.pa + (j : Int)) H') -∗
      (∀ (v : List (BitVec 8)) (rs' : RegFile), ⌜v.length = 8⌝ -∗
         ⌜regsAgree AxRunClose.pinReg rs0 rs'⌝ -∗
         @wpd hlc GF _ (ldspGa2 (GF := GF) GD0 γ) _ .MaybeStuck i
           ⟨.PHart cpu (KK (.Ok (wordOfBytes 8 v, none))) rs' none ib, k + 1⟩ Φ) -∗
      @wpd hlc GF _ (ldspGa2 (GF := GF) GD0 γ) _ .MaybeStuck i
        ⟨.PHart cpu (.impure (.ok (.memRead 8 va req)) KK) rs0 none ib, k⟩ Φ := by
  have Hob : ∀ (GD : Gdexec) (σ : Unit) (s : GSet Geid),
      AxirisG.obStInterp (self := ldspGa2 (GF := GF) GD0 γ) GD σ s ⊣⊢ protInv (GF := GF) γ GD s :=
    fun _ _ _ => .rfl
  have Han : ∀ m : Mea GF,
      AxirisG.annotInterp (self := ldspGa2 (GF := GF) GD0 γ) m ⊣⊢ AxAnnot.annotInterp m :=
    fun _ => .rfl
  have Hrow : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (self := ldspGa2 (GF := GF) GD0 γ) GD ⊢ ⌜loadRowOk GD i k⌝ := by
    intro GD _
    show iprop(⌜GD = GD0⌝) ⊢ _
    iintro %Heq
    subst Heq
    ipureintro
    exact Hrow0
  have Hok : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (self := ldspGa2 (GF := GF) GD0 γ) GD ⊢ ⌜ldspOwnOk GD i k eSd (paZ req.pa) Hs⌝ := by
    intro GD _
    show iprop(⌜GD = GD0⌝) ⊢ _
    iintro %Heq
    subst Heq
    ipureintro
    exact Hok0
  have Htok : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (self := ldspGa2 (GF := GF) GD0 γ) GD ⊢
        iprop(tokn (GF := GF) γ GD0 (paZ req.pa) Hs ({[eSd := (1 : Qp)]} : GMapF Geid Qp) ∗
          [∗list] j ↦ H' ∈ Hs, histSnap (GF := GF) γ (paZ req.pa + (j : Int)) H') -∗
        tokn γ GD (paZ req.pa) Hs ({[eSd := (1 : Qp)]} : GMapF Geid Qp) := by
    intro GD _
    show iprop(⌜GD = GD0⌝) ⊢ _
    iintro %Heq ⟨Ht, -⟩
    subst Heq
    iexact Ht
  have Hloc : ∀ GD ls, rvwmoCatConsistent GD →
      AxirisG.localInterp (self := ldspGa2 (GF := GF) GD0 γ) GD i k ls ⊢
        |==> ∃ ls', AxirisG.localInterp (self := ldspGa2 (GF := GF) GD0 γ) GD i (k + 1) ls' := by
    intro GD ls _
    show iprop(True) ⊢ iprop(|==> ∃ _ls' : Unit, True)
    iintro _
    imodintro
    iexists ()
    itrivial
  exact @wpdLdspOwned hlc GF _ (ldspGa2 (GF := GF) GD0 γ) _ _ _ γ Hob Han Φ i cpu va req KK ib k rs0 eSd _
    Hs Vs Hdev Hlat Hnf Hrow Hlen8 Hlens HlastSpill Hok Htok Hloc

end ga2

end Weak
