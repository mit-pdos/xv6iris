/-
Weak: **TIER A ADEQUACY (A6): the lock protocol's acquire step made ∀σ-ROBUST** (AxSL tier).
`AxProtLock2.protInvLock''` thickens `AxProtLock.protInvLock'` by three STANDING pieces, and the
acquire / release / x-write flow equations (`lockAcqFlowEq`/`lockRelFlowEq`/`lockXwriteFlowEq`)
discharge `AxWp.flowEqDyn` at a concrete `AxirisG` instance `lock2AxirisG` whose ob-state is
`(D, hm)`.

Rocq: `iris/AxProtLock2.v` @ xxvzwolszwmp.

## The Rocq header, in substance

Design `claude-notes/design/weak-memory-lb-axsl.md` §7.A (A6), §7.T, §7.L.
`AxProtLock.protInvLockRmwStep'` takes `w_rel ∉ D` and `get? hm w_rel = some Hh` as ordinary
hypotheses; `flowEqDyn` quantifies over EVERY reachable ob-state `σ`, so the acquire's flow
equation must DERIVE both.  `protInvLock''` adds:
- `∃ H_L, histAuth γ L 1 H_L` — the lock byte's own continuity resource, held by the invariant
  (the scheduler's bookkeeping, the mutex alternates `L`'s writer), so `flowIn := ∅` suffices
  for the acquire;
- the CLAIMS conjunct: every claimed release `r ∈ D` has an external-rf RMW witness already
  validated — with gatomicity's uniqueness (`lockExtRmwReaderUnique`, via
  `AxLockGraph.catRmwUniqueReader`) this turns `w_rel ∉ D` into a theorem (the unique reader
  would be `acq`, not yet validated);
- the HM conjunct: every validated release has an entry in `hm`, tied (`hhTiedOrEmpty`) and
  carrying the release clause's payload `histXWf` (a byte-`x` history, gmo-chained) and
  `lockHhPoLatest` (its last entry is the po-latest byte-`x` write before the release, or a
  later one exists in between).  The release proves the payload, the acquire hands it on.
`hhTiedOrEmpty` is the empty-history arm (`tieBase` is unsatisfiable at `[]`).  The x-write flow
equation is `AxProt.flowEqOwnedWrite`'s proof through the thicker invariant (`x ≠ L`).

**Fetches.** Nothing here depends on instruction fetches: only `gwritesByte`/`greadsByte`/
`gwriteAt`/`gmoLt`/`gpo` over graph labels (`Lbl` has no fetch constructor), the history and
claimed ghosts, and `flowEqDyn`.

## Deviations from Rocq

1. NAMES: camelCase (map below).  Duplicated Rocq names, file-qualified:
   `AxProtLock2.protInvLock''`, `AxProtLock2.protInvLockUnfold''` (also in AxLockMutex).
   Lean-only helpers, file-qualified: `AxProtLock2.xTokPure` (read `hhTiedOrEmpty` off an
   `xTok` without consuming it — Rocq's `iAssert … as %Htieb`), `AxProtLock2.ΦLock'OpenX` (open
   `ΦLock'` at a release write whose `hm` entry is known, keeping `xTok` folded).
2. VOCABULARY (as `AxProtLock` deviation 2): `last l` ↦ `l.getLast?`; `H.*1` ↦
   `H.map Prod.fst`; `gd_g GD` ↦ `GD.gdG`; `gpo` ↦ `WeakRvwmoGraph.gpo`; `gmap geid (list
   hent)` ↦ `GMapF Geid (List Hent)`; `hm !! w` ↦ `get? hm w`; `<[w := Hh]> hm` ↦
   `insert hm w Hh`; `{[e]} ∪ s` ↦ `({e} : GSet Geid) ∪ s`; `mea Σ` ↦ `Mea GF`;
   `WeakLitmus.b0/b1` ↦ `b0`/`b1`; `bv 8` ↦ `BitVec 8`; `Z` ↦ `Int`.
3. CONTEXTS: `invGS_gen HasNoLc Σ` ↦ `[InvGS_gen hlc GF]` for any `hlc` (as `AxWp` deviation
   6).  Rocq's section variables `(L x : Z)` are explicit leading arguments where used.  Rocq's
   `Proof using All` makes EVERY lemma of the section take `Hxy : x ≠ L` (and `L`/`x`); here
   only `lockXwriteFlowEq` (the one proof that uses it) takes `hxy : x ≠ L`, and
   `lockExtRmwReaderUnique`/`lockAcqFlowEq`/`lockRelFlowEq` take only the section variables
   their statements mention (strictly weaker premises).  The instance section's `(γ γc)` are
   explicit arguments of `lock2AxirisG`/`lock2ObStInterp`/the flow equations.
4. THE INSTANCE: Rocq's `Local Existing Instance lock2_axirisG` ↦ the statements name it
   (`@flowEqDyn hlc GF _ (lock2AxirisG L x γ γc) …`, `AxirisG.obStInterp (self := …)`), as
   `AxWp` deviation 8; `lock2AxirisG` is `@[reducible]`.  `lock2_axpol` (a `Local Instance`,
   used by no statement — `flowEqDyn` takes no `Axpol`) is the plain definition `lock2Axpol`.
5. STATEMENT SHAPES (as `AxProt` deviation 4): `P -∗ flowEqDyn …` ↦ `P ⊢ flowEqDyn …`;
   `⊢ flowEqDyn …` stays; pure premises stay `→`.
6. PROOFS: `chainWithSnocLocal` by list indexing on `getElem?` (Rocq `lookup_app_l/r`).

**Rocq → Lean name map.**  `lock_ext_rmw_reader` `lockExtRmwReader`,
`lock_ext_rmw_reader_unique` `lockExtRmwReaderUnique`, `hist_x_wf` `histXWf`,
`lock_hh_po_latest` `lockHhPoLatest`, `hist_x_wf_nil` `histXWfNil`, `chain_with_snoc_local`
`chainWithSnocLocal`, `hist_x_wf_snoc` `histXWfSnoc`, `hh_tied_or_empty` `hhTiedOrEmpty`,
`prot_inv_lock''` `AxProtLock2.protInvLock''`, `prot_inv_lock_unfold''`
`AxProtLock2.protInvLockUnfold''`, `lock2_axirisG` `lock2AxirisG`, `lock2_axpol` `lock2Axpol`,
`lock2_ob_st_interp` `lock2ObStInterp`, `lock_acq_flow_eq` `lockAcqFlowEq`, `lock_rel_flow_eq`
`lockRelFlowEq`, `lock_xwrite_flow_eq` `lockXwriteFlowEq`.

**Not ported:** the §4 `Print Assumptions` audit (the lint's axiom check covers it).
-/
import Weak.AxProtLock
import Weak.AxLockGraph

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp

/-! # 1. The atomicity-uniqueness corollary, at `L` -/

section pure

variable (L x : Int)

/-- `e` is an RMW that externally reads-from `r` at `L`. -/
def lockExtRmwReader (GD : Gdexec) (r e : Geid) : Prop :=
  (∃ t v, greadsByte GD.gdG e L t v ∧ gwriteAt GD.gdG t = some r) ∧
  r.1 ≠ e.1 ∧ (∃ v, gwritesByte GD.gdG e L v)

theorem lockExtRmwReaderUnique (GD : Gdexec) (r e1 e2 : Geid) :
    rvwmoCatConsistent GD →
    lockExtRmwReader L GD r e1 → lockExtRmwReader L GD r e2 → e1 = e2 := by
  rintro hcons ⟨⟨t1, v1, hrd1, hat1⟩, _, ⟨v1', hwr1⟩⟩ ⟨⟨t2, v2, hrd2, hat2⟩, _, ⟨v2', hwr2⟩⟩
  have hnd := hcons.1.1
  obtain ⟨_, ht1⟩ := gwriteAtInv GD.gdG t1 r hnd hat1
  obtain ⟨_, ht2⟩ := gwriteAtInv GD.gdG t2 r hnd hat2
  have heq : t1 = t2 := ht1.symm.trans ht2
  subst heq
  exact catRmwUniqueReader GD L t1 e1 e2 v1 v2 v1' v2' hcons hrd1 hwr1 hrd2 hwr2

/-! # 1.5 The release clause's payload -/

def histXWf (GD : Gdexec) (Hh : List Hent) : Prop :=
  (∀ p, p ∈ Hh → gwritesByte GD.gdG p.1 x p.2) ∧
  chainWith (gmoLt GD.gdG) (Hh.map Prod.fst)

def lockHhPoLatest (GD : Gdexec) (Hh : List Hent) (w : Geid) : Prop :=
  ∀ w' v, gwritesByte GD.gdG w' x v → WeakRvwmoGraph.gpo GD.gdG w' w →
    Hh.getLast? = some (w', v) ∨
    ∃ w'' v'', gwritesByte GD.gdG w'' x v'' ∧ WeakRvwmoGraph.gpo GD.gdG w' w'' ∧
      WeakRvwmoGraph.gpo GD.gdG w'' w

theorem histXWfNil (GD : Gdexec) : histXWf x GD [] := by
  refine ⟨fun p hp => (by cases hp), ?_⟩
  intro k w1 w2 hk1 _
  simp at hk1

/-- `chainWith` extends across one appended element, given the old last entry is related to
the new one. -/
theorem chainWithSnocLocal (R : Geid → Geid → Prop) (Hl0 : List Geid) (wl : Geid)
    (hch0 : chainWith R Hl0)
    (hlink : ∀ wlast, Hl0.getLast? = some wlast → R wlast wl) :
    chainWith R (Hl0 ++ [wl]) := by
  intro i w1 w2 hi1 hi2
  by_cases hlt : i + 1 < Hl0.length
  · rw [List.getElem?_append_left (by omega)] at hi1
    rw [List.getElem?_append_left hlt] at hi2
    exact hch0 i w1 w2 hi1 hi2
  · have hlen := lookup_lt_Some hi2
    simp only [List.length_append, List.length_singleton] at hlen
    have hi : i + 1 = Hl0.length := by omega
    rw [List.getElem?_append_right (by omega), hi, Nat.sub_self] at hi2
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hi2
    subst hi2
    rw [List.getElem?_append_left (by omega)] at hi1
    apply hlink
    rw [List.getLast?_eq_getElem?, show Hl0.length - 1 = i by omega]
    exact hi1

theorem histXWfSnoc (GD : Gdexec) (Hh : List Hent) (w : Geid) (v : BitVec 8) :
    histXWf x GD Hh → gwritesByte GD.gdG w x v →
    (∀ wlast vlast, Hh.getLast? = some (wlast, vlast) → gmoLt GD.gdG wlast w) →
    histXWf x GD (Hh ++ [(w, v)]) := by
  rintro ⟨hwr, hch⟩ hwb hlink
  refine ⟨?_, ?_⟩
  · intro p hp
    rcases List.mem_append.1 hp with hp | hp
    · exact hwr p hp
    · rw [List.mem_singleton] at hp
      subst hp
      exact hwb
  · rw [List.map_append, List.map_cons, List.map_nil]
    apply chainWithSnocLocal _ _ _ hch
    intro wlast0 hlast
    rw [List.getLast?_map] at hlast
    cases hq : Hh.getLast? with
    | none => rw [hq] at hlast; cases hlast
    | some p =>
      rw [hq] at hlast
      simp only [Option.map_some, Option.some.injEq] at hlast
      obtain ⟨wl, vl⟩ := p
      dsimp only at hlast
      subst hlast
      exact hlink wl vl hq

/-- THE EMPTY-HISTORY ARM: the raw genesis `[]`, or genuinely `tieBase`-tied. -/
def hhTiedOrEmpty (GD : Gdexec) (Hh : List Hent) (w : Geid) : Prop :=
  Hh = [] ∨ tieBase GD.gdG (Hh.map Prod.fst) w

end pure

/-! # 2. `protInvLock''` -/

section lock2

variable {GF : BundledGFunctors} [AxlogG GF Hent] [AxLockG GF] (L x : Int)

def AxProtLock2.protInvLock'' (γ γc : GName) (GD : Gdexec) (s D : GSet Geid)
    (hm : GMapF Geid (List Hent)) : IProp GF :=
  iprop(protInvLock' L x γ γc GD s D hm ∗
    (∃ H_L, histAuth γ L 1 H_L) ∗
    ⌜∀ r, r ∈ D → ∃ e, e ∈ s ∧ lockExtRmwReader L GD r e⌝ ∗
    ⌜∀ w, w ∈ s → gwritesByte GD.gdG w L b0 →
      ∃ Hh, get? hm w = some Hh ∧ hhTiedOrEmpty GD Hh w ∧
        histXWf x GD Hh ∧ lockHhPoLatest x GD Hh w⌝)

theorem AxProtLock2.protInvLockUnfold'' (γ γc : GName) (GD : Gdexec) (s D : GSet Geid)
    (hm : GMapF Geid (List Hent)) :
    AxProtLock2.protInvLock'' (GF := GF) L x γ γc GD s D hm ⊣⊢
      iprop(protInvLock' L x γ γc GD s D hm ∗ (∃ H_L, histAuth γ L 1 H_L) ∗
        ⌜∀ r, r ∈ D → ∃ e, e ∈ s ∧ lockExtRmwReader L GD r e⌝ ∗
        ⌜∀ w, w ∈ s → gwritesByte GD.gdG w L b0 →
          ∃ Hh, get? hm w = some Hh ∧ hhTiedOrEmpty GD Hh w ∧
            histXWf x GD Hh ∧ lockHhPoLatest x GD Hh w⌝) :=
  .rfl

/-- Lean-only: read `hhTiedOrEmpty` off an `xTok`, keeping it. -/
theorem AxProtLock2.xTokPure (GD : Gdexec) (γ : GName) (a : Int) (H : List Hent) (e : Geid) :
    xTok (GF := GF) GD γ a H e ⊢ xTok GD γ a H e ∗ ⌜hhTiedOrEmpty GD H e⌝ := by
  unfold xTok tokTie
  iintro (⟨T, %htie⟩ | ⟨%Heq, Ha⟩)
  · isplitl [T]
    · ileft
      isplitl [T]
      · iexact T
      · ipureintro
        exact htie
    · ipureintro
      right
      exact htie e (by rw [domSingleton, elemOfSingleton])
  · isplitl [Ha]
    · iright
      isplitl []
      · ipureintro
        exact Heq
      · iexact Ha
    · ipureintro
      left
      exact Heq

/-- Lean-only: open `ΦLock'` at a release write whose `hm` entry is `Hh` (`xTok` folded). -/
theorem AxProtLock2.ΦLock'OpenX (γ γc : GName) (GD : Gdexec) (hm : GMapF Geid (List Hent))
    (w : Geid) (Hh : List Hent) :
    get? hm w = some Hh → gwritesByte GD.gdG w L b0 →
    ΦLock' (GF := GF) L x γ γc GD w ((get? hm w).getD []) ⊢
      xTok GD γ x Hh w ∨ AxProtLock.claimed γc w := by
  intro hhm hwb
  rw [hhm, Option.getD_some]
  unfold ΦLock'
  iintro Hl
  iapply Hl
  ipureintro
  exact hwb

/-! # 3. The instance: `obSt` carries exactly `(D, hm)` -/

@[reducible] def lock2AxirisG (γ γc : GName) : AxirisG GF where
  annotInterp := fun _ => iprop(True)
  gconstInterp := fun _ => iprop(True)
  obSt := GSet Geid × GMapF Geid (List Hent)
  obStInterp := fun GD σ s => AxProtLock2.protInvLock'' L x γ γc GD s σ.1 σ.2
  logTsT := Unit
  localInterp := fun _ _ _ _ => iprop(True)

@[reducible] def lock2Axpol : Axpol where
  sPol := fun _ _ => ∅
  lobp := fun _ _ => ∅

theorem lock2ObStInterp (γ γc : GName) (GD : Gdexec) (D : GSet Geid)
    (hm : GMapF Geid (List Hent)) (s : GSet Geid) :
    AxirisG.obStInterp (self := lock2AxirisG (GF := GF) L x γ γc) GD
        ((D, hm) : GSet Geid × GMapF Geid (List Hent)) s ⊣⊢
      AxProtLock2.protInvLock'' L x γ γc GD s D hm :=
  .rfl

section flows

variable {hlc : HasLC} [InvGS_gen hlc GF]

/-! ## 3.1 THE ACQUIRE FLOW EQUATION -/

theorem lockAcqFlowEq (γ γc : GName) (GD : Gdexec) (w_rel acq : Geid)
    (sOb0 : GSet Geid) (flowIn : Mea GF) :
    rvwmoCatConsistent GD →
    gwritesByte GD.gdG w_rel L b0 →
    gwritesByte GD.gdG acq L b1 →
    (∀ a' v', gwritesByte GD.gdG acq a' v' → a' = L) →
    gobCat GD w_rel acq →
    lockExtRmwReader L GD w_rel acq →
    ({w_rel} : GSet Geid) ⊆ sOb0 →
    ⊢ @flowEqDyn hlc GF _ (lock2AxirisG L x γ γc) GD acq sOb0 flowIn
        iprop(∃ Hh, xTok GD γ x Hh acq ∗ ⌜histXWf x GD Hh ∧ lockHhPoLatest x GD Hh w_rel⌝) := by
  intro hcons hwb0 hwb1 hsingle hgob hrfe hsub0
  unfold flowEqDyn
  iintro %σ %sOb %Hsub %Hnin Hob -
  obtain ⟨D, hm⟩ := σ
  icases ((lock2ObStInterp L x γ γc GD D hm sOb).trans
    (AxProtLock2.protInvLockUnfold'' L x γ γc GD sOb D hm)).1 $$ Hob
    with ⟨Hlock', ⟨%H_L, HaL⟩, %Hclaims, %Hhmc⟩
  have hwrelOb : w_rel ∈ sOb := Hsub _ (hsub0 _ (elemOfSingleton.2 rfl))
  have hninD : w_rel ∉ D := by
    intro hinD
    obtain ⟨e, hein, hre⟩ := Hclaims w_rel hinD
    have heq : e = acq := lockExtRmwReaderUnique L GD w_rel e acq hcons hre hrfe
    subst heq
    exact Hnin hein
  obtain ⟨Hh, hhmeq, _, hxwf, hpl⟩ := Hhmc w_rel hwrelOb hwb0
  icases (protInvLockUnfold' L x γ γc GD sOb D hm).1 $$ Hlock' with ⟨Hc, Hpo, Hlocks⟩
  icases (BigSepS.bigSepS_delete
    (Φ := fun e => ΦLock' L x γ γc GD e ((get? hm e).getD [])) hwrelOb).1 $$ Hlocks
    with ⟨Hw, Hrest⟩
  icases AxProtLock2.ΦLock'OpenX L x γ γc GD hm w_rel Hh hhmeq hwb0 $$ Hw with (Htie | Hcl)
  · imod protInvWriteStep γ GD sOb acq L b1 H_L Hnin hwb1 hsingle $$ [$Hpo $HaL]
      with ⟨Hpo', HLtie⟩
    imod claimedAlloc γc D w_rel hninD $$ Hc with ⟨Hc', Hcl⟩
    ihave Htie' := xTokRetieOb GD γ x Hh w_rel acq hcons hgob $$ Htie
    ihave HLtok := tokTieTok GD γ L _ _ $$ HLtie
    ihave HLtok := (tokSingleton γ L _ acq 1).1 $$ HLtok
    iapply fupd_mask_intro LawfulSet.empty_subset
    iintro Hclose
    inext
    imod Hclose
    imodintro
    iexists ((({w_rel} : GSet Geid) ∪ D, hm) : GSet Geid × GMapF Geid (List Hent))
    isplitl [Hc' Hpo' Hcl Hrest HLtok]
    · iapply ((lock2ObStInterp L x γ γc GD (({w_rel} : GSet Geid) ∪ D) hm
        (({acq} : GSet Geid) ∪ sOb)).trans
        (AxProtLock2.protInvLockUnfold'' L x γ γc GD (({acq} : GSet Geid) ∪ sOb)
          (({w_rel} : GSet Geid) ∪ D) hm)).2
      isplitl [Hc' Hpo' Hcl Hrest]
      · iapply (protInvLockUnfold' L x γ γc GD (({acq} : GSet Geid) ∪ sOb)
          (({w_rel} : GSet Geid) ∪ D) hm).2
        isplitl [Hc']
        · iexact Hc'
        isplitl [Hpo']
        · iexact Hpo'
        iapply (AxProtLock.bigSepSUnionSingleton
          (Φ := fun e => ΦLock' L x γ γc GD e ((get? hm e).getD [])) Hnin).2
        isplitl []
        · iapply AxProtLock.ΦLock'Vacuous L x γ γc GD acq _
            (fun hbad => b0NeB1 (gwritesByteDet _ _ _ _ _ hbad hwb1))
        · iapply (BigSepS.bigSepS_delete
            (Φ := fun e => ΦLock' L x γ γc GD e ((get? hm e).getD [])) hwrelOb).2
          isplitl [Hcl]
          · iapply AxProtLock.ΦLock'Right L x γ γc GD w_rel _
            iexact Hcl
          · iexact Hrest
      · isplitl [HLtok]
        · iexists _
          iexact HLtok
        · isplitl []
          · ipureintro
            intro r hr
            rcases elemOfUnion.1 hr with hr | hr
            · rw [elemOfSingleton.1 hr]
              exact ⟨acq, elemOfUnionL (elemOfSingleton.2 rfl), hrfe⟩
            · obtain ⟨e, he, hre⟩ := Hclaims r hr
              exact ⟨e, elemOfUnionR he, hre⟩
          · ipureintro
            intro w hw hwb0'
            rcases elemOfUnion.1 hw with hw | hw
            · rw [elemOfSingleton.1 hw] at hwb0'
              exact (b0NeB1 (gwritesByteDet _ _ _ _ _ hwb0' hwb1)).elim
            · exact Hhmc w hw hwb0'
    · iexists Hh
      isplitl [Htie']
      · iexact Htie'
      · ipureintro
        exact ⟨hxwf, hpl⟩
  · ihave %hinD := claimedDom γc D w_rel $$ [$Hc $Hcl]
    exact (hninD hinD).elim

/-! ## 3.2 THE RELEASE FLOW EQUATION -/

theorem lockRelFlowEq (γ γc : GName) (GD : Gdexec) (w_rel e_last : Geid) (Hh : List Hent)
    (sOb0 : GSet Geid) (flowIn : Mea GF) :
    rvwmoCatConsistent GD →
    gwritesByte GD.gdG w_rel L b0 →
    (∀ a' v', gwritesByte GD.gdG w_rel a' v' → a' = L) →
    gobCat GD e_last w_rel →
    iprop(([∗map] Rin ∈ flowIn, Rin) -∗
      xTok GD γ x Hh e_last ∗ ⌜histXWf x GD Hh ∧ lockHhPoLatest x GD Hh w_rel⌝) ⊢
    @flowEqDyn hlc GF _ (lock2AxirisG L x γ γc) GD w_rel sOb0 flowIn iprop(True) := by
  intro hcons hwb hsingle hgob
  unfold flowEqDyn
  iintro Hflowin %σ %sOb %Hsub %Hnin Hob Hflow
  obtain ⟨D, hm⟩ := σ
  icases ((lock2ObStInterp L x γ γc GD D hm sOb).trans
    (AxProtLock2.protInvLockUnfold'' L x γ γc GD sOb D hm)).1 $$ Hob
    with ⟨Hlock', ⟨%H_L, HaL⟩, %Hclaims, %Hhmc⟩
  icases Hflowin $$ Hflow with ⟨Htie, %Hpayload⟩
  obtain ⟨hxwf, hpl⟩ := Hpayload
  icases (protInvLockUnfold' L x γ γc GD sOb D hm).1 $$ Hlock' with ⟨Hc, Hpo, Hlocks⟩
  imod protInvWriteStep γ GD sOb w_rel L b0 H_L Hnin hwb hsingle $$ [$Hpo $HaL]
    with ⟨Hpo', HLtie⟩
  ihave HLtok := tokTieTok GD γ L _ _ $$ HLtie
  ihave HLtok := (tokSingleton γ L _ w_rel 1).1 $$ HLtok
  ihave Htie' := xTokRetieOb GD γ x Hh e_last w_rel hcons hgob $$ Htie
  icases AxProtLock2.xTokPure GD γ x Hh w_rel $$ Htie' with ⟨Htie', %Htieb⟩
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  inext
  imod Hclose
  imodintro
  iexists ((D, insert hm w_rel Hh) : GSet Geid × GMapF Geid (List Hent))
  isplitl [Hc Hpo' Hlocks Htie' HLtok]
  · iapply ((lock2ObStInterp L x γ γc GD D (insert hm w_rel Hh)
      (({w_rel} : GSet Geid) ∪ sOb)).trans
      (AxProtLock2.protInvLockUnfold'' L x γ γc GD (({w_rel} : GSet Geid) ∪ sOb) D
        (insert hm w_rel Hh))).2
    isplitl [Hc Hpo' Hlocks Htie']
    · iapply (protInvLockUnfold' L x γ γc GD (({w_rel} : GSet Geid) ∪ sOb) D
        (insert hm w_rel Hh)).2
      isplitl [Hc]
      · iexact Hc
      isplitl [Hpo']
      · iexact Hpo'
      iapply (AxProtLock.bigSepSUnionSingleton
        (Φ := fun e => ΦLock' L x γ γc GD e ((get? (insert hm w_rel Hh) e).getD [])) Hnin).2
      isplitl [Htie']
      · rw [lookupInsert, Option.getD_some]
        iapply AxProtLock.ΦLock'Left L x γ γc GD w_rel Hh
        iexact Htie'
      · iapply (bigSepSLockInsertNe L x γ γc GD sOb hm w_rel Hh Hnin).1
        iexact Hlocks
    · isplitl [HLtok]
      · iexists _
        iexact HLtok
      · isplitl []
        · ipureintro
          intro r hr
          obtain ⟨e, he, hre⟩ := Hclaims r hr
          exact ⟨e, elemOfUnionR he, hre⟩
        · ipureintro
          intro w hw hwb0'
          rcases elemOfUnion.1 hw with hw | hw
          · rw [elemOfSingleton.1 hw]
            exact ⟨Hh, lookupInsert, Htieb, hxwf, hpl⟩
          · have hne : w_rel ≠ w := fun h => Hnin (h ▸ hw)
            obtain ⟨Hh0, hh0eq, hh0b⟩ := Hhmc w hw hwb0'
            exact ⟨Hh0, by rw [lookupInsertNe hne]; exact hh0eq, hh0b⟩
  · itrivial

/-! ## 3.3 THE `x`-WRITE FLOW EQUATION -/

theorem lockXwriteFlowEq (hxy : x ≠ L) (γ γc : GName) (GD : Gdexec) (w : Geid) (v : BitVec 8)
    (Hl : List Hent) (sOb0 : GSet Geid) (flowIn : Mea GF) (data : List (BitVec 8)) :
    gwritesByte GD.gdG w x v →
    (∀ a' v', gwritesByte GD.gdG w a' v' → a' = x) →
    graphData GD w = some data →
    iprop(([∗map] Rin ∈ flowIn, Rin) -∗ histAuth γ x 1 Hl) ⊢
    @flowEqDyn hlc GF _ (lock2AxirisG L x γ γc) GD w sOb0 flowIn
      iprop(⌜graphData GD w = some data⌝) := by
  intro hwb hsingle hgd
  unfold flowEqDyn
  iintro Hflowin %σ %sOb %Hsub %Hnin Hob Hflow
  obtain ⟨D, hm⟩ := σ
  icases ((lock2ObStInterp L x γ γc GD D hm sOb).trans
    (AxProtLock2.protInvLockUnfold'' L x γ γc GD sOb D hm)).1 $$ Hob
    with ⟨Hlock', HHL, %Hclaims, %Hhmc⟩
  ihave Hauth := Hflowin $$ Hflow
  icases (protInvLockUnfold' L x γ γc GD sOb D hm).1 $$ Hlock' with ⟨Hc, Hpo, Hlocks⟩
  imod protInvWriteStepAuth γ GD sOb w x v Hl Hnin hwb hsingle $$ [$Hpo $Hauth]
    with ⟨Hpo', -⟩
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  inext
  imod Hclose
  imodintro
  iexists ((D, hm) : GSet Geid × GMapF Geid (List Hent))
  isplitl [Hc Hpo' Hlocks HHL]
  · iapply ((lock2ObStInterp L x γ γc GD D hm (({w} : GSet Geid) ∪ sOb)).trans
      (AxProtLock2.protInvLockUnfold'' L x γ γc GD (({w} : GSet Geid) ∪ sOb) D hm)).2
    isplitl [Hc Hpo' Hlocks]
    · iapply (protInvLockUnfold' L x γ γc GD (({w} : GSet Geid) ∪ sOb) D hm).2
      isplitl [Hc]
      · iexact Hc
      isplitl [Hpo']
      · iexact Hpo'
      iapply (AxProtLock.bigSepSUnionSingleton
        (Φ := fun e => ΦLock' L x γ γc GD e ((get? hm e).getD [])) Hnin).2
      isplitl []
      · iapply AxProtLock.ΦLock'Vacuous L x γ γc GD w _
          (fun hbad => hxy (hsingle L _ hbad).symm)
      · iexact Hlocks
    · isplitl [HHL]
      · iexact HHL
      · isplitl []
        · ipureintro
          intro r hr
          obtain ⟨e, he, hre⟩ := Hclaims r hr
          exact ⟨e, elemOfUnionR he, hre⟩
        · ipureintro
          intro w' hw' hwb0'
          rcases elemOfUnion.1 hw' with hw' | hw'
          · rw [elemOfSingleton.1 hw'] at hwb0'
            exact (hxy (hsingle L _ hwb0').symm).elim
          · exact Hhmc w' hw' hwb0'
  · ipureintro
    exact hgd

end flows

end lock2

end Weak
