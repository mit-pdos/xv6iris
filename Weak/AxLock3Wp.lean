/-
Weak: **A7-T2c §0 TRANSPORT: the `AxProtLock3` flow equations at `axGA2`** (AxSL tier).  The
four flow equations of `AxProtLock3` (proved at its own `lock3AxirisG`) restated at the Tier A
instance `axGA2Lock3 L x GD0 nm` (= `axGA2` at `N := lock3N`, `obSt0 := lock3ObSt0`,
`obStInterp0 := lock3ObStInterp0 L x`), plus the reader's owned `x`-read flow equation
`lock3ReadFlowEq3A`.

Rocq: `iris/AxLock3Wp.v` @ xxvzwolszwmp.

## The Rocq header, in substance

Design `claude-notes/design/weak-memory-lb-axsl.md` §7.A7.  `flowEqDyn` mentions only the ambient
instance's `obSt`/`obStInterp`, so a flow equation proved at one instance is the same fact at any
other instance with the same ob-state and interpretation.  `axGA2Lock3`'s `obStInterp GD (g, D,
hm) s` IS `protInvLock3 L x nm.1 nm.2 GD s D hm g` (`lock3ObStInterpA`).  §0.5: the reader's
plain load `r_x` of `x`, holding the `tokTie` obtained at the acquire `acq` (`gacqPo acq r_x`)
and given `r_x`'s external rf-source `w0` at byte `x`, pins the value read at `vx` (`H`'s last
entry) via `AxLockOwn.lockReadOwn`.  Coverage — every byte-`x` write gmo-before `r_x` is in the
invariant — comes from `protInvPrefixCovMemByte` and a membership in `sPol GD r_x`, discharged by
`AxLockGraph.xWritesGmoBeforeRead` (such a write is `w0` or `gco`-before it) and
`lockPolSIntro`/`lockPolSIntro2`; no global critical-section discipline is assumed.  The read
deposits nothing (`protInvReadStep`).

**Fetches.** Nothing here depends on instruction fetches (graph-label relations and ghosts only).

## Deviations from Rocq

1. NAMES: camelCase (map below); no name of this file is in the duplicated-name table; no
   Lean-only helpers.
2. THE INSTANCE: Rocq's `Local Instance AxGA2_lock3` (over section variables) ↦ the
   `@[reducible] def axGA2Lock3 L x GD0 nm`, named in statements (`@flowEqDyn hlc GF _
   (axGA2Lock3 L x GD0 nm) …`), as `AxTierA2` deviation 3.  Rocq's `T` parameter is gone (O2
   Stage C: no `ax_text`).  `GF : BundledGFunctors.{0,0,0}` (`axGA2`).
3. CONTEXTS (as `AxProtLock3` deviation 3): `invGS_gen HasNoLc Σ` ↦ `[InvGS_gen hlc GF]` for
   any `hlc`; `Proof using All` makes every Rocq lemma take `Hxy`; here only
   `lockXwriteFlowEq3A` (whose proof uses it) takes `hxy : x ≠ L`.
4. STATEMENT SHAPES (as `AxProtLock3` deviation 6): `P -∗ flowEqDyn …` ↦ `P ⊢ flowEqDyn …`;
   `s_pol GD e` (at `lock_axpol`) ↦ `lockPolS GD e` (definitionally `lockAxpol.sPol GD e`);
   `last H` ↦ `H.getLast?`; `H.*1` ↦ `H.map Prod.fst`; `gpo` ↦ `WeakRvwmoGraph.gpo`.
5. PROOF ROUTE (not statements): Rocq's `flow_eq_dyn` is sealed, so its four transports copy
   `AxProtLock3.v`'s scripts; Lean's `flowEqDyn` is a plain definition and both instances'
   `obSt`/`obStInterp` agree definitionally, so each transport is the `AxProtLock3` lemma itself
   (`exact`).  In §0.5 Rocq keeps `protInv` across a persistent `iDestruct … as "#Hsn"`; Lean
   derives the pure read fact by `persistent_entails_left` (`protInv ∗ tokTie ⊢ … ∗ ⌜…⌝`).

**Rocq → Lean name map.**  `AxGA2_lock3` `axGA2Lock3`, `lock3_ob_st_interp_A`
`lock3ObStInterpA`, `lock_acq0_flow_eq3_A` `lockAcq0FlowEq3A`, `lock_acq_flow_eq3_A`
`lockAcqFlowEq3A`, `lock_rel_flow_eq3_A` `lockRelFlowEq3A`, `lock_xwrite_flow_eq3_A`
`lockXwriteFlowEq3A`, `lock3_read_flow_eq3_A` `lock3ReadFlowEq3A`.

**Not ported:** the `Print Assumptions` audit (the lint's axiom check covers it).
-/
import Weak.AxProtLock3
import Weak.AxLockOwn

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp

section lock3Transport

variable {GF : BundledGFunctors.{0,0,0}} [AxlogG GF Hent] [AxLockG GF] (L x : Int)

/-- THE INSTANCE: `axGA2` at `N := lock3N`, `obSt0 := lock3ObSt0`,
`obStInterp0 := lock3ObStInterp0 L x` — `lockHobAlloc`'s own choices. -/
@[reducible] def axGA2Lock3 [AxannotGS GF] (GD0 : Gdexec) (nm : lock3N) : AxirisG GF :=
  axGA2 GD0 lock3N lock3ObSt0 (lock3ObStInterp0 L x) nm

theorem lock3ObStInterpA [AxannotGS GF] (GD0 : Gdexec) (nm : lock3N) (GD : Gdexec) (g : Bool)
    (D : GSet Geid) (hm : GMapF Geid (List Hent)) (s : GSet Geid) :
    AxirisG.obStInterp (self := axGA2Lock3 (GF := GF) L x GD0 nm) GD
        ((g, D, hm) : Bool × GSet Geid × GMapF Geid (List Hent)) s ⊣⊢
      protInvLock3 L x nm.1 nm.2 GD s D hm g :=
  .rfl

variable {hlc : HasLC} [InvGS_gen hlc GF] [AxannotGS GF] (GD0 : Gdexec) (nm : lock3N)

/-! ## 0.1 THE GENESIS ACQUIRE -/

theorem lockAcq0FlowEq3A (GD : Gdexec) (acq : Geid) (flowIn : Mea GF) :
    rvwmoCatConsistent GD →
    GD.gdG.gxImg L = some b0 →
    greadsByte GD.gdG acq L 0 b0 →
    gwritesByte GD.gdG acq L b1 →
    (∀ a' v', gwritesByte GD.gdG acq a' v' → a' = L) →
    ⊢ @flowEqDyn hlc GF _ (axGA2Lock3 L x GD0 nm) GD acq (lockPolS GD acq) flowIn
        iprop(histAuth nm.1 x 1 []) := by
  intro hcons himg hrd0 hwb1 hsingle
  exact lockAcq0FlowEq3 (hlc := hlc) L x nm.1 nm.2 GD acq flowIn hcons himg hrd0 hwb1 hsingle

/-! ## 0.2 THE ORDINARY ACQUIRE -/

theorem lockAcqFlowEq3A (GD : Gdexec) (w_rel acq : Geid) (flowIn : Mea GF) :
    rvwmoCatConsistent GD →
    gwritesByte GD.gdG w_rel L b0 →
    gwritesByte GD.gdG acq L b1 →
    (∀ a' v', gwritesByte GD.gdG acq a' v' → a' = L) →
    gobCat GD w_rel acq →
    lockExtRmwReader L GD w_rel acq →
    ⊢ @flowEqDyn hlc GF _ (axGA2Lock3 L x GD0 nm) GD acq (lockPolS GD acq) flowIn
        iprop(∃ Hh, xTok GD nm.1 x Hh acq ∗
          ⌜histXWf x GD Hh ∧ lockHhPoLatest x GD Hh w_rel⌝) := by
  intro hcons hwb0 hwb1 hsingle hgob hrfe
  exact lockAcqFlowEq3 (hlc := hlc) L x nm.1 nm.2 GD w_rel acq flowIn hcons hwb0 hwb1 hsingle
    hgob hrfe

/-! ## 0.3 THE RELEASE -/

theorem lockRelFlowEq3A (GD : Gdexec) (w_rel e_last : Geid) (Hh : List Hent) (flowIn : Mea GF) :
    rvwmoCatConsistent GD →
    gwritesByte GD.gdG w_rel L b0 →
    (∀ a' v', gwritesByte GD.gdG w_rel a' v' → a' = L) →
    gobCat GD e_last w_rel →
    iprop(([∗map] Rin ∈ flowIn, Rin) -∗
      xTok GD nm.1 x Hh e_last ∗ ⌜histXWf x GD Hh ∧ lockHhPoLatest x GD Hh w_rel⌝) ⊢
    @flowEqDyn hlc GF _ (axGA2Lock3 L x GD0 nm) GD w_rel (lockPolS GD w_rel) flowIn
      iprop(True) := by
  intro hcons hwb hsingle hgob
  exact lockRelFlowEq3 (hlc := hlc) L x nm.1 nm.2 GD w_rel e_last Hh flowIn hcons hwb hsingle hgob

/-! ## 0.4 THE `x`-WRITE -/

theorem lockXwriteFlowEq3A (hxy : x ≠ L) (GD : Gdexec) (w : Geid) (v : BitVec 8)
    (Hl : List Hent) (flowIn : Mea GF) (data : List (BitVec 8)) :
    gwritesByte GD.gdG w x v →
    (∀ a' v', gwritesByte GD.gdG w a' v' → a' = x) →
    graphData GD w = some data →
    iprop(([∗map] Rin ∈ flowIn, Rin) -∗ histAuth nm.1 x 1 Hl) ⊢
    @flowEqDyn hlc GF _ (axGA2Lock3 L x GD0 nm) GD w (lockPolS GD w) flowIn
      iprop(⌜graphData GD w = some data⌝) := by
  intro hwb hsingle hgd
  exact lockXwriteFlowEq3 (hlc := hlc) L x hxy nm.1 nm.2 GD w v Hl flowIn data hwb hsingle hgd

/-! ## 0.5 THE `x`-READ -/

theorem lock3ReadFlowEq3A (GD : Gdexec) (r_x w0 acq : Geid) (H : List Hent) (w_x : Geid)
    (vx : BitVec 8) (flowIn : Mea GF) :
    rvwmoCatConsistent GD →
    (∀ p, p ∈ H → gwritesByte GD.gdG p.1 x p.2) →
    chainWith (gmoLt GD.gdG) (H.map Prod.fst) →
    (∀ w v, gwritesByte GD.gdG w x v → WeakRvwmoGraph.gpo GD.gdG w r_x →
      w ∈ H.map Prod.fst) →
    H.getLast? = some (w_x, vx) →
    gacqPo GD.gdG acq r_x →
    gisW GD.gdG r_x = false →
    grfAt GD.gdG x w0 r_x → w0.1 ≠ r_x.1 →
    (∃ t v, greadsByte GD.gdG r_x x t v) →
    iprop(([∗map] Rin ∈ flowIn, Rin) -∗ tokTie GD nm.1 x H {[acq := (1 : Qp)]}) ⊢
    @flowEqDyn hlc GF _ (axGA2Lock3 L x GD0 nm) GD r_x (lockPolS GD r_x) flowIn
      iprop(⌜∀ t v, greadsByte GD.gdG r_x x t v → v = vx⌝) := by
  intro hcons hwr hch hown hlast hacq hnw hrf0 hext0 hrd
  have hwf : gwf GD.gdG := hcons.1
  have hgrf0 : WeakRvwmoAcyc.grf GD.gdG w0 r_x := grfAtGrf _ _ _ _ hrf0
  have hgrfe0 : grfe GD.gdG w0 r_x := ⟨hgrf0, hext0⟩
  have hw0gmo : w0 ∈ GD.gdG.gxGmo := grfSrcGxGmo GD.gdG w0 r_x hgrf0
  have hcov : ∀ w v, gwritesByte GD.gdG w x v → gmoLt GD.gdG w r_x →
      w ∈ lockPolS GD r_x := by
    intro w v hwb hmo
    rcases xWritesGmoBeforeRead GD x r_x w w0 v hcons hrf0 hwb hmo with h | hco
    · rw [h]
      exact lockPolSIntro GD w0 r_x hw0gmo hgrfe0
    · exact lockPolSIntro2 GD w w0 r_x (gwritesByteGxGmo GD.gdG hwf w x v hwb) hco hgrfe0
  unfold flowEqDyn
  iintro Hflowin %σ %sOb %Hsub %Hnin Hob Hflow
  obtain ⟨g, D, hm⟩ := σ
  icases ((lock3ObStInterpA L x GD0 nm GD g D hm sOb).trans
    (protInvLock3Unfold L x nm.1 nm.2 GD sOb D hm g)).1 $$ Hob with ⟨Hlock'', Hgen⟩
  icases (AxProtLock2.protInvLockUnfold'' L x nm.1 nm.2 GD sOb D hm).1 $$ Hlock''
    with ⟨Hlock', HHL, %Hclaims, %Hhmc⟩
  ihave Htie := Hflowin $$ Hflow
  icases (protInvLockUnfold' L x nm.1 nm.2 GD sOb D hm).1 $$ Hlock' with ⟨Hc, Hpo, Hlocks⟩
  have hres : protInv (GF := GF) nm.1 GD sOb ∗ tokTie GD nm.1 x H {[acq := (1 : Qp)]} ⊢
      ⌜grfAt GD.gdG x w_x r_x ∧ ∀ t v, greadsByte GD.gdG r_x x t v → v = vx⌝ := by
    iintro ⟨Hpo, Htie⟩
    ihave Hsn := protInvPrefixCovMemByte nm.1 GD sOb r_x x
      (fun w v hwb hmo => Hsub _ (hcov w v hwb hmo)) $$ Hpo
    iapply lockReadOwn GD nm.1 x H w_x acq r_x vx hcons hwr hch hown hlast hacq hrd
    isplitl [Htie]
    · iexact Htie
    · iexact Hsn
  icases persistent_entails_left hres $$ [$Hpo $Htie] with ⟨⟨Hpo, -⟩, %Hval⟩
  ihave Hpo' := protInvReadStep nm.1 GD sOb r_x Hnin hnw $$ Hpo
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  inext
  imod Hclose
  imodintro
  iexists ((g, D, hm) : Bool × GSet Geid × GMapF Geid (List Hent))
  isplitl [Hc Hpo' Hlocks HHL Hgen]
  · iapply ((lock3ObStInterpA L x GD0 nm GD g D hm (({r_x} : GSet Geid) ∪ sOb)).trans
      (protInvLock3Unfold L x nm.1 nm.2 GD (({r_x} : GSet Geid) ∪ sOb) D hm g)).2
    isplitl [Hc Hpo' Hlocks HHL]
    · iapply (AxProtLock2.protInvLockUnfold'' L x nm.1 nm.2 GD (({r_x} : GSet Geid) ∪ sOb)
        D hm).2
      isplitl [Hc Hpo' Hlocks]
      · iapply (protInvLockUnfold' L x nm.1 nm.2 GD (({r_x} : GSet Geid) ∪ sOb) D hm).2
        isplitl [Hc]
        · iexact Hc
        isplitl [Hpo']
        · iexact Hpo'
        iapply (AxProtLock.bigSepSUnionSingleton
          (Φ := fun e => ΦLock' L x nm.1 nm.2 GD e ((get? hm e).getD [])) Hnin).2
        isplitl []
        · iapply AxProtLock.ΦLock'Vacuous L x nm.1 nm.2 GD r_x _ (fun hbad => by
            have h := AxProt.gwritesByteGisW _ _ _ _ hbad
            rw [hnw] at h
            cases h)
        · iexact Hlocks
      · isplitl [HHL]
        · iexact HHL
        · isplitl []
          · ipureintro
            intro r hr
            obtain ⟨e, he, hre⟩ := Hclaims r hr
            exact ⟨e, elemOfUnionR he, hre⟩
          · ipureintro
            intro w hw hwb0'
            rcases elemOfUnion.1 hw with hw | hw
            · rw [elemOfSingleton.1 hw] at hwb0'
              have h := AxProt.gwritesByteGisW _ _ _ _ hwb0'
              rw [hnw] at h
              cases h
            · exact Hhmc w hw hwb0'
    · iapply lockGenesisMono L x nm.1 GD g sOb (({r_x} : GSet Geid) ∪ sOb)
        (fun _ h => elemOfUnionR h)
      iexact Hgen
  · ipureintro
    exact Hval.2

end lock3Transport

end Weak
