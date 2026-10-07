/-
Weak: **A CONCRETE `Axpol` INSTANCE** for `Weak.AxProt`'s protocol (the gco-predecessor handout
policy), and the chain-preserving write flow equations.

Rocq: `iris/AxProtInst.v` @ xxvzwolszwmp.

## The Rocq header, in substance

§1 `axprotPred GD e`: every `gco`-predecessor of `e` (every earlier write to the same byte),
computed off `AxGraphDec.gcoB` over `gxGmo` — empty for a non-write.  Each element is a single
`gco` edge, hence a `gobCatFlow` predecessor (`axprotPredSubFlow`).
§2 `axprotPol` (`sPol` = `lobp` = `axprotPred`) and its three corollaries: `axprotAxpolWfL`,
`axprotSchedAxpolWfProc`, `axprotSchedProcAdequate` — the last is `AxSchedGD.schedProcAdequate`
with its `HsPolSub`/`HlobpSub` hypotheses DISCHARGED (proved, not assumed); `Hdefer` is still
carried.
§3 `flowEqOwnedWriteChain`: `AxProt.flowEqOwnedWrite` but returning the fresh `tokTie` as part
of `R` (`protInvWriteStep` instead of `protInvWriteStepAuth`).
§4 `flowEqOwnedWriteChainSnap`: the same, additionally depositing a persistent `histSnap` of the
fresh history (`AxToken.tokSnap`, no fraction split).  The Rocq header's open FINDING (wiring
the chain into `eaLocalWf`/`ordEaTodoL`) is continued in AxProtCov*.

**Fetches.** Nothing here depends on instruction fetches (graph events only; Stage C).  This file
does not touch the WP step clause (pending Q8 rework): its only WP-adjacent content is
`flowEqDyn` (§3/§4) and `schedProcAdequate` (§2), neither of which unfolds the step clause.

## Deviations from Rocq

1. NAMES: camelCase (map below); none of the names is duplicated in the Rocq tree.
2. VOCABULARY (as `AxProt` deviation 2): `list_to_set l` ↦ `(LawfulSet.ofList l : GSet Geid)`,
   `filter` ↦ `List.filter`, `gd_g GD` ↦ `GD.gdG`, `mea Σ`/`sra Σ` ↦ `Mea GF`/`Sra GF`,
   `dom` ↦ `FiniteMap.dom_set`, `from_option id emp` ↦ `AxWp.fromOption (fun P => P) emp`.
3. STATEMENT SHAPES (as `AxProt` deviation 4): `P -∗ flowEqDyn …` ↦ `P ⊢ flowEqDyn …`;
   `axprotSchedProcAdequate` is `⊢ A -∗ B -∗ C` (as `AxSchedGD.schedProcAdequate`).
4. CONTEXTS: `invGS_gen HasNoLc Σ` ↦ `[InvGS_gen hlc GF]` for any `hlc`; the §3/§4 section
   variables `γ`/`Hob_eq` are explicit leading arguments (as `AxProt.flowEqOwnedWrite`); the
   section's `axpol` context is unused by the §3/§4 statements and dropped.
5. `axprotPol` is a global `instance` (as Rocq's `Instance`); the §2 corollaries take no
   `[Axpol]` binder and resolve to it.

**Rocq → Lean name map.**  `axprot_pred` `axprotPred`, `axprot_pred_sub_flow`
`axprotPredSubFlow`, `axprot_pol` `axprotPol`, `axprot_axpol_wf_L` `axprotAxpolWfL`,
`axprot_sched_axpol_wf_proc` `axprotSchedAxpolWfProc`, `axprot_sched_proc_adequate`
`axprotSchedProcAdequate`, `flow_eq_owned_write_chain` `flowEqOwnedWriteChain`,
`flow_eq_owned_write_chain_snap` `flowEqOwnedWriteChainSnap`.

**Not ported:** the §5 `Print Assumptions` audit (the lint's axiom check covers it).
-/
import Weak.AxProt
import Weak.AxSchedGD

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp

/-! # 1. THE gco-PREDECESSOR SET, AND ITS FLOW-CLOSURE -/

/-- Every `gco`-predecessor of `e` (every write to the same byte, earlier in write-index order). -/
def axprotPred (GD : Gdexec) (e : Geid) : GSet Geid :=
  LawfulSet.ofList (GD.gdG.gxGmo.filter (fun w => gcoB GD.gdG w e))

/-- Every element of `axprotPred GD e` is a `gobCatFlow`-predecessor of `e` (one `gco` edge). -/
theorem axprotPredSubFlow (GD : Gdexec) (e e' : Geid) :
    e' ∈ axprotPred GD e → gobCatFlow GD e' e := by
  intro h
  rw [axprotPred, elemOfListToSet, List.mem_filter] at h
  exact tc_once (.inr (.inr (.inr (.inl ((gcoBSpec _ _ _).1 h.2)))))

/-! # 2. THE CONCRETE `Axpol` INSTANCE, AND ITS THREE COROLLARIES -/

/-- `sPol` and `lobp` both equal `axprotPred`. -/
instance axprotPol : Axpol := ⟨axprotPred, axprotPred⟩

/-- `axpolWfL` for `axprotPol`, via `axpolWfLOfPredClosedFlow`. -/
theorem axprotAxpolWfL (GD : Gdexec) (L : List Geid) (Hpc : LPredClosedFlow GD L) :
    axpolWfL GD L :=
  axpolWfLOfPredClosedFlow GD L (axprotPredSubFlow GD) (axprotPredSubFlow GD) Hpc

/-- The scheduler instance: `schedAxpolWfProc`'s policy hypotheses discharged. -/
theorem axprotSchedAxpolWfProc (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (st : Sstate) (Hrun : rtc (schedStep GD.gdG) sst0 st)
    (Hfull : st.sN = GD.gdG.gxGmo.length) (Hdone : st.sD = ∅) :
    axpolWfProc GD st.sProc :=
  schedAxpolWfProc GD Hcons st Hrun Hfull Hdone (axprotPredSubFlow GD) (axprotPredSubFlow GD)

section ProcAdequateInst
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF]

/-- THE ADEQUACY THEOREM, CONCRETELY, WITH NO POLICY HYPOTHESES LEFT (`Hdefer` still carried). -/
theorem axprotSchedProcAdequate (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (st : Sstate) (Hrun : rtc (schedStep GD.gdG) sst0 st)
    (Hfull : st.sN = GD.gdG.gxGmo.length) (Hdone : st.sD = ∅)
    (na : Mea GF) (ea : Sra GF)
    (HdomEq : (FiniteMap.dom_set ea : GSet Geid) = FiniteMap.dom_set na)
    (Hdom : (LawfulSet.ofList st.sProc : GSet Geid) ⊆ FiniteMap.dom_set na)
    (HeaLob : ∀ e0 gm, get? ea e0 = some gm →
      (FiniteMap.dom_set gm : GSet Geid) ⊆ Axpol.lobp GD e0)
    (Hdefer : ∀ r, deferredSnapAvail GD st.sEverD r)
    (σ0 : AxirisG.obSt GF) :
    ⊢ ordEaTodoL GD ea na st.sProc 0 -∗
      AxirisG.obStInterp GD σ0 ∅ -∗
      |={⊤}[∅]▷=>^[st.sProc.length]
        ∃ (σ : AxirisG.obSt GF),
          AxirisG.obStInterp GD σ (LawfulSet.ofList st.sProc) ∗
          [∗set] e0 ∈ (LawfulSet.ofList st.sProc : GSet Geid),
            AxWp.fromOption (fun P => P) iprop(emp) (get? na e0) :=
  schedProcAdequate GD Hcons st Hrun Hfull Hdone (axprotPredSubFlow GD) (axprotPredSubFlow GD)
    na ea HdomEq Hdom HeaLob Hdefer σ0

end ProcAdequateInst

/-! # 3./4. THE CHAIN-PRESERVING WRITE FLOW EQUATIONS -/

section flowChain

variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [axG : AxirisG GF]
  [AxlogG GF Hent]

/-- THE CHAIN-PRESERVING WRITE FLOW EQUATION: the fresh `tokTie` is kept in `R`. -/
theorem flowEqOwnedWriteChain (γ : GName)
    (Hob_eq : ∀ (GD : Gdexec) (σ : AxirisG.obSt GF) (s : GSet Geid),
      AxirisG.obStInterp GD σ s ⊣⊢ protInv γ GD s)
    (GD : Gdexec) (w : Geid) (a : Int) (v : BitVec 8) (Hl : List Hent) (sOb0 : GSet Geid)
    (flowIn : Mea GF) (data : List (BitVec 8)) :
    gwritesByte GD.gdG w a v →
    (∀ a' v', gwritesByte GD.gdG w a' v' → a' = a) →
    graphData GD w = some data →
    iprop(([∗map] Rin ∈ flowIn, Rin) -∗ histAuth γ a 1 Hl) ⊢
      flowEqDyn GD w sOb0 flowIn
        iprop(tokTie GD γ a (Hl ++ [(w, v)]) {[w := (1 : Qp)]} ∗
          ⌜graphData GD w = some data⌝) := by
  intro hwb hsingle hgd
  unfold flowEqDyn
  iintro Hflowin %σ %sOb %Hsub %Hnin Hob Hflow
  ihave Hob := (Hob_eq GD σ sOb).1 $$ Hob
  ihave Hauth := Hflowin $$ Hflow
  imod protInvWriteStep γ GD sOb w a v Hl Hnin hwb hsingle $$ [$Hob $Hauth]
    with ⟨Hinv, Htie⟩
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  inext
  imod Hclose
  imodintro
  iexists σ
  isplitl [Hinv]
  · iapply (Hob_eq GD σ (({w} : GSet Geid) ∪ sOb)).2
    iexact Hinv
  · isplitl [Htie]
    · iexact Htie
    · ipureintro
      exact hgd

/-- THE SAME, ADDITIONALLY DEPOSITING A PERSISTENT `histSnap` OF THE FRESH HISTORY. -/
theorem flowEqOwnedWriteChainSnap (γ : GName)
    (Hob_eq : ∀ (GD : Gdexec) (σ : AxirisG.obSt GF) (s : GSet Geid),
      AxirisG.obStInterp GD σ s ⊣⊢ protInv γ GD s)
    (GD : Gdexec) (w : Geid) (a : Int) (v : BitVec 8) (Hl : List Hent) (sOb0 : GSet Geid)
    (flowIn : Mea GF) (data : List (BitVec 8)) :
    gwritesByte GD.gdG w a v →
    (∀ a' v', gwritesByte GD.gdG w a' v' → a' = a) →
    graphData GD w = some data →
    iprop(([∗map] Rin ∈ flowIn, Rin) -∗ histAuth γ a 1 Hl) ⊢
      flowEqDyn GD w sOb0 flowIn
        iprop(tokTie GD γ a (Hl ++ [(w, v)]) {[w := (1 : Qp)]} ∗
          histSnap γ a (Hl ++ [(w, v)]) ∗
          ⌜graphData GD w = some data⌝) := by
  intro hwb hsingle hgd
  unfold flowEqDyn
  iintro Hflowin %σ %sOb %Hsub %Hnin Hob Hflow
  ihave Hob := (Hob_eq GD σ sOb).1 $$ Hob
  ihave Hauth := Hflowin $$ Hflow
  imod protInvWriteStep γ GD sOb w a v Hl Hnin hwb hsingle $$ [$Hob $Hauth]
    with ⟨Hinv, Htie⟩
  unfold tokTie
  icases Htie with ⟨Htok, %htie⟩
  icases tokSnap γ a (Hl ++ [(w, v)]) {[w := (1 : Qp)]} w 1 lookupSingleton $$ Htok
    with ⟨Htok, #Hs⟩
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  inext
  imod Hclose
  imodintro
  iexists σ
  isplitl [Hinv]
  · iapply (Hob_eq GD σ (({w} : GSet Geid) ∪ sOb)).2
    iexact Hinv
  · isplitl [Htok]
    · isplitl [Htok]
      · iexact Htok
      · ipureintro
        exact htie
    · isplitl []
      · iexact Hs
      · ipureintro
        exact hgd

end flowChain

end Weak
