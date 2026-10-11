/-
Weak: **TIED ANNOTATIONS AND THE BASE WEAKEST PRECONDITION**, part 1 of 2 (AxSL tier):
the pure vocabulary, the tied annotation resource `e ↦ₐ P`, the interface classes and the
`|=i=>` modality.  Part 2 (`Weak.AxWp2`) has the WP, the checkpointed WP and the skeleton.

Rocq: `iris/AxWp.v` @ xxvzwolszwmp (§§1–4 here, §§5–7 in `Weak/AxWp2.lean`).

## The Rocq header, in substance

LB via an AxSL-style base logic (design §1-L1, §0.5 "The step case").  Port of AxSL's
`low/iris.v` (interface parameters), `low/annot_res.v` (the tied annotation `e ↦ₐ P`),
`low/lib/annotations.v` (`na_splitting_wf`), `low/interp_mod.v` (`|=i=>`), `low/weakestpre.v`
and `low/weakestpre_chk.v`, over `AxOpsem`'s `Athread` / `AxOpsem.astepProg` / `areadStep` /
`awire`.  `wp st i s Φ` is the fixpoint of `wpPre`: at a (never reached) terminated state the
postcondition under the annotations; otherwise the progress obligation AND the step case, with
three conjuncts: (a) the read, ANGELIC in the value (a flow equation whose conclusion carries
`graphValue GD e = some v`; the fused RMW's read half posts no flow equation and is pinned to
the graph's value); (b) every other program step, DEMONIC (a write validates its data
`graphData GD e = some data`; administrative labels -- in Lean also the fetch -- and fences skip); (c) the
PLIC wire, a skip.  Both event cases are `wpEvStep`, both skips `wpSkipStep`.  The core is
parametric in `AxirisG` (annotation interpretation, graph agreement, ob-state, local state; Rocq's
text region `ax_text` is deleted, deviation 10) and `Axpol` (handout policy `sPol`, local flow set `lobp`); `AxirisGChk`
adds the checkpoint `chk` with `chkMidInstr`.  Rocq deviations from the AxSL source (kept):
(1) `ghost_map_ag` is a ghost map with DISCARDED elements; (2) `naAtProgress` fixes the local
domain to the MEMORY events before the position (`eidsBefore`); (3) `na_full` dropped; (4) skips
may change the local state; (5) `isTerminated s := false`, the terminated branch kept; (6) no
`sswp` layer.  FACTS FOR THE NEXT STAGE (argument orders): `wpEvStep GD i k ok val k' Ψ`;
`wpSkipStep GD i k' Ψ`; `flowEqDyn GD e sOb0 flowIn R`; `naAtProgress GD i k na`;
`naSplittingWf sLob na naUsed naUnused`; `postLifting Φ i s`; `progressObl st i s`;
`AxWp.wp st i s Φ`; `wpc st i s Φ`.  The annotation map after an event is
`union (union {[e := R]} naUnused) na` (left-biased, as AxSL).

## Deviations from Rocq (both parts)

1. NAMES: the tree's camelCase (map below).  Duplicated Rocq names, file-qualified:
   `AxWp.wp`, `AxWp.atBoundary`, `AxWp.growLookup`.  Lean-only helpers, file-qualified:
   `AxWp.fromOption` (stdpp `from_option`) + instance `AxWp.fromOptionPersistent`,
   `AxWp.eqWand`, `AxWp.singletonUnionMem`, `AxWp.bigSepMInsertWand`, `AxWp.bigSepMExtract`,
   `AxWp.bagFragIn(W)`, `AxWp.bagFragNe(W)`, `AxWp.annotOpen`, `AxWp.annotClose`,
   `AxWp.annotCloseSame`, `AxWp.savedPropAgreeW`, `AxWp.mergeWand`, `AxWp.agreeWand`,
   `AxWp.detachWand`, `AxWp.splitWand`, `AxWp.updateWand`, `AxAnnot.bagInv` (Rocq's inner
   `∃ res, …` of `annot_interp`, a definition so the bag can be opened by name); in part 2
   `AxWp.wpEvStepDist`, `AxWp.wpSkipStepDist`, `AxWp.wpPreStepDefDist` (one non-expansiveness
   proof shared by contractiveness and `wpNe`/`wpcNe`), `AxWp.wpcUnfoldStep`.
2. REPRESENTATION (the tree's shims): `gmap K V` ↦ `GMapF K V`, `gset A` ↦ `GSet A`,
   `dom m` ↦ `(FiniteMap.dom_set m : GSet _)`, `m !! e` ↦ `get? m e`, `<[e:=R]> m` ↦
   `insert m e R`, `delete`, `{[e := R]}` as stdpp; `m1 ∪ m2` on maps ↦ `PartialMap.union m1 m2`
   (a bare `∪` on `GMapF` elaborates to Std's `ExtTreeMap` union, which the shim lemmas do not
   speak about); `list_to_set ((λ j, (i,j)) <$> filter _ (seq 0 k))` ↦ `LawfulSet.ofList` of
   `List.range k` filtered and mapped; set `filter` ↦ `FiniteSet.filter` with `decide`;
   `bool_decide P` ↦ `if P`; `S k` ↦ `k + 1`; `Interface.Ret tt` ↦ `FreeM.pure ()`;
   `gx_img (gd_g GD)` ↦ `GD.gdG.gxImg`; `bv 8` ↦ `BitVec 8`; `Z` ↦ `Int`; `agent` ↦ `Agent`.
3. CAMERAS: iris-lean has no `gFunctors` lists or `subG`: `axannotΣ`, `subG_axannotΣ`,
   `axgraphΣ`, `subG_axgraphΣ` have no counterpart.  `axannotG Σ` is the class `AxannotG GF`
   (instance fields `SavedPropG GF`, `GhostMapG GF Geid GName (GMapF Geid)`, and
   `axannotSetG : ElemG GF (constOF AxannotSetR)` for Rocq's `inG (authR (gset_disjUR
   gname))`, `AxannotSetR := Auth (DisjointLeibnizSet (GSet GName))`); `axannotGS` is
   `AxannotGS GF` (`axannotInG`, `axannotName`).  `axgraphG`'s `agreeR (leibnizO gdexec)` is
   `Agree (DiscreteO Gdexec)`.  UNIVERSE: the annotation interpretation's `[∗map] e ↦ gn;P ∈
   annot;m` relates a `GName` map to an `IProp GF` map, and iris-lean's `bigSepM2` wants both
   value types in one universe, so every declaration over `AxannotGS` fixes `GF :
   BundledGFunctors.{0,0,0}` — the universe of `MachCSL.MachGS` (checked), i.e. of every GF in
   the tree.
4. SEALS: `annot_own`, `flow_eq_dyn`, `interp_mod`, `wp`, `wpc` are plain definitions (`wp`/`wpc`
   are `fixpoint`, already opaque); no `*_eq` unseal lemmas.
5. NOTATIONS are not provided: `e ↦ₐ P` is `AxAnnot.annotOwn e P`, `|=i=> P` is `interpMod P`,
   `WP s @ st; i {{ Φ }}` is `AxWp.wp st i s Φ` (iris-lean's `WP` notation belongs to its `Wp`
   class), `WPc …` is `wpc st i s Φ`.
6. `invGS_gen HasNoLc Σ` ↦ `[InvGS_gen hlc GF]` for an arbitrary `hlc` (strictly more general;
   only `flowEqDyn` and what is built on it use a fancy update).  Definitions take only the
   section variables they use (as Rocq's sections do): e.g. `postLifting`, `wpSkipStep` do not
   take `InvGS_gen`.
7. STATEMENT SHAPES: Rocq's wand chains `A -∗ B -∗ C` are kept as `⊢ A -∗ B -∗ C` (curried,
   so the hypotheses survive an `ihave` whose conclusion is pure/persistent, as Rocq's
   `iDestruct … as %_`); `P ⊢ Q` stays; pure premises are `→`.  `Proper` instances are theorems:
   `interpModProper`/`interpModFlipProper`/`interpModEquivProper`, `wpProper`/`wpMono'`/
   `wpFlipMono'`, `wpcProper`/`wpcMono'`; `NonExpansive` instances are iris-lean
   `OFE.NonExpansive` instances (`interpModNe`, `wpNe`, `wpcNe`; `flowEqDynNe` a theorem of
   that class).  `wp_ne`'s `pointwise_relation (dist n)` is the function OFE's `dist n`.
   Rocq's `Local Instance wp_pre_chk_contractive` is a global instance (the `fixpoint` needs it).
   iris-lean's `ElimModal`/`FromModal` take an `io : InOut` argument (instances are generic in
   it).
8. THE SKELETON (§7): Rocq's `Local Existing Instance skel_axirisG` ↦ the statements name the
   instance (`AxirisG.annotInterp (self := skelAxirisG γg Φp)`, `@flowEqDyn _ _ _
   (skelAxirisG γg Φp)`, `@wpSkipStep _ (skelAxirisG γg Φp)`); `skelAxirisG` is
   `@[reducible]` (a definition of class type).  `skel_wp_skip_step_of_psi` keeps the Rocq
   recipe (`BI.later_intro`, not `inext`, for the goal's later).
9. PROOFS (not statements): the annotation lemmas go through `AxWp.annotOpen`/`annotClose`
   (open one event's bag, close it at a new content) instead of re-deriving the ghost-map
   lookup in each proof; Rocq's `iRewrite` of a saved-proposition agreement under `▷` is
   `AxWp.eqWand` (an internal equality is a persistent wand); `annot_split` allocates the fresh
   saved proposition with `saved_prop_alloc_cofinite` at `toList (dom res)`.  The WP laws use
   `wpUnfoldStep` (the terminated branch is dead: `isTerminated s = false` by definition), so
   `post_lifting_strong_mono` is not needed inside `wpStrongMono`.
10. O2 STAGE C (`notes/weak-port-o2-stageC.md`, owner Q-C2): the fetch is an ADMINISTRATIVE
   label (`AxOpsem` deviation 2), so the L0 fetch oracle is gone: `AxirisG` has no `ax_text`
   field, `astepProgGraphData` has no `T`/`img` parameters and no `AStep_fetch` case, and the
   step case (`AxWp2`) quantifies `AxOpsem.astepProg (AxOpsem.grow GD i) s l s'` (Rocq:
   `astep_prog (grow GD i) ax_text (gx_img (gd_g GD))`).  OWNER Q8: the image half of Rocq's
   oracle is kept as a PIN on the step clause — `wpPreStepDef` (and `AxWpD.wpdMPreStepDef`)
   read `∀ l s', ⌜AxOpsem.astepProg (AxOpsem.grow GD i) s l s'⌝ -∗
   ⌜WeakAxRealize.fetchPin GD.gdG.gxImg l⌝ -∗ …`: a fetch step answers the graph's boot image
   at timestamp 0 (`True` off the fetch), as Rocq's `fetch_answers ax_text (gx_img (gd_g GD))`
   did for `AStepFetch`.  Adequacy discharges the pin from the pinned machine LTS
   (`AxAdequacy.astepProgNfOfPstepPin`).

**Rocq → Lean name map.**  §1: `is_terminated` `isTerminated`, `is_terminated_terminated`
`isTerminatedTerminated`, `at_boundary` `AxWp.atBoundary`, `lbl_value` `lblValue`,
`graph_value` `graphValue`, `graph_data` `graphData`, `wl_wdata_wr` `wlWdataWr`,
`wl_wdata_wr_n` `wlWdataWrN`, `grow_lookup` `AxWp.growLookup`, `aread_step_graph_value`
`areadStepGraphValue`, `astep_prog_graph_data` `astepProgGraphData`, `gmem_b` `gmemB`,
`eids_before` `eidsBefore`, `elem_of_eids_before` `elemOfEidsBefore`, `eids_before_0`
`eidsBefore0`, `eids_before_S_mem` `eidsBeforeSMem`, `eids_before_S_skip` `eidsBeforeSSkip`.
§2: `mea` `Mea`, `axannotG`/`AxAnnotG` `AxannotG` (fields `axannotSavedG`, `axannotMapG`,
`axannotSetG`), `axannotGS`/`AxAnnotGS` `AxannotGS` (`axannotInG`, `axannotName`),
`AxAnnot.annot_own(_def)` `AxAnnot.annotOwn`, `AxAnnot.annot_interp` `AxAnnot.annotInterp`,
`annot_lookup_bag` `annotLookupBag`, `annot_merge` `annotMerge`, `annot_agree` `annotAgree`,
`annot_agree_big` `annotAgreeBig`, `annot_detach` `annotDetach`, `annot_detach_big`
`annotDetachBig`, `annot_alloc` `annotAlloc`, `annot_split` `annotSplit`, `annot_update`
`annotUpdate`, `annot_entail` `annotEntail`, `annot_interp_alloc` `annotInterpAlloc`.
§3: `axirisG`/`AxIrisG` `AxirisG` (fields `annot_interp` `annotInterp`, `gconst_interp`
`gconstInterp`, `ob_st` `obSt`, `ob_st_interp` `obStInterp`, `log_ts_t` `logTsT`,
`local_interp` `localInterp`; `ax_text` deleted, deviation 10), `axpol`/`AxPol` `Axpol` (`s_pol` `sPol`,
`lobp`), `axirisGChk`/`AxIrisGChk` `AxirisGChk` (`chk`, `chk_mid_instr` `chkMidInstr`).
§4: `na_at_progress` `naAtProgress`, `na_at_progress_not_elem_of` `naAtProgressNotElemOf`,
`na_splitting_wf` `naSplittingWf`, `na_splitting_wf_persistent` `naSplittingWfPersistent`,
`na_splitting_wf_dom` `naSplittingWfDom`, `na_splitting_wf_mono` `naSplittingWfMono`,
`interp_mod(_def)` `interpMod`, `interp_mod_mono` `interpModMono`, `interp_mod_strong_mono`
`interpModStrongMono`, `interp_mod_bupd(')` `interpModBupd(')`, `interp_mod_intro`
`interpModIntro`, `interp_mod_frame_l/r` `interpModFrameL/R`, `interp_mod_sep` `interpModSep`,
`interp_mod_trans` `interpModTrans`, `interp_mod_and` `interpModAnd`, `interp_mod_exist`
`interpModExist`, `interp_mod_proper` `interpModProper`, `interp_mod_flip_proper`
`interpModFlipProper`, `interp_mod_ne` `interpModNe`, `interp_mod_equiv_proper`
`interpModEquivProper`, `elim_modal_bupd_interp_mod` `elimModalBupdInterpMod`,
`elim_modal_iupd_interp_mod` `elimModalIupdInterpMod`, `from_modal_interp_mod`
`fromModalInterpMod`.  (§§5–7: `Weak/AxWp2.lean`'s header.)

**Not ported:** the `Σ`/`subG` boilerplate (deviation 3) and the §8 `Print Assumptions` block
(the lint's axiom check covers it).
-/
import Weak.AxOpsem
import MachCSL.StdppMap
import MachCSL.OrdKeys
import Iris.Instances.Lib.SavedProp
import Iris.Instances.Lib.GhostMap
import Iris.Algebra.LeibnizSet
import Iris.Algebra.Auth

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp

/-! # 1. Pure vocabulary: termination, boundaries, event values, domains -/

/-- Harts never terminate (`AxOpsem.terminated s = False`, fact 4). -/
def isTerminated (_s : Athread) : Bool := false

theorem isTerminatedTerminated (s : Athread) : isTerminated s = true ↔ terminated s := by
  simp [isTerminated, terminated]

/-- The instruction boundary: the hart's node is the finished monad `.pure ()` (Rocq
`Interface.Ret tt`). -/
def AxWp.atBoundary (s : Athread) : Prop :=
  ∃ cpu rs fn ib, s.atP = .PHart cpu (.pure ()) rs fn ib

/-- The VALUE a row label reads. -/
def lblValue (l : Lbl) : Option (List (BitVec 8)) :=
  match l with
  | .LLoad _ _ _ vs => some vs
  | .LRmw _ _ _ _ rvs _ _ => some rvs
  | _ => none

def graphValue (GD : Gdexec) (e : Geid) : Option (List (BitVec 8)) :=
  (gxLbl GD.gdG e).bind lblValue

def graphData (GD : Gdexec) (e : Geid) : Option (List (BitVec 8)) :=
  (gxLbl GD.gdG e).bind lblData

theorem wlWdataWr (l : Wlabel) : (wlWdata l).isSome = true ↔ (wlWr l).isSome = true := by
  cases l <;> simp [wlWdata, wlWr]

theorem wlWdataWrN (l : Wlabel) (data : List (BitVec 8)) (rl : Bool) (base : Int) (n : Nat) :
    wlWdata l = some data → wlWr l = some (rl, base, n) → data.length = n := by
  cases l <;> simp [wlWdata, wlWr] <;> intro h1 h2 <;> subst h1 <;> omega

/-- The row of hart `i` IS the graph's row: a row lookup is a graph lookup. -/
theorem AxWp.growLookup (GD : Gdexec) (i k : Nat) (lb : Lbl) :
    (AxOpsem.grow GD i)[k]? = some lb → gxLbl GD.gdG (i, k) = some lb := by
  unfold AxOpsem.grow growG gxLbl
  cases GD.gdG.gxProg[i]? with
  | none => simp
  | some row => simp

/-- NON-VACUITY OF THE READ CASE'S PURE OBLIGATIONS: a read about to happen has a graph value,
of the identity's width for a plain read. -/
theorem areadStepGraphValue (GD : Gdexec) (i : Nat) (s : Athread) (id : AidentT)
    (K : List (BitVec 8) → Athread) :
    areadStep (AxOpsem.grow GD i) s id K →
    ∃ v, graphValue GD (i, s.atK) = some v ∧ (aidentAdvRd id = 1 → v.length = aidentN id) := by
  rintro ⟨lb, hrow, rfl, hrd, _⟩
  unfold graphValue
  rw [AxWp.growLookup GD i s.atK lb hrow]
  cases lb with
  | LLoad aq base ts vs => exact ⟨vs, rfl, fun _ => rfl⟩
  | LStore rl base vs k => simp [aident, aidentRd] at hrd
  | LFence pr pw sr sw => simp [aident, aidentRd] at hrd
  | LRmw aq rl base ts rvs wvs k => exact ⟨rvs, rfl, fun h => by simp [aident, aidentAdvRd] at h⟩
  | LIo kd base vs => simp [aident, aidentRd] at hrd

/-- ... and a write about to happen has graph data of the label's width. -/
theorem astepProgGraphData (GD : Gdexec) (i : Nat)
    (s : Athread) (l : Wlabel) (s' : Athread) (data : List (BitVec 8)) :
    AxOpsem.astepProg (AxOpsem.grow GD i) s l s' → wlWdata l = some data →
    ∃ d, graphData GD (i, s.atK) = some d ∧ d.length = data.length := by
  intro h hdata
  cases h with
  | AStepAdmin p k d l p' d' ha hs =>
    cases l <;> simp [lbAdmin, wlWdata] at ha hdata
  | AStepWrite p k d l lb p' d' hrow hs1 hid hdat hs =>
    refine ⟨data, ?_, rfl⟩
    unfold graphData
    rw [AxWp.growLookup GD i k lb hrow]
    show lblData lb = some data
    rw [← hdat, hdata]
  | AStepFence p k d l lb p' d' hrow hs1 hid hs =>
    cases l <;> simp [wlFence, wlWdata] at hs1 hdata

/-- Rocq `gmem_b`: the event is a memory event. -/
def gmemB (G : Gexec) (e : Geid) : Bool :=
  match gxLbl G e with
  | some l => lbIsMem l
  | none => false

/-- The MEMORY events of hart `i` before position `k`: the domain of the annotation map's
local part (Rocq deviation 2). -/
def eidsBefore (GD : Gdexec) (i : Agent) (k : Nat) : GSet Geid :=
  LawfulSet.ofList (((List.range k).filter (fun j => gmemB GD.gdG (i, j))).map (fun j => (i, j)))

theorem elemOfEidsBefore (GD : Gdexec) (i : Agent) (k : Nat) (e : Geid) :
    e ∈ eidsBefore GD i k ↔ e.1 = i ∧ e.2 < k ∧ gmemB GD.gdG e = true := by
  obtain ⟨i', j⟩ := e
  unfold eidsBefore
  rw [elemOfListToSet]
  simp only [List.mem_map, List.mem_filter, List.mem_range, Prod.mk.injEq]
  constructor
  · rintro ⟨j', ⟨hj, hm⟩, rfl, rfl⟩
    exact ⟨rfl, hj, hm⟩
  · rintro ⟨rfl, hj, hm⟩
    exact ⟨j, ⟨hj, hm⟩, rfl, rfl⟩

theorem eidsBefore0 (GD : Gdexec) (i : Agent) : eidsBefore GD i 0 = ∅ := by
  rw [setEq]
  intro e
  rw [elemOfEidsBefore, elemOfEmpty]
  simp

theorem eidsBeforeSMem (GD : Gdexec) (i : Agent) (k : Nat) :
    gmemB GD.gdG (i, k) = true →
    eidsBefore GD i (k + 1) = ({(i, k)} : GSet Geid) ∪ eidsBefore GD i k := by
  intro hm
  rw [setEq]
  rintro ⟨i', j⟩
  rw [elemOfUnion, elemOfSingleton, elemOfEidsBefore, elemOfEidsBefore]
  simp only [Prod.mk.injEq]
  constructor
  · rintro ⟨rfl, hj, hm'⟩
    by_cases hjk : j = k
    · exact .inl ⟨rfl, hjk⟩
    · exact .inr ⟨rfl, by omega, hm'⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, hj, hm'⟩)
    · exact ⟨rfl, by omega, hm⟩
    · exact ⟨rfl, by omega, hm'⟩

theorem eidsBeforeSSkip (GD : Gdexec) (i : Agent) (k : Nat) :
    gmemB GD.gdG (i, k) = false → eidsBefore GD i (k + 1) = eidsBefore GD i k := by
  intro hm
  rw [setEq]
  rintro ⟨i', j⟩
  rw [elemOfEidsBefore, elemOfEidsBefore]
  constructor
  · rintro ⟨h1, hj, hm'⟩
    refine ⟨h1, ?_, hm'⟩
    by_cases hjk : j = k
    · subst hjk; simp only at h1; subst h1; rw [hm] at hm'; cases hm'
    · simp only at hj ⊢; omega
  · rintro ⟨h1, hj, hm'⟩
    exact ⟨h1, by simp only at hj ⊢; omega, hm'⟩

/-! # 2. The annotation resource `e ↦ₐ P` (port of AxSL `low/annot_res.v`) -/

/-- Rocq `mea Σ`: the annotation map. -/
abbrev Mea (GF : BundledGFunctors) := GMapF Geid (IProp GF)

/-- The per-event bag camera: `authR (gset_disjUR gname)`. -/
abbrev AxannotSetR := Auth (DisjointLeibnizSet (GSet GName))

class AxannotG (GF : BundledGFunctors) where
  [axannotSavedG : SavedPropG GF]
  [axannotMapG : GhostMapG GF Geid GName (GMapF Geid)]
  axannotSetG : ElemG GF (constOF AxannotSetR)

attribute [reducible, instance] AxannotG.axannotSavedG AxannotG.axannotMapG AxannotG.axannotSetG

class AxannotGS (GF : BundledGFunctors) where
  [axannotInG : AxannotG GF]
  axannotName : GName

attribute [reducible, instance] AxannotGS.axannotInG

namespace AxAnnot

section annotDefs
variable {GF : BundledGFunctors} [AxannotGS GF]

/-- Rocq `annot_own_def` (`e ↦ₐ P`): the event's bag name (discarded map element), a
fragment of the bag naming the saved proposition `n'`, and half of that saved proposition. -/
def annotOwn (e : Geid) (P : IProp GF) : IProp GF :=
  iprop(∃ n n' : GName, ghost_map_elem (AxannotGS.axannotName (GF := GF)) DFrac.discard e n ∗
    iOwn (E := AxannotG.axannotSetG) n (◯ (DisjointLeibnizSet.valid ({n'} : GSet GName))) ∗
    saved_prop_own n' (DFrac.own (Qp.half 1)) P)

/-- Lean-only (file-qualified): one event's BAG, Rocq's inner `∃ res, …` of `annot_interp`. -/
def bagInv (gn : GName) (P : IProp GF) : IProp GF :=
  iprop(∃ res : GMapF GName (IProp GF),
    iOwn (E := AxannotG.axannotSetG) gn
      (● (DisjointLeibnizSet.valid (FiniteMap.dom_set res : GSet GName))) ∗
    ([∗map] gnp ↦ R ∈ res, saved_prop_own gnp (DFrac.own (Qp.half 1)) R) ∗
    ▷ □ (P -∗ [∗map] R ∈ res, R))

/-- Rocq `annot_interp`: the interpretation of the annotation map `m`. -/
def annotInterp (m : Mea GF) : IProp GF :=
  iprop(∃ annot : GMapF Geid GName,
    ghost_map_auth (AxannotGS.axannotName (GF := GF)) (DFrac.own 1) annot ∗
    ⌜(FiniteMap.dom_set annot : GSet Geid) = FiniteMap.dom_set m⌝ ∗
    [∗map] e ↦ gn; P ∈ annot; m, bagInv gn P)

end annotDefs
end AxAnnot

/-! ### Lean-only helpers (file-qualified) -/

/-- Rocq `from_option`. -/
def AxWp.fromOption {A PROP : Type _} (f : A → PROP) (d : PROP) : Option A → PROP
  | some a => f a
  | none => d

section annotHelpers
variable {GF : BundledGFunctors}

theorem AxWp.eqWand (P Q : IProp GF) : iprop(P ≡ Q) ⊢ □ (P -∗ Q) := by
  iintro #H
  imodintro
  iintro HP
  icases internalEq_iff P Q $$ H with ⟨H1, -⟩
  iapply H1
  iexact HP

theorem AxWp.singletonUnionMem {A : Type _} [Ord A] [Std.TransOrd A] [Std.LawfulEqOrd A]
    (x : A) (X : GSet A) (h : x ∈ X) : ({x} : GSet A) ∪ X = X := by
  rw [setEq]
  intro y
  rw [elemOfUnion, elemOfSingleton]
  constructor
  · rintro (rfl | hy)
    · exact h
    · exact hy
  · exact .inr

/-- Single-key monotonicity of `[∗map] x ∈ m, x`. -/
theorem AxWp.bigSepMInsertWand (m : GMapF GName (IProp GF)) (n : GName) (R R' : IProp GF)
    (h : get? m n = some R) :
    iprop(R -∗ R') ∗ ([∗map] x ∈ m, x) ⊢ [∗map] x ∈ insert m n R', x := by
  iintro ⟨Hw, Hm⟩
  icases (BigSepM.bigSepM_delete h).1 $$ Hm with ⟨HR, Hm⟩
  iapply BigSepM.bigSepM_insert_delete.2
  isplitl [Hw HR]
  · iapply Hw
    iexact HR
  · iexact Hm

/-- Taking a key's content out, leaving `emp`. -/
theorem AxWp.bigSepMExtract (m : GMapF GName (IProp GF)) (n : GName) (R : IProp GF)
    (h : get? m n = some R) :
    ([∗map] x ∈ m, x) ⊢ R ∗ [∗map] x ∈ insert m n iprop(emp), x := by
  iintro Hm
  icases (BigSepM.bigSepM_delete h).1 $$ Hm with ⟨HR, Hm⟩
  iframe HR
  iapply BigSepM.bigSepM_insert_delete.2
  isplitr
  · itrivial
  · iexact Hm

variable [AxannotGS GF]

theorem AxWp.bagFragIn (gn n' : GName) (S : GSet GName) :
    iOwn (E := AxannotG.axannotSetG) gn (● (DisjointLeibnizSet.valid S)) ∗
      iOwn (E := AxannotG.axannotSetG) gn (◯ (DisjointLeibnizSet.valid ({n'} : GSet GName)))
      ⊢@{IProp GF} ⌜n' ∈ S⌝ := by
  iintro ⟨Ha, Hf⟩
  icases iOwn_cmraValid_op $$ [$Ha $Hf] with %hv
  ipureintro
  have h := (Auth.auth_both_valid_discrete.mp hv).1
  have h2 := DisjointLeibnizSet.included_iff_subset.mp h
  exact h2 n' (elemOfSingleton.2 rfl)

theorem AxWp.bagFragNe (gn a b : GName) :
    iOwn (E := AxannotG.axannotSetG) gn (◯ (DisjointLeibnizSet.valid ({a} : GSet GName))) ∗
      iOwn (E := AxannotG.axannotSetG) gn (◯ (DisjointLeibnizSet.valid ({b} : GSet GName)))
      ⊢@{IProp GF} ⌜a ≠ b⌝ := by
  iintro ⟨Ha, Hb⟩
  icases iOwn_cmraValid_op $$ [$Ha $Hb] with %hv
  ipureintro
  rw [← Auth.frag_op] at hv
  have h := DisjointLeibnizSet.valid_op_iff_disj.mp (Auth.frag_valid.mp hv)
  intro hab
  subst hab
  exact h a ⟨elemOfSingleton.2 rfl, elemOfSingleton.2 rfl⟩

/-- Closing the interpretation after one event's bag changed. -/
theorem AxWp.annotClose (annot : GMapF Geid GName) (m : Mea GF) (e : Geid) (gn : GName)
    (P' : IProp GF) (Hlk : get? annot e = some gn)
    (Hdom : (FiniteMap.dom_set annot : GSet Geid) = FiniteMap.dom_set m) :
    ghost_map_auth (AxannotGS.axannotName (GF := GF)) (DFrac.own 1) annot ∗
      AxAnnot.bagInv gn P' ∗
      ([∗map] k ↦ y1;y2 ∈ delete annot e;delete m e, AxAnnot.bagInv y1 y2)
      ⊢ AxAnnot.annotInterp (insert m e P') := by
  unfold AxAnnot.annotInterp
  iintro ⟨Hauth, Hb, Hrest⟩
  iexists annot
  iframe Hauth
  isplitr
  · ipureintro
    rw [domInsert, ← Hdom]
    exact (AxWp.singletonUnionMem e _ (elemOfDom2 Hlk)).symm
  · have h := (BigSepM2.bigSepM2_insert_delete (Φ := fun _ gn P => AxAnnot.bagInv gn P)
      (m1 := annot) (m2 := m) (i := e) (x1 := gn) (x2 := P')).2
    rw [insertId Hlk] at h
    iapply h
    isplitl [Hb]
    · iexact Hb
    · iexact Hrest

/-- Opening the interpretation at one event's bag. -/
theorem AxWp.annotOpen (m : Mea GF) (e : Geid) (gn : GName) :
    AxAnnot.annotInterp m ∗ ghost_map_elem (AxannotGS.axannotName (GF := GF)) DFrac.discard e gn ⊢
      ∃ P, ⌜get? m e = some P⌝ ∗ AxAnnot.bagInv gn P ∗
        (∀ P', AxAnnot.bagInv gn P' -∗ AxAnnot.annotInterp (insert m e P')) := by
  unfold AxAnnot.annotInterp
  iintro ⟨⟨%annot, Hauth, %Hdom, Hmap⟩, Hel⟩
  ihave %Hlk := ghost_map_lookup $$ Hauth Hel
  have hm : (get? m e).isSome := by
    have : e ∈ (FiniteMap.dom_set m : GSet Geid) := Hdom ▸ elemOfDom2 Hlk
    exact elemOfDom.1 this
  obtain ⟨P, hP⟩ := Option.isSome_iff_exists.1 hm
  icases (BigSepM2.bigSepM2_delete (Φ := fun _ gn P => AxAnnot.bagInv gn P) Hlk hP).1 $$ Hmap
    with ⟨Hbag, Hrest⟩
  iexists P
  isplitr
  · ipureintro
    exact hP
  iframe Hbag
  iintro %P' Hb
  have hc := AxWp.annotClose annot m e gn P' Hlk Hdom
  unfold AxAnnot.annotInterp at hc
  iapply hc
  iframe Hauth Hb Hrest

theorem AxWp.annotCloseSame (m : Mea GF) (e : Geid) (gn : GName) (P : IProp GF)
    (hP : get? m e = some P) :
    iprop(∀ P', AxAnnot.bagInv gn P' -∗ AxAnnot.annotInterp (insert m e P')) ∗ AxAnnot.bagInv gn P
      ⊢ AxAnnot.annotInterp m := by
  have h : AxAnnot.annotInterp (GF := GF) (insert m e P) = AxAnnot.annotInterp m := by
    rw [insertId hP]
  rw [← h]
  iintro ⟨H, Hb⟩
  iapply H
  iexact Hb

theorem AxWp.bagFragInW (gn n' : GName) (S : GSet GName) :
    ⊢@{IProp GF} iOwn (E := AxannotG.axannotSetG) gn (● (DisjointLeibnizSet.valid S)) -∗
      iOwn (E := AxannotG.axannotSetG) gn (◯ (DisjointLeibnizSet.valid ({n'} : GSet GName))) -∗
      ⌜n' ∈ S⌝ := by
  iintro Ha Hf
  iapply AxWp.bagFragIn gn n' S
  iframe Ha Hf

theorem AxWp.bagFragNeW (gn a b : GName) :
    ⊢@{IProp GF} iOwn (E := AxannotG.axannotSetG) gn (◯ (DisjointLeibnizSet.valid ({a} : GSet GName))) -∗
      iOwn (E := AxannotG.axannotSetG) gn (◯ (DisjointLeibnizSet.valid ({b} : GSet GName))) -∗
      ⌜a ≠ b⌝ := by
  iintro Ha Hb
  iapply AxWp.bagFragNe gn a b
  iframe Ha Hb

theorem AxWp.savedPropAgreeW (γ : GName) (dq1 dq2 : DFrac) (P Q : IProp GF) :
    ⊢@{IProp GF} saved_prop_own γ dq1 P -∗ saved_prop_own γ dq2 Q -∗ ▷ (P ≡ Q) := by
  iintro H1 H2
  iapply saved_prop_agree γ dq1 dq2 P Q
  iframe H1 H2

end annotHelpers

instance AxWp.fromOptionPersistent {A : Type _} {GF : BundledGFunctors} (f : A → IProp GF)
    (d : IProp GF) (o : Option A) [∀ a, Persistent (f a)] [Persistent d] :
    Persistent (AxWp.fromOption f d o) := by
  cases o <;> simp only [AxWp.fromOption] <;> infer_instance

section annotLemmas
variable {GF : BundledGFunctors} [AxannotGS GF]

/-- Rocq `annot_lookup_bag` (local): the bag of `e` holds the fragment the assertion names. -/
theorem annotLookupBag (m : Mea GF) (e : Geid) (gn n' : GName) :
    ⊢ AxAnnot.annotInterp m -∗
      ghost_map_elem (AxannotGS.axannotName (GF := GF)) DFrac.discard e gn -∗
      iOwn (E := AxannotG.axannotSetG) gn (◯ (DisjointLeibnizSet.valid ({n'} : GSet GName))) -∗
      ∃ P, ⌜get? m e = some P⌝ := by
  iintro Hint Hel _
  icases AxWp.annotOpen m e gn $$ [$Hint $Hel] with ⟨%P, %hP, -, -⟩
  iexists P
  ipureintro
  exact hP

theorem AxWp.mergeWand (res : GMapF GName (IProp GF)) (gn gn' : GName) (R R' P Q P0 : IProp GF)
    (hne : gn ≠ gn') (hR : get? res gn = some R) (hR' : get? res gn' = some R') :
    iprop(▷ □ (P0 -∗ [∗map] x ∈ res, x)) ∗ iprop(▷ (P ≡ R)) ∗ iprop(▷ (Q ≡ R')) ⊢
      ▷ □ (P0 -∗ [∗map] x ∈ insert (insert res gn' iprop(emp)) gn iprop(P ∗ Q), x) := by
  iintro ⟨#H0, #H1, #H2⟩
  inext
  imodintro
  iintro HP0
  ihave Hres := H0 $$ HP0
  icases AxWp.bigSepMExtract res gn' R' hR' $$ Hres with ⟨HR', Hres⟩
  have hlk : get? (insert res gn' iprop(emp)) gn = some R := by
    rw [lookupInsertNe (Ne.symm hne)]; exact hR
  iapply AxWp.bigSepMInsertWand _ gn R _ hlk
  iframe Hres
  iintro HR
  ihave #H1s := internalEq.symm $$ H1
  ihave #H2s := internalEq.symm $$ H2
  ihave #W1 := AxWp.eqWand R P $$ H1s
  ihave #W2 := AxWp.eqWand R' Q $$ H2s
  isplitl [HR]
  · iapply W1
    iexact HR
  · iapply W2
    iexact HR'

theorem annotMerge (e : Geid) (P Q : IProp GF) :
    ⊢ AxAnnot.annotOwn e P -∗ AxAnnot.annotOwn e Q -∗
      ∀ na, AxAnnot.annotInterp na ==∗ AxAnnot.annotOwn e iprop(P ∗ Q) ∗ AxAnnot.annotInterp na := by
  unfold AxAnnot.annotOwn
  iintro ⟨%n, %gn, #Hel, Hset, Hprop⟩ ⟨%n2, %gn', #Hel', Hset', Hprop'⟩
  ihave %hn := ghost_map_elem_agree _ e _ _ n n2 $$ [$Hel $Hel']
  subst hn
  iintro %na Hint
  icases AxWp.annotOpen na e n $$ [$Hint $Hel] with ⟨%P0, %hP0, Hbag, Hclose⟩
  iunfold AxAnnot.bagInv at Hbag
  icases Hbag with ⟨%res, Hauth, Hmap, #Hsep⟩
  ihave %hin := AxWp.bagFragInW n gn _ $$ Hauth Hset
  ihave %hin' := AxWp.bagFragInW n gn' _ $$ Hauth Hset'
  ihave %hne := AxWp.bagFragNeW n gn gn' $$ Hset Hset'
  obtain ⟨R, hR⟩ := Option.isSome_iff_exists.1 (elemOfDom.1 hin)
  obtain ⟨R', hR'⟩ := Option.isSome_iff_exists.1 (elemOfDom.1 hin')
  icases (BigSepM.bigSepM_delete hR).1 $$ Hmap with ⟨Hsp, Hmap⟩
  have hR'd : get? (delete res gn) gn' = some R' := by rw [lookupDeleteNe hne]; exact hR'
  icases (BigSepM.bigSepM_delete hR'd).1 $$ Hmap with ⟨Hsp', Hmap⟩
  ihave #Heq := AxWp.savedPropAgreeW gn _ _ P R $$ Hprop Hsp
  ihave #Heq' := AxWp.savedPropAgreeW gn' _ _ Q R' $$ Hprop' Hsp'
  imod saved_prop_update_halves iprop(P ∗ Q) gn P R $$ [$Hprop $Hsp] with ⟨Hprop1, Hprop2⟩
  imod saved_prop_update_halves iprop(emp) gn' Q R' $$ [$Hprop' $Hsp'] with ⟨Hprop1', Hprop2'⟩
  imodintro
  isplitl [Hset Hprop2]
  · iexists n, gn
    iframe Hel Hset Hprop2
  · iapply AxWp.annotCloseSame na e n P0 hP0
    iframe Hclose
    iunfold AxAnnot.bagInv
    iexists (insert (insert res gn' iprop(emp)) gn iprop(P ∗ Q))
    have hdom : (FiniteMap.dom_set (insert (insert res gn' iprop(emp)) gn iprop(P ∗ Q)) :
        GSet GName) = FiniteMap.dom_set res := by
      rw [domInsert, domInsert, AxWp.singletonUnionMem gn' _ hin', AxWp.singletonUnionMem gn _ hin]
    rw [hdom]
    iframe Hauth
    isplitl [Hprop1 Hprop1' Hmap]
    · iapply BigSepM.bigSepM_insert_delete.2
      rw [deleteInsertNe hne]
      isplitl [Hprop1]
      · iexact Hprop1
      · iapply BigSepM.bigSepM_insert_delete.2
        isplitl [Hprop1']
        · iexact Hprop1'
        · iexact Hmap
    · iapply AxWp.mergeWand res gn gn' R R' P Q P0 hne hR hR'
      iframe Hsep Heq Heq'

theorem AxWp.agreeWand (res : GMapF GName (IProp GF)) (gn : GName) (R P P0 : IProp GF)
    (hR : get? res gn = some R) :
    iprop(▷ □ (P0 -∗ [∗map] x ∈ res, x)) ∗ iprop(▷ (P ≡ R)) ⊢ ▷ □ (P0 -∗ P) := by
  iintro ⟨#H0, #H1⟩
  inext
  imodintro
  iintro HP0
  ihave Hres := H0 $$ HP0
  icases (BigSepM.bigSepM_delete hR).1 $$ Hres with ⟨HR, -⟩
  ihave #H1s := internalEq.symm $$ H1
  ihave #W1 := AxWp.eqWand R P $$ H1s
  iapply W1
  iexact HR

theorem annotAgree (m : Mea GF) (e : Geid) (P : IProp GF) :
    ⊢ AxAnnot.annotInterp m -∗ AxAnnot.annotOwn e P -∗
      ⌜e ∈ (FiniteMap.dom_set m : GSet Geid)⌝ ∗
      AxWp.fromOption (fun P' => iprop(▷ □ (P' -∗ P))) iprop(emp) (get? m e) := by
  iintro Hint Hown
  unfold AxAnnot.annotOwn
  icases Hown with ⟨%n, %n', #Hel, Hset, Hprop⟩
  icases AxWp.annotOpen m e n $$ [$Hint $Hel] with ⟨%P0, %hP0, Hbag, -⟩
  iunfold AxAnnot.bagInv at Hbag
  icases Hbag with ⟨%res, Hauth, Hmap, #Hsep⟩
  ihave %hin := AxWp.bagFragInW n n' _ $$ Hauth Hset
  obtain ⟨R, hR⟩ := Option.isSome_iff_exists.1 (elemOfDom.1 hin)
  icases (BigSepM.bigSepM_delete hR).1 $$ Hmap with ⟨Hsp, -⟩
  ihave #Heq := AxWp.savedPropAgreeW n' _ _ P R $$ Hprop Hsp
  isplitr
  · ipureintro
    exact elemOfDom2 hP0
  · rw [hP0]
    simp only [AxWp.fromOption]
    iapply AxWp.agreeWand res n' R P P0 hR
    iframe Hsep Heq

theorem annotAgreeBig (m m' : Mea GF) :
    ⊢ AxAnnot.annotInterp m -∗ ([∗map] e ↦ P ∈ m', AxAnnot.annotOwn e P) -∗
      ⌜(FiniteMap.dom_set m' : GSet Geid) ⊆ FiniteMap.dom_set m⌝ ∗
      [∗map] e ↦ R ∈ m', AxWp.fromOption (fun P' => iprop(▷ □ (P' -∗ R))) iprop(emp) (get? m e) := by
  induction m' using mapInd with
  | hemp =>
    iintro _ _
    isplitr
    · ipureintro
      rw [domEmpty]
      exact fun x hx => absurd hx (fun h => (elemOfEmpty (S := GSet Geid)).1 h)
    · iapply BigSepM.bigSepM_empty.2
      itrivial
  | hins e P m' hnone IH =>
    iintro Hann Hm
    icases (BigSepM.bigSepM_insert hnone).1 $$ Hm with ⟨H, Hm⟩
    ihave ⟨%hd1, #Hq⟩ := annotAgree m e P $$ Hann H
    ihave ⟨%hd2, IH'⟩ := IH $$ Hann Hm
    isplitr
    · ipureintro
      rw [domInsert]
      intro x hx
      rcases elemOfUnion.1 hx with h | h
      · rw [elemOfSingleton.1 h]; exact hd1
      · exact hd2 x h
    · iapply (BigSepM.bigSepM_insert hnone).2
      iframe Hq IH'

theorem AxWp.detachWand (res : GMapF GName (IProp GF)) (gn : GName) (R P P0 : IProp GF)
    (hR : get? res gn = some R) :
    iprop(▷ □ (P0 -∗ [∗map] x ∈ res, x)) ∗ iprop(▷ (P ≡ R)) ⊢
      ▷ □ (P0 -∗ P ∗ [∗map] y ∈ delete res gn, y) := by
  iintro ⟨#H0, #H1⟩
  inext
  imodintro
  iintro HP0
  ihave Hres := H0 $$ HP0
  icases (BigSepM.bigSepM_delete hR).1 $$ Hres with ⟨HR, Hres⟩
  ihave #H1s := internalEq.symm $$ H1
  ihave #W1 := AxWp.eqWand R P $$ H1s
  iframe Hres
  iapply W1
  iexact HR

/-- Detaching `P` from `e`: the annotation keeps the remainder `R`. -/
theorem annotDetach (m : Mea GF) (e : Geid) (P : IProp GF) :
    ⊢ AxAnnot.annotInterp m -∗ AxAnnot.annotOwn e P ==∗
      ∃ R, AxAnnot.annotInterp (insert m e R) ∗
        AxWp.fromOption (fun P' => iprop(▷ □ (P' -∗ P ∗ R))) iprop(emp) (get? m e) := by
  iintro Hint Hown
  unfold AxAnnot.annotOwn
  icases Hown with ⟨%n, %gn, #Hel, Hset, Hprop⟩
  icases AxWp.annotOpen m e n $$ [$Hint $Hel] with ⟨%P0, %hP0, Hbag, Hclose⟩
  iunfold AxAnnot.bagInv at Hbag
  icases Hbag with ⟨%res, Hauth, Hmap, #Hsep⟩
  ihave %hin := AxWp.bagFragInW n gn _ $$ Hauth Hset
  obtain ⟨R', hR'⟩ := Option.isSome_iff_exists.1 (elemOfDom.1 hin)
  icases (BigSepM.bigSepM_delete hR').1 $$ Hmap with ⟨Hsp, Hmap⟩
  ihave #Heq := AxWp.savedPropAgreeW gn _ _ P R' $$ Hprop Hsp
  imod saved_prop_update_halves iprop(emp) gn P R' $$ [$Hprop $Hsp] with ⟨Hprop1, Hprop2⟩
  imodintro
  iexists iprop([∗map] y ∈ delete res gn, y)
  rw [hP0]
  simp only [AxWp.fromOption]
  isplitl [Hclose Hauth Hprop1 Hmap]
  · iapply Hclose
    iunfold AxAnnot.bagInv
    iexists (insert res gn iprop(emp))
    have hdom : (FiniteMap.dom_set (insert res gn iprop(emp)) : GSet GName) =
        FiniteMap.dom_set res := by
      rw [domInsert, AxWp.singletonUnionMem gn _ hin]
    rw [hdom]
    iframe Hauth
    isplitl [Hprop1 Hmap]
    · iapply BigSepM.bigSepM_insert_delete.2
      iframe Hprop1 Hmap
    · inext
      imodintro
      iintro HR
      iapply BigSepM.bigSepM_insert_delete.2
      isplitr
      · itrivial
      · iexact HR
  · iapply AxWp.detachWand res gn R' P P0 hR'
    iframe Hsep Heq

theorem annotDetachBig (m m' : Mea GF) :
    ⊢ AxAnnot.annotInterp m -∗ ([∗map] e ↦ P ∈ m', AxAnnot.annotOwn e P) ==∗
      ∃ m'' : Mea GF, ⌜(FiniteMap.dom_set m'' : GSet Geid) = FiniteMap.dom_set m'⌝ ∗
        AxAnnot.annotInterp (PartialMap.union m'' m) ∗
        ([∗map] e ↦ R;R' ∈ m';m'',
          AxWp.fromOption (fun P' => iprop(▷ □ (P' -∗ R ∗ R'))) iprop(emp) (get? m e)) := by
  induction m' using mapInd with
  | hemp =>
    iintro Hann _
    imodintro
    iexists (∅ : Mea GF)
    isplitr
    · ipureintro
      rfl
    · have h : PartialMap.union (∅ : Mea GF) m = m := mapUnionEmptyL (M := GMapF Geid) (m := m)
      rw [h]
      iframe Hann
      iapply (BigSepM2.bigSepM2_empty _).2
      itrivial
  | hins e P m' hnone IH =>
    iintro Hann Hm
    icases (BigSepM.bigSepM_insert hnone).1 $$ Hm with ⟨Hi, Hm⟩
    imod IH $$ Hann Hm with ⟨%m'', %Hdom, Hann, Hequiv⟩
    imod annotDetach (PartialMap.union m'' m) e P $$ Hann Hi with ⟨%R, Hann, Hi⟩
    imodintro
    have hn'' : get? m'' e = none := by
      apply notElemOfDom1 (S := GSet Geid)
      rw [Hdom]
      exact notElemOfDom2 hnone
    iexists (insert m'' e R)
    isplitr
    · ipureintro
      rw [domInsert, domInsert, Hdom]
    · have h : insert (PartialMap.union m'' m) e R = PartialMap.union (insert m'' e R) m :=
        insertUnionL (M := GMapF Geid) (m1 := m'') (m2 := m)
      rw [← h]
      iframe Hann
      iapply (BigSepM2.bigSepM2_insert hnone hn'').2
      have hl : get? (PartialMap.union m'' m) e = get? m e := lookupUnionR hn''
      rw [hl]
      iframe Hi Hequiv

/-- Allocating a fresh annotation at an event not yet in the map. -/
theorem annotAlloc (na : Mea GF) (e : Geid) (P : IProp GF) :
    e ∉ (FiniteMap.dom_set na : GSet Geid) →
    ⊢ AxAnnot.annotInterp na ==∗ AxAnnot.annotInterp (insert na e P) ∗ AxAnnot.annotOwn e P := by
  intro Hnin
  iintro Hann
  unfold AxAnnot.annotInterp
  icases Hann with ⟨%annot, Hauth, %Hdom, Hmap⟩
  imod saved_prop_alloc P (DFrac.own 1) DFrac.valid_own_one with ⟨%γ, Hnew⟩
  have hv : ✓ ((● (DisjointLeibnizSet.valid ({γ} : GSet GName)) : AxannotSetR) •
      ◯ (DisjointLeibnizSet.valid ({γ} : GSet GName))) :=
    Auth.auth_both_valid_discrete.mpr
      ⟨DisjointLeibnizSet.included_iff_subset.mpr (fun _ h => h), DisjointLeibnizSet.valid_set⟩
  imod iOwn_alloc (E := AxannotG.axannotSetG) _ hv with ⟨%gn, Hset⟩
  icases iOwn_op.1 $$ Hset with ⟨Hseta, Hsetf⟩
  have hnone : get? annot e = none := by
    apply notElemOfDom1 (S := GSet Geid)
    rw [Hdom]
    exact Hnin
  imod ghost_map_insert_persist e gn hnone $$ Hauth with ⟨Hauth, #Hel⟩
  imodintro
  have hsplit := (saved_prop_fractional γ P).fractional (Qp.half 1) (Qp.half 1)
  rw [Qp.half_add_half 1] at hsplit
  icases hsplit.1 $$ Hnew with ⟨Hp1, Hp2⟩
  isplitl [Hauth Hmap Hseta Hp1]
  · iexists (insert annot e gn)
    iframe Hauth
    isplitr
    · ipureintro
      rw [domInsert, domInsert, Hdom]
    · iapply (BigSepM2.bigSepM2_insert hnone (notElemOfDom1 (S := GSet Geid) Hnin)).2
      iframe Hmap
      iunfold AxAnnot.bagInv
      iexists ({[γ := P]} : GMapF GName (IProp GF))
      rw [domSingleton]
      iframe Hseta
      isplitl [Hp1]
      · iapply BigSepM.bigSepM_singleton.2
        iexact Hp1
      · inext
        imodintro
        iintro HP
        iapply BigSepM.bigSepM_singleton.2
        iexact HP
  · unfold AxAnnot.annotOwn
    iexists gn, γ
    iframe Hel Hsetf Hp2

theorem AxWp.splitWand (res : GMapF GName (IProp GF)) (gn gnp : GName) (R P Q P0 : IProp GF)
    (hR : get? res gn = some R) (hfresh : get? res gnp = none) :
    iprop(▷ □ (P0 -∗ [∗map] x ∈ res, x)) ∗ iprop(▷ (iprop(P ∗ Q) ≡ R)) ⊢
      ▷ □ (P0 -∗ [∗map] x ∈ insert (insert res gn Q) gnp P, x) := by
  have hne : gn ≠ gnp := by intro h; subst h; rw [hR] at hfresh; cases hfresh
  have hfr' : get? (insert res gn Q) gnp = none := by rw [lookupInsertNe hne]; exact hfresh
  iintro ⟨#H0, #H1⟩
  inext
  imodintro
  iintro HP0
  ihave Hres := H0 $$ HP0
  icases (BigSepM.bigSepM_delete hR).1 $$ Hres with ⟨HR, Hres⟩
  ihave #H1s := internalEq.symm $$ H1
  ihave #W1 := AxWp.eqWand R iprop(P ∗ Q) $$ H1s
  ihave HPQ := W1 $$ HR
  icases HPQ with ⟨HP, HQ⟩
  iapply (BigSepM.bigSepM_insert hfr').2
  iframe HP
  iapply BigSepM.bigSepM_insert_delete.2
  iframe HQ Hres

theorem annotSplit (e : Geid) (P Q : IProp GF) :
    ⊢ AxAnnot.annotOwn e iprop(P ∗ Q) -∗
      ∀ na, AxAnnot.annotInterp na ==∗
        (AxAnnot.annotOwn e P ∗ AxAnnot.annotOwn e Q) ∗ AxAnnot.annotInterp na := by
  unfold AxAnnot.annotOwn
  iintro ⟨%n, %gn, #Hel, Hset, Hprop⟩ %na Hint
  icases AxWp.annotOpen na e n $$ [$Hint $Hel] with ⟨%P0, %hP0, Hbag, Hclose⟩
  iunfold AxAnnot.bagInv at Hbag
  icases Hbag with ⟨%res, Hauth, Hmap, #Hsep⟩
  ihave %hin := AxWp.bagFragInW n gn _ $$ Hauth Hset
  obtain ⟨R, hR⟩ := Option.isSome_iff_exists.1 (elemOfDom.1 hin)
  icases (BigSepM.bigSepM_delete hR).1 $$ Hmap with ⟨Hsp, Hmap⟩
  ihave #Heq := AxWp.savedPropAgreeW gn _ _ iprop(P ∗ Q) R $$ Hprop Hsp
  imod saved_prop_alloc_cofinite (FiniteSet.toList (FiniteMap.dom_set res : GSet GName)) P
    (DFrac.own 1) DFrac.valid_own_one with ⟨%gnp, %Hnin, Hnew⟩
  imod saved_prop_update_halves Q gn iprop(P ∗ Q) R $$ [$Hprop $Hsp] with ⟨Hprop1, Hprop2⟩
  have hsplit := (saved_prop_fractional gnp P).fractional (Qp.half 1) (Qp.half 1)
  rw [Qp.half_add_half 1] at hsplit
  icases hsplit.1 $$ Hnew with ⟨Hp1, Hp2⟩
  have hfresh : gnp ∉ (FiniteMap.dom_set res : GSet GName) := fun h => Hnin (elemOfElements.2 h)
  have hfr : get? res gnp = none := notElemOfDom1 (S := GSet GName) hfresh
  have hdisj : ({gnp} : GSet GName) ## FiniteMap.dom_set res := by
    rw [elemOfDisjoint]
    intro x hx hx'
    rw [elemOfSingleton.1 hx] at hx'
    exact hfresh hx'
  have hupd : (● (DisjointLeibnizSet.valid (FiniteMap.dom_set res : GSet GName)) : AxannotSetR) ~~>
      (● (DisjointLeibnizSet.valid (({gnp} : GSet GName) ∪ FiniteMap.dom_set res))) •
        ◯ (DisjointLeibnizSet.valid ({gnp} : GSet GName)) :=
    Auth.auth_update_alloc (DisjointLeibnizSet.localUpdate_alloc_empty_of_disj _ _ hdisj)
  imod iOwn_update hupd $$ Hauth with Hauth
  icases iOwn_op.1 $$ Hauth with ⟨Hauth, Hset'⟩
  imodintro
  isplitl [Hset Hset' Hprop2 Hp2]
  · isplitl [Hset' Hp2]
    · iexists n, gnp
      iframe Hel Hset' Hp2
    · iexists n, gn
      iframe Hel Hset Hprop2
  · iapply AxWp.annotCloseSame na e n P0 hP0
    iframe Hclose
    iunfold AxAnnot.bagInv
    iexists (insert (insert res gn Q) gnp P)
    have hdom : (FiniteMap.dom_set (insert (insert res gn Q) gnp P) : GSet GName) =
        ({gnp} : GSet GName) ∪ FiniteMap.dom_set res := by
      rw [domInsert, domInsert, AxWp.singletonUnionMem gn _ hin]
    rw [hdom]
    iframe Hauth
    have hne : gn ≠ gnp := by intro h; subst h; rw [hR] at hfr; cases hfr
    have hfr' : get? (insert res gn Q) gnp = none := by rw [lookupInsertNe hne]; exact hfr
    isplitl [Hprop1 Hp1 Hmap]
    · iapply (BigSepM.bigSepM_insert hfr').2
      iframe Hp1
      iapply BigSepM.bigSepM_insert_delete.2
      iframe Hprop1 Hmap
    · iapply AxWp.splitWand res gn gnp R P Q P0 hR hfr
      iframe Hsep Heq

theorem AxWp.updateWand (res : GMapF GName (IProp GF)) (gn : GName) (R P Q P0 : IProp GF)
    (hR : get? res gn = some R) :
    iprop(□ (P -∗ Q)) ∗ iprop(▷ □ (P0 -∗ [∗map] x ∈ res, x)) ∗ iprop(▷ (P ≡ R)) ⊢
      ▷ □ (P0 -∗ [∗map] x ∈ insert res gn Q, x) := by
  iintro ⟨#HPQ, #H0, #H1⟩
  inext
  imodintro
  iintro HP0
  ihave Hres := H0 $$ HP0
  icases (BigSepM.bigSepM_delete hR).1 $$ Hres with ⟨HR, Hres⟩
  ihave #H1s := internalEq.symm $$ H1
  ihave #W1 := AxWp.eqWand R P $$ H1s
  iapply BigSepM.bigSepM_insert_delete.2
  iframe Hres
  iapply HPQ
  iapply W1
  iexact HR

/-- Weakening an annotation under a persistent wand (the source's `annot_wand`). -/
theorem annotUpdate (e : Geid) (P Q : IProp GF) :
    iprop(□ (P -∗ Q)) ⊢
      AxAnnot.annotOwn e P -∗ ∀ na, AxAnnot.annotInterp na ==∗
        AxAnnot.annotOwn e Q ∗ AxAnnot.annotInterp na := by
  unfold AxAnnot.annotOwn
  iintro #HPQ ⟨%n, %gn, #Hel, Hset, Hprop⟩ %na Hint
  icases AxWp.annotOpen na e n $$ [$Hint $Hel] with ⟨%P0, %hP0, Hbag, Hclose⟩
  iunfold AxAnnot.bagInv at Hbag
  icases Hbag with ⟨%res, Hauth, Hmap, #Hsep⟩
  ihave %hin := AxWp.bagFragInW n gn _ $$ Hauth Hset
  obtain ⟨R, hR⟩ := Option.isSome_iff_exists.1 (elemOfDom.1 hin)
  icases (BigSepM.bigSepM_delete hR).1 $$ Hmap with ⟨Hsp, Hmap⟩
  ihave #Heq := AxWp.savedPropAgreeW gn _ _ P R $$ Hprop Hsp
  imod saved_prop_update_halves Q gn P R $$ [$Hprop $Hsp] with ⟨Hprop1, Hprop2⟩
  imodintro
  isplitl [Hset Hprop2]
  · iexists n, gn
    iframe Hel Hset Hprop2
  · iapply AxWp.annotCloseSame na e n P0 hP0
    iframe Hclose
    iunfold AxAnnot.bagInv
    iexists (insert res gn Q)
    have hdom : (FiniteMap.dom_set (insert res gn Q) : GSet GName) = FiniteMap.dom_set res := by
      rw [domInsert, AxWp.singletonUnionMem gn _ hin]
    rw [hdom]
    iframe Hauth
    isplitl [Hprop1 Hmap]
    · iapply BigSepM.bigSepM_insert_delete.2
      iframe Hprop1 Hmap
    · iapply AxWp.updateWand res gn R P Q P0 hR
      iframe HPQ Hsep Heq

theorem annotEntail (e : Geid) (P Q : IProp GF) (HPQ : P ⊢ Q) :
    ⊢ AxAnnot.annotOwn e P -∗ ∀ na, AxAnnot.annotInterp na ==∗
        AxAnnot.annotOwn e Q ∗ AxAnnot.annotInterp na := by
  have h : ⊢ iprop(□ (P -∗ Q)) := by
    iintro !>
    iintro HP
    iapply HPQ
    iexact HP
  exact h.trans (annotUpdate e P Q)

end annotLemmas

/-- The empty interpretation, allocating the map's name. -/
theorem annotInterpAlloc {GF : BundledGFunctors} [AxannotG GF] :
    ⊢ |==> ∃ γ : GName, @AxAnnot.annotInterp GF { axannotName := γ } (∅ : Mea GF) := by
  imod (ghost_map_alloc_empty (GF := GF) (K := Geid) (V := GName) (H := GMapF Geid))
    with ⟨%γ, Hauth⟩
  imodintro
  iexists γ
  unfold AxAnnot.annotInterp
  iexists (∅ : GMapF Geid GName)
  iframe Hauth
  isplitr
  · ipureintro
    rw [domEmpty, domEmpty]
  · iapply (BigSepM2.bigSepM2_empty _).2
    itrivial

/-! # 3. The interface parameters (port of AxSL `low/iris.v`) -/

class AxirisG (GF : BundledGFunctors) where
  /-- interpretation of the annotation map -/
  annotInterp : Mea GF → IProp GF
  /-- graph agreement -/
  gconstInterp : Gdexec → IProp GF
  /-- the logical state updated along the phase-2 order, and its interpretation over the set of
  already-validated events -/
  obSt : Type
  obStInterp : Gdexec → obSt → GSet Geid → IProp GF
  /-- the per-hart logical state -/
  logTsT : Type
  localInterp : Gdexec → Agent → Nat → logTsT → IProp GF

/-- The policies of design §1-L1, deviations 1 and 2. -/
class Axpol where
  /-- the handout policy -/
  sPol : Gdexec → Geid → GSet Geid
  /-- the local flow set lob′ -/
  lobp : Gdexec → Geid → GSet Geid

/-- The checkpoint predicate (T4). -/
class AxirisGChk (GF : BundledGFunctors) where
  chk : Agent → Athread → IProp GF
  chkMidInstr : ∀ i s, ¬ AxWp.atBoundary s → iprop(True) ⊢ chk i s

/-! # 4. Annotation-map predicates and the `|=i=>` modality -/

section na
variable {GF : BundledGFunctors}

/-- `na` is in sync with the position: its local part is exactly the hart's memory events
before `k`. -/
def naAtProgress (GD : Gdexec) (i : Agent) (k : Nat) (na : Mea GF) : IProp GF :=
  iprop(⌜FiniteSet.filter (fun e : Geid => decide (e.1 = i)) (FiniteMap.dom_set na : GSet Geid) =
    eidsBefore GD i k⌝)

theorem naAtProgressNotElemOf (GD : Gdexec) (i : Agent) (k : Nat) (na : Mea GF) :
    naAtProgress GD i k na ⊢ ⌜(i, k) ∉ (FiniteMap.dom_set na : GSet Geid)⌝ := by
  unfold naAtProgress
  iintro %Hna
  ipureintro
  intro Hin
  have Hf : (i, k) ∈ FiniteSet.filter (fun e : Geid => decide (e.1 = i))
      (FiniteMap.dom_set na : GSet Geid) := elemOfFilter.2 ⟨by simp, Hin⟩
  rw [Hna, elemOfEidsBefore] at Hf
  exact Nat.lt_irrefl _ Hf.2.1

/-- `naUsed`/`naUnused` split the fragment of `na` on `sLob`. -/
def naSplittingWf (sLob : GSet Geid) (na naUsed naUnused : Mea GF) : IProp GF :=
  iprop(⌜(FiniteMap.dom_set naUsed : GSet Geid) ⊆ sLob⌝ ∗
    [∗map] e ↦ Pu;Puu ∈ naUsed;naUnused,
      ▷ □ (AxWp.fromOption (fun P => P) iprop(emp) (get? na e) -∗ Pu ∗ Puu))

instance naSplittingWfPersistent (sLob : GSet Geid) (na naUsed naUnused : Mea GF) :
    Persistent (naSplittingWf sLob na naUsed naUnused) := by
  unfold naSplittingWf; infer_instance

theorem naSplittingWfDom (sLob : GSet Geid) (na naUsed naUnused : Mea GF) :
    naSplittingWf sLob na naUsed naUnused ⊢
      ⌜(FiniteMap.dom_set naUsed : GSet Geid) ⊆ sLob ∧
        (FiniteMap.dom_set naUsed : GSet Geid) = FiniteMap.dom_set naUnused⌝ := by
  unfold naSplittingWf
  iintro ⟨%Hsub, H⟩
  ihave %Hdom := BigSepM2.bigSepM2_dom _ naUsed naUnused $$ H
  ipureintro
  refine ⟨Hsub, ?_⟩
  rw [setEq]
  intro x
  rw [elemOfDom, elemOfDom]
  exact iff_of_eq (congrFun Hdom x)

theorem naSplittingWfMono (sLob sLob' : GSet Geid) (na naUsed naUnused : Mea GF) :
    sLob ⊆ sLob' →
    naSplittingWf sLob na naUsed naUnused ⊢ naSplittingWf sLob' na naUsed naUnused := by
  intro Hsub
  unfold naSplittingWf
  iintro ⟨%H, Hm⟩
  iframe Hm
  ipureintro
  exact fun x hx => Hsub x (H x hx)

variable [AxirisG GF]

/-- `|=i=> P`: `P` under a basic update with access to the annotation interpretation (port of
AxSL `low/interp_mod.v`). -/
def interpMod (P : IProp GF) : IProp GF :=
  iprop(∀ na, AxirisG.annotInterp na ==∗ P ∗ AxirisG.annotInterp na)

end na

section interpModLemmas
variable {GF : BundledGFunctors} [AxirisG GF]

theorem interpModMono (P Q : IProp GF) : iprop(P -∗ Q) ⊢ interpMod P -∗ interpMod Q := by
  unfold interpMod
  iintro H HP %na Hann
  imod HP $$ %na Hann with ⟨HP, Hann⟩
  imodintro
  iframe Hann
  iapply H
  iexact HP

theorem interpModStrongMono (P Q : IProp GF) : iprop(P ==∗ Q) ⊢ interpMod P -∗ interpMod Q := by
  unfold interpMod
  iintro H HP %na Hann
  imod HP $$ %na Hann with ⟨HP, Hann⟩
  imod H $$ HP with HQ
  imodintro
  iframe Hann HQ

theorem interpModBupd (P : IProp GF) : iprop(|==> interpMod P) ⊢ interpMod P := by
  unfold interpMod
  iintro H %na Hann
  imod H
  iapply H $$ %na Hann

theorem interpModBupd' (P : IProp GF) : iprop(|==> P) ⊢ interpMod P := by
  unfold interpMod
  iintro H %na Hann
  imod H
  imodintro
  iframe H Hann

theorem interpModIntro (P : IProp GF) : P ⊢ interpMod P := by
  unfold interpMod
  iintro HP %na Hann
  imodintro
  iframe HP Hann

theorem interpModFrameL (P Q : IProp GF) : P ∗ interpMod Q ⊢ interpMod iprop(P ∗ Q) := by
  iintro ⟨HP, HQ⟩
  iapply interpModMono Q iprop(P ∗ Q) $$ [HP] HQ
  iintro HQ
  iframe HP HQ

theorem interpModFrameR (P Q : IProp GF) : interpMod P ∗ Q ⊢ interpMod iprop(P ∗ Q) := by
  iintro ⟨HP, HQ⟩
  iapply interpModMono P iprop(P ∗ Q) $$ [HQ] HP
  iintro HP
  iframe HP HQ

theorem interpModSep (P Q : IProp GF) : interpMod P ∗ interpMod Q ⊢ interpMod iprop(P ∗ Q) := by
  unfold interpMod
  iintro ⟨HP, HQ⟩ %na Hann
  imod HP $$ %na Hann with ⟨HP, Hann⟩
  imod HQ $$ %na Hann with ⟨HQ, Hann⟩
  imodintro
  iframe HP HQ Hann

theorem interpModTrans (P : IProp GF) : interpMod (interpMod P) ⊢ interpMod P := by
  unfold interpMod
  iintro HP %na Hann
  imod HP $$ %na Hann with ⟨HP, Hann⟩
  iapply HP $$ %na Hann

theorem interpModAnd (P Q : IProp GF) :
    interpMod iprop(P ∧ Q) ⊢ interpMod P ∧ interpMod Q := by
  iintro H
  isplit
  · iapply interpModMono iprop(P ∧ Q) P $$ [] H
    iintro ⟨HP, -⟩
    iexact HP
  · iapply interpModMono iprop(P ∧ Q) Q $$ [] H
    iintro ⟨-, HQ⟩
    iexact HQ

theorem interpModExist {A : Type _} (P : A → IProp GF) :
    iprop(∃ x, interpMod (P x)) ⊢ interpMod iprop(∃ x, P x) := by
  iintro ⟨%x, H⟩
  iapply interpModMono (P x) iprop(∃ x, P x) $$ [] H
  iintro H
  iexists x
  iexact H

/-- Rocq `interp_mod_proper` (a `Proper (⊢ ==> ⊢)` instance; a theorem here). -/
theorem interpModProper (P Q : IProp GF) (HPQ : P ⊢ Q) : interpMod P ⊢ interpMod Q := by
  iintro H
  iapply interpModMono P Q $$ [] H
  iintro HP
  iapply HPQ
  iexact HP

/-- Rocq `interp_mod_flip_proper`. -/
theorem interpModFlipProper (P Q : IProp GF) (HQP : Q ⊢ P) : interpMod Q ⊢ interpMod P :=
  interpModProper Q P HQP

/-- Rocq `interp_mod_ne`. -/
instance interpModNe : OFE.NonExpansive (interpMod (GF := GF)) where
  ne {n P Q} h := by
    unfold interpMod
    refine BI.forall_ne (fun na => ?_)
    refine BI.wand_ne.ne .rfl ?_
    refine (BIUpdate.bupd_ne).ne ?_
    exact BI.sep_ne.ne h .rfl

/-- Rocq `interp_mod_equiv_proper`. -/
theorem interpModEquivProper (P Q : IProp GF) (h : P ⊣⊢ Q) : interpMod P ⊣⊢ interpMod Q :=
  ⟨interpModProper P Q h.1, interpModProper Q P h.2⟩

instance elimModalBupdInterpMod {io : InOut} (p : Bool) (P Q : IProp GF) :
    ElimModal True p io false iprop(|==> P) P (interpMod Q) (interpMod Q) where
  elim_modal := by
    iintro %_ ⟨H, G⟩
    icases BI.intuitionisticallyIf_elim $$ H with H
    iapply interpModBupd
    imod H
    imodintro
    iapply G $$ H

instance elimModalIupdInterpMod {io : InOut} (p : Bool) (P Q : IProp GF) :
    ElimModal True p io false (interpMod P) P (interpMod Q) (interpMod Q) where
  elim_modal := by
    iintro %_ ⟨H, G⟩
    icases BI.intuitionisticallyIf_elim $$ H with H
    iapply interpModTrans
    iapply interpModMono P (interpMod Q) $$ G H

/-- `imodintro` on a `|=i=> P` goal (Rocq `from_modal_interp_mod`). -/
instance fromModalInterpMod {io : InOut} (P : IProp GF) :
    FromModal io modality_id True (interpMod P) (interpMod P) P where
  from_modal := by simp [modality_id]; exact interpModIntro P

end interpModLemmas

end Weak
