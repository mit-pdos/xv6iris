/-
Weak: **ADEQUACY, phases 1 and 2 core** (AxSL tier): threading `eaLocalWf` along a hart's run to
annotation coverage (phase 1, the single step `stepAnnot`), then discharging every event's flow
equation in gmo order (phase 2, `adequacyOrdAux`/`adequacyOrd`).

Rocq: `iris/AxAdequacy.v` @ xxvzwolszwmp.

## The Rocq header, in substance

LB via an AxSL-style base logic (design §1-L1, deviation 1: phase 2 inducts along a GIVEN linear
order instead of AxSL's `ob_set_ind_L`).  Port of the phases-1-and-2 core of AxSL's
`low/adequacy.v` + `low/adequacy_partial.v`'s `tpcoverage` shape, over `AxWp`'s `wp` and
`AxLifting`'s `eaLocalWf`/`eaLocalWfEvStep`.

THE SHAPE THAT MAKES PHASE 1 DIFFERENT FROM AxSL.  Reads are ANGELIC (`wpPreStepDef`'s clause
(a)): `wp` does not accept an externally chosen value, it PRODUCES its own.  So the per-step lemma
`stepAnnot` takes an EXTERNAL step only for its STRUCTURAL content (row position, identity `id` /
continuation `K` for a read, the concrete label/target for a write/fence/admin/wire — never a
read's VALUE) and produces `wp`'s OWN shadow continuation `sw`, related to the external step ONLY
by row POSITION (`sw.atK = s'.atK`).  For the demonic shapes (write/fence/admin/wire) the external
step's own target instantiates `wp`'s clause directly (`sw := s'`).

§4 of the Rocq file (prose only, no declarations) records the MULTI-STEP FINDING: `stepAnnot`
composes across two steps only when the second step's structural witness is stated relative to
the first step's OWN output `sw`; an externally given run states it relative to its own state,
which differs past a divergent angelic read.  The two escapes (a run-pairing hypothesis from
`AxPair`, or a `progressObl`-driven fresh construction with a new well-founded step bound) are
NOT delivered here, nor in Rocq.  §5 is the vocabulary (`expectedRun`, `expectedRunCoverage`,
`annotatedPrefix`, `writeCoverageHyp`); §6 is PHASE 2 — a plain induction along the `gxGmo` LIST
(every ob edge is gmo-forward, `obCatSubGmo`), taking full gmo coverage of `na`/`ea`'s domain as
an explicit hypothesis.  `axpolWfGmo` is the induction hypothesis a concrete `Axpol` must supply
(each handout field bounded by the gmo prefix at its own event); `gobCatPredSubGmoTake` shows the
natural `gobCat`-predecessor choice satisfies it.

## Deviations from Rocq

1. NAMES: camelCase (map below).  Representation as `AxWp` deviation 2 / `AxLifting` deviation 1:
   `m1 ∪ m2` on maps ↦ `PartialMap.union`, `dom` ↦ `FiniteMap.dom_set … : GSet Geid`,
   `from_option id emp` ↦ `AxWp.fromOption (fun P => P) iprop(emp)`, `list_to_set` ↦
   `LawfulSet.ofList`, `take`/`drop` ↦ `List.take`/`List.drop`, `is_Some` ↦ `isSome = true`,
   `S k` ↦ `k + 1`; `|={⊤}[∅]▷=>^n` ↦ iris-lean's `|={⊤}[∅]▷=>^[n]` (`Nat.repeat`, outermost
   step first, as Rocq).  `invGS_gen HasNoLc Σ` ↦ `[InvGS_gen hlc GF]` for any `hlc` (as AxWp
   deviation 6).  Wand chains `A -∗ B -∗ C` are stated `⊢ A -∗ B -∗ C` (AxWp deviation 7).
2. O2 STAGE C (`notes/weak-port-o2-stageC.md` §D) — NO FETCH EXCLUSION.  There is no
   `AStepFetch`: a fetch is an `AStepAdmin` step (`lbAdmin true (LIFetch ..)`), handled by
   `wpSkipStep` with `atK` unchanged like every administrative label.  So Rocq's
   `wlabel_is_fetch` side condition is dropped (AxLifting deviation 2): `astepProgNf` is
   `∃ l, AxOpsem.astepProg row s l s'` (no label filter), `astepAnyNf` is therefore equivalent to
   `astepAny` (kept as its own inductive, the name downstream files use), and
   `astepProgNodataFenceGmem` loses its `wlabel_is_fetch l = false` premise (an advancing
   no-data step is a fence: `AStepAdmin` keeps the position).  The oracle parameters `T`/`img`
   (`ax_text`, `gx_img`) of `astep_prog_nf`, `astep_any_nf`, `astep_prog_wdata_gmem`,
   `astep_prog_nodata_fence_gmem`, `expected_run(_coverage)` are deleted (AxOpsem deviation 2),
   so `expectedRun`/`expectedRunCoverage` need no `AxirisG` instance (Rocq: only for `ax_text`).
3. `stepAnnot`'s three proof arms share two Lean-only helpers, `AxAdequacy.evCase` (an annotated
   event step: `wpEvStep` + `eaLocalWfEvStep` + `naDomGrow`) and `AxAdequacy.skipCase` (an
   unannotated skip, `wpSkipStep`); Rocq inlines them.  `flow_eq_dyn_mono … "[$ _]"` is
   `AxAdequacy.flowEqDynDropPure`.  `adequacyOrdAux`'s induction on `k = len - n` is the
   Lean-only `AxAdequacy.ordAuxK`.  Other Lean-only helpers (file-qualified):
   `AxAdequacy.memTake`, `AxAdequacy.memTakeOfLookup`, `AxAdequacy.bigSepSSingleUnion`,
   `AxAdequacy.stepFupdNZero`, `AxAdequacy.stepFupdNSucc`.
4. `big_sepS_split_sub`/`big_sepS_merge_sub` are the two halves of iris-lean's
   `BigSepS.bigSepS_split_subset` (kept as named lemmas).  `ord_pending_extract`'s first
   conclusion `[∗ map] e0 ↦ v ∈ flow_in, v` is written `[∗map] Rin ∈ flowIn, Rin` (the same term;
   the form `flowEqDyn`'s premise uses).

**Rocq → Lean name map.**  `astep_prog_nf` `astepProgNf`, `astep_any_nf` `astepAnyNf`
(`ANFProg`/`ANFWire`/`ANFRead`), `astep_any_nf_any` `astepAnyNfAny`, `astep_any_nf_k`
`astepAnyNfK`, `nsteps_astep_any_nf_any` `nstepsAstepAnyNfAny`, `aident_rd_is_r` `aidentRdIsR`,
`aident_wr_is_w` `aidentWrIsW`, `aident_fence_not_mem` `aidentFenceNotMem`, `aread_step_gmem`
`areadStepGmem`, `astep_prog_wdata_gmem` `astepProgWdataGmem`, `astep_prog_nodata_fence_gmem`
`astepProgNodataFenceGmem`, `eids_before_k_or_skip` `eidsBeforeKOrSkip`, `aread_step_pos`
`areadStepPos`, `grow_prog_eq` `growProgEq`, `aread_step_rmw_value` `areadStepRmwValue`,
`aident_adv_rd_not_1` `aidentAdvRdNot1`, `na_dom_grow` `naDomGrow`, `step_annot` `stepAnnot`,
`expected_run` `expectedRun`, `expected_run_coverage` `expectedRunCoverage`, `annotated_prefix`
`annotatedPrefix`, `annotated_prefix_0` `annotatedPrefix0`, `annotated_prefix_full`
`annotatedPrefixFull`, `write_coverage_hyp` `writeCoverageHyp`, `gmo_take` `gmoTake`,
`gmo_take_0` `gmoTake0`, `gmo_take_full` `gmoTakeFull`, `gmo_take_snoc` `gmoTakeSnoc`,
`gmo_lt_take` `gmoLtTake`, `gob_cat_pred_sub_gmo_take` `gobCatPredSubGmoTake`, `axpol_wf_gmo`
`axpolWfGmo`, `ord_pending` `ordPending`, `ord_ea_todo` `ordEaTodo`, `ord_ea_todo_cons`
`ordEaTodoCons`, `lob_succ_not_in_gmo_take` `lobSuccNotInGmoTake`, `big_sepS_dom_from_option`
`bigSepSDomFromOption`, `big_sepS_split_sub` `bigSepSSplitSub`, `big_sepS_merge_sub`
`bigSepSMergeSub`, `ord_pending_extract` `ordPendingExtract`, `adequacy_ord_aux`
`adequacyOrdAux`, `adequacy_ord` `adequacyOrd`.

**Dropped:** nothing but the §7 `Print Assumptions` block (the lint's axiom check covers it).
No premise of any Rocq lemma is carried as an undischarged hypothesis beyond Rocq's own.
-/
import Weak.AxLifting

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp

/-! # 1. The (formerly fetch-excluding) step relation -/

/-- Rocq `astep_prog_nf`: `astepProg` minus its fetch arm — under Stage C there is none
(deviation 2), so no label filter. -/
def astepProgNf (row : List Lbl) (s s' : Athread) : Prop :=
  ∃ l, AxOpsem.astepProg row s l s'

inductive astepAnyNf (row : List Lbl) : Athread → Athread → Prop where
  | ANFProg (s s' : Athread) : astepProgNf row s s' → astepAnyNf row s s'
  | ANFWire (s s' : Athread) : awire s s' → astepAnyNf row s s'
  | ANFRead (s : Athread) (id : AidentT) (K : List (BitVec 8) → Athread) (vs : List (BitVec 8)) :
      areadStep row s id K → vs.length = aidentN id → astepAnyNf row s (K vs)

theorem astepAnyNfAny (row : List Lbl) (s s' : Athread) :
    astepAnyNf row s s' → astepAny row s s'
  | .ANFProg _ _ ⟨l, hl⟩ => .AAStep _ _ (.inl ⟨l, hl⟩)
  | .ANFWire _ _ hw => .AAStep _ _ (.inr hw)
  | .ANFRead _ id K vs h hl => .AARead _ id K vs h hl

theorem astepAnyNfK (row : List Lbl) (s s' : Athread) :
    astepAnyNf row s s' →
    s'.atK = s.atK ∨ (s'.atK = s.atK + 1 ∧ (row[s.atK]?).isSome = true) :=
  fun h => astepAnyK row s s' (astepAnyNfAny row s s' h)

theorem nstepsAstepAnyNfAny (row : List Lbl) (n : Nat) (s s' : Athread) :
    nsteps (astepAnyNf row) n s s' → nsteps (astepAny row) n s s' := by
  intro h
  induction h with
  | rfl => exact nsteps_O _
  | tail _ _ h ih => exact nsteps_r ih (astepAnyNfAny row _ _ h)

/-! # 2. Row-identity classification -/

theorem aidentRdIsR (lb : Lbl) : (aidentRd (aident lb)).isSome = true → lbIsR lb = true := by
  cases lb <;> simp_all [aident, aidentRd, lbIsR]

theorem aidentWrIsW (lb : Lbl) : (aidentWr (aident lb)).isSome = true → lbIsW lb = true := by
  cases lb <;> simp_all [aident, aidentWr, lbIsW]

theorem aidentFenceNotMem (lb : Lbl) :
    (aidentFence (aident lb)).isSome = true → lbIsR lb = false ∧ lbIsW lb = false := by
  cases lb <;> simp_all [aident, aidentFence, lbIsR, lbIsW]

/-- A read-shaped row position is a graph memory event. -/
theorem areadStepGmem (GD : Gdexec) (i : Nat) (s : Athread) (id : AidentT)
    (K : List (BitVec 8) → Athread) :
    areadStep (AxOpsem.grow GD i) s id K → gmemB GD.gdG (i, s.atK) = true := by
  rintro ⟨lb, hrow, rfl, hrd, _⟩
  unfold gmemB
  rw [AxWp.growLookup GD i s.atK lb hrow]
  simp [lbIsMem, aidentRdIsR lb hrd]

/-- A write-shaped `astepProg` step is at a graph memory event. -/
theorem astepProgWdataGmem (GD : Gdexec) (i : Nat) (s : Athread) (l : Wlabel) (s' : Athread)
    (data : List (BitVec 8)) :
    AxOpsem.astepProg (AxOpsem.grow GD i) s l s' → wlWdata l = some data →
    gmemB GD.gdG (i, s.atK) = true := by
  intro h hwd
  cases h with
  | AStepAdmin p k d l p' d' ha hs =>
    cases l <;> simp [lbAdmin, wlWdata] at ha hwd
  | AStepWrite p k d l lb p' d' hrow hs1 hid hdat hs =>
    have hw : (aidentWr (aident lb)).isSome = true := by rw [← hid]; exact hs1
    show gmemB GD.gdG (i, k) = true
    unfold gmemB
    rw [AxWp.growLookup GD i k lb hrow]
    simp [lbIsMem, aidentWrIsW lb hw]
  | AStepFence p k d l lb p' d' hrow hs1 hid hs =>
    cases l <;> simp [wlFence, wlWdata] at hs1 hwd

/-- A `none`-data `astepProg` step that ADVANCES the position is a fence, hence not a graph
memory event (deviation 2: no fetch hazard, so no `wlabel_is_fetch` premise). -/
theorem astepProgNodataFenceGmem (GD : Gdexec) (i : Nat) (s : Athread) (l : Wlabel)
    (s' : Athread) :
    AxOpsem.astepProg (AxOpsem.grow GD i) s l s' → wlWdata l = none →
    s'.atK = s.atK + 1 → gmemB GD.gdG (i, s.atK) = false := by
  intro h hwd hk
  cases h with
  | AStepAdmin p k d l p' d' ha hs =>
    have : k = k + 1 := hk
    omega
  | AStepWrite p k d l lb p' d' hrow hs1 hid hdat hs =>
    have := (wlWdataWr l).2 hs1
    simp [hwd] at this
  | AStepFence p k d l lb p' d' hrow hs1 hid hs =>
    have hf : (aidentFence (aident lb)).isSome = true := by rw [← hid]; exact hs1
    obtain ⟨h1, h2⟩ := aidentFenceNotMem lb hf
    show gmemB GD.gdG (i, k) = false
    unfold gmemB
    rw [AxWp.growLookup GD i k lb hrow]
    simp [lbIsMem, h1, h2]

/-- `naAtProgress`'s target is unaffected by an unannotated step. -/
theorem eidsBeforeKOrSkip (GD : Gdexec) (i k k' : Nat) :
    k' = k ∨ (k' = k + 1 ∧ gmemB GD.gdG (i, k) = false) →
    eidsBefore GD i k = eidsBefore GD i k' := by
  rintro (rfl | ⟨rfl, hg⟩)
  · rfl
  · exact (eidsBeforeSSkip GD i k hg).symm

/-- The read continuation's position advance, at ANY value of the right length. -/
theorem areadStepPos (row : List Lbl) (s : Athread) (id : AidentT)
    (K : List (BitVec 8) → Athread) (v : List (BitVec 8)) :
    areadStep row s id K → v.length = aidentN id → (K v).atK = s.atK + aidentAdvRd id := by
  rintro ⟨lb, _, _, _, HK⟩ hv
  obtain ⟨_, _, _, _, _, _, hk⟩ := HK v hv
  exact hk

/-- The row program of a valid hart matches `grow`. -/
theorem growProgEq (GD : Gdexec) (i k : Nat) (lb : Lbl) :
    (AxOpsem.grow GD i)[k]? = some lb → GD.gdG.gxProg[i]? = some (AxOpsem.grow GD i) := by
  unfold AxOpsem.grow growG
  cases h : GD.gdG.gxProg[i]? with
  | none => simp
  | some row => intro _; rfl

/-- THE DEMONIC READ FACT (RMW exclusive-read half): the graph's own value at this position, of
the right width (from `gwf`'s RMW shape clause). -/
theorem areadStepRmwValue (GD : Gdexec) (i : Nat) (s : Athread) (id : AidentT)
    (K : List (BitVec 8) → Athread) (Hgwf : gwf GD.gdG) :
    areadStep (AxOpsem.grow GD i) s id K → aidentAdvRd id = 0 →
    ∃ v, graphValue GD (i, s.atK) = some v ∧ v.length = aidentN id := by
  rintro ⟨lb, hrow, rfl, _, _⟩ hadv
  cases lb with
  | LLoad aq base ts vs => simp [aident, aidentAdvRd] at hadv
  | LStore rl base vs k => simp [aident, aidentAdvRd] at hadv
  | LFence pr pw sr sw => simp [aident, aidentAdvRd] at hadv
  | LRmw aq rl base ts rvs wvs k =>
    refine ⟨rvs, ?_, ?_⟩
    · unfold graphValue
      rw [AxWp.growLookup GD i s.atK _ hrow]
      rfl
    · obtain ⟨_, h2, h3⟩ := Hgwf.2.2 i (AxOpsem.grow GD i) s.atK _
        (growProgEq GD i s.atK _ hrow) hrow
      show rvs.length = wvs.length
      omega

/-- `aidentAdvRd` only ever returns `0` (an `IRmw` identity) or `1`. -/
theorem aidentAdvRdNot1 (id : AidentT) : aidentAdvRd id ≠ 1 → aidentAdvRd id = 0 := by
  cases id <;> simp [aidentAdvRd]

/-! # 3. The single step -/

section step
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]

/-- The domain growth `wpEvStep`'s output undergoes: inserting at the fresh event `(i,k)` grows
`na`'s hart-`i` domain by that one key. -/
theorem naDomGrow (Hwf : axpolWf) (GD : Gdexec) (i k : Nat) (na nu nuu : Mea GF)
    (R : IProp GF) :
    FiniteSet.filter (fun e : Geid => decide (e.1 = i)) (FiniteMap.dom_set na : GSet Geid) =
      eidsBefore GD i k →
    (FiniteMap.dom_set nu : GSet Geid) ⊆ Axpol.lobp GD (i, k) →
    (FiniteMap.dom_set nu : GSet Geid) = FiniteMap.dom_set nuu →
    gmemB GD.gdG (i, k) = true →
    FiniteSet.filter (fun e : Geid => decide (e.1 = i))
        (FiniteMap.dom_set (PartialMap.union (PartialMap.union {[(i, k) := R]} nuu) na) :
          GSet Geid) =
      eidsBefore GD i (k + 1) := by
  intro Hna Hsub Heq Hgmem
  have HnuNa : ∀ x, x ∈ (FiniteMap.dom_set nuu : GSet Geid) →
      x ∈ (FiniteMap.dom_set na : GSet Geid) := by
    intro x hx
    rw [← Heq] at hx
    exact lobpSubDom Hwf GD i k _ Hna x (Hsub x hx)
  rw [eidsBeforeSMem GD i k Hgmem, ← Hna, AxLifting.domUnionG, AxLifting.domUnionG, domSingleton]
  rw [setEq]
  intro x
  simp only [elemOfFilter, elemOfUnion, elemOfSingleton, decide_eq_true_eq]
  constructor
  · rintro ⟨h1, (hx | hx) | hx⟩
    · exact .inl hx
    · exact .inr ⟨h1, HnuNa x hx⟩
    · exact .inr ⟨h1, hx⟩
  · rintro (rfl | ⟨h1, hx⟩)
    · exact ⟨rfl, .inl (.inl rfl)⟩
    · exact ⟨h1, .inr hx⟩

/-- Lean-only: `flow_eq_dyn_mono … "[$ _]"` — drop the value-validation conjunct. -/
theorem AxAdequacy.flowEqDynDropPure (GD : Gdexec) (e : Geid) (sOb0 : GSet Geid)
    (flowIn : Mea GF) (R : IProp GF) (φ : Prop) :
    flowEqDyn GD e sOb0 flowIn iprop(R ∗ ⌜φ⌝) ⊢ flowEqDyn GD e sOb0 flowIn R := by
  iintro H
  ihave Hw : ▷ (iprop(R ∗ ⌜φ⌝) -∗ R) $$ []
  · inext
    iintro ⟨HR, -⟩
    iexact HR
  iapply flowEqDynMono GD e sOb0 flowIn _ _ $$ Hw H

/-- Lean-only: `stepAnnot`'s unannotated arms (fence/admin, wire, RMW read half). -/
theorem AxAdequacy.skipCase (GD : Gdexec) (i : Agent) (st : Stuckness) (k : Nat)
    (sw s' : Athread) (na : Mea GF) (ea : Sra GF) (Φ : Athread → IProp GF)
    (hk : sw.atK = s'.atK)
    (Hna : FiniteSet.filter (fun e : Geid => decide (e.1 = i))
      (FiniteMap.dom_set na : GSet Geid) = eidsBefore GD i k)
    (Heq : eidsBefore GD i k = eidsBefore GD i sw.atK) :
    ⊢ AxirisG.annotInterp na -∗ eaLocalWf GD ea na -∗
      wpSkipStep GD i sw.atK (AxWp.wp st i sw Φ) -∗
      |==> ▷ |==> ∃ (sw' : Athread) (na' : Mea GF) (ea' : Sra GF) (ls' : AxirisG.logTsT GF),
        ⌜sw'.atK = s'.atK⌝ ∗ naAtProgress GD i sw'.atK na' ∗ AxirisG.annotInterp na' ∗
        eaLocalWf GD ea' na' ∗ AxirisG.localInterp GD i sw'.atK ls' ∗ AxWp.wp st i sw' Φ := by
  iintro Hannot Hea Hb
  iunfold wpSkipStep at Hb
  imod Hb $$ %na Hannot with Hb
  imodintro
  inext
  imod Hb with ⟨%ls', Hannot', Hloc', HΨ⟩
  imodintro
  iexists sw, na, ea, ls'
  isplitr
  · ipureintro
    exact hk
  isplitr
  · iunfold naAtProgress
    ipureintro
    rw [← Heq]
    exact Hna
  isplitl [Hannot']
  · iexact Hannot'
  isplitl [Hea]
  · iexact Hea
  isplitl [Hloc']
  · iexact Hloc'
  · iexact HΨ

/-- Lean-only: `stepAnnot`'s annotated arms (write, angelic read). -/
theorem AxAdequacy.evCase {A : Type} (Hwf : axpolWf) (GD : Gdexec) (Hgwf : gwf GD.gdG)
    (i : Agent) (st : Stuckness) (k : Nat) (Hgmem : gmemB GD.gdG (i, k) = true)
    (ok val : A → Prop) (kf : A → Nat) (Kf : A → Athread) (hK : ∀ a, kf a = (Kf a).atK)
    (s' : Athread) (hpos : ∀ a, ok a → (Kf a).atK = s'.atK ∧ kf a = k + 1)
    (na : Mea GF) (ea : Sra GF) (Φ : Athread → IProp GF)
    (Hna : FiniteSet.filter (fun e : Geid => decide (e.1 = i))
      (FiniteMap.dom_set na : GSet Geid) = eidsBefore GD i k) :
    ⊢ AxirisG.annotInterp na -∗ eaLocalWf GD ea na -∗
      wpEvStep GD i k ok val kf (fun a => AxWp.wp st i (Kf a) Φ) -∗
      |==> ▷ |==> ∃ (sw' : Athread) (na' : Mea GF) (ea' : Sra GF) (ls' : AxirisG.logTsT GF),
        ⌜sw'.atK = s'.atK⌝ ∗ naAtProgress GD i sw'.atK na' ∗ AxirisG.annotInterp na' ∗
        eaLocalWf GD ea' na' ∗ AxirisG.localInterp GD i sw'.atK ls' ∗ AxWp.wp st i sw' Φ := by
  iintro Hannot Hea Hb
  iunfold wpEvStep at Hb
  ihave Hpre : naAtProgress GD i k na $$ []
  · iunfold naAtProgress
    ipureintro
    exact Hna
  imod Hb $$ %na [$Hpre $Hannot] with Hb
  imodintro
  inext
  imod Hb with ⟨%a, %R, %nu, %nuu, %ls', %Hok, #Hsplit, Hfe, Hannot', Hloc', HΨ⟩
  ihave %Hd := naSplittingWfDom (Axpol.lobp GD (i, k)) na nu nuu $$ Hsplit
  ihave Hfe' := AxAdequacy.flowEqDynDropPure GD (i, k) (Axpol.sPol GD (i, k)) nu R (val a) $$ Hfe
  ihave Hea' := eaLocalWfEvStep Hwf GD i k na ea nu nuu R Hgwf Hgmem Hna $$ Hsplit Hea Hfe'
  imodintro
  obtain ⟨h1, h2⟩ := hpos a Hok
  iexists Kf a, PartialMap.union (PartialMap.union {[(i, k) := R]} nuu) na,
    PartialMap.union {[(i, k) := nu]} ea, ls'
  isplitr
  · ipureintro
    exact h1
  isplitr
  · iunfold naAtProgress
    ipureintro
    rw [← hK a, h2]
    exact naDomGrow Hwf GD i k na nu nuu R Hna Hd.1 Hd.2 Hgmem
  isplitl [Hannot']
  · iexact Hannot'
  isplitl [Hea']
  · iexact Hea'
  isplitl [Hloc']
  · rw [← hK a]
    iexact Hloc'
  · iexact HΨ

/-- THE SINGLE STEP: an external step's STRUCTURE drives `wp`'s own step; the shadow state `sw`
agrees with `s'` in row position. -/
theorem stepAnnot (GD : Gdexec) (Hwf : axpolWf) (Hcons : rvwmoCatConsistent GD)
    (i : Agent) (st : Stuckness) (s s' : Athread)
    (Hstep : astepAnyNf (AxOpsem.grow GD i) s s')
    (na : Mea GF) (ea : Sra GF) (ls : AxirisG.logTsT GF) (Φ : Athread → IProp GF) :
    ⊢ naAtProgress GD i s.atK na -∗
      AxirisG.annotInterp na -∗
      eaLocalWf GD ea na -∗
      AxirisG.localInterp GD i s.atK ls -∗
      □ AxirisG.gconstInterp GD -∗
      wpPreStepDef i (AxWp.wp st i) s Φ -∗
      |==> ▷ |==> ∃ (sw : Athread) (na' : Mea GF) (ea' : Sra GF) (ls' : AxirisG.logTsT GF),
        ⌜sw.atK = s'.atK⌝ ∗
        naAtProgress GD i sw.atK na' ∗
        AxirisG.annotInterp na' ∗
        eaLocalWf GD ea' na' ∗
        AxirisG.localInterp GD i sw.atK ls' ∗
        AxWp.wp st i sw Φ := by
  have Hgwf := Hcons.1
  iintro Hnap Hannot Hea Hloc #Hgconst H
  iunfold naAtProgress at Hnap
  icases Hnap with %Hna
  iunfold wpPreStepDef at H
  ihave Hpre : (⌜rvwmoCatConsistent GD⌝ ∗ □ AxirisG.gconstInterp GD ∗
      AxirisG.localInterp GD i s.atK ls) $$ [Hloc]
  · isplitr
    · ipureintro
      exact Hcons
    · isplitr
      · imodintro
        iexact Hgconst
      · iexact Hloc
  ihave Habc := H $$ %GD %ls Hpre
  cases Hstep with
  | ANFProg _ Hprog =>
    obtain ⟨l, Hap⟩ := Hprog
    ihave Hb := (and_elim_r.trans and_elim_l) $$ Habc
    ihave Hb := Hb $$ %l %s' %Hap
    cases hwd : wlWdata l with
    | some data =>
      have Hgmem := astepProgWdataGmem GD i s l s' data Hap hwd
      have Hk := astepProgWdataSk _ s l s' data Hap hwd
      try isimp only [] at Hb
      iapply AxAdequacy.evCase (A := Unit) Hwf GD Hgwf i st s.atK Hgmem (fun _ => True)
        (fun _ => graphData GD (i, s.atK) = some data) (fun _ => s'.atK) (fun _ => s')
        (fun _ => rfl) s' (fun _ _ => ⟨rfl, Hk⟩) na ea Φ Hna $$ Hannot Hea Hb
    | none =>
      have Heq : eidsBefore GD i s.atK = eidsBefore GD i s'.atK := by
        rcases astepProgNodataK _ s l s' Hap hwd with hk | hk
        · exact eidsBeforeKOrSkip GD i s.atK s'.atK (.inl hk)
        · exact eidsBeforeKOrSkip GD i s.atK s'.atK
            (.inr ⟨hk, astepProgNodataFenceGmem GD i s l s' Hap hwd hk⟩)
      try isimp only [] at Hb
      iapply AxAdequacy.skipCase GD i st s.atK s' s' na ea Φ rfl Hna Heq $$ Hannot Hea Hb
  | ANFWire _ Hw =>
    ihave Hc := (and_elim_r.trans and_elim_r) $$ Habc
    ihave Hc := Hc $$ %s' %Hw
    iapply AxAdequacy.skipCase GD i st s.atK s' s' na ea Φ rfl Hna (by rw [Hw.1])
      $$ Hannot Hea Hc
  | ANFRead id K vs Hrd Hlen =>
    ihave Ha := and_elim_l $$ Habc
    ihave Ha := Ha $$ %id %K %Hrd
    by_cases Hadv : aidentAdvRd id = 1
    · isimp only [if_pos Hadv] at Ha
      have Hgmem := areadStepGmem GD i s id K Hrd
      iapply AxAdequacy.evCase (A := List (BitVec 8)) Hwf GD Hgwf i st s.atK Hgmem
        (fun v => v.length = aidentN id) (fun v => graphValue GD (i, s.atK) = some v)
        (fun v => (K v).atK) K (fun _ => rfl) (K vs)
        (fun a hok => ⟨by rw [areadStepPos _ _ _ _ _ Hrd hok, areadStepPos _ _ _ _ _ Hrd Hlen],
          by rw [areadStepPos _ _ _ _ _ Hrd hok, Hadv]⟩) na ea Φ Hna $$ Hannot Hea Ha
    · have Hadv0 := aidentAdvRdNot1 id Hadv
      obtain ⟨v, Hgv, Hlenv⟩ := areadStepRmwValue GD i s id K Hgwf Hrd Hadv0
      isimp only [if_neg Hadv] at Ha
      ihave Ha := Ha $$ %v %Hgv %Hlenv
      iapply AxAdequacy.skipCase GD i st s.atK (K v) (K vs) na ea Φ
        (by rw [areadStepPos _ _ _ _ _ Hrd Hlenv, areadStepPos _ _ _ _ _ Hrd Hlen]) Hna
        (by rw [areadStepPos _ _ _ _ _ Hrd Hlenv, Hadv0, Nat.add_zero]) $$ Hannot Hea Ha

end step

/-! # 4. The multi-step finding: prose only (module header). -/

/-! # 5. Vocabulary: `expectedRun`, `tpcoverage`, `annotatedPrefix` -/

/-- A hart's EXPECTED RUN: an opax run from the boot state to a given final state (deviation 2:
no oracle parameters, no `AxirisG` instance). -/
def expectedRun (GD : Gdexec) (i : Agent) (p0 pfin : Pexv6) (kfin : Nat) : Prop :=
  rtc (astepAnyNf (AxOpsem.grow GD i)) ⟨p0, 0⟩ ⟨pfin, kfin⟩

/-- ROW COVERAGE (AxSL's `tpcoverage`), via `coverageOfRow`. -/
theorem expectedRunCoverage (GD : Gdexec) (i : Agent) (p0 pfin : Pexv6) :
    expectedRun GD i p0 pfin (AxOpsem.grow GD i).length →
    ∀ j, consumed (AxOpsem.grow GD i) ⟨p0, 0⟩ ⟨pfin, (AxOpsem.grow GD i).length⟩ j ↔
      j < (AxOpsem.grow GD i).length := by
  intro Hrun
  exact coverageOfRow _ p0 pfin (rtc_subrel (fun x y h => astepAnyNfAny _ x y h) Hrun)

/-- PHASE 2's INVARIANT, replacing AxSL's `na_full`: at gmo-prefix length `n`, every WRITE at or
before it is annotated. -/
def annotatedPrefix (GD : Gdexec) (na : GSet Geid) (n : Nat) : Prop :=
  ∀ e, e ∈ GD.gdG.gxGmo.take n → gisW GD.gdG e = true → e ∈ na

theorem annotatedPrefix0 (GD : Gdexec) (na : GSet Geid) : annotatedPrefix GD na 0 := by
  intro e he
  simp at he

theorem annotatedPrefixFull (GD : Gdexec) (na : GSet Geid) :
    (∀ e, e ∈ GD.gdG.gxGmo → gisW GD.gdG e = true → e ∈ na) →
    annotatedPrefix GD na GD.gdG.gxGmo.length := by
  intro H e he
  exact H e (List.mem_of_mem_take he)

/-- THE NAMED HYPOTHESIS (task A4): every graph write not annotated by phase 1 is gmo-after
some read of its own hart. -/
def writeCoverageHyp (GD : Gdexec) (na : GSet Geid) : Prop :=
  ∀ w, gisW GD.gdG w = true → w ∉ na →
    ∃ r : Geid, r.1 = w.1 ∧ gisW GD.gdG r = false ∧ gmem GD.gdG r ∧ gmoLt GD.gdG r w

/-! # 6. PHASE 2: the gmo-order induction -/

/-- The gmo prefix of length `n`, as a set. -/
def gmoTake (GD : Gdexec) (n : Nat) : GSet Geid :=
  LawfulSet.ofList (GD.gdG.gxGmo.take n)

theorem gmoTake0 (GD : Gdexec) : gmoTake GD 0 = ∅ := by
  unfold gmoTake
  rw [List.take_zero]
  exact listToSetNil

theorem gmoTakeFull (GD : Gdexec) :
    gmoTake GD GD.gdG.gxGmo.length = (LawfulSet.ofList GD.gdG.gxGmo : GSet Geid) := by
  unfold gmoTake
  rw [List.take_length]

theorem gmoTakeSnoc (GD : Gdexec) (n : Nat) (e : Geid) :
    GD.gdG.gxGmo[n]? = some e → gmoTake GD (n + 1) = ({e} : GSet Geid) ∪ gmoTake GD n := by
  intro hn
  unfold gmoTake
  rw [List.take_add_one, hn, listToSetApp]
  rw [setEq]
  intro x
  simp only [elemOfUnion, elemOfListToSet, elemOfSingleton, Option.toList_some,
    List.mem_singleton]
  exact Or.comm

/-- Lean-only: a member of a `take` prefix sits at an index below the cut. -/
theorem AxAdequacy.memTake {α : Type _} {l : List α} {m : Nat} {x : α} (h : x ∈ l.take m) :
    ∃ j, j < m ∧ l[j]? = some x := by
  obtain ⟨j, hj⟩ := elem_of_list_lookup_1 h
  have hlt : j < (l.take m).length := lookup_lt_Some hj
  rw [List.length_take] at hlt
  refine ⟨j, by omega, ?_⟩
  rw [List.getElem?_take_of_lt (by omega)] at hj
  exact hj

/-- Lean-only: the converse of `AxAdequacy.memTake`. -/
theorem AxAdequacy.memTakeOfLookup {α : Type _} {l : List α} {m j : Nat} {x : α}
    (h : l[j]? = some x) (hj : j < m) : x ∈ l.take m :=
  elem_of_list_lookup_2 (by rw [List.getElem?_take_of_lt hj]; exact h)

/-- An event's gmo-position predecessors sit inside the take-prefix at its own position. -/
theorem gmoLtTake (GD : Gdexec) (n : Nat) (e e' : Geid) :
    GD.gdG.gxGmo.Nodup → GD.gdG.gxGmo[n]? = some e → gmoLt GD.gdG e' e → e' ∈ gmoTake GD n := by
  rintro hnd hn ⟨he', _, hlt⟩
  rw [gposOfLookup _ n e hnd hn] at hlt
  unfold gmoTake
  rw [elemOfListToSet]
  exact AxAdequacy.memTakeOfLookup (gposElemLookup _ e' he') hlt

/-- THE SUPERSET HANDOUT: an event's `gobCat` predecessors are gmo-prefix bounded. -/
theorem gobCatPredSubGmoTake (GD : Gdexec) (Hcons : rvwmoCatConsistent GD) (n : Nat) (e : Geid) :
    GD.gdG.gxGmo[n]? = some e → ∀ e', gobCat GD e' e → e' ∈ gmoTake GD n := by
  intro hn e' hob
  exact gmoLtTake GD n e e' Hcons.1.1 hn (obCatSubGmo GD e' e Hcons hob)

/-- THE INDUCTION HYPOTHESIS a concrete `Axpol` must supply: both handout fields are bounded by
the gmo prefix at each event. -/
def axpolWfGmo [Axpol] (GD : Gdexec) : Prop :=
  ∀ n e, GD.gdG.gxGmo[n]? = some e →
    Axpol.sPol GD e ⊆ gmoTake GD n ∧ Axpol.lobp GD e ⊆ gmoTake GD n

/-- No lob′-successor of an event at gmo position `n` sits in the gmo prefix at `n`. -/
theorem lobSuccNotInGmoTake [Axpol] (GD : Gdexec) (Hpol : axpolWfGmo GD) (n : Nat) (e : Geid)
    (He : GD.gdG.gxGmo[n]? = some e) (Hnd : GD.gdG.gxGmo.Nodup) :
    ∀ eOut, eOut ∈ lobSuccOf GD e → eOut ∉ gmoTake GD n := by
  intro eOut hsucc hcon
  obtain ⟨hlob, hgmo⟩ := (elemOfLobSuccOf GD e eOut).1 hsucc
  have hm := gposElemLookup _ _ hgmo
  have h1 := (Hpol _ eOut hm).2 e hlob
  unfold gmoTake at h1 hcon
  rw [elemOfListToSet] at h1 hcon
  obtain ⟨j, hj, hjl⟩ := AxAdequacy.memTake h1
  have e1 := NoDup_lookup Hnd hjl He
  obtain ⟨j', hj', hjl'⟩ := AxAdequacy.memTake hcon
  have e2 := NoDup_lookup Hnd hjl' hm
  omega

section ord
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]

/-- The piece an already-processed event `e` still owes its lob′-successors OUTSIDE the
processed set `P`. -/
def ordPending (GD : Gdexec) (ea : Sra GF) (P : GSet Geid) (e : Geid) : IProp GF :=
  eaDeposit ea (lobSuccOf GD e \ P) e

/-- The events STILL TO PROCESS, from position `n` on. -/
def ordEaTodo (GD : Gdexec) (ea : Sra GF) (na : Mea GF) (n : Nat) : IProp GF :=
  iprop([∗list] e0 ∈ GD.gdG.gxGmo.drop n,
    AxWp.fromOption (fun R0 => AxWp.fromOption
        (fun flowIn => flowEqEa GD e0 (Axpol.sPol GD e0) flowIn ea R0) iprop(emp) (get? ea e0))
      iprop(emp) (get? na e0))

theorem ordEaTodoCons (GD : Gdexec) (ea : Sra GF) (na : Mea GF) (n : Nat) (e : Geid) :
    GD.gdG.gxGmo[n]? = some e →
    ordEaTodo GD ea na n ⊣⊢
    iprop(AxWp.fromOption (fun R0 => AxWp.fromOption
          (fun flowIn => flowEqEa GD e (Axpol.sPol GD e) flowIn ea R0) iprop(emp) (get? ea e))
        iprop(emp) (get? na e)
      ∗ ordEaTodo GD ea na (n + 1)) := by
  intro hn
  obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.1 hn
  have hd : GD.gdG.gxGmo.drop n = e :: GD.gdG.gxGmo.drop (n + 1) := by
    rw [List.drop_eq_getElem_cons hlt, hget]
  unfold ordEaTodo
  rw [hd]
  exact BigSepL.bigSepL_cons

theorem bigSepSDomFromOption {A : Type _} (m : GMapF Geid A) (Φ : A → IProp GF) :
    ([∗set] e0 ∈ (FiniteMap.dom_set m : GSet Geid), AxWp.fromOption Φ iprop(emp) (get? m e0)) ⊣⊢
      [∗map] _e0 ↦ v ∈ m, Φ v := by
  refine (BigSepM.bigSepM_dom (S := GSet Geid)
    (Φ := fun k => AxWp.fromOption Φ iprop(emp) (get? m k)) (m := m)).symm.trans ?_
  exact BiEntails.of_eq (BigSepM.bigSepM_eq fun {k x} h => by simp only [h, AxWp.fromOption])

/-- Splitting a `[∗set]` across a subset. -/
theorem bigSepSSplitSub (Φ : Geid → IProp GF) (X P : GSet Geid) :
    X ⊆ P → ([∗set] e0 ∈ P, Φ e0) ⊢ iprop(([∗set] e0 ∈ X, Φ e0) ∗ ([∗set] e0 ∈ P \ X, Φ e0)) :=
  fun h => (BigSepS.bigSepS_split_subset h).1

theorem bigSepSMergeSub (Φ : Geid → IProp GF) (X P : GSet Geid) :
    X ⊆ P → iprop(([∗set] e0 ∈ X, Φ e0) ∗ ([∗set] e0 ∈ P \ X, Φ e0)) ⊢ ([∗set] e0 ∈ P, Φ e0) :=
  fun h => (BigSepS.bigSepS_split_subset h).2

/-- Extracting the flow-in resources a step at `e` needs from the running pending bag, and
re-threading the pending bag past `e`. -/
theorem ordPendingExtract (GD : Gdexec) (ea : Sra GF) (P : GSet Geid) (e : Geid)
    (flowIn : Mea GF) (HeGmo : e ∈ GD.gdG.gxGmo) (Henin : e ∉ P)
    (HeaE : get? ea e = some flowIn)
    (Hsub : (FiniteMap.dom_set flowIn : GSet Geid) ⊆ Axpol.lobp GD e)
    (HsubP : Axpol.lobp GD e ⊆ P) :
    ([∗set] e0 ∈ P, ordPending GD ea P e0) ⊢
    iprop(([∗map] Rin ∈ flowIn, Rin) ∗
      ([∗set] e0 ∈ P, ordPending GD ea (({e} : GSet Geid) ∪ P) e0)) := by
  have hpt1 : ∀ e0, e0 ∈ Axpol.lobp GD e →
      ordPending GD ea P e0 ⊢ iprop(AxWp.fromOption (fun Q => Q) iprop(emp) (get? flowIn e0) ∗
        ordPending GD ea (({e} : GSet Geid) ∪ P) e0) := by
    intro e0 he0
    have hin : e ∈ lobSuccOf GD e0 \ P :=
      elemOfDifference.2 ⟨(elemOfLobSuccOf GD e0 e).2 ⟨he0, HeGmo⟩, Henin⟩
    have hd : AxLifting.depAt ea e0 e = AxWp.fromOption (fun Q => Q) iprop(emp) (get? flowIn e0) := by
      unfold AxLifting.depAt
      rw [HeaE]
      rfl
    have hs : (lobSuccOf GD e0 \ P) \ ({e} : GSet Geid) =
        lobSuccOf GD e0 \ (({e} : GSet Geid) ∪ P) := by
      rw [setEq]
      intro x
      simp only [elemOfDifference, elemOfUnion, elemOfSingleton]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨h1, fun h => h.elim h3 h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨⟨h1, fun h => h2 (.inr h)⟩, fun h => h2 (.inl h)⟩
    unfold ordPending eaDeposit
    have h := (BigSepS.bigSepS_delete (Φ := fun eOut => AxLifting.depAt ea e0 eOut) hin).1
    rw [hd, hs] at h
    exact h
  have hpt2 : ∀ e0, e0 ∈ P \ Axpol.lobp GD e →
      ordPending GD ea P e0 = ordPending GD ea (({e} : GSet Geid) ∪ P) e0 := by
    intro e0 he0
    have hnin : e ∉ lobSuccOf GD e0 := fun h =>
      (elemOfDifference.1 he0).2 ((elemOfLobSuccOf GD e0 e).1 h).1
    have hs : lobSuccOf GD e0 \ (({e} : GSet Geid) ∪ P) = lobSuccOf GD e0 \ P := by
      rw [setEq]
      intro x
      simp only [elemOfDifference, elemOfUnion, elemOfSingleton]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, fun h => h2 (.inr h)⟩
      · rintro ⟨h1, h2⟩
        refine ⟨h1, fun h => h.elim (fun h' => hnin (h' ▸ h1)) h2⟩
    unfold ordPending
    rw [hs]
  have h1 : ([∗set] e0 ∈ Axpol.lobp GD e, ordPending GD ea P e0) ⊢
      iprop(([∗set] e0 ∈ Axpol.lobp GD e,
          AxWp.fromOption (fun Q => Q) iprop(emp) (get? flowIn e0)) ∗
        ([∗set] e0 ∈ Axpol.lobp GD e, ordPending GD ea (({e} : GSet Geid) ∪ P) e0)) :=
    (BigSepS.bigSepS_mono fun {x} hx => hpt1 x hx).trans BigSepS.bigSepS_sep.1
  have h2 : ([∗set] e0 ∈ P \ Axpol.lobp GD e, ordPending GD ea P e0) ⊢
      ([∗set] e0 ∈ P \ Axpol.lobp GD e, ordPending GD ea (({e} : GSet Geid) ∪ P) e0) :=
    BigSepS.bigSepS_mono fun {x} hx => by rw [hpt2 x hx]
  have h3 : ([∗set] e0 ∈ Axpol.lobp GD e,
        AxWp.fromOption (fun Q => Q) iprop(emp) (get? flowIn e0)) ⊢
      [∗map] Rin ∈ flowIn, Rin :=
    (BigSepS.bigSepS_split_subset Hsub).1.trans
      (sep_elim_left.trans (bigSepSDomFromOption flowIn (fun Q => Q)).1)
  have h4 := (BigSepS.bigSepS_split_subset
    (Φ := fun e0 => ordPending GD ea (({e} : GSet Geid) ∪ P) e0) HsubP).2
  refine (BigSepS.bigSepS_split_subset HsubP).1.trans ?_
  refine (sep_mono h1 h2).trans ?_
  refine sep_assoc.1.trans ?_
  exact sep_mono h3 h4

/-- Lean-only: `[∗set]` over `{x} ∪ X` for a fresh `x`. -/
theorem AxAdequacy.bigSepSSingleUnion (Φ : Geid → IProp GF) (X : GSet Geid) (x : Geid)
    (h : x ∉ X) :
    ([∗set] y ∈ ({x} : GSet Geid) ∪ X, Φ y) ⊣⊢ iprop(Φ x ∗ [∗set] y ∈ X, Φ y) :=
  (BigSepS.bigSepS_union ((elemOfDisjoint (X := ({x} : GSet Geid)) (Y := X)).2 fun y hy hy' => h ((elemOfSingleton.1 hy) ▸ hy'))).trans
    (sep_congr BigSepS.bigSepS_singleton .rfl)

/-- Lean-only: unfolding the iterated step-update. -/
theorem AxAdequacy.stepFupdNZero (P : IProp GF) :
    iprop(|={⊤}[∅]▷=>^[0] P) = P := rfl

theorem AxAdequacy.stepFupdNSucc (n : Nat) (P : IProp GF) :
    iprop(|={⊤}[∅]▷=>^[n + 1] P) = iprop(|={⊤}[∅]▷=> |={⊤}[∅]▷=>^[n] P) := rfl

/-- Lean-only: `adequacyOrdAux`'s induction, on `k = len - n`. -/
theorem AxAdequacy.ordAuxK (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (Hpol : axpolWfGmo GD) (na : Mea GF) (ea : Sra GF)
    (HdomEq : (FiniteMap.dom_set ea : GSet Geid) = FiniteMap.dom_set na)
    (Hdom : (LawfulSet.ofList GD.gdG.gxGmo : GSet Geid) ⊆ FiniteMap.dom_set na)
    (HeaLob : ∀ e0 gm, get? ea e0 = some gm → (FiniteMap.dom_set gm : GSet Geid) ⊆ Axpol.lobp GD e0) :
    ∀ k n, k = GD.gdG.gxGmo.length - n → n ≤ GD.gdG.gxGmo.length →
    ⊢ ordEaTodo GD ea na n -∗
      (∃ (σ : AxirisG.obSt GF), AxirisG.obStInterp GD σ (gmoTake GD n) ∗
        ([∗set] e0 ∈ gmoTake GD n, AxWp.fromOption (fun P => P) iprop(emp) (get? na e0)) ∗
        ([∗set] e0 ∈ gmoTake GD n, ordPending GD ea (gmoTake GD n) e0)) -∗
      |={⊤}[∅]▷=>^[k]
        ∃ (σ : AxirisG.obSt GF),
          AxirisG.obStInterp GD σ (LawfulSet.ofList GD.gdG.gxGmo) ∗
          [∗set] e0 ∈ (LawfulSet.ofList GD.gdG.gxGmo : GSet Geid),
            AxWp.fromOption (fun P => P) iprop(emp) (get? na e0) := by
  intro k
  induction k with
  | zero =>
    intro n hk hn
    have hn' : n = GD.gdG.gxGmo.length := by omega
    subst hn'
    rw [AxAdequacy.stepFupdNZero, gmoTakeFull]
    iintro _ ⟨%σ, Hob, Hbag, -⟩
    iexists σ
    isplitl [Hob]
    · iexact Hob
    · iexact Hbag
  | succ k IHk =>
    intro n hk hn
    have Hnlt : n < GD.gdG.gxGmo.length := by omega
    obtain ⟨e, He⟩ := Option.isSome_iff_exists.1 (lookup_lt_is_Some_2 Hnlt)
    have HeGmo : e ∈ GD.gdG.gxGmo := elem_of_list_lookup_2 He
    obtain ⟨Re, HnaE⟩ := Option.isSome_iff_exists.1
      (elemOfDom.1 (Hdom e (elemOfListToSet.2 HeGmo)))
    have HeDom : e ∈ (FiniteMap.dom_set ea : GSet Geid) := by
      rw [HdomEq]
      exact elemOfDom2 HnaE
    obtain ⟨flowIn, HeaE⟩ := Option.isSome_iff_exists.1 (elemOfDom.1 HeDom)
    have Hnd := Hcons.1.1
    have Henin : e ∉ gmoTake GD n := by
      intro hin
      unfold gmoTake at hin
      rw [elemOfListToSet] at hin
      obtain ⟨j, hj, hjl⟩ := AxAdequacy.memTake hin
      have := NoDup_lookup Hnd hjl He
      omega
    have Hsub := HeaLob e flowIn HeaE
    obtain ⟨HspolP, HlobP⟩ := Hpol n e He
    have Hself : e ∉ lobSuccOf GD e := fun h =>
      Henin (HlobP e ((elemOfLobSuccOf GD e e).1 h).1)
    have Hnosucc := lobSuccNotInGmoTake GD Hpol n e He Hnd
    have hs : lobSuccOf GD e \ (({e} : GSet Geid) ∪ gmoTake GD n) = lobSuccOf GD e := by
      rw [setEq]
      intro x
      simp only [elemOfDifference, elemOfUnion, elemOfSingleton]
      constructor
      · exact fun h => h.1
      · intro hx
        refine ⟨hx, fun h => h.elim (fun h' => Hself (h' ▸ hx)) (Hnosucc x hx)⟩
    rw [AxAdequacy.stepFupdNSucc]
    iintro Htodo ⟨%σ, Hob, Hbag, Hpend⟩
    icases (ordEaTodoCons GD ea na n e He).1 $$ Htodo with ⟨Hhd, Htodo⟩
    isimp only [HnaE, HeaE, AxWp.fromOption] at Hhd
    ihave ⟨Hflow, Hpend⟩ :=
      ordPendingExtract GD ea (gmoTake GD n) e flowIn HeGmo Henin HeaE Hsub HlobP $$ Hpend
    iunfold flowEqEa, flowEqDyn at Hhd
    imod Hhd $$ %σ %(gmoTake GD n) %HspolP %Henin Hob Hflow with Hhd
    imodintro
    inext
    imod Hhd with ⟨%σ', Hob', HRe, Hdep⟩
    imodintro
    iapply (IHk (n + 1) (by omega) Hnlt) $$ Htodo
    iexists σ'
    rw [gmoTakeSnoc GD n e He]
    isplitl [Hob']
    · iexact Hob'
    isplitl [HRe Hbag]
    · iapply (AxAdequacy.bigSepSSingleUnion _ (gmoTake GD n) e Henin).2
      isplitl [HRe]
      · isimp only [HnaE, AxWp.fromOption]
        iexact HRe
      · iexact Hbag
    · iapply (AxAdequacy.bigSepSSingleUnion _ (gmoTake GD n) e Henin).2
      isplitl [Hdep]
      · iunfold ordPending
        rw [hs]
        iexact Hdep
      · iexact Hpend

/-- THE INDUCTION.  `HdomEq`/`Hdom` are the coverage facts phase 1 is responsible for. -/
theorem adequacyOrdAux (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (Hpol : axpolWfGmo GD) (na : Mea GF) (ea : Sra GF)
    (HdomEq : (FiniteMap.dom_set ea : GSet Geid) = FiniteMap.dom_set na)
    (Hdom : (LawfulSet.ofList GD.gdG.gxGmo : GSet Geid) ⊆ FiniteMap.dom_set na)
    (HeaLob : ∀ e0 gm, get? ea e0 = some gm → (FiniteMap.dom_set gm : GSet Geid) ⊆ Axpol.lobp GD e0) :
    ∀ n, n ≤ GD.gdG.gxGmo.length →
    ⊢ ordEaTodo GD ea na n -∗
      (∃ (σ : AxirisG.obSt GF), AxirisG.obStInterp GD σ (gmoTake GD n) ∗
        ([∗set] e0 ∈ gmoTake GD n, AxWp.fromOption (fun P => P) iprop(emp) (get? na e0)) ∗
        ([∗set] e0 ∈ gmoTake GD n, ordPending GD ea (gmoTake GD n) e0)) -∗
      |={⊤}[∅]▷=>^[GD.gdG.gxGmo.length - n]
        ∃ (σ : AxirisG.obSt GF),
          AxirisG.obStInterp GD σ (LawfulSet.ofList GD.gdG.gxGmo) ∗
          [∗set] e0 ∈ (LawfulSet.ofList GD.gdG.gxGmo : GSet Geid),
            AxWp.fromOption (fun P => P) iprop(emp) (get? na e0) :=
  fun n hn => AxAdequacy.ordAuxK GD Hcons Hpol na ea HdomEq Hdom HeaLob _ n rfl hn

/-- THE WRAPPER, at full gmo coverage. -/
theorem adequacyOrd (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (Hpol : axpolWfGmo GD) (na : Mea GF) (ea : Sra GF)
    (HdomEq : (FiniteMap.dom_set ea : GSet Geid) = FiniteMap.dom_set na)
    (Hdom : (LawfulSet.ofList GD.gdG.gxGmo : GSet Geid) ⊆ FiniteMap.dom_set na)
    (HeaLob : ∀ e0 gm, get? ea e0 = some gm → (FiniteMap.dom_set gm : GSet Geid) ⊆ Axpol.lobp GD e0)
    (σ0 : AxirisG.obSt GF) :
    ⊢ ordEaTodo GD ea na 0 -∗
      AxirisG.obStInterp GD σ0 ∅ -∗
      |={⊤}[∅]▷=>^[GD.gdG.gxGmo.length]
        ∃ (σ : AxirisG.obSt GF),
          AxirisG.obStInterp GD σ (LawfulSet.ofList GD.gdG.gxGmo) ∗
          [∗set] e0 ∈ (LawfulSet.ofList GD.gdG.gxGmo : GSet Geid),
            AxWp.fromOption (fun P => P) iprop(emp) (get? na e0) := by
  have h := adequacyOrdAux GD Hcons Hpol na ea HdomEq Hdom HeaLob 0 (Nat.zero_le _)
  rw [Nat.sub_zero, gmoTake0] at h
  iintro Htodo Hob
  iapply h $$ Htodo
  iexists σ0
  isplitl [Hob]
  · iexact Hob
  isplitl
  · iapply BigSepS.bigSepS_empty.2
    itrivial
  · iapply BigSepS.bigSepS_empty.2
    itrivial

end ord

end Weak
