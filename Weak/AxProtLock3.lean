/-
Weak: **TIER A ADEQUACY (A7, stage T1): the GENESIS extension of `AxProtLock2.protInvLock''`**
(AxSL tier).  `protInvLock3` adds a genesis flag `g`; a fresh concrete `AxirisG` instance
`lock3AxirisG` (ob-state `(g, D, hm)`) carries the four flow equations (`lockAcq0FlowEq3`,
`lockAcqFlowEq3`, `lockRelFlowEq3`, `lockXwriteFlowEq3`); the policy `lockAxpol` with its
`tierAAdequacyAnn` side conditions; and the allocation obligation `lockHobAlloc`.

Rocq: `iris/AxProtLock3.v` @ xxvzwolszwmp.

## The Rocq header, in substance

Design `claude-notes/design/weak-memory-lb-axsl.md` §7.A, §7.A7.  Builds on `AxProtLock2`
(`protInvLock''`, `lockExtRmwReader(Unique)`, the three flow equations baked to ITS
`lock2AxirisG`) and `AxTierA2` (`tierAAdequacyAnn`'s parameter shape: `N`, `obSt0`,
`obStInterp0`, `init`, `HobAlloc`, `HsPolSub`, `HlobpSub`).
- §1 GENESIS: `lockExtRmwReader0`/`lockExtRmwReader0Unique` (the `t = 0` analogue —
  `AxLockGraph.catRmwUniqueReader` already covers `t = 0`, so it is a direct instantiation) and
  `protInvLock3`: while `g = false` the RAW genesis history `histAuth γ x 1 []` sits in the
  invariant; once the first acquire consumes it (`g = true`) the invariant records purely that
  some validated event is the (unique) `t = 0`-reading RMW on `L`.
- §2 POLICY: `lockAxpol` — `sPol e` := external rf-sources of `e` and their `gco`-predecessors
  (the reader's owned read needs the wider set; a `gmoLt`-prefix would be unsound), `lobp e` :=
  same-hart `gppoCat6`-predecessors; `lockAxpolWf`, `lockAxpolHsPolSub`, `lockAxpolHlobpSub`.
- §3 the four flow equations at `lock3AxirisG` (re-proved, since AxProtLock2's are baked to its
  own instance); `sOb0` is fixed to `sPol GD e`, the acquire's `{w_rel} ⊆ sPol GD acq` DERIVED
  (`lockPolSIntro`); the genesis conjunct is threaded through by `lockGenesisMono`.
- §4 `lockHobAlloc`, the allocation obligation at `N := GName × GName`.

**Fetches.** Nothing here depends on instruction fetches: only graph-label relations (`Lbl` has no
fetch constructor), the history and claimed ghosts, and `flowEqDyn`.

## Deviations from Rocq

1. NAMES: camelCase (map below).  No Rocq name of this file is duplicated; there are no Lean-only
   helpers (AxProtLock2's `AxProtLock2.xTokPure`/`ΦLock'OpenX` are reused).
2. VOCABULARY (as `AxProtLock2` deviation 2): `existsb` ↦ `List.any`; `list_to_set (filter …)` ↦
   `LawfulSet.ofList (List.filter …)`; `grf` ↦ `WeakRvwmoAcyc.grf`; `gx_gmo` ↦ `gxGmo`.
   The ob-state `(bool * gset geid * gmap …)` is LEFT-nested in Rocq (`σ.1.1 = g`, `σ.1.2 = D`,
   `σ.2 = hm`), RIGHT-nested in Lean (`σ.1 = g`, `σ.2.1 = D`, `σ.2.2 = hm`); literals
   `(g, D, hm)` read the same.
3. CONTEXTS (as `AxProtLock2` deviation 3): `invGS_gen HasNoLc Σ` ↦ `[InvGS_gen hlc GF]` for any
   `hlc`; `(L x)` explicit leading arguments; Rocq's `Proof using All` makes every lemma take
   `Hxy`; here only `lockXwriteFlowEq3` and `lockHobAlloc` (the proofs that use it) take
   `hxy : x ≠ L`.  `(γ γc)` are explicit arguments of the instance and the flow equations.
4. THE POLICY: Rocq's `Global Instance lock_axpol` ↦ the plain `@[reducible] def lockAxpol`
   (NOT an instance — `AxProtInst` already declares a global `Axpol` instance, and an imported
   second one would hijack every anonymous `[Axpol]` binder downstream); statements name it
   (`@Axpol.sPol lockAxpol`, `@axpolWf lockAxpol`).  Inside the flow equations `s_pol GD e` is
   written `lockPolS GD e` (definitionally `lockAxpol.sPol GD e`).
5. THE INSTANCE (as `AxProtLock2` deviation 4): `lock3AxirisG` is `@[reducible]`, named in
   statements; Rocq's `ax_text` field does not exist in Lean (Stage C).
6. STATEMENT SHAPES (as `AxProt` deviation 4): `P -∗ flowEqDyn …` ↦ `P ⊢ flowEqDyn …`;
   `lockGenesisMono`'s `P -∗ Q` ↦ `P ⊢ Q`; pure premises stay `→`.

**Rocq → Lean name map.**  `lock_pol_s_b` `lockPolSB`, `lock_pol_s` `lockPolS`,
`grf_src_gx_gmo` `grfSrcGxGmo`, `lock_pol_s_b_spec` `lockPolSBSpec`, `lock_pol_lobp`
`lockPolLobp`, `lock_axpol` `lockAxpol`, `lock_axpol_Hs_pol_sub` `lockAxpolHsPolSub`,
`lock_axpol_Hlobp_sub` `lockAxpolHlobpSub`, `gmem_b_iff` `gmemBIff`, `lb_rcsc_is_r` `lbRcscIsR`,
`gppo_cat6_gmem1` `gppoCat6Gmem1`, `lock_axpol_wf` `lockAxpolWf`, `gwrites_byte_gx_gmo`
`gwritesByteGxGmo`, `lock_pol_s_intro` `lockPolSIntro`, `lock_pol_s_intro2` `lockPolSIntro2`,
`lock_ext_rmw_reader0` `lockExtRmwReader0`, `lock_ext_rmw_reader0_unique`
`lockExtRmwReader0Unique`, `prot_inv_lock3` `protInvLock3`, `prot_inv_lock3_unfold`
`protInvLock3Unfold`, `lock_genesis_mono` `lockGenesisMono`, `lock3_axirisG` `lock3AxirisG`,
`lock3_ob_st_interp` `lock3ObStInterp`, `lock_acq0_flow_eq3` `lockAcq0FlowEq3`,
`lock_acq_flow_eq3` `lockAcqFlowEq3`, `lock_rel_flow_eq3` `lockRelFlowEq3`,
`lock_xwrite_flow_eq3` `lockXwriteFlowEq3`, `lock3_N` `lock3N`, `lock3_ob_st0` `lock3ObSt0`,
`lock3_ob_st_interp0` `lock3ObStInterp0`, `lock3_init` `lock3Init`,
`lock_claimed_alloc_empty` `lockClaimedAllocEmpty`, `lock_Hob_alloc` `lockHobAlloc`.

**Not ported:** the §5 `Print Assumptions` audit (the lint's axiom check covers it).
-/
import Weak.AxProtLock2
import Weak.AxLockGraph
import Weak.AxGraphDec
import Weak.AxLifting
import Weak.AxAdequacyL
import Weak.AxTierA2

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp

/-! # 2. POLICY: `lockAxpol` -/

/-- `w ∈ sPol e`: `w` is an external rf-source of `e`, or `gco`-before one. -/
def lockPolSB (GD : Gdexec) (w e : Geid) : Bool :=
  grfeB GD.gdG w e ||
  GD.gdG.gxGmo.any (fun w0 => grfeB GD.gdG w0 e && gcoB GD.gdG w w0)

def lockPolS (GD : Gdexec) (e : Geid) : GSet Geid :=
  LawfulSet.ofList (GD.gdG.gxGmo.filter (fun w => lockPolSB GD w e))

/-- A `grf` SOURCE is always a member of `gxGmo`. -/
theorem grfSrcGxGmo (G : Gexec) (w r : Geid) : WeakRvwmoAcyc.grf G w r → w ∈ G.gxGmo := by
  rintro ⟨a, t, v, _, hat⟩
  cases t with
  | zero => simp [gwriteAt] at hat
  | succ i =>
    simp only [gwriteAt] at hat
    exact ((gwritesElemOf G w).1 (List.mem_of_getElem? hat)).1

theorem lockPolSBSpec (GD : Gdexec) (w e : Geid) :
    lockPolSB GD w e = true ↔
    grfe GD.gdG w e ∨ (∃ w0, grfe GD.gdG w0 e ∧ gco GD.gdG w w0) := by
  unfold lockPolSB
  rw [Bool.or_eq_true, grfeBSpec, List.any_eq_true]
  constructor
  · rintro (h | ⟨w0, _, hb⟩)
    · exact .inl h
    · rw [Bool.and_eq_true, grfeBSpec, gcoBSpec] at hb
      exact .inr ⟨w0, hb⟩
  · rintro (h | ⟨w0, hg, hc⟩)
    · exact .inl h
    · refine .inr ⟨w0, grfSrcGxGmo _ _ _ hg.1, ?_⟩
      rw [Bool.and_eq_true, grfeBSpec, gcoBSpec]
      exact ⟨hg, hc⟩

/-- `lobp e`: the same-hart `gppoCat6`-predecessors of `e`. -/
def lockPolLobp (GD : Gdexec) (e : Geid) : GSet Geid :=
  LawfulSet.ofList (GD.gdG.gxGmo.filter (fun w => gppoCat6B GD.gdG w e))

/-- Rocq's `Global Instance lock_axpol`, as a named definition (deviation 4). -/
@[reducible] def lockAxpol : Axpol where
  sPol := lockPolS
  lobp := lockPolLobp

theorem lockAxpolHsPolSub (GD : Gdexec) (e e' : Geid) :
    e' ∈ @Axpol.sPol lockAxpol GD e → gobCatFlow GD e' e := by
  intro h
  change e' ∈ lockPolS GD e at h
  unfold lockPolS at h
  rw [elemOfListToSet, List.mem_filter] at h
  rcases (lockPolSBSpec GD e' e).1 h.2 with hg | ⟨w0, hg0, hco⟩
  · exact .single (.inr (.inr (.inl hg)))
  · exact .tail (.single (.inr (.inr (.inr (.inl hco))))) (.inr (.inr (.inl hg0)))

theorem lockAxpolHlobpSub (GD : Gdexec) (e e' : Geid) :
    e' ∈ @Axpol.lobp lockAxpol GD e → gobCatFlow GD e' e := by
  intro h
  change e' ∈ lockPolLobp GD e at h
  unfold lockPolLobp at h
  rw [elemOfListToSet, List.mem_filter] at h
  exact .single (.inl (.inl ((gppoCat6BSpec _ _ _).1 h.2)))

theorem gmemBIff (G : Gexec) (e : Geid) : gmemB G e = true ↔ gmem G e := by
  unfold gmemB gmem
  cases hl : gxLbl G e with
  | some l =>
    constructor
    · intro h
      exact ⟨l, rfl, h⟩
    · rintro ⟨l', hl', hm⟩
      cases hl'
      exact hm
  | none =>
    constructor
    · intro h
      cases h
    · rintro ⟨l', hl', _⟩
      cases hl'

/-- Only an `LRmw` carries both annotation bits, so an RCsc endpoint is a read. -/
theorem lbRcscIsR (l : Lbl) : lbRcsc l = true → lbIsR l = true := by
  cases l <;> simp_all [lbRcsc, lbAq, lbRl, lbIsR]

/-- Every `gppoCat6` arm's predecessor endpoint is a memory event. -/
theorem gppoCat6Gmem1 (G : Gexec) (e1 e2 : Geid) : gppoCat6 G e1 e2 → gmem G e1 := by
  rintro (h1 | h2 | h3 | h4 | h5 | h6)
  · obtain ⟨_, a, hacc, _⟩ := h1
    exact gaccessesGmem G e1 a hacc
  · obtain ⟨_, a, t1, v1, t2, v2, hrd, _⟩ := h2
    exact WeakRvwmoGraph.glblIsRGmem G e1 (greadsByteGlblR G e1 a t1 v1 hrd)
  · obtain ⟨_, ⟨l, hl, hb⟩, _⟩ := h3
    simp only [lbIsRmw, Bool.and_eq_true] at hb
    exact WeakRvwmoGraph.glblIsRGmem G e1 ⟨l, hl, hb.1⟩
  · obtain ⟨pr, pw, sr, sw, _, (⟨hr, _⟩ | ⟨hw, _⟩), _⟩ := h4
    · exact WeakRvwmoGraph.glblIsRGmem G e1 hr
    · exact WeakRvwmoGraph.glblIsWGmem G e1 hw
  · obtain ⟨_, hr, _, _⟩ := h5
    exact WeakRvwmoGraph.glblIsRGmem G e1 hr
  · obtain ⟨_, ⟨l, hl, hb⟩, _⟩ := h6
    exact WeakRvwmoGraph.glblIsRGmem G e1 ⟨l, hl, lbRcscIsR l hb⟩

theorem lockAxpolWf : @axpolWf lockAxpol := by
  intro GD i k w hw
  change w ∈ lockPolLobp GD (i, k) at hw
  unfold lockPolLobp at hw
  rw [elemOfListToSet, List.mem_filter] at hw
  have hb := (gppoCat6BSpec _ _ _).1 hw.2
  obtain ⟨heq, hlt, _, _⟩ := gppoCat6Gpo _ _ _ hb
  have hmem := gppoCat6Gmem1 _ _ _ hb
  exact (elemOfEidsBefore GD i k w).2 ⟨heq, hlt, (gmemBIff GD.gdG w).2 hmem⟩

/-- `w`'s own membership in `gxGmo`, from any of its byte-write facts. -/
theorem gwritesByteGxGmo (G : Gexec) (hwf : gwf G) (w : Geid) (a : Int) (v : BitVec 8) :
    gwritesByte G w a v → w ∈ G.gxGmo := by
  intro hwb
  exact ((gwritesElemOf G w).1 (gwritesByteGwrites G w a v hwf hwb)).1

/-- THE MEMBERSHIP LEMMA the acquire uses to DERIVE `{w_rel} ⊆ sPol GD acq`. -/
theorem lockPolSIntro (GD : Gdexec) (w e : Geid) :
    w ∈ GD.gdG.gxGmo → grfe GD.gdG w e → w ∈ @Axpol.sPol lockAxpol GD e := by
  intro hin hrfe
  change w ∈ lockPolS GD e
  unfold lockPolS
  rw [elemOfListToSet, List.mem_filter]
  exact ⟨hin, (lockPolSBSpec GD w e).2 (.inl hrfe)⟩

/-- A `gco`-predecessor of the external rf-source of `e` is also in `sPol GD e`. -/
theorem lockPolSIntro2 (GD : Gdexec) (w w0 e : Geid) :
    w ∈ GD.gdG.gxGmo → gco GD.gdG w w0 → grfe GD.gdG w0 e → w ∈ @Axpol.sPol lockAxpol GD e := by
  intro hin hco hrfe
  change w ∈ lockPolS GD e
  unfold lockPolS
  rw [elemOfListToSet, List.mem_filter]
  exact ⟨hin, (lockPolSBSpec GD w e).2 (.inr ⟨w0, hrfe, hco⟩)⟩

/-! # 1. GENESIS: `protInvLock3` -/

section lock3pure

variable (L : Int)

/-- `e` is an RMW on `L` whose read half reads the INITIAL IMAGE (`t = 0`). -/
def lockExtRmwReader0 (GD : Gdexec) (e : Geid) : Prop :=
  (∃ v, greadsByte GD.gdG e L 0 v) ∧ (∃ v, gwritesByte GD.gdG e L v)

theorem lockExtRmwReader0Unique (GD : Gdexec) (e1 e2 : Geid) :
    rvwmoCatConsistent GD →
    lockExtRmwReader0 L GD e1 → lockExtRmwReader0 L GD e2 → e1 = e2 := by
  rintro hcons ⟨⟨v1, hrd1⟩, ⟨v1', hwr1⟩⟩ ⟨⟨v2, hrd2⟩, ⟨v2', hwr2⟩⟩
  exact catRmwUniqueReader GD L 0 e1 e2 v1 v2 v1' v2' hcons hrd1 hwr1 hrd2 hwr2

end lock3pure

section lock3

variable {GF : BundledGFunctors} [AxlogG GF Hent] [AxLockG GF] (L x : Int)

/-- `protInvLock''` plus the genesis flag `g`. -/
def protInvLock3 (γ γc : GName) (GD : Gdexec) (s D : GSet Geid)
    (hm : GMapF Geid (List Hent)) (g : Bool) : IProp GF :=
  iprop(AxProtLock2.protInvLock'' L x γ γc GD s D hm ∗
    ((⌜g = false⌝ ∗ histAuth γ x 1 []) ∨
     (⌜g = true⌝ ∗ ⌜∃ e, e ∈ s ∧ lockExtRmwReader0 L GD e⌝)))

theorem protInvLock3Unfold (γ γc : GName) (GD : Gdexec) (s D : GSet Geid)
    (hm : GMapF Geid (List Hent)) (g : Bool) :
    protInvLock3 (GF := GF) L x γ γc GD s D hm g ⊣⊢
      iprop(AxProtLock2.protInvLock'' L x γ γc GD s D hm ∗
        ((⌜g = false⌝ ∗ histAuth γ x 1 []) ∨
         (⌜g = true⌝ ∗ ⌜∃ e, e ∈ s ∧ lockExtRmwReader0 L GD e⌝))) :=
  .rfl

omit [AxLockG GF] in
/-- The genesis conjunct is monotone in the validated set. -/
theorem lockGenesisMono (γ : GName) (GD : Gdexec) (g : Bool) (s s' : GSet Geid) :
    s ⊆ s' →
    iprop((⌜g = false⌝ ∗ histAuth (GF := GF) γ x 1 []) ∨
      (⌜g = true⌝ ∗ ⌜∃ e, e ∈ s ∧ lockExtRmwReader0 L GD e⌝)) ⊢
    iprop((⌜g = false⌝ ∗ histAuth γ x 1 []) ∨
      (⌜g = true⌝ ∗ ⌜∃ e, e ∈ s' ∧ lockExtRmwReader0 L GD e⌝)) := by
  intro hsub
  iintro (H | ⟨%hg, %hw⟩)
  · ileft
    iexact H
  · iright
    isplitl []
    · ipureintro
      exact hg
    · ipureintro
      obtain ⟨e, hin, hp⟩ := hw
      exact ⟨e, hsub _ hin, hp⟩

/-! # 3. The four flow equations at `lock3AxirisG` -/

@[reducible] def lock3AxirisG (γ γc : GName) : AxirisG GF where
  annotInterp := fun _ => iprop(True)
  gconstInterp := fun _ => iprop(True)
  obSt := Bool × GSet Geid × GMapF Geid (List Hent)
  obStInterp := fun GD σ s => protInvLock3 L x γ γc GD s σ.2.1 σ.2.2 σ.1
  logTsT := Unit
  localInterp := fun _ _ _ _ => iprop(True)

theorem lock3ObStInterp (γ γc : GName) (GD : Gdexec) (g : Bool) (D : GSet Geid)
    (hm : GMapF Geid (List Hent)) (s : GSet Geid) :
    AxirisG.obStInterp (self := lock3AxirisG (GF := GF) L x γ γc) GD
        ((g, D, hm) : Bool × GSet Geid × GMapF Geid (List Hent)) s ⊣⊢
      protInvLock3 L x γ γc GD s D hm g :=
  .rfl

section flows

variable {hlc : HasLC} [InvGS_gen hlc GF]

/-! ## 3.1 THE GENESIS ACQUIRE -/

theorem lockAcq0FlowEq3 (γ γc : GName) (GD : Gdexec) (acq : Geid) (flowIn : Mea GF) :
    rvwmoCatConsistent GD →
    GD.gdG.gxImg L = some b0 →
    greadsByte GD.gdG acq L 0 b0 →
    gwritesByte GD.gdG acq L b1 →
    (∀ a' v', gwritesByte GD.gdG acq a' v' → a' = L) →
    ⊢ @flowEqDyn hlc GF _ (lock3AxirisG L x γ γc) GD acq (lockPolS GD acq) flowIn
        iprop(histAuth γ x 1 []) := by
  intro hcons _ hrd0 hwb1 hsingle
  unfold flowEqDyn
  iintro %σ %sOb %Hsub %Hnin Hob -
  obtain ⟨g, D, hm⟩ := σ
  icases ((lock3ObStInterp L x γ γc GD g D hm sOb).trans
    (protInvLock3Unfold L x γ γc GD sOb D hm g)).1 $$ Hob with ⟨Hlock'', Hgen⟩
  icases Hgen with (⟨-, Hx⟩ | ⟨-, %Hwit⟩)
  · icases (AxProtLock2.protInvLockUnfold'' L x γ γc GD sOb D hm).1 $$ Hlock''
      with ⟨Hlock', ⟨%H_L, HaL⟩, %Hclaims, %Hhmc⟩
    icases (protInvLockUnfold' L x γ γc GD sOb D hm).1 $$ Hlock' with ⟨Hc, Hpo, Hlocks⟩
    imod protInvWriteStep γ GD sOb acq L b1 H_L Hnin hwb1 hsingle $$ [$Hpo $HaL]
      with ⟨Hpo', HLtie⟩
    ihave HLtok := tokTieTok GD γ L _ _ $$ HLtie
    ihave HLtok := (tokSingleton γ L _ acq 1).1 $$ HLtok
    iapply fupd_mask_intro LawfulSet.empty_subset
    iintro Hclose
    inext
    imod Hclose
    imodintro
    iexists ((true, D, hm) : Bool × GSet Geid × GMapF Geid (List Hent))
    isplitl [Hc Hpo' Hlocks HLtok]
    · iapply ((lock3ObStInterp L x γ γc GD true D hm (({acq} : GSet Geid) ∪ sOb)).trans
        (protInvLock3Unfold L x γ γc GD (({acq} : GSet Geid) ∪ sOb) D hm true)).2
      isplitl [Hc Hpo' Hlocks HLtok]
      · iapply (AxProtLock2.protInvLockUnfold'' L x γ γc GD (({acq} : GSet Geid) ∪ sOb) D hm).2
        isplitl [Hc Hpo' Hlocks]
        · iapply (protInvLockUnfold' L x γ γc GD (({acq} : GSet Geid) ∪ sOb) D hm).2
          isplitl [Hc]
          · iexact Hc
          isplitl [Hpo']
          · iexact Hpo'
          iapply (AxProtLock.bigSepSUnionSingleton
            (Φ := fun e => ΦLock' L x γ γc GD e ((get? hm e).getD [])) Hnin).2
          isplitl []
          · iapply AxProtLock.ΦLock'Vacuous L x γ γc GD acq _
              (fun hbad => b0NeB1 (gwritesByteDet _ _ _ _ _ hbad hwb1))
          · iexact Hlocks
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
              · rw [elemOfSingleton.1 hw] at hwb0'
                exact (b0NeB1 (gwritesByteDet _ _ _ _ _ hwb0' hwb1)).elim
              · exact Hhmc w hw hwb0'
      · iright
        isplitl []
        · ipureintro
          rfl
        · ipureintro
          exact ⟨acq, elemOfUnionL (elemOfSingleton.2 rfl), ⟨b0, hrd0⟩, ⟨b1, hwb1⟩⟩
    · iexact Hx
  · obtain ⟨e, hein, hwe⟩ := Hwit
    have heq : e = acq :=
      lockExtRmwReader0Unique L GD e acq hcons hwe ⟨⟨b0, hrd0⟩, ⟨b1, hwb1⟩⟩
    subst heq
    exact (Hnin hein).elim

/-! ## 3.2 THE ORDINARY ACQUIRE -/

theorem lockAcqFlowEq3 (γ γc : GName) (GD : Gdexec) (w_rel acq : Geid) (flowIn : Mea GF) :
    rvwmoCatConsistent GD →
    gwritesByte GD.gdG w_rel L b0 →
    gwritesByte GD.gdG acq L b1 →
    (∀ a' v', gwritesByte GD.gdG acq a' v' → a' = L) →
    gobCat GD w_rel acq →
    lockExtRmwReader L GD w_rel acq →
    ⊢ @flowEqDyn hlc GF _ (lock3AxirisG L x γ γc) GD acq (lockPolS GD acq) flowIn
        iprop(∃ Hh, xTok GD γ x Hh acq ∗ ⌜histXWf x GD Hh ∧ lockHhPoLatest x GD Hh w_rel⌝) := by
  intro hcons hwb0 hwb1 hsingle hgob hrfe
  have hgmo0 : w_rel ∈ GD.gdG.gxGmo := gwritesByteGxGmo _ hcons.1 _ _ _ hwb0
  have hgrfe0 : grfe GD.gdG w_rel acq := by
    obtain ⟨⟨t, v, hrd, hat⟩, hhart, _⟩ := hrfe
    exact ⟨⟨L, t, v, hrd, hat⟩, hhart⟩
  have hsub0 : ({w_rel} : GSet Geid) ⊆ lockPolS GD acq := by
    intro y hy
    rw [elemOfSingleton.1 hy]
    exact lockPolSIntro GD w_rel acq hgmo0 hgrfe0
  unfold flowEqDyn
  iintro %σ %sOb %Hsub %Hnin Hob -
  obtain ⟨g, D, hm⟩ := σ
  icases ((lock3ObStInterp L x γ γc GD g D hm sOb).trans
    (protInvLock3Unfold L x γ γc GD sOb D hm g)).1 $$ Hob with ⟨Hlock'', Hgen⟩
  icases (AxProtLock2.protInvLockUnfold'' L x γ γc GD sOb D hm).1 $$ Hlock''
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
    iexists ((g, ({w_rel} : GSet Geid) ∪ D, hm) : Bool × GSet Geid × GMapF Geid (List Hent))
    isplitl [Hc' Hpo' Hcl Hrest HLtok Hgen]
    · iapply ((lock3ObStInterp L x γ γc GD g (({w_rel} : GSet Geid) ∪ D) hm
        (({acq} : GSet Geid) ∪ sOb)).trans
        (protInvLock3Unfold L x γ γc GD (({acq} : GSet Geid) ∪ sOb)
          (({w_rel} : GSet Geid) ∪ D) hm g)).2
      isplitl [Hc' Hpo' Hcl Hrest HLtok]
      · iapply (AxProtLock2.protInvLockUnfold'' L x γ γc GD (({acq} : GSet Geid) ∪ sOb)
          (({w_rel} : GSet Geid) ∪ D) hm).2
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
      · iapply lockGenesisMono L x γ GD g sOb (({acq} : GSet Geid) ∪ sOb)
          (fun _ h => elemOfUnionR h)
        iexact Hgen
    · iexists Hh
      isplitl [Htie']
      · iexact Htie'
      · ipureintro
        exact ⟨hxwf, hpl⟩
  · ihave %hinD := claimedDom γc D w_rel $$ [$Hc $Hcl]
    exact (hninD hinD).elim

/-! ## 3.3 THE RELEASE -/

theorem lockRelFlowEq3 (γ γc : GName) (GD : Gdexec) (w_rel e_last : Geid) (Hh : List Hent)
    (flowIn : Mea GF) :
    rvwmoCatConsistent GD →
    gwritesByte GD.gdG w_rel L b0 →
    (∀ a' v', gwritesByte GD.gdG w_rel a' v' → a' = L) →
    gobCat GD e_last w_rel →
    iprop(([∗map] Rin ∈ flowIn, Rin) -∗
      xTok GD γ x Hh e_last ∗ ⌜histXWf x GD Hh ∧ lockHhPoLatest x GD Hh w_rel⌝) ⊢
    @flowEqDyn hlc GF _ (lock3AxirisG L x γ γc) GD w_rel (lockPolS GD w_rel) flowIn
      iprop(True) := by
  intro hcons hwb hsingle hgob
  unfold flowEqDyn
  iintro Hflowin %σ %sOb %Hsub %Hnin Hob Hflow
  obtain ⟨g, D, hm⟩ := σ
  icases ((lock3ObStInterp L x γ γc GD g D hm sOb).trans
    (protInvLock3Unfold L x γ γc GD sOb D hm g)).1 $$ Hob with ⟨Hlock'', Hgen⟩
  icases (AxProtLock2.protInvLockUnfold'' L x γ γc GD sOb D hm).1 $$ Hlock''
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
  iexists ((g, D, insert hm w_rel Hh) : Bool × GSet Geid × GMapF Geid (List Hent))
  isplitl [Hc Hpo' Hlocks Htie' HLtok Hgen]
  · iapply ((lock3ObStInterp L x γ γc GD g D (insert hm w_rel Hh)
      (({w_rel} : GSet Geid) ∪ sOb)).trans
      (protInvLock3Unfold L x γ γc GD (({w_rel} : GSet Geid) ∪ sOb) D
        (insert hm w_rel Hh) g)).2
    isplitl [Hc Hpo' Hlocks Htie' HLtok]
    · iapply (AxProtLock2.protInvLockUnfold'' L x γ γc GD (({w_rel} : GSet Geid) ∪ sOb) D
        (insert hm w_rel Hh)).2
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
    · iapply lockGenesisMono L x γ GD g sOb (({w_rel} : GSet Geid) ∪ sOb)
        (fun _ h => elemOfUnionR h)
      iexact Hgen
  · itrivial

/-! ## 3.4 THE `x`-WRITE -/

theorem lockXwriteFlowEq3 (hxy : x ≠ L) (γ γc : GName) (GD : Gdexec) (w : Geid)
    (v : BitVec 8) (Hl : List Hent) (flowIn : Mea GF) (data : List (BitVec 8)) :
    gwritesByte GD.gdG w x v →
    (∀ a' v', gwritesByte GD.gdG w a' v' → a' = x) →
    graphData GD w = some data →
    iprop(([∗map] Rin ∈ flowIn, Rin) -∗ histAuth γ x 1 Hl) ⊢
    @flowEqDyn hlc GF _ (lock3AxirisG L x γ γc) GD w (lockPolS GD w) flowIn
      iprop(⌜graphData GD w = some data⌝) := by
  intro hwb hsingle hgd
  unfold flowEqDyn
  iintro Hflowin %σ %sOb %Hsub %Hnin Hob Hflow
  obtain ⟨g, D, hm⟩ := σ
  icases ((lock3ObStInterp L x γ γc GD g D hm sOb).trans
    (protInvLock3Unfold L x γ γc GD sOb D hm g)).1 $$ Hob with ⟨Hlock'', Hgen⟩
  icases (AxProtLock2.protInvLockUnfold'' L x γ γc GD sOb D hm).1 $$ Hlock''
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
  iexists ((g, D, hm) : Bool × GSet Geid × GMapF Geid (List Hent))
  isplitl [Hc Hpo' Hlocks HHL Hgen]
  · iapply ((lock3ObStInterp L x γ γc GD g D hm (({w} : GSet Geid) ∪ sOb)).trans
      (protInvLock3Unfold L x γ γc GD (({w} : GSet Geid) ∪ sOb) D hm g)).2
    isplitl [Hc Hpo' Hlocks HHL]
    · iapply (AxProtLock2.protInvLockUnfold'' L x γ γc GD (({w} : GSet Geid) ∪ sOb) D hm).2
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
    · iapply lockGenesisMono L x γ GD g sOb (({w} : GSet Geid) ∪ sOb)
        (fun _ h => elemOfUnionR h)
      iexact Hgen
  · ipureintro
    exact hgd

end flows

/-! # 4. `lockHobAlloc` — the allocation obligation at `N := GName × GName` -/

def lock3N : Type := GName × GName

def lock3ObSt0 : Type := Bool × GSet Geid × GMapF Geid (List Hent)

def lock3ObStInterp0 (nm : lock3N) (GD : Gdexec) (σ : lock3ObSt0) (s : GSet Geid) :
    IProp GF :=
  protInvLock3 L x nm.1 nm.2 GD s σ.2.1 σ.2.2 σ.1

def lock3Init (_nm : lock3N) (_i : Agent) : IProp GF := iprop(emp)

omit [AxlogG GF Hent] in
/-- A fresh, empty claimed authority. -/
theorem lockClaimedAllocEmpty : ⊢@{IProp GF} |==> ∃ γc, claimedAuth γc (∅ : GSet Geid) := by
  have hv : ✓ (● (DisjointLeibnizSet.valid (∅ : GSet Geid)) : Auth ClaimedUR) :=
    Auth.auth_valid.mpr DisjointLeibnizSet.valid_set
  unfold claimedAuth
  iapply iOwn_alloc (E := AxLockG.axLockInG) _ hv

/-- `tierAAdequacyAnn`'s `HobAlloc` at these choices: fresh `γ`/`γc`, genesis state
`(false, ∅, ∅)`. -/
theorem lockHobAlloc (hxy : x ≠ L) (GD : Gdexec) (harts : List Agent) :
    ⊢@{IProp GF} |==> ∃ (nm : lock3N) (σ0 : lock3ObSt0),
      lock3ObStInterp0 L x nm GD σ0 ∅ ∗ [∗list] i ∈ harts, lock3Init nm i := by
  have hdisj : ({x} : GSet Int) ## ({L} : GSet Int) := by
    rw [elemOfDisjoint]
    intro y hy hy'
    rw [elemOfSingleton.1 hy] at hy'
    exact hxy (elemOfSingleton.1 hy')
  iintro
  imod histAlloc (GF := GF) (({x} : GSet Int) ∪ {L}) [] with ⟨%γ, Halloc⟩
  imod lockClaimedAllocEmpty (GF := GF) with ⟨%γc, Hc⟩
  icases ((BigSepS.bigSepS_union hdisj).trans
    (BI.sep_congr BigSepS.bigSepS_singleton BigSepS.bigSepS_singleton)).1 $$ Halloc
    with ⟨Hx, HL⟩
  imodintro
  iexists ((γ, γc) : GName × GName)
  iexists ((false, ∅, ∅) : Bool × GSet Geid × GMapF Geid (List Hent))
  isplitl [Hc HL Hx]
  · unfold lock3ObStInterp0
    iapply (protInvLock3Unfold L x γ γc GD ∅ ∅ ∅ false).2
    isplitl [Hc HL]
    · iapply (AxProtLock2.protInvLockUnfold'' L x γ γc GD ∅ ∅ ∅).2
      isplitl [Hc]
      · iapply (protInvLockUnfold' L x γ γc GD ∅ ∅ ∅).2
        isplitl [Hc]
        · iexact Hc
        isplitl []
        · unfold protInv
          iapply BigSepS.bigSepS_empty.2
          iempintro
        · iapply BigSepS.bigSepS_empty.2
          iempintro
      · isplitl [HL]
        · iexists []
          iexact HL
        · isplitl []
          · ipureintro
            intro r hr
            exact (elemOfEmpty.1 hr).elim
          · ipureintro
            intro w hw
            exact (elemOfEmpty.1 hw).elim
    · ileft
      isplitl []
      · ipureintro
        rfl
      · iexact Hx
  · unfold lock3Init
    iapply BigSepL.bigSepL_emp.2
    iempintro

end lock3

end Weak
