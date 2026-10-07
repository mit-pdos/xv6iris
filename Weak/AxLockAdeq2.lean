/-
Weak: **PHASE-2 ADEQUACY FOR THE FOUR-EVENT LOCK HANDOFF**, part 2 of 2: the ghost allocation
`lockInitialAlloc` and the Prop-level soundness results `lockSliceSound` (§3),
`lockSliceSound'` (§4b, fresh names + the concrete instance `axGInst`) and `lockSliceSound''`
(§§5–6, the concrete instance `axG4` whose `Unit` ob-state is read off the validated set, so no
premise quantifies over the ob-state and none is `⊢`-closed).

Rocq: `iris/AxLockAdeq.v` @ xxvzwolszwmp, §§3–6 (§§0–2 in `Weak/AxLockAdeq.lean`; the Rocq
header is summarised there).

## The Rocq §§3–6 headers, in substance

§3 `lockSliceSound` strips `|={⊤}[∅]▷=>^4` and `⊢ ⌜_⌝` down to a Prop; its `Hx0`/`HL0`/`Hc0`
(`⊢ histAuth …`, `⊢ claimedAuth …`) are REFUTABLE (two full-fraction copies), `Hsn` is
unprovable — kept verbatim, as Rocq.  §4b `lockSliceSound'`: `γ`/`γc` allocated FRESH inside
the soundness continuation by `lockInitialAlloc`; the concrete instance `axGInst` makes the
bridge an identity; its `Hunclaimed`/`Hhm` (`∀ σ` over the product ob-state) are REFUTABLE —
kept verbatim, as Rocq.  §5 THE FIX: `DOf4 s`/`hmOf4 s` are plain functions of the validated
set (`w_rel4` claimed exactly once `acq4 ∈ s`; `hm` has `w_rel4 ↦ Hh4` exactly once
`w_rel4 ∈ s`), `axG4`'s `obStInterp` bakes them in, the acquire step `flowEqAmoswapAqWl4`
DERIVES "unclaimed"/"recorded" from `DOf4Unclaimed`/`hmOf4At` and calls
`protInvLockRmwStep'` directly; every other step shows `DOf4`/`hmOf4` unchanged.  §6
`lockSliceSound''`: every premise is a plain Prop about the graph.

**Ghost state allocated** (`lockInitialAlloc`, used by `lockSliceSound'`/`lockSliceSound''`):
the history log (`AxlogG GF Hent`, one name `γ`) at the two addresses `x` and `L` with empty
histories (`histAlloc` over `{x} ∪ {L}`), and the claimed-set authority (`AxLockG GF`, name
`γc`) at `∅` (`claimedAllocEmpty`).  The invariant world (`InvGS_gen .hasNoLC`) comes from
`step_fupdN_soundness_close`.  No `KptGS`/`SpinlockG` state is involved (this slice uses
neither).

**Carried premises.**  None beyond Rocq's own: `lockSliceSound` keeps Rocq's (refutable)
`Hx0`/`HL0`/`Hc0`/`Hsn` and bridge, `lockSliceSound'` Rocq's (refutable) `Hunclaimed`/`Hhm`;
`lockSliceSound''` has only graph premises (`Hcons`, the write/read/rf/ppo/acq facts,
`Hlobp_*`/`Hspol_*`, `Hgmo_perm`).

**Fetches / Q8.** No fetch content; the WP step clause is never used (phase 2 consumes only
`flowEqEa`/`flowEqDyn`), so the Q8 `fetchPin` rework does not touch this file.

## Deviations from Rocq

1. VOCABULARY as `Weak/AxLockAdeq.lean` deviation 1; `step_fupdN_soundness_no_lc'` ↦ iris-lean
   `step_fupdN_soundness_close` at `hlc := .hasNoLC` (with `m = 0` credits);
   `uPred.pure_soundness` ↦ `Iris.pure_soundness`; `bool_decide (a ∈ s)` ↦ `if a ∈ s`.
2. CONCRETE INSTANCES: Rocq's `Local Instance AxG_inst`/`AxG4` ↦ the `@[reducible] def`s
   `axGInst`/`axG4`, passed explicitly (`@lockSliceFinal2 … (axGInst γ γc L x) …`,
   `@flowEqDyn hlc GF _ (axG4 …)`, `@ordEaTodoL _ hlc GF _ (axG4 …)`,
   `AxirisG.obStInterp (self := …)`), with `letI` inside proofs; Lean's `AxirisG` has no
   `ax_text` field (O2 Stage C).  `ob_st := unit` ↦ `Unit`, `tt` ↦ `()`.
3. SECTION VARIABLES as `Weak/AxLockAdeq.lean` deviation 3: the headline §5.9 results
   (`lockSliceOrdEaTodo4`, `lockSliceAdequate4`, `lockSliceFinal4`) take Rocq's full Context
   (`γ γc L x Hxl GD i_A i_B k_rel k_acq w_x r_x vx` and every hypothesis); the bookkeeping and
   per-event lemmas take only the hypotheses their proofs use.
4. REUSE: §5's verbatim-port bookkeeping (`L44*`, `inL44`, `lobSucc*4`, `na04*`/`ea04*`,
   `axpolWfL44`, `HdomEq04`/`Hdom04`/`HeaLob04`, `Hwonly4`, `Hh4*`) is proved by the §2
   lemma of `Weak/AxLockAdeq.lean` (the §5 definitions unfold to the §2 ones); the statements
   are Rocq's.  `RAcq4`'s body equals `RAcq2 … (wRel4) (acq4) (Hh4)`.
5. The step-fupd count `4` is rewritten to `3 + 1` around the `imod` of `lockInitialAlloc` (an
   `rfl` unfolding of one step).
6. Lean-only helpers (file-qualified): `AxLockAdeq.memUnionNe` (membership in `{e} ∪ s` away
   from `e`), `AxLockAdeq.todo4Wx`/`todo4Wrel`/`todo4Acq`/`todo4Rx`/`todo4Tail` (the bullets of
   `lockSliceOrdEaTodo4`).

**Rocq → Lean name map.**  §3–4b: `lock_initial_alloc` `lockInitialAlloc`, `lock_slice_sound`
`lockSliceSound`, `AxG_inst` `axGInst`, `ob_D3` `obD3`, `ob_hm3` `obHm3`, `mk_ob'3` `mkOb'3`,
`Hmk_ob'_D3` `HmkOb'D3`, `Hmk_ob'_hm3` `HmkOb'Hm3`, `Hob_eq'3` `HobEq'3`, `lock_slice_final3`
`lockSliceFinal3`, `lock_slice_sound'` `lockSliceSound'`.  §5–6: `w_rel4` `AxLockAdeq.wRel4`,
`acq4` `AxLockAdeq.acq4`, `Hh4` `AxLockAdeq.Hh4`, `L44` `AxLockAdeq.L44`, `L44_nodup`
`L44Nodup`, `L44_ne_*` `L44NeWxWrel4`/`L44NeWxAcq4`/`L44NeWxRx`/`L44NeWrel4Acq4`/`L44NeWrel4Rx`/
`L44NeAcq4Rx`, `in_L44` `inL44`, `D_of4` `AxLockAdeq.DOf4`, `hm_of4` `AxLockAdeq.hmOf4`,
`D_of4_unclaimed` `DOf4Unclaimed`, `hm_of4_at` `hmOf4At`, `D_of4_init` `DOf4Init`,
`hm_of4_init` `hmOf4Init`, `D_of4_pres_wx` `DOf4PresWx`, `hm_of4_pres_wx` `hmOf4PresWx`,
`D_of4_pres_wrel4` `DOf4PresWrel4`, `hm_of4_new_wrel4` `hmOf4NewWrel4`, `D_of4_after_acq4`
`DOf4AfterAcq4`, `hm_of4_pres_acq4` `hmOf4PresAcq4`, `D_of4_pres_rx` `DOf4PresRx`,
`hm_of4_pres_rx` `hmOf4PresRx`, `Hwonly4` `Hwonly4`, `Hh4_own2` `Hh4Own2`, `Hh4_wr` `Hh4Wr`,
`Hh4_ch` `Hh4Ch`, `Hh4_last` `Hh4Last`, `lob_succ_*4` `lobSuccWx4`/`lobSuccWrel4`/
`lobSuccAcq4`/`lobSuccRx4`, `na04` `na04`, `R_acq4` `RAcq4`, `ea04` `ea04`, `na04_*`
`na04Wx`/`na04Wrel4`/`na04Acq4`/`na04Rx`, `ea04_*` `ea04Wx`/`ea04Wrel4`/`ea04Acq4`/`ea04Rx`,
`L44_0..3` `L440..L443`, `axpol_wf_L44` `axpolWfL44`, `Hdom_eq04` `HdomEq04`, `Hdom04`
`Hdom04`, `Hea_lob04` `HeaLob04`, `AxG4` `axG4`, `ob_st_interp4_unfold` `obStInterp4Unfold`,
`flow_eq_owned_write_x4` `flowEqOwnedWriteX4`, `flow_eq_release_wx4` `flowEqReleaseWx4`,
`flow_eq_amoswap_aq_wl4` `flowEqAmoswapAqWl4`, `flow_eq_lock_read_wl4` `flowEqLockReadWl4`,
`lock_slice_ord_ea_todo4` `lockSliceOrdEaTodo4`, `lock_slice_adequate4` `lockSliceAdequate4`,
`lock_slice_final4` `lockSliceFinal4`, `lock_slice_sound''` `lockSliceSound''`.

**Not ported:** the `Print Assumptions` audits (the lint's axiom check covers them).
-/
import Weak.AxLockAdeq

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp

/-! # 3. THE Prop-LEVEL SOUNDNESS RESULT -/

section initialAlloc
variable {GF : BundledGFunctors} [AxlogG GF Hent] [AxLockG GF] (x L : Int)

/-- The three initial ghost facts, jointly allocated for fresh names. -/
theorem lockInitialAlloc (Hxl : x ≠ L) :
    ⊢ |==> ∃ γ γc, histAuth (GF := GF) γ x 1 ([] : List Hent) ∗
      histAuth γ L 1 ([] : List Hent) ∗ claimedAuth γc (∅ : GSet Geid) := by
  imod histAlloc (GF := GF) (({x} : GSet Int) ∪ {L}) ([] : List Hent) with ⟨%γ, Halloc⟩
  imod claimedAllocEmpty (GF := GF) with ⟨%γc, Hc⟩
  have hdisj : ({x} : GSet Int) ## {L} := by
    rw [elemOfDisjoint]
    intro y hy hy'
    rw [elemOfSingleton.1 hy] at hy'
    exact Hxl (elemOfSingleton.1 hy')
  icases (BigSepS.bigSepS_union (Φ := fun a => histAuth (GF := GF) γ a 1 []) hdisj).1 $$ Halloc
    with ⟨Hx, HL⟩
  ihave Hx := BigSepS.bigSepS_singleton.1 $$ Hx
  ihave HL := BigSepS.bigSepS_singleton.1 $$ HL
  imodintro
  iexists γ, γc
  isplitl [Hx]
  · iexact Hx
  isplitl [HL]
  · iexact HL
  · iexact Hc

end initialAlloc

theorem lockSliceSound {GF : BundledGFunctors} [InvGpreS GF] [axG : AxirisG GF] [Axpol]
    [AxlogG GF Hent] [AxLockG GF]
    (γ γc : GName) (L x : Int) (Hxl : x ≠ L)
    (ob_D : AxirisG.obSt GF → GSet Geid) (ob_hm : AxirisG.obSt GF → GMapF Geid (List Hent))
    (mk_ob' : GSet Geid → GMapF Geid (List Hent) → AxirisG.obSt GF)
    (Hmk_ob'_D : ∀ D hm, ob_D (mk_ob' D hm) = D)
    (Hmk_ob'_hm : ∀ D hm, ob_hm (mk_ob' D hm) = hm)
    (Hob_eq' : ∀ (GD : Gdexec) (σ : AxirisG.obSt GF) (s : GSet Geid),
      AxirisG.obStInterp GD σ s ⊣⊢ protInvLock' L x γ γc GD s (ob_D σ) (ob_hm σ))
    (Hx0 : ⊢ histAuth (GF := GF) γ x 1 ([] : List Hent))
    (HL0 : ⊢ histAuth (GF := GF) γ L 1 ([] : List Hent))
    (Hc0 : ⊢ claimedAuth (GF := GF) γc (∅ : GSet Geid))
    (GD : Gdexec) (i_A i_B : Agent) (k_rel k_acq : Nat) (w_x r_x : Geid) (vx : BitVec 8)
    (Hcons : rvwmoCatConsistent GD)
    (Hwx : gwritesByte GD.gdG w_x x vx)
    (Hsingle_wx : ∀ a' v', gwritesByte GD.gdG w_x a' v' → a' = x)
    (Hgd_wx : graphData GD w_x = some [vx])
    (Hfence : gppoCat GD w_x (i_A, k_rel))
    (Hwb0 : gwritesByte GD.gdG (i_A, k_rel) L b0)
    (Hsingle_rel : ∀ a' v', gwritesByte GD.gdG (i_A, k_rel) a' v' → a' = L)
    (Hrf : grfe GD.gdG (i_A, k_rel) (i_B, k_acq))
    (Hwb1 : gwritesByte GD.gdG (i_B, k_acq) L b1)
    (Hsingle_acq : ∀ a' v', gwritesByte GD.gdG (i_B, k_acq) a' v' → a' = L)
    (Hval_acq : graphData GD (i_B, k_acq) = some [b1])
    (Hpol : (i_A, k_rel) ∈ Axpol.sPol GD (i_B, k_acq))
    (Hunclaimed : ∀ σ : AxirisG.obSt GF, (i_A, k_rel) ∉ ob_D σ)
    (Hhm : ∀ σ : AxirisG.obSt GF, get? (ob_hm σ) (i_A, k_rel) = some [(w_x, vx)])
    (Hacq_po : gacqPo GD.gdG (i_B, k_acq) r_x)
    (Hnw : gisW GD.gdG r_x = false)
    (Hrd : ∃ t v, greadsByte GD.gdG r_x x t v)
    (Hsn : ⊢ iprop(∀ w v, ⌜gwritesByte GD.gdG w x v⌝ -∗ ⌜gmoLt GD.gdG w r_x⌝ -∗
      ∃ H', ⌜w ∈ H'.map Prod.fst⌝ ∗ histSnap (GF := GF) γ x H'))
    (Hdisc : ∀ w vv, gwritesByte GD.gdG w x vv → WeakRvwmoGraph.gpo GD.gdG w r_x → w = w_x)
    (Hlobp_wx : Axpol.lobp GD w_x = (∅ : GSet Geid))
    (Hlobp_wrel : Axpol.lobp GD (i_A, k_rel) = ({w_x} : GSet Geid))
    (Hlobp_acq : Axpol.lobp GD (i_B, k_acq) = ({(i_A, k_rel)} : GSet Geid))
    (Hlobp_rx : Axpol.lobp GD r_x = ({(i_B, k_acq)} : GSet Geid))
    (Hspol_wx : Axpol.sPol GD w_x ⊆ (∅ : GSet Geid))
    (Hspol_wrel : Axpol.sPol GD (i_A, k_rel) ⊆ ({w_x} : GSet Geid))
    (Hspol_acq_wf : Axpol.sPol GD (i_B, k_acq) ⊆ (({w_x} : GSet Geid) ∪ {(i_A, k_rel)}))
    (Hspol_rx : Axpol.sPol GD r_x ⊆
      ((({w_x} : GSet Geid) ∪ {(i_A, k_rel)}) ∪ {(i_B, k_acq)}))
    (Hgmo_perm : [w_x, (i_A, k_rel), (i_B, k_acq), r_x].Perm GD.gdG.gxGmo) :
    ∀ t v, greadsByte GD.gdG r_x x t v → v = vx := by
  intro t v Hread
  apply Iris.pure_soundness (PROP := IProp GF)
  refine step_fupdN_soundness_close (hlc := HasLC.hasNoLC) (P := iprop(⌜v = vx⌝)) 4 0 ?_
  intro Hinv
  iintro _
  ihave Hx := Hx0
  ihave HL := HL0
  ihave Hc := Hc0
  ihave Hfinal := lockSliceFinal γ γc L x Hxl ob_D ob_hm mk_ob' Hmk_ob'_D Hmk_ob'_hm Hob_eq'
    GD i_A i_B k_rel k_acq w_x r_x vx Hcons Hwx Hsingle_wx Hgd_wx Hfence Hwb0 Hsingle_rel Hrf
    Hwb1 Hsingle_acq Hval_acq Hpol Hunclaimed Hhm Hacq_po Hnw Hrd Hsn Hdisc Hlobp_wx Hlobp_wrel
    Hlobp_acq Hlobp_rx Hspol_wx Hspol_wrel Hspol_acq_wf Hspol_rx Hgmo_perm $$ Hx HL Hc
  iapply step_fupdN_wand $$ Hfinal
  iintro %H
  ipureintro
  exact H.2 t v Hread

/-! # 4b. `lockSliceSound'` — fresh names, a concrete instance -/

section lockSliceFinal3Sec
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [Axpol]
  [AxlogG GF Hent] [AxLockG GF]
variable (γ γc : GName) (L x : Int) (Hxl : x ≠ L)

/-- THE CONCRETE `AxirisG` INSTANCE: `obStInterp` IS `protInvLock'`. -/
@[reducible] def axGInst : AxirisG GF where
  annotInterp := fun _ => iprop(True)
  gconstInterp := fun _ => iprop(True)
  obSt := GSet Geid × GMapF Geid (List Hent)
  obStInterp := fun GD0 σ s => protInvLock' L x γ γc GD0 s σ.1 σ.2
  logTsT := Unit
  localInterp := fun _ _ _ _ => iprop(True)

def obD3 (σ : GSet Geid × GMapF Geid (List Hent)) : GSet Geid := σ.1
def obHm3 (σ : GSet Geid × GMapF Geid (List Hent)) : GMapF Geid (List Hent) := σ.2
def mkOb'3 (D : GSet Geid) (hm : GMapF Geid (List Hent)) :
    GSet Geid × GMapF Geid (List Hent) := (D, hm)

theorem HmkOb'D3 : ∀ D hm, obD3 (mkOb'3 D hm) = D := fun _ _ => rfl
theorem HmkOb'Hm3 : ∀ D hm, obHm3 (mkOb'3 D hm) = hm := fun _ _ => rfl

theorem HobEq'3 : ∀ (GD0 : Gdexec) (σ : GSet Geid × GMapF Geid (List Hent)) (s : GSet Geid),
    AxirisG.obStInterp (self := axGInst (GF := GF) γ γc L x) GD0 σ s ⊣⊢
      protInvLock' L x γ γc GD0 s (obD3 σ) (obHm3 σ) :=
  fun _ _ _ => ⟨.rfl, .rfl⟩

include Hxl in
theorem lockSliceFinal3 (GD : Gdexec) (i_A i_B : Agent) (k_rel k_acq : Nat)
    (w_x r_x : Geid) (vx : BitVec 8)
    (Hcons : rvwmoCatConsistent GD)
    (Hwx : gwritesByte GD.gdG w_x x vx)
    (Hsingle_wx : ∀ a' v', gwritesByte GD.gdG w_x a' v' → a' = x)
    (Hgd_wx : graphData GD w_x = some [vx])
    (Hfence : gppoCat GD w_x (i_A, k_rel))
    (Hwb0 : gwritesByte GD.gdG (i_A, k_rel) L b0)
    (Hsingle_rel : ∀ a' v', gwritesByte GD.gdG (i_A, k_rel) a' v' → a' = L)
    (Hrf : grfe GD.gdG (i_A, k_rel) (i_B, k_acq))
    (Hwb1 : gwritesByte GD.gdG (i_B, k_acq) L b1)
    (Hsingle_acq : ∀ a' v', gwritesByte GD.gdG (i_B, k_acq) a' v' → a' = L)
    (Hval_acq : graphData GD (i_B, k_acq) = some [b1])
    (Hpol : (i_A, k_rel) ∈ Axpol.sPol GD (i_B, k_acq))
    (Hunclaimed : ∀ σ : GSet Geid × GMapF Geid (List Hent), (i_A, k_rel) ∉ σ.1)
    (Hhm : ∀ σ : GSet Geid × GMapF Geid (List Hent), get? σ.2 (i_A, k_rel) = some [(w_x, vx)])
    (Hacq_po : gacqPo GD.gdG (i_B, k_acq) r_x)
    (Hnw : gisW GD.gdG r_x = false)
    (Hrd : ∃ t v, greadsByte GD.gdG r_x x t v)
    (Hlobp_wx : Axpol.lobp GD w_x = (∅ : GSet Geid))
    (Hlobp_wrel : Axpol.lobp GD (i_A, k_rel) = ({w_x} : GSet Geid))
    (Hlobp_acq : Axpol.lobp GD (i_B, k_acq) = ({(i_A, k_rel)} : GSet Geid))
    (Hlobp_rx : Axpol.lobp GD r_x = ({(i_B, k_acq)} : GSet Geid))
    (Hspol_wx : Axpol.sPol GD w_x ⊆ (∅ : GSet Geid))
    (Hspol_wrel : Axpol.sPol GD (i_A, k_rel) ⊆ ({w_x} : GSet Geid))
    (Hspol_acq_wf : Axpol.sPol GD (i_B, k_acq) ⊆ (({w_x} : GSet Geid) ∪ {(i_A, k_rel)}))
    (Hspol_rx : Axpol.sPol GD r_x ⊆
      ((({w_x} : GSet Geid) ∪ {(i_A, k_rel)}) ∪ {(i_B, k_acq)}))
    (Hgmo_perm : [w_x, (i_A, k_rel), (i_B, k_acq), r_x].Perm GD.gdG.gxGmo) :
    ⊢ histAuth (GF := GF) γ x 1 [] -∗ histAuth γ L 1 [] -∗ claimedAuth γc (∅ : GSet Geid) -∗
      |={⊤}[∅]▷=>^[4]
        ⌜grfAt GD.gdG x w_x r_x ∧ ∀ t v, greadsByte GD.gdG r_x x t v → v = vx⌝ :=
  @lockSliceFinal2 hlc GF _ (axGInst γ γc L x) _ _ _ γ γc L x Hxl obD3 obHm3 mkOb'3
    HmkOb'D3 HmkOb'Hm3 (HobEq'3 γ γc L x)
    GD i_A i_B k_rel k_acq w_x r_x vx Hcons Hwx Hsingle_wx Hgd_wx Hfence Hwb0 Hsingle_rel Hrf
    Hwb1 Hsingle_acq Hval_acq Hpol Hunclaimed Hhm Hacq_po Hnw Hrd Hlobp_wx Hlobp_wrel
    Hlobp_acq Hlobp_rx Hspol_wx Hspol_wrel Hspol_acq_wf Hspol_rx Hgmo_perm

end lockSliceFinal3Sec

theorem lockSliceSound' {GF : BundledGFunctors} [AxlogG GF Hent] [AxLockG GF] [InvGpreS GF]
    [Axpol]
    (L x : Int) (Hxl : x ≠ L)
    (GD : Gdexec) (i_A i_B : Agent) (k_rel k_acq : Nat) (w_x r_x : Geid) (vx : BitVec 8)
    (Hcons : rvwmoCatConsistent GD)
    (Hwx : gwritesByte GD.gdG w_x x vx)
    (Hsingle_wx : ∀ a' v', gwritesByte GD.gdG w_x a' v' → a' = x)
    (Hgd_wx : graphData GD w_x = some [vx])
    (Hfence : gppoCat GD w_x (i_A, k_rel))
    (Hwb0 : gwritesByte GD.gdG (i_A, k_rel) L b0)
    (Hsingle_rel : ∀ a' v', gwritesByte GD.gdG (i_A, k_rel) a' v' → a' = L)
    (Hrf : grfe GD.gdG (i_A, k_rel) (i_B, k_acq))
    (Hwb1 : gwritesByte GD.gdG (i_B, k_acq) L b1)
    (Hsingle_acq : ∀ a' v', gwritesByte GD.gdG (i_B, k_acq) a' v' → a' = L)
    (Hval_acq : graphData GD (i_B, k_acq) = some [b1])
    (Hpol : (i_A, k_rel) ∈ Axpol.sPol GD (i_B, k_acq))
    (Hunclaimed : ∀ σ : GSet Geid × GMapF Geid (List Hent), (i_A, k_rel) ∉ σ.1)
    (Hhm : ∀ σ : GSet Geid × GMapF Geid (List Hent), get? σ.2 (i_A, k_rel) = some [(w_x, vx)])
    (Hacq_po : gacqPo GD.gdG (i_B, k_acq) r_x)
    (Hnw : gisW GD.gdG r_x = false)
    (Hrd : ∃ t v, greadsByte GD.gdG r_x x t v)
    (Hlobp_wx : Axpol.lobp GD w_x = (∅ : GSet Geid))
    (Hlobp_wrel : Axpol.lobp GD (i_A, k_rel) = ({w_x} : GSet Geid))
    (Hlobp_acq : Axpol.lobp GD (i_B, k_acq) = ({(i_A, k_rel)} : GSet Geid))
    (Hlobp_rx : Axpol.lobp GD r_x = ({(i_B, k_acq)} : GSet Geid))
    (Hspol_wx : Axpol.sPol GD w_x ⊆ (∅ : GSet Geid))
    (Hspol_wrel : Axpol.sPol GD (i_A, k_rel) ⊆ ({w_x} : GSet Geid))
    (Hspol_acq_wf : Axpol.sPol GD (i_B, k_acq) ⊆ (({w_x} : GSet Geid) ∪ {(i_A, k_rel)}))
    (Hspol_rx : Axpol.sPol GD r_x ⊆
      ((({w_x} : GSet Geid) ∪ {(i_A, k_rel)}) ∪ {(i_B, k_acq)}))
    (Hgmo_perm : [w_x, (i_A, k_rel), (i_B, k_acq), r_x].Perm GD.gdG.gxGmo) :
    ∀ t v, greadsByte GD.gdG r_x x t v → v = vx := by
  intro t v Hread
  apply Iris.pure_soundness (PROP := IProp GF)
  refine step_fupdN_soundness_close (hlc := HasLC.hasNoLC) (P := iprop(⌜v = vx⌝)) 4 0 ?_
  intro Hinv
  iintro _
  have hs : ∀ (P : IProp GF),
      iprop(|={⊤}[∅]▷=>^[3 + 1] P) = iprop(|={⊤}[∅]▷=> |={⊤}[∅]▷=>^[3] P) := fun _ => rfl
  rw [show (4 : Nat) = 3 + 1 from rfl, hs]
  imod lockInitialAlloc (GF := GF) x L Hxl with ⟨%γ, %γc, Hx, HL, Hc⟩
  rw [← hs]
  ihave Hfinal := lockSliceFinal3 γ γc L x Hxl GD i_A i_B k_rel k_acq w_x r_x vx
    Hcons Hwx Hsingle_wx Hgd_wx Hfence Hwb0 Hsingle_rel Hrf Hwb1 Hsingle_acq Hval_acq
    Hpol Hunclaimed Hhm Hacq_po Hnw Hrd Hlobp_wx Hlobp_wrel Hlobp_acq Hlobp_rx
    Hspol_wx Hspol_wrel Hspol_acq_wf Hspol_rx Hgmo_perm $$ Hx HL Hc
  iapply step_fupdN_wand $$ Hfinal
  iintro %H
  ipureintro
  exact H.2 t v Hread


/-! # 5. `lockSliceSound''` — no `∀ σ` over the ob-state, no `⊢`-closed premise

The ob-state of the concrete instance `axG4` is `Unit`; its interpretation reads the claimed
domain and the handoff map off the validated set (`AxLockAdeq.DOf4`/`AxLockAdeq.hmOf4`), so
the acquire's step DERIVES "`w_rel4` unclaimed" / "`hm` has `w_rel4 ↦ Hh4`". -/

/-! ## 5.0 The four events (as §2) -/

abbrev AxLockAdeq.wRel4 (i_A : Agent) (k_rel : Nat) : Geid := (i_A, k_rel)
abbrev AxLockAdeq.acq4 (i_B : Agent) (k_acq : Nat) : Geid := (i_B, k_acq)
def AxLockAdeq.Hh4 (w_x : Geid) (vx : BitVec 8) : List Hent := [(w_x, vx)]
def AxLockAdeq.L44 (i_A i_B : Agent) (k_rel k_acq : Nat) (w_x r_x : Geid) : List Geid :=
  [w_x, AxLockAdeq.wRel4 i_A k_rel, AxLockAdeq.acq4 i_B k_acq, r_x]

/-! ## 5.2 `DOf4`/`hmOf4` — the claimed domain and the handoff map, read off `s` -/

def AxLockAdeq.DOf4 (i_A i_B : Agent) (k_rel k_acq : Nat) (s : GSet Geid) : GSet Geid :=
  if AxLockAdeq.acq4 i_B k_acq ∈ s then {AxLockAdeq.wRel4 i_A k_rel} else ∅

def AxLockAdeq.hmOf4 (i_A : Agent) (k_rel : Nat) (w_x : Geid) (vx : BitVec 8) (s : GSet Geid) :
    GMapF Geid (List Hent) :=
  if AxLockAdeq.wRel4 i_A k_rel ∈ s then {[AxLockAdeq.wRel4 i_A k_rel := AxLockAdeq.Hh4 w_x vx]}
  else ∅

/-- Lean-only: membership in `{e} ∪ s` away from `e`. -/
theorem AxLockAdeq.memUnionNe {a e : Geid} {s : GSet Geid} (h : e ≠ a) :
    a ∈ ({e} : GSet Geid) ∪ s ↔ a ∈ s :=
  ⟨fun hm => (elemOfUnion.1 hm).resolve_left (fun he => h (elemOfSingleton.1 he).symm),
    elemOfUnionR⟩

section graph4
variable (GD : Gdexec) (i_A i_B : Agent) (k_rel k_acq : Nat) (w_x r_x : Geid)

/-! ## 5.1 Bookkeeping (as §2.1) -/

theorem L44Nodup (Hcons : rvwmoCatConsistent GD)
    (Hgmo_perm : (AxLockAdeq.L44 i_A i_B k_rel k_acq w_x r_x).Perm GD.gdG.gxGmo) :
    (AxLockAdeq.L44 i_A i_B k_rel k_acq w_x r_x).Nodup :=
  L4Nodup GD i_A i_B k_rel k_acq w_x r_x Hcons Hgmo_perm

theorem L44NeWxWrel4 (Hcons : rvwmoCatConsistent GD)
    (Hgmo_perm : (AxLockAdeq.L44 i_A i_B k_rel k_acq w_x r_x).Perm GD.gdG.gxGmo) :
    w_x ≠ AxLockAdeq.wRel4 i_A k_rel :=
  L4NeWxWrel GD i_A i_B k_rel k_acq w_x r_x Hcons Hgmo_perm

theorem L44NeWxAcq4 (Hcons : rvwmoCatConsistent GD)
    (Hgmo_perm : (AxLockAdeq.L44 i_A i_B k_rel k_acq w_x r_x).Perm GD.gdG.gxGmo) :
    w_x ≠ AxLockAdeq.acq4 i_B k_acq :=
  L4NeWxAcq GD i_A i_B k_rel k_acq w_x r_x Hcons Hgmo_perm

theorem L44NeWxRx (Hcons : rvwmoCatConsistent GD)
    (Hgmo_perm : (AxLockAdeq.L44 i_A i_B k_rel k_acq w_x r_x).Perm GD.gdG.gxGmo) :
    w_x ≠ r_x :=
  L4NeWxRx GD i_A i_B k_rel k_acq w_x r_x Hcons Hgmo_perm

theorem L44NeWrel4Acq4 (Hcons : rvwmoCatConsistent GD)
    (Hgmo_perm : (AxLockAdeq.L44 i_A i_B k_rel k_acq w_x r_x).Perm GD.gdG.gxGmo) :
    AxLockAdeq.wRel4 i_A k_rel ≠ AxLockAdeq.acq4 i_B k_acq :=
  L4NeWrelAcq GD i_A i_B k_rel k_acq w_x r_x Hcons Hgmo_perm

theorem L44NeWrel4Rx (Hcons : rvwmoCatConsistent GD)
    (Hgmo_perm : (AxLockAdeq.L44 i_A i_B k_rel k_acq w_x r_x).Perm GD.gdG.gxGmo) :
    AxLockAdeq.wRel4 i_A k_rel ≠ r_x :=
  L4NeWrelRx GD i_A i_B k_rel k_acq w_x r_x Hcons Hgmo_perm

theorem L44NeAcq4Rx (Hcons : rvwmoCatConsistent GD)
    (Hgmo_perm : (AxLockAdeq.L44 i_A i_B k_rel k_acq w_x r_x).Perm GD.gdG.gxGmo) :
    AxLockAdeq.acq4 i_B k_acq ≠ r_x :=
  L4NeAcqRx GD i_A i_B k_rel k_acq w_x r_x Hcons Hgmo_perm

theorem inL44 (Hgmo_perm : (AxLockAdeq.L44 i_A i_B k_rel k_acq w_x r_x).Perm GD.gdG.gxGmo)
    (e : Geid) : e ∈ GD.gdG.gxGmo →
      e = w_x ∨ e = AxLockAdeq.wRel4 i_A k_rel ∨ e = AxLockAdeq.acq4 i_B k_acq ∨ e = r_x :=
  inL4 GD i_A i_B k_rel k_acq w_x r_x Hgmo_perm e

/-! ## 5.2 `DOf4`/`hmOf4` facts -/

variable (vx : BitVec 8)

theorem DOf4Unclaimed (s : GSet Geid) :
    AxLockAdeq.acq4 i_B k_acq ∉ s → AxLockAdeq.DOf4 i_A i_B k_rel k_acq s = ∅ := by
  intro Hn
  unfold AxLockAdeq.DOf4
  rw [if_neg Hn]

theorem hmOf4At (s : GSet Geid) :
    AxLockAdeq.wRel4 i_A k_rel ∈ s →
      get? (AxLockAdeq.hmOf4 i_A k_rel w_x vx s) (AxLockAdeq.wRel4 i_A k_rel) =
        some (AxLockAdeq.Hh4 w_x vx) := by
  intro Hin
  unfold AxLockAdeq.hmOf4
  rw [if_pos Hin]
  exact lookupSingleton

theorem DOf4Init : AxLockAdeq.DOf4 i_A i_B k_rel k_acq ∅ = ∅ :=
  DOf4Unclaimed i_A i_B k_rel k_acq ∅ notElemOfEmpty

theorem hmOf4Init : AxLockAdeq.hmOf4 i_A k_rel w_x vx ∅ = ∅ := by
  unfold AxLockAdeq.hmOf4
  rw [if_neg notElemOfEmpty]

theorem DOf4PresWx (Hcons : rvwmoCatConsistent GD)
    (Hgmo_perm : (AxLockAdeq.L44 i_A i_B k_rel k_acq w_x r_x).Perm GD.gdG.gxGmo)
    (s : GSet Geid) :
    AxLockAdeq.DOf4 i_A i_B k_rel k_acq (({w_x} : GSet Geid) ∪ s) =
      AxLockAdeq.DOf4 i_A i_B k_rel k_acq s := by
  have hne := L44NeWxAcq4 GD i_A i_B k_rel k_acq w_x r_x Hcons Hgmo_perm
  unfold AxLockAdeq.DOf4
  by_cases h : AxLockAdeq.acq4 i_B k_acq ∈ s
  · rw [if_pos ((AxLockAdeq.memUnionNe hne).2 h), if_pos h]
  · rw [if_neg (fun h' => h ((AxLockAdeq.memUnionNe hne).1 h')), if_neg h]

theorem hmOf4PresWx (Hcons : rvwmoCatConsistent GD)
    (Hgmo_perm : (AxLockAdeq.L44 i_A i_B k_rel k_acq w_x r_x).Perm GD.gdG.gxGmo)
    (s : GSet Geid) :
    AxLockAdeq.hmOf4 i_A k_rel w_x vx (({w_x} : GSet Geid) ∪ s) =
      AxLockAdeq.hmOf4 i_A k_rel w_x vx s := by
  have hne := L44NeWxWrel4 GD i_A i_B k_rel k_acq w_x r_x Hcons Hgmo_perm
  unfold AxLockAdeq.hmOf4
  by_cases h : AxLockAdeq.wRel4 i_A k_rel ∈ s
  · rw [if_pos ((AxLockAdeq.memUnionNe hne).2 h), if_pos h]
  · rw [if_neg (fun h' => h ((AxLockAdeq.memUnionNe hne).1 h')), if_neg h]

theorem DOf4PresWrel4 (Hcons : rvwmoCatConsistent GD)
    (Hgmo_perm : (AxLockAdeq.L44 i_A i_B k_rel k_acq w_x r_x).Perm GD.gdG.gxGmo)
    (s : GSet Geid) :
    AxLockAdeq.DOf4 i_A i_B k_rel k_acq (({AxLockAdeq.wRel4 i_A k_rel} : GSet Geid) ∪ s) =
      AxLockAdeq.DOf4 i_A i_B k_rel k_acq s := by
  have hne := L44NeWrel4Acq4 GD i_A i_B k_rel k_acq w_x r_x Hcons Hgmo_perm
  unfold AxLockAdeq.DOf4
  by_cases h : AxLockAdeq.acq4 i_B k_acq ∈ s
  · rw [if_pos ((AxLockAdeq.memUnionNe hne).2 h), if_pos h]
  · rw [if_neg (fun h' => h ((AxLockAdeq.memUnionNe hne).1 h')), if_neg h]

theorem hmOf4NewWrel4 (s : GSet Geid) :
    AxLockAdeq.wRel4 i_A k_rel ∉ s →
    AxLockAdeq.hmOf4 i_A k_rel w_x vx (({AxLockAdeq.wRel4 i_A k_rel} : GSet Geid) ∪ s) =
      insert (AxLockAdeq.hmOf4 i_A k_rel w_x vx s) (AxLockAdeq.wRel4 i_A k_rel)
        (AxLockAdeq.Hh4 w_x vx) := by
  intro Hn
  unfold AxLockAdeq.hmOf4
  rw [if_pos (elemOfUnionL (elemOfSingleton.2 rfl)), if_neg Hn]
  exact insertEmpty.symm

theorem DOf4AfterAcq4 (s : GSet Geid) :
    AxLockAdeq.DOf4 i_A i_B k_rel k_acq (({AxLockAdeq.acq4 i_B k_acq} : GSet Geid) ∪ s) =
      {AxLockAdeq.wRel4 i_A k_rel} := by
  unfold AxLockAdeq.DOf4
  rw [if_pos (elemOfUnionL (elemOfSingleton.2 rfl))]

theorem hmOf4PresAcq4 (s : GSet Geid) :
    AxLockAdeq.wRel4 i_A k_rel ∈ s →
    AxLockAdeq.hmOf4 i_A k_rel w_x vx (({AxLockAdeq.acq4 i_B k_acq} : GSet Geid) ∪ s) =
      AxLockAdeq.hmOf4 i_A k_rel w_x vx s := by
  intro Hin
  unfold AxLockAdeq.hmOf4
  rw [if_pos (elemOfUnionR Hin), if_pos Hin]

theorem DOf4PresRx (Hcons : rvwmoCatConsistent GD)
    (Hgmo_perm : (AxLockAdeq.L44 i_A i_B k_rel k_acq w_x r_x).Perm GD.gdG.gxGmo)
    (s : GSet Geid) :
    AxLockAdeq.DOf4 i_A i_B k_rel k_acq (({r_x} : GSet Geid) ∪ s) =
      AxLockAdeq.DOf4 i_A i_B k_rel k_acq s := by
  have hne := (L44NeAcq4Rx GD i_A i_B k_rel k_acq w_x r_x Hcons Hgmo_perm).symm
  unfold AxLockAdeq.DOf4
  by_cases h : AxLockAdeq.acq4 i_B k_acq ∈ s
  · rw [if_pos ((AxLockAdeq.memUnionNe hne).2 h), if_pos h]
  · rw [if_neg (fun h' => h ((AxLockAdeq.memUnionNe hne).1 h')), if_neg h]

theorem hmOf4PresRx (Hcons : rvwmoCatConsistent GD)
    (Hgmo_perm : (AxLockAdeq.L44 i_A i_B k_rel k_acq w_x r_x).Perm GD.gdG.gxGmo)
    (s : GSet Geid) :
    AxLockAdeq.hmOf4 i_A k_rel w_x vx (({r_x} : GSet Geid) ∪ s) =
      AxLockAdeq.hmOf4 i_A k_rel w_x vx s := by
  have hne := (L44NeWrel4Rx GD i_A i_B k_rel k_acq w_x r_x Hcons Hgmo_perm).symm
  unfold AxLockAdeq.hmOf4
  by_cases h : AxLockAdeq.wRel4 i_A k_rel ∈ s
  · rw [if_pos ((AxLockAdeq.memUnionNe hne).2 h), if_pos h]
  · rw [if_neg (fun h' => h ((AxLockAdeq.memUnionNe hne).1 h')), if_neg h]

/-! ## 5.3 The four-event lock discipline (as §2.9/§2.3) -/

variable (x L : Int)

theorem Hwonly4 (Hxl : x ≠ L) (Hcons : rvwmoCatConsistent GD)
    (Hgmo_perm : (AxLockAdeq.L44 i_A i_B k_rel k_acq w_x r_x).Perm GD.gdG.gxGmo)
    (Hsingle_rel : ∀ a' v', gwritesByte GD.gdG (AxLockAdeq.wRel4 i_A k_rel) a' v' → a' = L)
    (Hsingle_acq : ∀ a' v', gwritesByte GD.gdG (AxLockAdeq.acq4 i_B k_acq) a' v' → a' = L)
    (Hnw : gisW GD.gdG r_x = false) :
    ∀ w v, gwritesByte GD.gdG w x v → w = w_x :=
  Hwonly GD i_A i_B k_rel k_acq w_x r_x x L Hxl Hcons Hgmo_perm Hsingle_rel Hsingle_acq Hnw

theorem Hh4Own2 (Hxl : x ≠ L) (Hcons : rvwmoCatConsistent GD)
    (Hgmo_perm : (AxLockAdeq.L44 i_A i_B k_rel k_acq w_x r_x).Perm GD.gdG.gxGmo)
    (Hsingle_rel : ∀ a' v', gwritesByte GD.gdG (AxLockAdeq.wRel4 i_A k_rel) a' v' → a' = L)
    (Hsingle_acq : ∀ a' v', gwritesByte GD.gdG (AxLockAdeq.acq4 i_B k_acq) a' v' → a' = L)
    (Hnw : gisW GD.gdG r_x = false) :
    ∀ w vv, gwritesByte GD.gdG w x vv → WeakRvwmoGraph.gpo GD.gdG w r_x →
      w ∈ (AxLockAdeq.Hh4 w_x vx).map Prod.fst :=
  HhOwn2 GD i_A i_B k_rel k_acq w_x r_x x vx L Hxl Hcons Hgmo_perm Hsingle_rel Hsingle_acq Hnw

theorem Hh4Wr (Hwx : gwritesByte GD.gdG w_x x vx) :
    ∀ p, p ∈ AxLockAdeq.Hh4 w_x vx → gwritesByte GD.gdG p.1 x p.2 :=
  HhWr GD w_x x vx Hwx

theorem Hh4Ch : chainWith (gmoLt GD.gdG) ((AxLockAdeq.Hh4 w_x vx).map Prod.fst) :=
  HhCh GD w_x vx

theorem Hh4Last : (AxLockAdeq.Hh4 w_x vx).getLast? = some (w_x, vx) := rfl

/-! ## 5.4 `lobSuccOf` at the four events (as §2.2) -/

section lobSucc4
variable [Axpol]
  (Hlobp_wx : Axpol.lobp GD w_x = (∅ : GSet Geid))
  (Hlobp_wrel : Axpol.lobp GD (AxLockAdeq.wRel4 i_A k_rel) = ({w_x} : GSet Geid))
  (Hlobp_acq : Axpol.lobp GD (AxLockAdeq.acq4 i_B k_acq) =
    ({AxLockAdeq.wRel4 i_A k_rel} : GSet Geid))
  (Hlobp_rx : Axpol.lobp GD r_x = ({AxLockAdeq.acq4 i_B k_acq} : GSet Geid))

include Hlobp_wx Hlobp_wrel Hlobp_acq Hlobp_rx

theorem lobSuccWx4 (Hcons : rvwmoCatConsistent GD)
    (Hgmo_perm : (AxLockAdeq.L44 i_A i_B k_rel k_acq w_x r_x).Perm GD.gdG.gxGmo) :
    lobSuccOf GD w_x = ({AxLockAdeq.wRel4 i_A k_rel} : GSet Geid) :=
  lobSuccWx GD i_A i_B k_rel k_acq w_x r_x Hcons Hgmo_perm Hlobp_wx Hlobp_wrel Hlobp_acq Hlobp_rx

theorem lobSuccWrel4 (Hcons : rvwmoCatConsistent GD)
    (Hgmo_perm : (AxLockAdeq.L44 i_A i_B k_rel k_acq w_x r_x).Perm GD.gdG.gxGmo) :
    lobSuccOf GD (AxLockAdeq.wRel4 i_A k_rel) = ({AxLockAdeq.acq4 i_B k_acq} : GSet Geid) :=
  lobSuccWrel GD i_A i_B k_rel k_acq w_x r_x Hcons Hgmo_perm Hlobp_wx Hlobp_wrel Hlobp_acq
    Hlobp_rx

theorem lobSuccAcq4 (Hcons : rvwmoCatConsistent GD)
    (Hgmo_perm : (AxLockAdeq.L44 i_A i_B k_rel k_acq w_x r_x).Perm GD.gdG.gxGmo) :
    lobSuccOf GD (AxLockAdeq.acq4 i_B k_acq) = ({r_x} : GSet Geid) :=
  lobSuccAcq GD i_A i_B k_rel k_acq w_x r_x Hcons Hgmo_perm Hlobp_wx Hlobp_wrel Hlobp_acq
    Hlobp_rx

theorem lobSuccRx4 (Hcons : rvwmoCatConsistent GD)
    (Hgmo_perm : (AxLockAdeq.L44 i_A i_B k_rel k_acq w_x r_x).Perm GD.gdG.gxGmo) :
    lobSuccOf GD r_x = (∅ : GSet Geid) :=
  lobSuccRx GD i_A i_B k_rel k_acq w_x r_x Hcons Hgmo_perm Hlobp_wx Hlobp_wrel Hlobp_acq Hlobp_rx

end lobSucc4

end graph4

/-! ## 5.5 `na04`/`ea04` and their lookups (as §2.4) -/

section maps4
variable {GF : BundledGFunctors}

def na04 (x : Int) (GD : Gdexec) (i_A i_B : Agent) (k_rel k_acq : Nat) (w_x r_x : Geid)
    (vx : BitVec 8) : Mea GF :=
  insert (insert (insert (insert (∅ : Mea GF) r_x
      iprop(⌜grfAt GD.gdG x w_x r_x ∧ ∀ t v, greadsByte GD.gdG r_x x t v → v = vx⌝))
    (AxLockAdeq.acq4 i_B k_acq) iprop(emp)) (AxLockAdeq.wRel4 i_A k_rel) iprop(emp)) w_x iprop(emp)

variable [AxlogG GF Hent]

def RAcq4 (γ : GName) (L x : Int) (GD : Gdexec) (i_A i_B : Agent) (k_rel k_acq : Nat)
    (w_x : Geid) (vx : BitVec 8) : IProp GF :=
  iprop(⌜gwritesByte GD.gdG (AxLockAdeq.wRel4 i_A k_rel) L b0⌝ ∗
    tokTie GD γ x (AxLockAdeq.Hh4 w_x vx) {[AxLockAdeq.acq4 i_B k_acq := (1 : Qp)]})

def ea04 (γ : GName) (L x : Int) (GD : Gdexec) (i_A i_B : Agent) (k_rel k_acq : Nat)
    (w_x r_x : Geid) (vx : BitVec 8) : Sra GF :=
  insert (insert (insert (insert (∅ : Sra GF) r_x
      ({[AxLockAdeq.acq4 i_B k_acq := RAcq4 γ L x GD i_A i_B k_rel k_acq w_x vx]} : Mea GF))
    (AxLockAdeq.acq4 i_B k_acq)
      ({[AxLockAdeq.wRel4 i_A k_rel := histAuth γ L 1 [(AxLockAdeq.wRel4 i_A k_rel, b0)]]} :
        Mea GF))
    (AxLockAdeq.wRel4 i_A k_rel)
      ({[w_x := tokTie GD γ x (AxLockAdeq.Hh4 w_x vx) {[w_x := (1 : Qp)]}]} : Mea GF))
    w_x (∅ : Mea GF)

end maps4

section lookups4
variable {GF : BundledGFunctors} (GD : Gdexec) (i_A i_B : Agent) (k_rel k_acq : Nat)
  (w_x r_x : Geid) (x : Int) (vx : BitVec 8)
  (Hcons : rvwmoCatConsistent GD)
  (Hgmo_perm : (AxLockAdeq.L44 i_A i_B k_rel k_acq w_x r_x).Perm GD.gdG.gxGmo)

theorem na04Wx :
    get? (na04 (GF := GF) x GD i_A i_B k_rel k_acq w_x r_x vx) w_x = some iprop(emp) :=
  na0Wx GD i_A i_B k_rel k_acq w_x r_x x vx

include Hcons Hgmo_perm

theorem na04Wrel4 :
    get? (na04 (GF := GF) x GD i_A i_B k_rel k_acq w_x r_x vx) (AxLockAdeq.wRel4 i_A k_rel) =
      some iprop(emp) :=
  na0Wrel GD i_A i_B k_rel k_acq w_x r_x x vx Hcons Hgmo_perm

theorem na04Acq4 :
    get? (na04 (GF := GF) x GD i_A i_B k_rel k_acq w_x r_x vx) (AxLockAdeq.acq4 i_B k_acq) =
      some iprop(emp) :=
  na0Acq GD i_A i_B k_rel k_acq w_x r_x x vx Hcons Hgmo_perm

theorem na04Rx :
    get? (na04 (GF := GF) x GD i_A i_B k_rel k_acq w_x r_x vx) r_x =
      some iprop(⌜grfAt GD.gdG x w_x r_x ∧ ∀ t v, greadsByte GD.gdG r_x x t v → v = vx⌝) :=
  na0Rx GD i_A i_B k_rel k_acq w_x r_x x vx Hcons Hgmo_perm

variable [AxlogG GF Hent] (γ : GName) (L : Int)

omit Hcons Hgmo_perm in
theorem ea04Wx :
    get? (ea04 (GF := GF) γ L x GD i_A i_B k_rel k_acq w_x r_x vx) w_x = some (∅ : Mea GF) :=
  ea0Wx GD i_A i_B k_rel k_acq w_x r_x x vx γ L

theorem ea04Wrel4 :
    get? (ea04 (GF := GF) γ L x GD i_A i_B k_rel k_acq w_x r_x vx) (AxLockAdeq.wRel4 i_A k_rel) =
      some ({[w_x := tokTie GD γ x (AxLockAdeq.Hh4 w_x vx) {[w_x := (1 : Qp)]}]} : Mea GF) :=
  ea0Wrel GD i_A i_B k_rel k_acq w_x r_x x vx γ L Hcons Hgmo_perm

theorem ea04Acq4 :
    get? (ea04 (GF := GF) γ L x GD i_A i_B k_rel k_acq w_x r_x vx) (AxLockAdeq.acq4 i_B k_acq) =
      some ({[AxLockAdeq.wRel4 i_A k_rel := histAuth γ L 1 [(AxLockAdeq.wRel4 i_A k_rel, b0)]]} :
        Mea GF) :=
  ea0Acq GD i_A i_B k_rel k_acq w_x r_x x vx γ L Hcons Hgmo_perm

theorem ea04Rx :
    get? (ea04 (GF := GF) γ L x GD i_A i_B k_rel k_acq w_x r_x vx) r_x =
      some ({[AxLockAdeq.acq4 i_B k_acq := RAcq4 γ L x GD i_A i_B k_rel k_acq w_x vx]} : Mea GF) :=
  ea0Rx GD i_A i_B k_rel k_acq w_x r_x x vx γ L Hcons Hgmo_perm

end lookups4

/-! ## 5.6 `axpolWfL44`/`Hdom`/`HeaLob` (as §2.6) -/

section wf4
variable {GF : BundledGFunctors} (GD : Gdexec) (i_A i_B : Agent) (k_rel k_acq : Nat)
  (w_x r_x : Geid) (x : Int) (vx : BitVec 8)

theorem L440 : (AxLockAdeq.L44 i_A i_B k_rel k_acq w_x r_x)[0]? = some w_x := rfl
theorem L441 : (AxLockAdeq.L44 i_A i_B k_rel k_acq w_x r_x)[1]? =
    some (AxLockAdeq.wRel4 i_A k_rel) := rfl
theorem L442 : (AxLockAdeq.L44 i_A i_B k_rel k_acq w_x r_x)[2]? =
    some (AxLockAdeq.acq4 i_B k_acq) := rfl
theorem L443 : (AxLockAdeq.L44 i_A i_B k_rel k_acq w_x r_x)[3]? = some r_x := rfl

theorem axpolWfL44 [Axpol]
    (Hlobp_wx : Axpol.lobp GD w_x = (∅ : GSet Geid))
    (Hlobp_wrel : Axpol.lobp GD (AxLockAdeq.wRel4 i_A k_rel) = ({w_x} : GSet Geid))
    (Hlobp_acq : Axpol.lobp GD (AxLockAdeq.acq4 i_B k_acq) =
      ({AxLockAdeq.wRel4 i_A k_rel} : GSet Geid))
    (Hlobp_rx : Axpol.lobp GD r_x = ({AxLockAdeq.acq4 i_B k_acq} : GSet Geid))
    (Hspol_wx : Axpol.sPol GD w_x ⊆ (∅ : GSet Geid))
    (Hspol_wrel : Axpol.sPol GD (AxLockAdeq.wRel4 i_A k_rel) ⊆ ({w_x} : GSet Geid))
    (Hspol_acq_wf : Axpol.sPol GD (AxLockAdeq.acq4 i_B k_acq) ⊆
      (({w_x} : GSet Geid) ∪ {AxLockAdeq.wRel4 i_A k_rel}))
    (Hspol_rx : Axpol.sPol GD r_x ⊆
      ((({w_x} : GSet Geid) ∪ {AxLockAdeq.wRel4 i_A k_rel}) ∪ {AxLockAdeq.acq4 i_B k_acq})) :
    axpolWfL GD (AxLockAdeq.L44 i_A i_B k_rel k_acq w_x r_x) :=
  axpolWfL4 GD i_A i_B k_rel k_acq w_x r_x Hlobp_wx Hlobp_wrel Hlobp_acq Hlobp_rx Hspol_wx
    Hspol_wrel Hspol_acq_wf Hspol_rx

variable [AxlogG GF Hent] (γ : GName) (L : Int)

theorem HdomEq04 :
    (FiniteMap.dom_set (ea04 (GF := GF) γ L x GD i_A i_B k_rel k_acq w_x r_x vx) : GSet Geid) =
    FiniteMap.dom_set (na04 (GF := GF) x GD i_A i_B k_rel k_acq w_x r_x vx) :=
  HdomEq0 GD i_A i_B k_rel k_acq w_x r_x x vx γ L

theorem Hdom04 :
    (LawfulSet.ofList (AxLockAdeq.L44 i_A i_B k_rel k_acq w_x r_x) : GSet Geid) ⊆
      FiniteMap.dom_set (na04 (GF := GF) x GD i_A i_B k_rel k_acq w_x r_x vx) :=
  Hdom0 GD i_A i_B k_rel k_acq w_x r_x x vx

theorem HeaLob04 [Axpol]
    (Hlobp_wx : Axpol.lobp GD w_x = (∅ : GSet Geid))
    (Hlobp_wrel : Axpol.lobp GD (AxLockAdeq.wRel4 i_A k_rel) = ({w_x} : GSet Geid))
    (Hlobp_acq : Axpol.lobp GD (AxLockAdeq.acq4 i_B k_acq) =
      ({AxLockAdeq.wRel4 i_A k_rel} : GSet Geid))
    (Hlobp_rx : Axpol.lobp GD r_x = ({AxLockAdeq.acq4 i_B k_acq} : GSet Geid)) :
    ∀ e0 gm, get? (ea04 (GF := GF) γ L x GD i_A i_B k_rel k_acq w_x r_x vx) e0 = some gm →
      (FiniteMap.dom_set gm : GSet Geid) ⊆ Axpol.lobp GD e0 :=
  AxLockAdeq.HeaLob0 GD i_A i_B k_rel k_acq w_x r_x x vx γ L Hlobp_wx Hlobp_wrel Hlobp_acq
    Hlobp_rx

end wf4

/-! ## 5.7 `axG4` — the concrete instance, `obSt := Unit` -/

section inst4
variable {GF : BundledGFunctors} [AxlogG GF Hent] [AxLockG GF]
  (γ γc : GName) (L x : Int) (i_A i_B : Agent) (k_rel k_acq : Nat) (w_x : Geid) (vx : BitVec 8)

@[reducible] def axG4 : AxirisG GF where
  annotInterp := fun _ => iprop(True)
  gconstInterp := fun _ => iprop(True)
  obSt := Unit
  obStInterp := fun GD0 _ s => protInvLock' L x γ γc GD0 s (AxLockAdeq.DOf4 i_A i_B k_rel k_acq s)
    (AxLockAdeq.hmOf4 i_A k_rel w_x vx s)
  logTsT := Unit
  localInterp := fun _ _ _ _ => iprop(True)

theorem obStInterp4Unfold (GD0 : Gdexec) (σ : Unit) (s : GSet Geid) :
    AxirisG.obStInterp (self := axG4 (GF := GF) γ γc L x i_A i_B k_rel k_acq w_x vx) GD0 σ s ⊣⊢
      protInvLock' L x γ γc GD0 s (AxLockAdeq.DOf4 i_A i_B k_rel k_acq s)
        (AxLockAdeq.hmOf4 i_A k_rel w_x vx s) :=
  ⟨.rfl, .rfl⟩

end inst4

/-! ## 5.8 The four per-event lemmas, against `axG4` -/

section events4
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [Axpol]
  [AxlogG GF Hent] [AxLockG GF]
variable (γ γc : GName) (L x : Int) (Hxl : x ≠ L)
variable (GD : Gdexec) (i_A i_B : Agent) (k_rel k_acq : Nat) (w_x r_x : Geid) (vx : BitVec 8)

include Hxl in
theorem flowEqOwnedWriteX4 (Hcons : rvwmoCatConsistent GD)
    (Hwx : gwritesByte GD.gdG w_x x vx)
    (Hsingle_wx : ∀ a' v', gwritesByte GD.gdG w_x a' v' → a' = x)
    (Hgd_wx : graphData GD w_x = some [vx])
    (Hgmo_perm : (AxLockAdeq.L44 i_A i_B k_rel k_acq w_x r_x).Perm GD.gdG.gxGmo)
    (Hl : List Hent) (s_ob0 : GSet Geid) :
    histAuth γ x 1 Hl ⊢
      @flowEqDyn hlc GF _ (axG4 γ γc L x i_A i_B k_rel k_acq w_x vx) GD w_x s_ob0 (∅ : Mea GF)
        iprop(tokTie GD γ x (Hl ++ [(w_x, vx)]) {[w_x := (1 : Qp)]} ∗
          ⌜graphData GD w_x = some [vx]⌝) := by
  iintro Hauth
  unfold flowEqDyn
  iintro %σ %sOb %Hsub %Hnin Hob -
  ihave Hob := (obStInterp4Unfold γ γc L x i_A i_B k_rel k_acq w_x vx GD σ sOb).1 $$ Hob
  icases (protInvLockUnfold' L x γ γc GD sOb _ _).1 $$ Hob with ⟨Hc, Hpo, Hlocks⟩
  imod protInvWriteStep γ GD sOb w_x x vx Hl Hnin Hwx Hsingle_wx $$ [$Hpo $Hauth]
    with ⟨Hpo', Htie⟩
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  inext
  imod Hclose
  imodintro
  iexists ()
  isplitl [Hc Hpo' Hlocks]
  · iapply (obStInterp4Unfold γ γc L x i_A i_B k_rel k_acq w_x vx GD ()
      (({w_x} : GSet Geid) ∪ sOb)).2
    rw [DOf4PresWx GD i_A i_B k_rel k_acq w_x r_x Hcons Hgmo_perm sOb,
      hmOf4PresWx GD i_A i_B k_rel k_acq w_x r_x vx Hcons Hgmo_perm sOb]
    iapply (protInvLockUnfold' L x γ γc GD (({w_x} : GSet Geid) ∪ sOb)
      (AxLockAdeq.DOf4 i_A i_B k_rel k_acq sOb) (AxLockAdeq.hmOf4 i_A k_rel w_x vx sOb)).2
    isplitl [Hc]
    · iexact Hc
    isplitl [Hpo']
    · iexact Hpo'
    iapply (AxProtLock.bigSepSUnionSingleton
      (Φ := fun e => ΦLock' L x γ γc GD e
        ((get? (AxLockAdeq.hmOf4 i_A k_rel w_x vx sOb) e).getD [])) Hnin).2
    isplitl []
    · iapply AxProtLock.ΦLock'Vacuous L x γ γc GD w_x _
        (fun hbad => Hxl (Hsingle_wx L b0 hbad).symm)
    · iexact Hlocks
  · isplitl [Htie]
    · iexact Htie
    · ipureintro
      exact Hgd_wx

theorem flowEqReleaseWx4 (Hcons : rvwmoCatConsistent GD)
    (Hfence : gppoCat GD w_x (AxLockAdeq.wRel4 i_A k_rel))
    (Hwb0 : gwritesByte GD.gdG (AxLockAdeq.wRel4 i_A k_rel) L b0)
    (Hsingle_rel : ∀ a' v', gwritesByte GD.gdG (AxLockAdeq.wRel4 i_A k_rel) a' v' → a' = L)
    (Hgmo_perm : (AxLockAdeq.L44 i_A i_B k_rel k_acq w_x r_x).Perm GD.gdG.gxGmo)
    (H_L : List Hent) (flowIn : Mea GF) :
    ⊢ histAuth γ L 1 H_L -∗
      (([∗map] Rin ∈ flowIn, Rin) -∗
        tokTie GD γ x (AxLockAdeq.Hh4 w_x vx) {[w_x := (1 : Qp)]}) -∗
      @flowEqDyn hlc GF _ (axG4 γ γc L x i_A i_B k_rel k_acq w_x vx) GD
        (AxLockAdeq.wRel4 i_A k_rel) (Axpol.sPol GD (AxLockAdeq.wRel4 i_A k_rel)) flowIn
        (histAuth γ L 1 (H_L ++ [(AxLockAdeq.wRel4 i_A k_rel, b0)])) := by
  letI : AxirisG GF := axG4 γ γc L x i_A i_B k_rel k_acq w_x vx
  have Hgob : gobCat GD w_x (AxLockAdeq.wRel4 i_A k_rel) := gobCatStep GD _ _ (Or.inl Hfence)
  iintro HaL Hwand
  iapply flowEqDynFromFlowin GD (AxLockAdeq.wRel4 i_A k_rel)
    (Axpol.sPol GD (AxLockAdeq.wRel4 i_A k_rel)) flowIn
    (tokTie GD γ x (AxLockAdeq.Hh4 w_x vx) {[w_x := (1 : Qp)]}) _ $$ [HaL] Hwand
  iintro Htie
  unfold flowEqDyn
  iintro %σ %sOb %Hsub %Hnin Hob -
  ihave Hob := (obStInterp4Unfold γ γc L x i_A i_B k_rel k_acq w_x vx GD σ sOb).1 $$ Hob
  icases (protInvLockUnfold' L x γ γc GD sOb _ _).1 $$ Hob with ⟨Hc, Hpo, Hlocks⟩
  imod protInvWriteStep γ GD sOb (AxLockAdeq.wRel4 i_A k_rel) L b0 H_L Hnin Hwb0 Hsingle_rel
    $$ [$Hpo $HaL] with ⟨Hpo', HtieL⟩
  ihave Htie' := tokRetieOb GD γ x (AxLockAdeq.Hh4 w_x vx) w_x (AxLockAdeq.wRel4 i_A k_rel)
    Hcons Hgob $$ Htie
  iunfold tokTie at HtieL
  icases HtieL with ⟨HaL', -⟩
  ihave HaL' := (tokSingleton γ L (H_L ++ [(AxLockAdeq.wRel4 i_A k_rel, b0)])
    (AxLockAdeq.wRel4 i_A k_rel) 1).1 $$ HaL'
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  inext
  imod Hclose
  imodintro
  iexists ()
  isplitl [Hc Hpo' Htie' Hlocks]
  · iapply (obStInterp4Unfold γ γc L x i_A i_B k_rel k_acq w_x vx GD ()
      (({AxLockAdeq.wRel4 i_A k_rel} : GSet Geid) ∪ sOb)).2
    rw [DOf4PresWrel4 GD i_A i_B k_rel k_acq w_x r_x Hcons Hgmo_perm sOb,
      hmOf4NewWrel4 i_A k_rel w_x vx sOb Hnin]
    iapply (protInvLockUnfold' L x γ γc GD (({AxLockAdeq.wRel4 i_A k_rel} : GSet Geid) ∪ sOb)
      (AxLockAdeq.DOf4 i_A i_B k_rel k_acq sOb)
      (insert (AxLockAdeq.hmOf4 i_A k_rel w_x vx sOb) (AxLockAdeq.wRel4 i_A k_rel)
        (AxLockAdeq.Hh4 w_x vx))).2
    isplitl [Hc]
    · iexact Hc
    isplitl [Hpo']
    · iexact Hpo'
    iapply (AxProtLock.bigSepSUnionSingleton
      (Φ := fun e => ΦLock' L x γ γc GD e ((get? (insert (AxLockAdeq.hmOf4 i_A k_rel w_x vx sOb)
        (AxLockAdeq.wRel4 i_A k_rel) (AxLockAdeq.Hh4 w_x vx)) e).getD [])) Hnin).2
    isplitl [Htie']
    · rw [lookupInsert, Option.getD_some]
      iapply AxProtLock.ΦLock'Left L x γ γc GD (AxLockAdeq.wRel4 i_A k_rel) (AxLockAdeq.Hh4 w_x vx)
      iapply tokTieXTok
      iexact Htie'
    · iapply (bigSepSLockInsertNe L x γ γc GD sOb (AxLockAdeq.hmOf4 i_A k_rel w_x vx sOb)
        (AxLockAdeq.wRel4 i_A k_rel) (AxLockAdeq.Hh4 w_x vx) Hnin).1
      iexact Hlocks
  · iexact HaL'

/-- THE KEY LEMMA: no `Hunclaimed`/`Hhm` — both DERIVED from `DOf4Unclaimed`/`hmOf4At`. -/
theorem flowEqAmoswapAqWl4 (Hcons : rvwmoCatConsistent GD)
    (Hwb0 : gwritesByte GD.gdG (AxLockAdeq.wRel4 i_A k_rel) L b0)
    (Hrf : grfe GD.gdG (AxLockAdeq.wRel4 i_A k_rel) (AxLockAdeq.acq4 i_B k_acq))
    (Hwb1 : gwritesByte GD.gdG (AxLockAdeq.acq4 i_B k_acq) L b1)
    (Hsingle_acq : ∀ a' v', gwritesByte GD.gdG (AxLockAdeq.acq4 i_B k_acq) a' v' → a' = L)
    (Hpol : AxLockAdeq.wRel4 i_A k_rel ∈ Axpol.sPol GD (AxLockAdeq.acq4 i_B k_acq))
    (H_L : List Hent) (flowIn : Mea GF) :
    (([∗map] Rin ∈ flowIn, Rin) -∗ histAuth γ L 1 H_L) ⊢
      @flowEqDyn hlc GF _ (axG4 γ γc L x i_A i_B k_rel k_acq w_x vx) GD
        (AxLockAdeq.acq4 i_B k_acq) (Axpol.sPol GD (AxLockAdeq.acq4 i_B k_acq)) flowIn
        (RAcq4 γ L x GD i_A i_B k_rel k_acq w_x vx) := by
  letI : AxirisG GF := axG4 γ γc L x i_A i_B k_rel k_acq w_x vx
  have Hgob : gobCat GD (AxLockAdeq.wRel4 i_A k_rel) (AxLockAdeq.acq4 i_B k_acq) :=
    gobCatStep GD _ _ (Or.inr (Or.inr (Or.inl Hrf)))
  have Hne4 : AxLockAdeq.Hh4 w_x vx ≠ [] := by
    unfold AxLockAdeq.Hh4
    exact List.cons_ne_nil _ _
  iintro Hwand
  iapply flowEqDynFromFlowin GD (AxLockAdeq.acq4 i_B k_acq)
    (Axpol.sPol GD (AxLockAdeq.acq4 i_B k_acq)) flowIn (histAuth γ L 1 H_L) _ $$ [] Hwand
  iintro HaL
  unfold flowEqDyn
  iintro %σ %sOb %Hsub %Hnin Hob -
  ihave Hob := (obStInterp4Unfold γ γc L x i_A i_B k_rel k_acq w_x vx GD σ sOb).1 $$ Hob
  have Hin : AxLockAdeq.wRel4 i_A k_rel ∈ sOb := Hsub _ Hpol
  have HDeq : AxLockAdeq.DOf4 i_A i_B k_rel k_acq sOb = ∅ :=
    DOf4Unclaimed i_A i_B k_rel k_acq sOb Hnin
  have HninD : AxLockAdeq.wRel4 i_A k_rel ∉ AxLockAdeq.DOf4 i_A i_B k_rel k_acq sOb := by
    rw [HDeq]
    exact notElemOfEmpty
  have Hhmeq := hmOf4At i_A k_rel w_x vx sOb Hin
  imod protInvLockRmwStep' L x γ γc GD sOb (AxLockAdeq.DOf4 i_A i_B k_rel k_acq sOb)
      (AxLockAdeq.hmOf4 i_A k_rel w_x vx sOb) (AxLockAdeq.wRel4 i_A k_rel)
      (AxLockAdeq.acq4 i_B k_acq) (AxLockAdeq.Hh4 w_x vx) H_L Hcons Hin Hnin HninD Hhmeq Hwb0
      Hwb1 Hsingle_acq Hgob Hne4 $$ [$Hob $HaL] with ⟨Hinv', %Hpure, Htie⟩
  have HDeq2 : AxLockAdeq.DOf4 i_A i_B k_rel k_acq
      (({AxLockAdeq.acq4 i_B k_acq} : GSet Geid) ∪ sOb) =
      ({AxLockAdeq.wRel4 i_A k_rel} : GSet Geid) ∪ AxLockAdeq.DOf4 i_A i_B k_rel k_acq sOb := by
    rw [DOf4AfterAcq4, HDeq, setEq]
    intro y
    simp only [elemOfUnion, elemOfEmpty, or_false]
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  inext
  imod Hclose
  imodintro
  iexists ()
  isplitl [Hinv']
  · iapply (obStInterp4Unfold γ γc L x i_A i_B k_rel k_acq w_x vx GD ()
      (({AxLockAdeq.acq4 i_B k_acq} : GSet Geid) ∪ sOb)).2
    rw [HDeq2, hmOf4PresAcq4 i_A i_B k_rel k_acq w_x vx sOb Hin]
    iexact Hinv'
  · iunfold RAcq4
    isplitl []
    · ipureintro
      exact Hpure
    · iexact Htie

theorem flowEqLockReadWl4 (Hxl : x ≠ L) (Hcons : rvwmoCatConsistent GD)
    (Hwx : gwritesByte GD.gdG w_x x vx)
    (Hsingle_rel : ∀ a' v', gwritesByte GD.gdG (AxLockAdeq.wRel4 i_A k_rel) a' v' → a' = L)
    (Hsingle_acq : ∀ a' v', gwritesByte GD.gdG (AxLockAdeq.acq4 i_B k_acq) a' v' → a' = L)
    (Hnw : gisW GD.gdG r_x = false)
    (Hrd : ∃ t v, greadsByte GD.gdG r_x x t v)
    (Hgmo_perm : (AxLockAdeq.L44 i_A i_B k_rel k_acq w_x r_x).Perm GD.gdG.gxGmo)
    (acq_e : Geid) (s_ob0 : GSet Geid) (flowIn : Mea GF)
    (Hacq : gacqPo GD.gdG acq_e r_x) :
    (([∗map] Rin ∈ flowIn, Rin) -∗
        tokTie GD γ x (AxLockAdeq.Hh4 w_x vx) {[acq_e := (1 : Qp)]}) ⊢
      @flowEqDyn hlc GF _ (axG4 γ γc L x i_A i_B k_rel k_acq w_x vx) GD r_x s_ob0 flowIn
        iprop(⌜grfAt GD.gdG x w_x r_x ∧ ∀ t v, greadsByte GD.gdG r_x x t v → v = vx⌝) := by
  have Hwo := Hwonly4 GD i_A i_B k_rel k_acq w_x r_x x L Hxl Hcons Hgmo_perm Hsingle_rel
    Hsingle_acq Hnw
  iintro Hflowin
  unfold flowEqDyn
  iintro %σ %sOb %Hsub %Hnin Hob Hflow
  ihave Htie := Hflowin $$ Hflow
  iunfold tokTie at Htie
  icases Htie with ⟨Hauth, %Htiebase⟩
  ihave Hauth := (tokSingleton γ x (AxLockAdeq.Hh4 w_x vx) acq_e 1).1 $$ Hauth
  ihave #Hsnap := histSnapGet γ x 1 (AxLockAdeq.Hh4 w_x vx) $$ Hauth
  ihave Hsn' : iprop(∀ w v, ⌜gwritesByte GD.gdG w x v⌝ -∗ ⌜gmoLt GD.gdG w r_x⌝ -∗
      ∃ (H' : List Hent), ⌜w ∈ H'.map Prod.fst⌝ ∗ histSnap (GF := GF) γ x H') $$ []
  · iintro %w %v %Hwb %_Hlt
    iexists (AxLockAdeq.Hh4 w_x vx)
    isplitl []
    · ipureintro
      rw [Hwo w v Hwb]
      exact histSnapLastIn (AxLockAdeq.Hh4 w_x vx) w_x vx (Hh4Last w_x vx)
    · iexact Hsnap
  ihave Htie2 : tokTie GD γ x (AxLockAdeq.Hh4 w_x vx) {[acq_e := (1 : Qp)]} $$ [Hauth]
  · iunfold tokTie
    isplitl [Hauth]
    · iapply (tokSingleton γ x (AxLockAdeq.Hh4 w_x vx) acq_e 1).2
      iexact Hauth
    · ipureintro
      exact Htiebase
  ihave %Hres := lockReadOwn GD γ x (AxLockAdeq.Hh4 w_x vx) w_x acq_e r_x vx Hcons
    (Hh4Wr GD w_x vx x Hwx) (Hh4Ch GD w_x vx)
    (Hh4Own2 GD i_A i_B k_rel k_acq w_x r_x vx x L Hxl Hcons Hgmo_perm Hsingle_rel Hsingle_acq
      Hnw)
    (Hh4Last w_x vx) Hacq Hrd $$ [$Htie2 $Hsn']
  ihave Hob := (obStInterp4Unfold γ γc L x i_A i_B k_rel k_acq w_x vx GD σ sOb).1 $$ Hob
  ihave Hob' : protInvLock' (GF := GF) L x γ γc GD (({r_x} : GSet Geid) ∪ sOb)
      (AxLockAdeq.DOf4 i_A i_B k_rel k_acq sOb) (AxLockAdeq.hmOf4 i_A k_rel w_x vx sOb) $$ [Hob]
  · icases (protInvLockUnfold' L x γ γc GD sOb _ _).1 $$ Hob with ⟨Hc, Hpo, Hlocks⟩
    ihave Hpo' := protInvReadStep γ GD sOb r_x Hnin Hnw $$ Hpo
    iapply (protInvLockUnfold' L x γ γc GD (({r_x} : GSet Geid) ∪ sOb) _ _).2
    isplitl [Hc]
    · iexact Hc
    isplitl [Hpo']
    · iexact Hpo'
    iapply (AxProtLock.bigSepSUnionSingleton
      (Φ := fun e => ΦLock' L x γ γc GD e
        ((get? (AxLockAdeq.hmOf4 i_A k_rel w_x vx sOb) e).getD [])) Hnin).2
    isplitl []
    · iapply AxProtLock.ΦLock'Vacuous L x γ γc GD r_x _ (fun hbad => by
        have h := AxProt.gwritesByteGisW _ _ _ _ hbad
        rw [Hnw] at h
        cases h)
    · iexact Hlocks
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  inext
  imod Hclose
  imodintro
  iexists ()
  isplitl [Hob']
  · iapply (obStInterp4Unfold γ γc L x i_A i_B k_rel k_acq w_x vx GD ()
      (({r_x} : GSet Geid) ∪ sOb)).2
    rw [DOf4PresRx GD i_A i_B k_rel k_acq w_x r_x Hcons Hgmo_perm sOb,
      hmOf4PresRx GD i_A i_B k_rel k_acq w_x r_x vx Hcons Hgmo_perm sOb]
    iexact Hob'
  · ipureintro
    exact Hres

/-! ## 5.9 The wiring, the phase-2 adequacy and the final iProp-level result -/

/-- Lean-only: `w_x`'s bullet of the walk. -/
theorem AxLockAdeq.todo4Wx (Hxl : x ≠ L) (Hcons : rvwmoCatConsistent GD)
    (Hwx : gwritesByte GD.gdG w_x x vx)
    (Hsingle_wx : ∀ a' v', gwritesByte GD.gdG w_x a' v' → a' = x)
    (Hgd_wx : graphData GD w_x = some [vx])
    (Hgmo_perm : (AxLockAdeq.L44 i_A i_B k_rel k_acq w_x r_x).Perm GD.gdG.gxGmo)
    (Hlobp_wx : Axpol.lobp GD w_x = (∅ : GSet Geid))
    (Hlobp_wrel : Axpol.lobp GD (AxLockAdeq.wRel4 i_A k_rel) = ({w_x} : GSet Geid))
    (Hlobp_acq : Axpol.lobp GD (AxLockAdeq.acq4 i_B k_acq) =
      ({AxLockAdeq.wRel4 i_A k_rel} : GSet Geid))
    (Hlobp_rx : Axpol.lobp GD r_x = ({AxLockAdeq.acq4 i_B k_acq} : GSet Geid)) :
    histAuth (GF := GF) γ x 1 [] ⊢
      AxWp.fromOption (fun R0 => AxWp.fromOption (fun flowIn =>
          @flowEqEa hlc GF _ (axG4 γ γc L x i_A i_B k_rel k_acq w_x vx) _ GD w_x
            (Axpol.sPol GD w_x) flowIn (ea04 (GF := GF) γ L x GD i_A i_B k_rel k_acq w_x r_x vx) R0)
          iprop(emp) (get? (ea04 (GF := GF) γ L x GD i_A i_B k_rel k_acq w_x r_x vx) w_x))
        iprop(emp) (get? (na04 (GF := GF) x GD i_A i_B k_rel k_acq w_x r_x vx) w_x) := by
  letI : AxirisG GF := axG4 γ γc L x i_A i_B k_rel k_acq w_x vx
  rw [na04Wx, ea04Wx]
  simp only [AxWp.fromOption]
  unfold flowEqEa
  have hdep := AxLockAdeq.eaDepositOne (ea04 (GF := GF) γ L x GD i_A i_B k_rel k_acq w_x r_x vx)
    (lobSuccOf GD w_x) w_x (AxLockAdeq.wRel4 i_A k_rel) _ _
    (lobSuccWx4 GD i_A i_B k_rel k_acq w_x r_x Hlobp_wx Hlobp_wrel Hlobp_acq Hlobp_rx Hcons
      Hgmo_perm)
    (ea04Wrel4 GD i_A i_B k_rel k_acq w_x r_x x vx Hcons Hgmo_perm γ L) lookupSingleton
  rw [show AxLockAdeq.Hh4 w_x vx = ([] : List Hent) ++ [(w_x, vx)] from rfl] at hdep
  iintro Hx
  ihave Hsrc := flowEqOwnedWriteX4 γ γc L x Hxl GD i_A i_B k_rel k_acq w_x r_x vx Hcons Hwx
    Hsingle_wx Hgd_wx Hgmo_perm [] (Axpol.sPol GD w_x) $$ Hx
  iapply AxLockAdeq.flowMono GD w_x (Axpol.sPol GD w_x) (∅ : Mea GF) _ _ $$ Hsrc
  inext
  iintro ⟨Htie, -⟩
  isplitl []
  · itrivial
  · iapply hdep.2
    iexact Htie

/-- Lean-only: `w_rel4`'s bullet. -/
theorem AxLockAdeq.todo4Wrel (Hcons : rvwmoCatConsistent GD)
    (Hfence : gppoCat GD w_x (AxLockAdeq.wRel4 i_A k_rel))
    (Hwb0 : gwritesByte GD.gdG (AxLockAdeq.wRel4 i_A k_rel) L b0)
    (Hsingle_rel : ∀ a' v', gwritesByte GD.gdG (AxLockAdeq.wRel4 i_A k_rel) a' v' → a' = L)
    (Hgmo_perm : (AxLockAdeq.L44 i_A i_B k_rel k_acq w_x r_x).Perm GD.gdG.gxGmo)
    (Hlobp_wx : Axpol.lobp GD w_x = (∅ : GSet Geid))
    (Hlobp_wrel : Axpol.lobp GD (AxLockAdeq.wRel4 i_A k_rel) = ({w_x} : GSet Geid))
    (Hlobp_acq : Axpol.lobp GD (AxLockAdeq.acq4 i_B k_acq) =
      ({AxLockAdeq.wRel4 i_A k_rel} : GSet Geid))
    (Hlobp_rx : Axpol.lobp GD r_x = ({AxLockAdeq.acq4 i_B k_acq} : GSet Geid)) :
    histAuth (GF := GF) γ L 1 [] ⊢
      AxWp.fromOption (fun R0 => AxWp.fromOption (fun flowIn =>
          @flowEqEa hlc GF _ (axG4 γ γc L x i_A i_B k_rel k_acq w_x vx) _ GD
            (AxLockAdeq.wRel4 i_A k_rel) (Axpol.sPol GD (AxLockAdeq.wRel4 i_A k_rel)) flowIn
            (ea04 (GF := GF) γ L x GD i_A i_B k_rel k_acq w_x r_x vx) R0)
          iprop(emp) (get? (ea04 (GF := GF) γ L x GD i_A i_B k_rel k_acq w_x r_x vx)
            (AxLockAdeq.wRel4 i_A k_rel)))
        iprop(emp) (get? (na04 (GF := GF) x GD i_A i_B k_rel k_acq w_x r_x vx)
          (AxLockAdeq.wRel4 i_A k_rel)) := by
  letI : AxirisG GF := axG4 γ γc L x i_A i_B k_rel k_acq w_x vx
  rw [na04Wrel4 GD i_A i_B k_rel k_acq w_x r_x x vx Hcons Hgmo_perm,
    ea04Wrel4 GD i_A i_B k_rel k_acq w_x r_x x vx Hcons Hgmo_perm γ L]
  simp only [AxWp.fromOption]
  unfold flowEqEa
  have hdep := AxLockAdeq.eaDepositOne (ea04 (GF := GF) γ L x GD i_A i_B k_rel k_acq w_x r_x vx)
    (lobSuccOf GD (AxLockAdeq.wRel4 i_A k_rel)) (AxLockAdeq.wRel4 i_A k_rel)
    (AxLockAdeq.acq4 i_B k_acq) _ _
    (lobSuccWrel4 GD i_A i_B k_rel k_acq w_x r_x Hlobp_wx Hlobp_wrel Hlobp_acq Hlobp_rx Hcons
      Hgmo_perm)
    (ea04Acq4 GD i_A i_B k_rel k_acq w_x r_x x vx Hcons Hgmo_perm γ L) lookupSingleton
  rw [show [(AxLockAdeq.wRel4 i_A k_rel, b0)] =
    ([] : List Hent) ++ [(AxLockAdeq.wRel4 i_A k_rel, b0)] from rfl] at hdep
  iintro HL
  ihave Hsrc := flowEqReleaseWx4 γ γc L x GD i_A i_B k_rel k_acq w_x r_x vx Hcons Hfence Hwb0
    Hsingle_rel Hgmo_perm []
    ({[w_x := tokTie GD γ x (AxLockAdeq.Hh4 w_x vx) {[w_x := (1 : Qp)]}]} : Mea GF) $$ HL []
  · iintro Hbag
    ihave Hbag := BigSepM.bigSepM_singleton.1 $$ Hbag
    iexact Hbag
  iapply AxLockAdeq.flowMono GD (AxLockAdeq.wRel4 i_A k_rel)
    (Axpol.sPol GD (AxLockAdeq.wRel4 i_A k_rel)) _ _ _ $$ Hsrc
  inext
  iintro HaL'
  isplitl []
  · itrivial
  · iapply hdep.2
    iexact HaL'

/-- Lean-only: `acq4`'s bullet. -/
theorem AxLockAdeq.todo4Acq (Hcons : rvwmoCatConsistent GD)
    (Hwb0 : gwritesByte GD.gdG (AxLockAdeq.wRel4 i_A k_rel) L b0)
    (Hrf : grfe GD.gdG (AxLockAdeq.wRel4 i_A k_rel) (AxLockAdeq.acq4 i_B k_acq))
    (Hwb1 : gwritesByte GD.gdG (AxLockAdeq.acq4 i_B k_acq) L b1)
    (Hsingle_acq : ∀ a' v', gwritesByte GD.gdG (AxLockAdeq.acq4 i_B k_acq) a' v' → a' = L)
    (Hpol : AxLockAdeq.wRel4 i_A k_rel ∈ Axpol.sPol GD (AxLockAdeq.acq4 i_B k_acq))
    (Hgmo_perm : (AxLockAdeq.L44 i_A i_B k_rel k_acq w_x r_x).Perm GD.gdG.gxGmo)
    (Hlobp_wx : Axpol.lobp GD w_x = (∅ : GSet Geid))
    (Hlobp_wrel : Axpol.lobp GD (AxLockAdeq.wRel4 i_A k_rel) = ({w_x} : GSet Geid))
    (Hlobp_acq : Axpol.lobp GD (AxLockAdeq.acq4 i_B k_acq) =
      ({AxLockAdeq.wRel4 i_A k_rel} : GSet Geid))
    (Hlobp_rx : Axpol.lobp GD r_x = ({AxLockAdeq.acq4 i_B k_acq} : GSet Geid)) :
    ⊢ AxWp.fromOption (fun R0 => AxWp.fromOption (fun flowIn =>
          @flowEqEa hlc GF _ (axG4 γ γc L x i_A i_B k_rel k_acq w_x vx) _ GD
            (AxLockAdeq.acq4 i_B k_acq) (Axpol.sPol GD (AxLockAdeq.acq4 i_B k_acq)) flowIn
            (ea04 (GF := GF) γ L x GD i_A i_B k_rel k_acq w_x r_x vx) R0)
          iprop(emp) (get? (ea04 (GF := GF) γ L x GD i_A i_B k_rel k_acq w_x r_x vx)
            (AxLockAdeq.acq4 i_B k_acq)))
        iprop(emp) (get? (na04 (GF := GF) x GD i_A i_B k_rel k_acq w_x r_x vx)
          (AxLockAdeq.acq4 i_B k_acq)) := by
  letI : AxirisG GF := axG4 γ γc L x i_A i_B k_rel k_acq w_x vx
  rw [na04Acq4 GD i_A i_B k_rel k_acq w_x r_x x vx Hcons Hgmo_perm,
    ea04Acq4 GD i_A i_B k_rel k_acq w_x r_x x vx Hcons Hgmo_perm γ L]
  simp only [AxWp.fromOption]
  unfold flowEqEa
  have hdep := AxLockAdeq.eaDepositOne (ea04 (GF := GF) γ L x GD i_A i_B k_rel k_acq w_x r_x vx)
    (lobSuccOf GD (AxLockAdeq.acq4 i_B k_acq)) (AxLockAdeq.acq4 i_B k_acq) r_x _ _
    (lobSuccAcq4 GD i_A i_B k_rel k_acq w_x r_x Hlobp_wx Hlobp_wrel Hlobp_acq Hlobp_rx Hcons
      Hgmo_perm)
    (ea04Rx GD i_A i_B k_rel k_acq w_x r_x x vx Hcons Hgmo_perm γ L) lookupSingleton
  ihave Hsrc := flowEqAmoswapAqWl4 γ γc L x GD i_A i_B k_rel k_acq w_x vx Hcons Hwb0 Hrf Hwb1
    Hsingle_acq Hpol [(AxLockAdeq.wRel4 i_A k_rel, b0)]
    ({[AxLockAdeq.wRel4 i_A k_rel := histAuth γ L 1 [(AxLockAdeq.wRel4 i_A k_rel, b0)]]} :
      Mea GF) $$ []
  · iintro Hbag
    ihave Hbag := BigSepM.bigSepM_singleton.1 $$ Hbag
    iexact Hbag
  iapply AxLockAdeq.flowMono GD (AxLockAdeq.acq4 i_B k_acq)
    (Axpol.sPol GD (AxLockAdeq.acq4 i_B k_acq)) _ _ _ $$ Hsrc
  inext
  iintro HR
  isplitl []
  · itrivial
  · iapply hdep.2
    iexact HR

/-- Lean-only: `r_x`'s bullet. -/
theorem AxLockAdeq.todo4Rx (Hxl : x ≠ L) (Hcons : rvwmoCatConsistent GD)
    (Hwx : gwritesByte GD.gdG w_x x vx)
    (Hsingle_rel : ∀ a' v', gwritesByte GD.gdG (AxLockAdeq.wRel4 i_A k_rel) a' v' → a' = L)
    (Hsingle_acq : ∀ a' v', gwritesByte GD.gdG (AxLockAdeq.acq4 i_B k_acq) a' v' → a' = L)
    (Hacq_po : gacqPo GD.gdG (AxLockAdeq.acq4 i_B k_acq) r_x)
    (Hnw : gisW GD.gdG r_x = false)
    (Hrd : ∃ t v, greadsByte GD.gdG r_x x t v)
    (Hgmo_perm : (AxLockAdeq.L44 i_A i_B k_rel k_acq w_x r_x).Perm GD.gdG.gxGmo)
    (Hlobp_wx : Axpol.lobp GD w_x = (∅ : GSet Geid))
    (Hlobp_wrel : Axpol.lobp GD (AxLockAdeq.wRel4 i_A k_rel) = ({w_x} : GSet Geid))
    (Hlobp_acq : Axpol.lobp GD (AxLockAdeq.acq4 i_B k_acq) =
      ({AxLockAdeq.wRel4 i_A k_rel} : GSet Geid))
    (Hlobp_rx : Axpol.lobp GD r_x = ({AxLockAdeq.acq4 i_B k_acq} : GSet Geid)) :
    ⊢ AxWp.fromOption (fun R0 => AxWp.fromOption (fun flowIn =>
          @flowEqEa hlc GF _ (axG4 γ γc L x i_A i_B k_rel k_acq w_x vx) _ GD r_x
            (Axpol.sPol GD r_x) flowIn (ea04 (GF := GF) γ L x GD i_A i_B k_rel k_acq w_x r_x vx) R0)
          iprop(emp) (get? (ea04 (GF := GF) γ L x GD i_A i_B k_rel k_acq w_x r_x vx) r_x))
        iprop(emp) (get? (na04 (GF := GF) x GD i_A i_B k_rel k_acq w_x r_x vx) r_x) := by
  letI : AxirisG GF := axG4 γ γc L x i_A i_B k_rel k_acq w_x vx
  rw [na04Rx GD i_A i_B k_rel k_acq w_x r_x x vx Hcons Hgmo_perm,
    ea04Rx GD i_A i_B k_rel k_acq w_x r_x x vx Hcons Hgmo_perm γ L]
  simp only [AxWp.fromOption]
  unfold flowEqEa
  have hdep := AxLockAdeq.eaDepositNone (ea04 (GF := GF) γ L x GD i_A i_B k_rel k_acq w_x r_x vx)
    (lobSuccOf GD r_x) r_x
    (lobSuccRx4 GD i_A i_B k_rel k_acq w_x r_x Hlobp_wx Hlobp_wrel Hlobp_acq Hlobp_rx Hcons
      Hgmo_perm)
  ihave Hsrc := flowEqLockReadWl4 γ γc L x GD i_A i_B k_rel k_acq w_x r_x vx Hxl Hcons Hwx
    Hsingle_rel Hsingle_acq Hnw Hrd Hgmo_perm (AxLockAdeq.acq4 i_B k_acq) (Axpol.sPol GD r_x)
    ({[AxLockAdeq.acq4 i_B k_acq := RAcq4 γ L x GD i_A i_B k_rel k_acq w_x vx]} : Mea GF)
    Hacq_po $$ []
  · iintro Hbag
    ihave Hbag := BigSepM.bigSepM_singleton.1 $$ Hbag
    iunfold RAcq4 at Hbag
    icases Hbag with ⟨-, Hbag⟩
    iexact Hbag
  iapply AxLockAdeq.flowMono GD r_x (Axpol.sPol GD r_x) _ _ _ $$ Hsrc
  inext
  iintro HP
  isplitl [HP]
  · iexact HP
  · iapply hdep.2
    itrivial

/-- Lean-only: the walk's empty tail. -/
theorem AxLockAdeq.todo4Tail :
    ⊢ @ordEaTodoL _ hlc GF _ (axG4 γ γc L x i_A i_B k_rel k_acq w_x vx) GD
        (ea04 γ L x GD i_A i_B k_rel k_acq w_x r_x vx) (na04 x GD i_A i_B k_rel k_acq w_x r_x vx)
        (AxLockAdeq.L44 i_A i_B k_rel k_acq w_x r_x) 4 := by
  unfold ordEaTodoL AxLockAdeq.L44
  simp only [List.drop_succ_cons, List.drop_zero]
  exact BigSepL.bigSepL_nil.2

/-! ### The headline results, over Rocq's full Context -/

variable (Hcons : rvwmoCatConsistent GD)
  (Hwx : gwritesByte GD.gdG w_x x vx)
  (Hsingle_wx : ∀ a' v', gwritesByte GD.gdG w_x a' v' → a' = x)
  (Hgd_wx : graphData GD w_x = some [vx])
  (Hfence : gppoCat GD w_x (AxLockAdeq.wRel4 i_A k_rel))
  (Hwb0 : gwritesByte GD.gdG (AxLockAdeq.wRel4 i_A k_rel) L b0)
  (Hsingle_rel : ∀ a' v', gwritesByte GD.gdG (AxLockAdeq.wRel4 i_A k_rel) a' v' → a' = L)
  (Hrf : grfe GD.gdG (AxLockAdeq.wRel4 i_A k_rel) (AxLockAdeq.acq4 i_B k_acq))
  (Hwb1 : gwritesByte GD.gdG (AxLockAdeq.acq4 i_B k_acq) L b1)
  (Hsingle_acq : ∀ a' v', gwritesByte GD.gdG (AxLockAdeq.acq4 i_B k_acq) a' v' → a' = L)
  (Hval_acq : graphData GD (AxLockAdeq.acq4 i_B k_acq) = some [b1])
  (Hpol : AxLockAdeq.wRel4 i_A k_rel ∈ Axpol.sPol GD (AxLockAdeq.acq4 i_B k_acq))
  (Hacq_po : gacqPo GD.gdG (AxLockAdeq.acq4 i_B k_acq) r_x)
  (Hnw : gisW GD.gdG r_x = false)
  (Hrd : ∃ t v, greadsByte GD.gdG r_x x t v)
  (Hlobp_wx : Axpol.lobp GD w_x = (∅ : GSet Geid))
  (Hlobp_wrel : Axpol.lobp GD (AxLockAdeq.wRel4 i_A k_rel) = ({w_x} : GSet Geid))
  (Hlobp_acq : Axpol.lobp GD (AxLockAdeq.acq4 i_B k_acq) =
    ({AxLockAdeq.wRel4 i_A k_rel} : GSet Geid))
  (Hlobp_rx : Axpol.lobp GD r_x = ({AxLockAdeq.acq4 i_B k_acq} : GSet Geid))
  (Hspol_wx : Axpol.sPol GD w_x ⊆ (∅ : GSet Geid))
  (Hspol_wrel : Axpol.sPol GD (AxLockAdeq.wRel4 i_A k_rel) ⊆ ({w_x} : GSet Geid))
  (Hspol_acq_wf : Axpol.sPol GD (AxLockAdeq.acq4 i_B k_acq) ⊆
    (({w_x} : GSet Geid) ∪ {AxLockAdeq.wRel4 i_A k_rel}))
  (Hspol_rx : Axpol.sPol GD r_x ⊆
    ((({w_x} : GSet Geid) ∪ {AxLockAdeq.wRel4 i_A k_rel}) ∪ {AxLockAdeq.acq4 i_B k_acq}))
  (Hgmo_perm : (AxLockAdeq.L44 i_A i_B k_rel k_acq w_x r_x).Perm GD.gdG.gxGmo)

include Hxl Hcons Hwx Hsingle_wx Hgd_wx Hfence Hwb0 Hsingle_rel Hrf Hwb1 Hsingle_acq Hval_acq
  Hpol Hacq_po Hnw Hrd Hlobp_wx Hlobp_wrel Hlobp_acq Hlobp_rx Hspol_wx Hspol_wrel Hspol_acq_wf
  Hspol_rx Hgmo_perm

theorem lockSliceOrdEaTodo4 :
    ⊢ histAuth (GF := GF) γ x 1 [] -∗ histAuth γ L 1 [] -∗
      @ordEaTodoL _ hlc GF _ (axG4 γ γc L x i_A i_B k_rel k_acq w_x vx) GD
        (ea04 γ L x GD i_A i_B k_rel k_acq w_x r_x vx) (na04 x GD i_A i_B k_rel k_acq w_x r_x vx)
        (AxLockAdeq.L44 i_A i_B k_rel k_acq w_x r_x) 0 := by
  letI : AxirisG GF := axG4 γ γc L x i_A i_B k_rel k_acq w_x vx
  iintro Hx HL
  iapply (ordEaTodoLCons GD _ _ _ 0 w_x (L440 i_A i_B k_rel k_acq w_x r_x)).2
  isplitl [Hx]
  · iapply AxLockAdeq.todo4Wx γ γc L x GD i_A i_B k_rel k_acq w_x r_x vx Hxl Hcons Hwx
      Hsingle_wx Hgd_wx Hgmo_perm Hlobp_wx Hlobp_wrel Hlobp_acq Hlobp_rx $$ Hx
  iapply (ordEaTodoLCons GD _ _ _ 1 _ (L441 i_A i_B k_rel k_acq w_x r_x)).2
  isplitl [HL]
  · iapply AxLockAdeq.todo4Wrel γ γc L x GD i_A i_B k_rel k_acq w_x r_x vx Hcons Hfence Hwb0
      Hsingle_rel Hgmo_perm Hlobp_wx Hlobp_wrel Hlobp_acq Hlobp_rx $$ HL
  iapply (ordEaTodoLCons GD _ _ _ 2 _ (L442 i_A i_B k_rel k_acq w_x r_x)).2
  isplitl []
  · iapply AxLockAdeq.todo4Acq γ γc L x GD i_A i_B k_rel k_acq w_x r_x vx Hcons Hwb0 Hrf Hwb1
      Hsingle_acq Hpol Hgmo_perm Hlobp_wx Hlobp_wrel Hlobp_acq Hlobp_rx
  iapply (ordEaTodoLCons GD _ _ _ 3 _ (L443 i_A i_B k_rel k_acq w_x r_x)).2
  isplitl []
  · iapply AxLockAdeq.todo4Rx γ γc L x GD i_A i_B k_rel k_acq w_x r_x vx Hxl Hcons Hwx
      Hsingle_rel Hsingle_acq Hacq_po Hnw Hrd Hgmo_perm Hlobp_wx Hlobp_wrel Hlobp_acq Hlobp_rx
  · iapply AxLockAdeq.todo4Tail γ γc L x GD i_A i_B k_rel k_acq w_x r_x vx

theorem lockSliceAdequate4 :
    ⊢ histAuth (GF := GF) γ x 1 [] -∗ histAuth γ L 1 [] -∗ claimedAuth γc (∅ : GSet Geid) -∗
      |={⊤}[∅]▷=>^[(AxLockAdeq.L44 i_A i_B k_rel k_acq w_x r_x).length]
        ∃ (σ : @AxirisG.obSt GF (axG4 γ γc L x i_A i_B k_rel k_acq w_x vx)),
          AxirisG.obStInterp (self := axG4 γ γc L x i_A i_B k_rel k_acq w_x vx) GD σ
            (LawfulSet.ofList (AxLockAdeq.L44 i_A i_B k_rel k_acq w_x r_x)) ∗
          [∗set] e0 ∈ (LawfulSet.ofList (AxLockAdeq.L44 i_A i_B k_rel k_acq w_x r_x) : GSet Geid),
            AxWp.fromOption (fun P => P) iprop(emp)
              (get? (na04 x GD i_A i_B k_rel k_acq w_x r_x vx) e0) := by
  letI : AxirisG GF := axG4 γ γc L x i_A i_B k_rel k_acq w_x vx
  iintro Hx HL Hc
  ihave Htodo := lockSliceOrdEaTodo4 γ γc L x Hxl GD i_A i_B k_rel k_acq w_x r_x vx Hcons Hwx
    Hsingle_wx Hgd_wx Hfence Hwb0 Hsingle_rel Hrf Hwb1 Hsingle_acq Hval_acq Hpol Hacq_po Hnw Hrd
    Hlobp_wx Hlobp_wrel Hlobp_acq Hlobp_rx Hspol_wx Hspol_wrel Hspol_acq_wf Hspol_rx Hgmo_perm
    $$ Hx HL
  ihave Hob0 : AxirisG.obStInterp GD () ∅ $$ [Hc]
  · iapply (obStInterp4Unfold γ γc L x i_A i_B k_rel k_acq w_x vx GD () ∅).2
    rw [DOf4Init, hmOf4Init]
    iapply AxLockAdeq.obInit γ γc L x GD $$ Hc
  iapply adequacyOrdL GD Hcons (AxLockAdeq.L44 i_A i_B k_rel k_acq w_x r_x) Hgmo_perm
    (axpolWfL44 GD i_A i_B k_rel k_acq w_x r_x Hlobp_wx Hlobp_wrel Hlobp_acq Hlobp_rx Hspol_wx
      Hspol_wrel Hspol_acq_wf Hspol_rx)
    _ _ (HdomEq04 GD i_A i_B k_rel k_acq w_x r_x x vx γ L)
    (Hdom04 GD i_A i_B k_rel k_acq w_x r_x x vx)
    (HeaLob04 GD i_A i_B k_rel k_acq w_x r_x x vx γ L Hlobp_wx Hlobp_wrel Hlobp_acq Hlobp_rx)
    () $$ Htodo Hob0

theorem lockSliceFinal4 :
    ⊢ histAuth (GF := GF) γ x 1 [] -∗ histAuth γ L 1 [] -∗ claimedAuth γc (∅ : GSet Geid) -∗
      |={⊤}[∅]▷=>^[4]
        ⌜grfAt GD.gdG x w_x r_x ∧ ∀ t v, greadsByte GD.gdG r_x x t v → v = vx⌝ := by
  have hadeq := lockSliceAdequate4 (hlc := hlc) (GF := GF) γ γc L x Hxl GD i_A i_B k_rel k_acq w_x r_x vx
    Hcons Hwx Hsingle_wx Hgd_wx Hfence Hwb0 Hsingle_rel Hrf Hwb1 Hsingle_acq Hval_acq Hpol
    Hacq_po Hnw Hrd Hlobp_wx Hlobp_wrel Hlobp_acq Hlobp_rx Hspol_wx Hspol_wrel Hspol_acq_wf
    Hspol_rx Hgmo_perm
  have hlen : (AxLockAdeq.L44 i_A i_B k_rel k_acq w_x r_x).length = 4 := rfl
  rw [hlen] at hadeq
  have hbag : ([∗set] e0 ∈ (LawfulSet.ofList (AxLockAdeq.L44 i_A i_B k_rel k_acq w_x r_x) :
        GSet Geid), AxWp.fromOption (fun P => P) iprop(emp)
          (get? (na04 (GF := GF) x GD i_A i_B k_rel k_acq w_x r_x vx) e0)) ⊢
      ⌜grfAt GD.gdG x w_x r_x ∧ ∀ t v, greadsByte GD.gdG r_x x t v → v = vx⌝ :=
    AxLockAdeq.bagRx GD i_A i_B k_rel k_acq w_x r_x x vx Hcons Hgmo_perm
  iintro Hx HL Hc
  ihave Hadeq := hadeq $$ Hx HL Hc
  iapply step_fupdN_wand $$ Hadeq
  iintro ⟨%σ, -, Hbag⟩
  iapply hbag $$ Hbag

end events4

/-! # 6. `lockSliceSound''` — THE Prop-LEVEL RESULT, no `∀σ`/`⊢` premise left -/

theorem lockSliceSound'' {GF : BundledGFunctors} [InvGpreS GF] [Axpol]
    [AxlogG GF Hent] [AxLockG GF]
    (L x : Int) (Hxl : x ≠ L)
    (GD : Gdexec) (i_A i_B : Agent) (k_rel k_acq : Nat) (w_x r_x : Geid) (vx : BitVec 8)
    (Hcons : rvwmoCatConsistent GD)
    (Hwx : gwritesByte GD.gdG w_x x vx)
    (Hsingle_wx : ∀ a' v', gwritesByte GD.gdG w_x a' v' → a' = x)
    (Hgd_wx : graphData GD w_x = some [vx])
    (Hfence : gppoCat GD w_x (i_A, k_rel))
    (Hwb0 : gwritesByte GD.gdG (i_A, k_rel) L b0)
    (Hsingle_rel : ∀ a' v', gwritesByte GD.gdG (i_A, k_rel) a' v' → a' = L)
    (Hrf : grfe GD.gdG (i_A, k_rel) (i_B, k_acq))
    (Hwb1 : gwritesByte GD.gdG (i_B, k_acq) L b1)
    (Hsingle_acq : ∀ a' v', gwritesByte GD.gdG (i_B, k_acq) a' v' → a' = L)
    (Hval_acq : graphData GD (i_B, k_acq) = some [b1])
    (Hpol : (i_A, k_rel) ∈ Axpol.sPol GD (i_B, k_acq))
    (Hacq_po : gacqPo GD.gdG (i_B, k_acq) r_x)
    (Hnw : gisW GD.gdG r_x = false)
    (Hrd : ∃ t v, greadsByte GD.gdG r_x x t v)
    (Hlobp_wx : Axpol.lobp GD w_x = (∅ : GSet Geid))
    (Hlobp_wrel : Axpol.lobp GD (i_A, k_rel) = ({w_x} : GSet Geid))
    (Hlobp_acq : Axpol.lobp GD (i_B, k_acq) = ({(i_A, k_rel)} : GSet Geid))
    (Hlobp_rx : Axpol.lobp GD r_x = ({(i_B, k_acq)} : GSet Geid))
    (Hspol_wx : Axpol.sPol GD w_x ⊆ (∅ : GSet Geid))
    (Hspol_wrel : Axpol.sPol GD (i_A, k_rel) ⊆ ({w_x} : GSet Geid))
    (Hspol_acq_wf : Axpol.sPol GD (i_B, k_acq) ⊆ (({w_x} : GSet Geid) ∪ {(i_A, k_rel)}))
    (Hspol_rx : Axpol.sPol GD r_x ⊆
      ((({w_x} : GSet Geid) ∪ {(i_A, k_rel)}) ∪ {(i_B, k_acq)}))
    (Hgmo_perm : [w_x, (i_A, k_rel), (i_B, k_acq), r_x].Perm GD.gdG.gxGmo) :
    ∀ t v, greadsByte GD.gdG r_x x t v → v = vx := by
  intro t v Hread
  apply Iris.pure_soundness (PROP := IProp GF)
  refine step_fupdN_soundness_close (hlc := HasLC.hasNoLC) (P := iprop(⌜v = vx⌝)) 4 0 ?_
  intro Hinv
  iintro _
  have hs : ∀ (P : IProp GF),
      iprop(|={⊤}[∅]▷=>^[3 + 1] P) = iprop(|={⊤}[∅]▷=> |={⊤}[∅]▷=>^[3] P) := fun _ => rfl
  rw [show (4 : Nat) = 3 + 1 from rfl, hs]
  imod lockInitialAlloc (GF := GF) x L Hxl with ⟨%γ, %γc, Hx, HL, Hc⟩
  rw [← hs]
  ihave Hfinal := lockSliceFinal4 (hlc := HasLC.hasNoLC) γ γc L x Hxl GD i_A i_B k_rel k_acq
    w_x r_x vx Hcons Hwx Hsingle_wx Hgd_wx Hfence Hwb0 Hsingle_rel Hrf Hwb1 Hsingle_acq
    Hval_acq Hpol Hacq_po Hnw Hrd Hlobp_wx Hlobp_wrel Hlobp_acq Hlobp_rx Hspol_wx Hspol_wrel
    Hspol_acq_wf Hspol_rx Hgmo_perm $$ Hx HL Hc
  iapply step_fupdN_wand $$ Hfinal
  iintro %H
  ipureintro
  exact H.2 t v Hread

end Weak
