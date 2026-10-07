/-
Weak: **PHASE-2 ADEQUACY FOR THE FOUR-EVENT LOCK HANDOFF** (AxSL tier, LB/AxSL lock slice),
part 1 of 2: the per-event flow rules over the primed bridge and the iProp-level capstone
`lockSliceAdequate`/`lockSliceFinal` (the gmo-order induction `adequacyOrdL` run over the four
events `w_x`, `w_rel`, `acq`, `r_x`), with and without `Hsn`.

Rocq: `iris/AxLockAdeq.v` @ xxvzwolszwmp, §§0–2 (split for size: §§3–6 — the ghost allocation
`lockInitialAlloc` and the Prop-level `lockSliceSound`/`lockSliceSound'`/`lockSliceSound''` —
are in `Weak/AxLockAdeq2.lean`).

## The Rocq header, in substance

(1) SCOPE: the graph's ENTIRE gmo list is exactly the four lock events (`Hgmo_perm : L4 ~
gxGmo`), a schematic two-hart graph; `axpolWfL` is established from explicit `lobp`/`sPol` facts
at those events (`Hlobp_*`/`Hspol_*`), `Axpol` staying abstract.
(2) THE ea/na MAP: the public bag `na` carries only `emp` at `w_x`/`w_rel`/`acq` and the read's
pure result at `r_x`; every resource (the `x`-token, `w_rel`'s `L`-history, the acquire's mixed
`RAcq2`) travels along lob through `ea`'s deposits only (two copies of one `tokTie` would be
unsound).
(3) THE `histAuth γ L` THREADING GAP, CLOSED: the release step `flowEqReleaseWx` re-derives
`protInvLockReleaseStep'`'s body but KEEPS the fresh `L`-tie (as `histAuth γ L 1 (H_L ++
[(w_rel, b0)])`, via `tokSingleton`) and routes it to `acq` through `ea`.
(4) ONE UNIFORM (primed) `obSt` BRIDGE `Hob_eq'` across all four steps.
(5) `lockSliceSound`: a plain Prop; its `⊢ histAuth …`/`⊢ claimedAuth …` premises were later
found REFUTABLE (two full-fraction copies) and `Hsn` unprovable, hence §2.9–2.10 (`Hsn`-free
`flowEqLockReadWl2`, deriving the coverage wand from `Hwonly` + the deposited token) and §4b
(`lockSliceSound'`: fresh `γ`/`γc` allocated INSIDE the soundness continuation by
`lockInitialAlloc`, a concrete `AxirisG` instance `axGInst` whose `obStInterp` IS
`protInvLock'`, so the bridge holds by construction).  `lockSliceSound'`'s `Hunclaimed`/`Hhm`
quantify over the whole concrete ob-state and are refutable; `Weak/AxLockAdeq2.lean` removes
them.

RESIDUAL HYPOTHESES (as Rocq): `Hgmo_perm` (scope reduction), `Hlobp_*`/`Hspol_*` (the abstract
policy's values), `Hpol`/`Hunclaimed`/`Hhm` (copied from `AxLockWp2.flowEqAmoswapAqLob'`), the
bridge `ob_D`/`ob_hm`/`mk_ob'`/`Hmk_ob'_*`/`Hob_eq'` (architecture wiring), `Hfence` (an abstract
ppo edge), `Hsn` (§§2.5–2.8 only), `InvGpreS GF` (the soundness corollaries).

**Ghost state**: `claimedAllocEmpty` (here) allocates the claimed-set authority (`AxLockG GF`)
at `∅`; the joint allocation `lockInitialAlloc` is in `Weak/AxLockAdeq2.lean`.

**Fetches / Q8.** Nothing here depends on instruction fetches; the WP step clause
(`AxWp2.wpPreStepDef`) is never introduced or eliminated here (phase 2 only consumes
`flowEqEa`/`flowEqDyn`), so the pending Q8 `fetchPin` rework does not touch this file.

## Deviations from Rocq

1. VOCABULARY (as `AxProtLock`/`AxLockWp2`/`AxAdequacyL`): `<[k := v]> m` ↦ `insert m k v`;
   `{[a; b]}` ↦ `({a} : GSet Geid) ∪ {b}`; `L ≡ₚ l` ↦ `L.Perm l`; `list_to_set` ↦
   `LawfulSet.ofList`; `dom` ↦ `FiniteMap.dom_set`; `from_option id emp` ↦
   `AxWp.fromOption (fun P => P) iprop(emp)`; `|={⊤}[∅]▷=>^n` ↦ `|={⊤}[∅]▷=>^[n]`; `H.*1` ↦
   `H.map Prod.fst`; `last` ↦ `getLast?`; `gpo` ↦ `WeakRvwmoGraph.gpo`; `WeakLitmus.b0/b1` ↦
   `b0`/`b1`; `Z` ↦ `Int`; `bv 8` ↦ `BitVec 8`; `invGS_gen HasNoLc Σ` ↦ `[InvGS_gen hlc GF]` for
   any `hlc`.  The ea0 bags `<[k := R]> ∅` are written as singletons `{[k := R]}` (equal by
   `insertEmpty`, `rfl`).
2. STATEMENT SHAPES (as `AxLockWp2` deviation 5): `A -∗ B` ↦ `A ⊢ B`; `A -∗ B -∗ …` ↦
   `⊢ A -∗ B -∗ …`; the `⊢`-closed premise `Hsn` stays `⊢`-closed.
3. SECTION VARIABLES.  §1 (Rocq `Section LockAdeq`, all `Proof using All`): `γ γc L x Hxl ob_D
   ob_hm mk_ob' Hmk_ob'_D Hmk_ob'_hm Hob_eq'` are the leading explicit arguments of every §1/§2
   lemma, in that order.  §2 (Rocq `Section Capstone`): the data `GD i_A i_B k_rel k_acq w_x
   r_x vx` are leading arguments (those a statement mentions, in that order); the HEADLINE
   results (`lockSliceOrdEaTodo(2)`, `lockSliceAdequate(2)`, `lockSliceFinal(2)`) take Rocq's
   full Context hypothesis list (`2` versions without `Hsn`/`Hdisc`, Rocq's `Proof using All -
   Hsn - Hdisc`), while the BOOKKEEPING lemmas of §§2.1–2.6/2.9 take only the hypotheses their
   proofs use (a strengthening: Rocq's post-section signatures carry the whole Context).  The
   pure bookkeeping lemmas (no ghost state) do not take the §1 variables at all.
4. DEFINITIONS `wRel`/`AxLockAdeq.acq` are `abbrev`s; `na0`/`AxLockAdeq.ea0`/`L4`/`Hh`/`RAcq2`
   take the section data they mention as explicit arguments (Rocq's post-section form).
5. Lean-only helpers (file-qualified): `AxLockAdeq.L4Mem` (membership of the four events),
   `AxLockAdeq.eaDepositOne`/`eaDepositNone` (a singleton/empty deposit), `AxLockAdeq.flowMono`
   (`flowEqDynMono` with the flow equation first),
   `AxLockAdeq.todoWx`/`todoWrel`/`todoAcq`/`todoRx`/`todoRx2`/`todoTail` (the four bullets and
   the tail of `lockSliceOrdEaTodo(2)`, shared by both versions), `AxLockAdeq.bagRx` (the final
   bag projection), `AxLockAdeq.obInit` (the initial ob-state of `lockSliceAdequate(2)`).

**Rocq → Lean name map.**  `flow_eq_dyn_from_flowin` `flowEqDynFromFlowin`,
`claimed_alloc_empty` `claimedAllocEmpty`, `flow_eq_owned_write_x2` `flowEqOwnedWriteX2`,
`flow_eq_release_wx` `flowEqReleaseWx`, `R_acq2` `RAcq2`, `flow_eq_amoswap_aq_wl`
`flowEqAmoswapAqWl`, `prot_inv_lock_read_step2` `protInvLockReadStep2`, `flow_eq_lock_read_wl`
`flowEqLockReadWl`, `w_rel` `wRel`, `acq` `AxLockAdeq.acq`, `Hh` `Hh`, `L4` `L4`, `na0` `na0`,
`ea0` `AxLockAdeq.ea0`, `L4_nodup` `L4Nodup`, `L4_ne_*` `L4NeWxWrel`/`L4NeWxAcq`/`L4NeWxRx`/
`L4NeWrelAcq`/`L4NeWrelRx`/`L4NeAcqRx`, `in_L4` `inL4`, `lob_succ_*` `lobSuccWx`/`lobSuccWrel`/
`lobSuccAcq`/`lobSuccRx`, `Hh_wr` `HhWr`, `Hh_ch` `HhCh`, `Hh_own` `HhOwn`, `Hh_last` `HhLast`,
`na0_*` `na0Wx`/`na0Wrel`/`na0Acq`/`na0Rx`, `ea0_*` `ea0Wx`/`ea0Wrel`/`ea0Acq`/`ea0Rx`,
`lock_slice_ord_ea_todo` `lockSliceOrdEaTodo`, `L4_0..3` `L40..L43`, `axpol_wf_L4` `axpolWfL4`,
`Hdom_eq0` `HdomEq0`, `Hdom0` `Hdom0`, `Hea_lob0` `AxLockAdeq.HeaLob0`, `lock_slice_adequate`
`lockSliceAdequate`, `lock_slice_final` `lockSliceFinal`, `Hwonly` `Hwonly`, `Hh_own2`
`HhOwn2`, `flow_eq_lock_read_wl2` `flowEqLockReadWl2`, `lock_slice_ord_ea_todo2`
`lockSliceOrdEaTodo2`, `lock_slice_adequate2` `lockSliceAdequate2`, `lock_slice_final2`
`lockSliceFinal2` (§§3–6 names: `Weak/AxLockAdeq2.lean`).

**Not ported:** the `Print Assumptions` audits (the lint's axiom check covers them).
-/
import Weak.AxAdequacyL
import Weak.AxLockWp2

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp

/-! # 0. Generic helpers -/

section flowinFrom
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]

/-- Extracting a resource from `flowIn` BEFORE invoking a `flowIn = ∅` flow rule. -/
theorem flowEqDynFromFlowin (GD : Gdexec) (e : Geid) (sOb0 : GSet Geid) (flowIn : Mea GF)
    (Hextra R : IProp GF) :
    ⊢ (Hextra -∗ flowEqDyn GD e sOb0 (∅ : Mea GF) R) -∗
      (([∗map] Rin ∈ flowIn, Rin) -∗ Hextra) -∗
      flowEqDyn GD e sOb0 flowIn R := by
  iintro Hbuild Hwand
  unfold flowEqDyn
  iintro %σ %sOb %Hsub %Hnin Hob Rin
  ihave Hextra := Hwand $$ Rin
  ihave Hb := Hbuild $$ Hextra
  iapply Hb $$ %σ %sOb %Hsub %Hnin Hob
  iapply BigSepM.bigSepM_empty.2
  itrivial

/-- Lean-only: `flowEqDynMono` with the flow equation first (so the old result is known when
the later wand is proved). -/
theorem AxLockAdeq.flowMono (GD : Gdexec) (e : Geid) (sOb0 : GSet Geid) (flowIn : Mea GF)
    (R1 R2 : IProp GF) :
    flowEqDyn GD e sOb0 flowIn R1 ⊢ ▷ (R1 -∗ R2) -∗ flowEqDyn GD e sOb0 flowIn R2 := by
  iintro H Hw
  iapply flowEqDynMono GD e sOb0 flowIn R1 R2 $$ Hw H

end flowinFrom

section claimedAllocSec
variable {GF : BundledGFunctors} [AxLockG GF]

/-- The allocation of the claimed authority from scratch. -/
theorem claimedAllocEmpty : ⊢ |==> ∃ γc, claimedAuth (GF := GF) γc (∅ : GSet Geid) := by
  imod iOwn_alloc (E := AxLockG.axLockInG)
      (● (DisjointLeibnizSet.valid (∅ : GSet Geid)) : Auth ClaimedUR)
      (Auth.auth_valid.mpr DisjointLeibnizSet.valid_set) with ⟨%γc, H⟩
  imodintro
  iexists γc
  unfold claimedAuth
  iexact H

end claimedAllocSec

section depositHelpers
variable {GF : BundledGFunctors} [AxirisG GF] [Axpol]

/-- Lean-only: a deposit over the singleton successor set. -/
theorem AxLockAdeq.eaDepositOne (ea : Sra GF) (S : GSet Geid)
    (e eOut : Geid) (gm : Mea GF) (gv : IProp GF) :
    S = {eOut} → get? ea eOut = some gm → get? gm e = some gv → eaDeposit ea S e ⊣⊢ gv := by
  intro hS h1 h2
  subst hS
  unfold eaDeposit
  refine BigSepS.bigSepS_singleton.trans ?_
  rw [AxLifting.depAtSomeSome ea e eOut gm gv h1 h2]
  exact ⟨.rfl, .rfl⟩

/-- Lean-only: a deposit over the empty successor set. -/
theorem AxLockAdeq.eaDepositNone (ea : Sra GF) (S : GSet Geid)
    (e : Geid) : S = ∅ → eaDeposit ea S e ⊣⊢ iprop(emp) := by
  intro hS
  subst hS
  unfold eaDeposit
  exact BigSepS.bigSepS_empty

end depositHelpers

/-! # 1. The per-event rules, through the PRIMED bridge -/

section racq
variable {GF : BundledGFunctors} [AxlogG GF Hent]

/-- The acquire's mixed deposit (Rocq `R_acq2`). -/
def RAcq2 (γ : GName) (L x : Int) (GD : Gdexec) (w_rel acq : Geid) (Hh : List Hent) :
    IProp GF :=
  iprop(⌜gwritesByte GD.gdG w_rel L b0⌝ ∗ tokTie GD γ x Hh {[acq := (1 : Qp)]})

end racq

section lockAdeq
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [axG : AxirisG GF] [Axpol]
  [AxlogG GF Hent] [AxLockG GF]
variable (γ γc : GName) (L x : Int) (Hxl : x ≠ L)
variable (ob_D : AxirisG.obSt GF → GSet Geid) (ob_hm : AxirisG.obSt GF → GMapF Geid (List Hent))
  (mk_ob' : GSet Geid → GMapF Geid (List Hent) → AxirisG.obSt GF)
  (Hmk_ob'_D : ∀ D hm, ob_D (mk_ob' D hm) = D)
  (Hmk_ob'_hm : ∀ D hm, ob_hm (mk_ob' D hm) = hm)
  (Hob_eq' : ∀ (GD : Gdexec) (σ : AxirisG.obSt GF) (s : GSet Geid),
    AxirisG.obStInterp GD σ s ⊣⊢ protInvLock' L x γ γc GD s (ob_D σ) (ob_hm σ))

include Hxl Hmk_ob'_D Hmk_ob'_hm Hob_eq'

/-- 1.1 `w_x`'s rule: write `w`, deposit the fresh `tokTie`; vacuous `ΦLock'` conjunct. -/
theorem flowEqOwnedWriteX2 (GD : Gdexec) (w : Geid) (v : BitVec 8) (Hl : List Hent)
    (s_ob0 : GSet Geid) (data : List (BitVec 8)) :
    gwritesByte GD.gdG w x v →
    (∀ a' v', gwritesByte GD.gdG w a' v' → a' = x) →
    graphData GD w = some data →
    histAuth γ x 1 Hl ⊢
      flowEqDyn GD w s_ob0 (∅ : Mea GF)
        iprop(tokTie GD γ x (Hl ++ [(w, v)]) {[w := (1 : Qp)]} ∗ ⌜graphData GD w = some data⌝) := by
  intro Hwb Hsingle Hgd
  iintro Hauth
  unfold flowEqDyn
  iintro %σ %sOb %Hsub %Hnin Hob -
  ihave Hob := (Hob_eq' GD σ sOb).1 $$ Hob
  icases (protInvLockUnfold' L x γ γc GD sOb (ob_D σ) (ob_hm σ)).1 $$ Hob
    with ⟨Hc, Hpo, Hlocks⟩
  imod protInvWriteStep γ GD sOb w x v Hl Hnin Hwb Hsingle $$ [$Hpo $Hauth] with ⟨Hpo', Htie⟩
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  inext
  imod Hclose
  imodintro
  iexists mk_ob' (ob_D σ) (ob_hm σ)
  isplitl [Hc Hpo' Hlocks]
  · iapply (Hob_eq' GD (mk_ob' (ob_D σ) (ob_hm σ)) (({w} : GSet Geid) ∪ sOb)).2
    rw [Hmk_ob'_D, Hmk_ob'_hm]
    iapply (protInvLockUnfold' L x γ γc GD (({w} : GSet Geid) ∪ sOb) (ob_D σ) (ob_hm σ)).2
    isplitl [Hc]
    · iexact Hc
    isplitl [Hpo']
    · iexact Hpo'
    iapply (AxProtLock.bigSepSUnionSingleton
      (Φ := fun e => ΦLock' L x γ γc GD e ((get? (ob_hm σ) e).getD [])) Hnin).2
    isplitl []
    · iapply AxProtLock.ΦLock'Vacuous L x γ γc GD w _
        (fun hbad => Hxl (Hsingle L b0 hbad).symm)
    · iexact Hlocks
  · isplitl [Htie]
    · iexact Htie
    · ipureintro
      exact Hgd

/-- 1.2 `w_rel`'s rule: `protInvLockReleaseStep'`'s body, KEEPING the fresh `L`-tie (as the
full `histAuth`), the `x`-token extracted from `flowIn`. -/
theorem flowEqReleaseWx (GD : Gdexec) (i : Agent) (k : Nat) (e_last : Geid)
    (Hh H_L : List Hent) (flowIn : Mea GF)
    (Hcons : rvwmoCatConsistent GD)
    (Hwb : gwritesByte GD.gdG (i, k) L b0)
    (Hsingle : ∀ a' v', gwritesByte GD.gdG (i, k) a' v' → a' = L)
    (Hgob : gobCat GD e_last (i, k)) :
    ⊢ histAuth γ L 1 H_L -∗
      (([∗map] Rin ∈ flowIn, Rin) -∗ tokTie GD γ x Hh {[e_last := (1 : Qp)]}) -∗
      flowEqDyn GD (i, k) (Axpol.sPol GD (i, k)) flowIn
        (histAuth γ L 1 (H_L ++ [((i, k), b0)])) := by
  iintro HaL Hwand
  iapply flowEqDynFromFlowin GD (i, k) (Axpol.sPol GD (i, k)) flowIn
    (tokTie GD γ x Hh {[e_last := (1 : Qp)]}) _ $$ [HaL] Hwand
  iintro Htie
  unfold flowEqDyn
  iintro %σ %sOb %Hsub %Hnin Hob -
  ihave Hob := (Hob_eq' GD σ sOb).1 $$ Hob
  icases (protInvLockUnfold' L x γ γc GD sOb (ob_D σ) (ob_hm σ)).1 $$ Hob
    with ⟨Hc, Hpo, Hlocks⟩
  imod protInvWriteStep γ GD sOb (i, k) L b0 H_L Hnin Hwb Hsingle $$ [$Hpo $HaL]
    with ⟨Hpo', HtieL⟩
  ihave Htie' := tokRetieOb GD γ x Hh e_last (i, k) Hcons Hgob $$ Htie
  iunfold tokTie at HtieL
  icases HtieL with ⟨HaL', -⟩
  ihave HaL' := (tokSingleton γ L (H_L ++ [((i, k), b0)]) (i, k) 1).1 $$ HaL'
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  inext
  imod Hclose
  imodintro
  iexists mk_ob' (ob_D σ) (insert (ob_hm σ) (i, k) Hh)
  isplitl [Hc Hpo' Htie' Hlocks]
  · iapply (Hob_eq' GD (mk_ob' (ob_D σ) (insert (ob_hm σ) (i, k) Hh))
      (({(i, k)} : GSet Geid) ∪ sOb)).2
    rw [Hmk_ob'_D, Hmk_ob'_hm]
    iapply (protInvLockUnfold' L x γ γc GD (({(i, k)} : GSet Geid) ∪ sOb) (ob_D σ)
      (insert (ob_hm σ) (i, k) Hh)).2
    isplitl [Hc]
    · iexact Hc
    isplitl [Hpo']
    · iexact Hpo'
    iapply (AxProtLock.bigSepSUnionSingleton
      (Φ := fun e => ΦLock' L x γ γc GD e ((get? (insert (ob_hm σ) (i, k) Hh) e).getD []))
      Hnin).2
    isplitl [Htie']
    · rw [lookupInsert, Option.getD_some]
      iapply AxProtLock.ΦLock'Left L x γ γc GD (i, k) Hh
      iapply tokTieXTok
      iexact Htie'
    · iapply (bigSepSLockInsertNe L x γ γc GD sOb (ob_hm σ) (i, k) Hh Hnin).1
      iexact Hlocks
  · iexact HaL'

/-- 1.3 `acq`'s rule: `AxLockWp2.flowEqAmoswapAqLob'` with its `histAuth` from `flowIn`. -/
theorem flowEqAmoswapAqWl (GD : Gdexec) (i : Agent) (k : Nat) (w_rel : Geid)
    (Hh H_L : List Hent) (flowIn : Mea GF)
    (Hcons : rvwmoCatConsistent GD)
    (Hpol : w_rel ∈ Axpol.sPol GD (i, k))
    (Hunclaimed : ∀ σ : AxirisG.obSt GF, w_rel ∉ ob_D σ)
    (Hhm : ∀ σ : AxirisG.obSt GF, get? (ob_hm σ) w_rel = some Hh)
    (Hwb0 : gwritesByte GD.gdG w_rel L b0)
    (Hwb1 : gwritesByte GD.gdG (i, k) L b1)
    (Hsingle : ∀ a' v', gwritesByte GD.gdG (i, k) a' v' → a' = L)
    (Hgob : gobCat GD w_rel (i, k))
    (Hval : graphData GD (i, k) = some [b1])
    (Hne : Hh ≠ []) :
    (([∗map] Rin ∈ flowIn, Rin) -∗ histAuth γ L 1 H_L) ⊢
      flowEqDyn GD (i, k) (Axpol.sPol GD (i, k)) flowIn (RAcq2 γ L x GD w_rel (i, k) Hh) := by
  iintro Hwand
  iapply flowEqDynFromFlowin GD (i, k) (Axpol.sPol GD (i, k)) flowIn
    (histAuth γ L 1 H_L) _ $$ [] Hwand
  iintro HaL
  ihave Hfeq := flowEqAmoswapAqLob' γ γc L x ob_D ob_hm mk_ob' Hmk_ob'_D Hmk_ob'_hm Hob_eq'
    GD i k w_rel Hh H_L Hcons Hpol Hunclaimed Hhm Hwb0 Hwb1 Hsingle Hgob Hval Hne $$ HaL
  iapply AxLockAdeq.flowMono GD (i, k) (Axpol.sPol GD (i, k)) (∅ : Mea GF) _ _ $$ Hfeq
  inext
  iintro ⟨⟨%Hpure, Htie⟩, -⟩
  iunfold RAcq2
  isplitl []
  · ipureintro
    exact Hpure
  · iexact Htie

/-- 1.4 A read may always join the validated set (primed bridge). -/
theorem protInvLockReadStep2 (r : Geid) (s D : GSet Geid) (hm : GMapF Geid (List Hent))
    (GD : Gdexec) :
    r ∉ s → gisW GD.gdG r = false →
    protInvLock' (GF := GF) L x γ γc GD s D hm ⊢
      protInvLock' L x γ γc GD (({r} : GSet Geid) ∪ s) D hm := by
  intro Hnin Hr
  iintro Hinv
  icases (protInvLockUnfold' L x γ γc GD s D hm).1 $$ Hinv with ⟨Hc, Hpo, Hlocks⟩
  ihave Hpo' := protInvReadStep γ GD s r Hnin Hr $$ Hpo
  iapply (protInvLockUnfold' L x γ γc GD (({r} : GSet Geid) ∪ s) D hm).2
  isplitl [Hc]
  · iexact Hc
  isplitl [Hpo']
  · iexact Hpo'
  iapply (AxProtLock.bigSepSUnionSingleton
    (Φ := fun e => ΦLock' L x γ γc GD e ((get? hm e).getD [])) Hnin).2
  isplitl []
  · iapply AxProtLock.ΦLock'Vacuous L x γ γc GD r _ (fun hbad => by
      have h := AxProt.gwritesByteGisW _ _ _ _ hbad
      rw [Hr] at h
      cases h)
  · iexact Hlocks

/-- 1.4 `r_x`'s rule, primed (`AxLockWp2.flowEqLockReadLob`'s body). -/
theorem flowEqLockReadWl (GD : Gdexec) (acq_e r_x : Geid)
    (Hh : List Hent) (w_x : Geid) (vx : BitVec 8)
    (s_ob0 : GSet Geid) (flowIn : Mea GF)
    (Hcons : rvwmoCatConsistent GD)
    (Hnw : gisW GD.gdG r_x = false)
    (Hwr : ∀ p, p ∈ Hh → gwritesByte GD.gdG p.1 x p.2)
    (Hch : chainWith (gmoLt GD.gdG) (Hh.map Prod.fst))
    (Hown : ∀ w v, gwritesByte GD.gdG w x v → WeakRvwmoGraph.gpo GD.gdG w r_x →
      w ∈ Hh.map Prod.fst)
    (Hlast : Hh.getLast? = some (w_x, vx))
    (Hacq : gacqPo GD.gdG acq_e r_x)
    (Hrd : ∃ t v, greadsByte GD.gdG r_x x t v)
    (Hsn : ⊢ iprop(∀ w v, ⌜gwritesByte GD.gdG w x v⌝ -∗ ⌜gmoLt GD.gdG w r_x⌝ -∗
      ∃ H', ⌜w ∈ H'.map Prod.fst⌝ ∗ histSnap (GF := GF) γ x H')) :
    (([∗map] Rin ∈ flowIn, Rin) -∗ tokTie GD γ x Hh {[acq_e := (1 : Qp)]}) ⊢
      flowEqDyn GD r_x s_ob0 flowIn
        iprop(⌜grfAt GD.gdG x w_x r_x ∧ ∀ t v, greadsByte GD.gdG r_x x t v → v = vx⌝) := by
  iintro Hflowin
  unfold flowEqDyn
  iintro %σ %sOb %Hsub %Hnin Hob Hflow
  ihave Htie := Hflowin $$ Hflow
  ihave Hsn' := Hsn
  ihave %Hres := lockReadOwn GD γ x Hh w_x acq_e r_x vx Hcons Hwr Hch Hown Hlast Hacq Hrd
    $$ [$Htie $Hsn']
  ihave Hob := (Hob_eq' GD σ sOb).1 $$ Hob
  ihave Hob' := protInvLockReadStep2 γ γc L x Hxl ob_D ob_hm mk_ob' Hmk_ob'_D Hmk_ob'_hm Hob_eq'
    r_x sOb (ob_D σ) (ob_hm σ) GD Hnin Hnw $$ Hob
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  inext
  imod Hclose
  imodintro
  iexists σ
  isplitl [Hob']
  · iapply (Hob_eq' GD σ (({r_x} : GSet Geid) ∪ sOb)).2
    iexact Hob'
  · ipureintro
    exact Hres

end lockAdeq

/-! # 2. THE FOUR-EVENT CAPSTONE -/

/-! ## 2.0 The four events, the history, the ea/na maps -/

/-- The release store's event. -/
abbrev wRel (i_A : Agent) (k_rel : Nat) : Geid := (i_A, k_rel)
/-- The acquire RMW's event. -/
abbrev AxLockAdeq.acq (i_B : Agent) (k_acq : Nat) : Geid := (i_B, k_acq)
/-- `w_x`'s singleton write-history. -/
def Hh (w_x : Geid) (vx : BitVec 8) : List Hent := [(w_x, vx)]
/-- The processing list (po/rf order). -/
def L4 (i_A i_B : Agent) (k_rel k_acq : Nat) (w_x r_x : Geid) : List Geid :=
  [w_x, wRel i_A k_rel, AxLockAdeq.acq i_B k_acq, r_x]

section maps
variable {GF : BundledGFunctors}

/-- The public bag: `emp` at the three writes, the read's pure result at `r_x`. -/
def na0 (x : Int) (GD : Gdexec) (i_A i_B : Agent) (k_rel k_acq : Nat) (w_x r_x : Geid)
    (vx : BitVec 8) : Mea GF :=
  insert (insert (insert (insert (∅ : Mea GF) r_x
      iprop(⌜grfAt GD.gdG x w_x r_x ∧ ∀ t v, greadsByte GD.gdG r_x x t v → v = vx⌝))
    (AxLockAdeq.acq i_B k_acq) iprop(emp)) (wRel i_A k_rel) iprop(emp)) w_x iprop(emp)

variable [AxlogG GF Hent]

/-- The edge annotations: every resource travels along lob. -/
def AxLockAdeq.ea0 (γ : GName) (L x : Int) (GD : Gdexec) (i_A i_B : Agent) (k_rel k_acq : Nat)
    (w_x r_x : Geid) (vx : BitVec 8) : Sra GF :=
  insert (insert (insert (insert (∅ : Sra GF) r_x
      ({[AxLockAdeq.acq i_B k_acq :=
        RAcq2 γ L x GD (wRel i_A k_rel) (AxLockAdeq.acq i_B k_acq) (Hh w_x vx)]} : Mea GF))
    (AxLockAdeq.acq i_B k_acq)
      ({[wRel i_A k_rel := histAuth γ L 1 [(wRel i_A k_rel, b0)]]} : Mea GF))
    (wRel i_A k_rel)
      ({[w_x := tokTie GD γ x (Hh w_x vx) {[w_x := (1 : Qp)]}]} : Mea GF))
    w_x (∅ : Mea GF)

end maps

/-! ## 2.1–2.6 Pure bookkeeping -/

section graph
variable (GD : Gdexec) (i_A i_B : Agent) (k_rel k_acq : Nat) (w_x r_x : Geid)

theorem L4Nodup (Hcons : rvwmoCatConsistent GD)
    (Hgmo_perm : (L4 i_A i_B k_rel k_acq w_x r_x).Perm GD.gdG.gxGmo) :
    (L4 i_A i_B k_rel k_acq w_x r_x).Nodup :=
  Hgmo_perm.nodup_iff.2 Hcons.1.1

theorem L4NeWxWrel (Hcons : rvwmoCatConsistent GD)
    (Hgmo_perm : (L4 i_A i_B k_rel k_acq w_x r_x).Perm GD.gdG.gxGmo) :
    w_x ≠ wRel i_A k_rel := by
  intro heq
  have h := L4Nodup GD i_A i_B k_rel k_acq w_x r_x Hcons Hgmo_perm
  unfold L4 at h
  rw [heq] at h
  simp at h

theorem L4NeWxAcq (Hcons : rvwmoCatConsistent GD)
    (Hgmo_perm : (L4 i_A i_B k_rel k_acq w_x r_x).Perm GD.gdG.gxGmo) :
    w_x ≠ AxLockAdeq.acq i_B k_acq := by
  intro heq
  have h := L4Nodup GD i_A i_B k_rel k_acq w_x r_x Hcons Hgmo_perm
  unfold L4 at h
  rw [heq] at h
  simp at h

theorem L4NeWxRx (Hcons : rvwmoCatConsistent GD)
    (Hgmo_perm : (L4 i_A i_B k_rel k_acq w_x r_x).Perm GD.gdG.gxGmo) :
    w_x ≠ r_x := by
  intro heq
  have h := L4Nodup GD i_A i_B k_rel k_acq w_x r_x Hcons Hgmo_perm
  unfold L4 at h
  rw [heq] at h
  simp at h

theorem L4NeWrelAcq (Hcons : rvwmoCatConsistent GD)
    (Hgmo_perm : (L4 i_A i_B k_rel k_acq w_x r_x).Perm GD.gdG.gxGmo) :
    wRel i_A k_rel ≠ AxLockAdeq.acq i_B k_acq := by
  intro heq
  have h := L4Nodup GD i_A i_B k_rel k_acq w_x r_x Hcons Hgmo_perm
  unfold L4 at h
  rw [heq] at h
  simp at h

theorem L4NeWrelRx (Hcons : rvwmoCatConsistent GD)
    (Hgmo_perm : (L4 i_A i_B k_rel k_acq w_x r_x).Perm GD.gdG.gxGmo) :
    wRel i_A k_rel ≠ r_x := by
  intro heq
  have h := L4Nodup GD i_A i_B k_rel k_acq w_x r_x Hcons Hgmo_perm
  unfold L4 at h
  rw [heq] at h
  simp at h

theorem L4NeAcqRx (Hcons : rvwmoCatConsistent GD)
    (Hgmo_perm : (L4 i_A i_B k_rel k_acq w_x r_x).Perm GD.gdG.gxGmo) :
    AxLockAdeq.acq i_B k_acq ≠ r_x := by
  intro heq
  have h := L4Nodup GD i_A i_B k_rel k_acq w_x r_x Hcons Hgmo_perm
  unfold L4 at h
  rw [heq] at h
  simp at h

/-- Lean-only: membership in the processing list. -/
theorem AxLockAdeq.L4Mem (e : Geid) :
    e ∈ L4 i_A i_B k_rel k_acq w_x r_x ↔
      e = w_x ∨ e = wRel i_A k_rel ∨ e = AxLockAdeq.acq i_B k_acq ∨ e = r_x := by
  unfold L4
  simp only [List.mem_cons, List.not_mem_nil, or_false]

theorem inL4 (Hgmo_perm : (L4 i_A i_B k_rel k_acq w_x r_x).Perm GD.gdG.gxGmo) (e : Geid) :
    e ∈ GD.gdG.gxGmo →
      e = w_x ∨ e = wRel i_A k_rel ∨ e = AxLockAdeq.acq i_B k_acq ∨ e = r_x := by
  intro He
  exact (AxLockAdeq.L4Mem i_A i_B k_rel k_acq w_x r_x e).1 (Hgmo_perm.mem_iff.2 He)

section lobSucc
variable [Axpol]

theorem lobSuccWx (Hcons : rvwmoCatConsistent GD)
    (Hgmo_perm : (L4 i_A i_B k_rel k_acq w_x r_x).Perm GD.gdG.gxGmo)
    (Hlobp_wx : Axpol.lobp GD w_x = (∅ : GSet Geid))
    (Hlobp_wrel : Axpol.lobp GD (wRel i_A k_rel) = ({w_x} : GSet Geid))
    (Hlobp_acq : Axpol.lobp GD (AxLockAdeq.acq i_B k_acq) = ({wRel i_A k_rel} : GSet Geid))
    (Hlobp_rx : Axpol.lobp GD r_x = ({AxLockAdeq.acq i_B k_acq} : GSet Geid)) :
    lobSuccOf GD w_x = ({wRel i_A k_rel} : GSet Geid) := by
  rw [setEq]
  intro e'
  rw [elemOfLobSuccOf, elemOfSingleton]
  constructor
  · rintro ⟨hin, hgmo⟩
    rcases inL4 GD i_A i_B k_rel k_acq w_x r_x Hgmo_perm e' hgmo with h | h | h | h <;>
      rw [h] at hin ⊢
    · rw [Hlobp_wx] at hin
      exact absurd hin notElemOfEmpty
    · rw [Hlobp_acq, elemOfSingleton] at hin
      exact absurd hin (L4NeWxWrel GD i_A i_B k_rel k_acq w_x r_x Hcons Hgmo_perm)
    · rw [Hlobp_rx, elemOfSingleton] at hin
      exact absurd hin (L4NeWxAcq GD i_A i_B k_rel k_acq w_x r_x Hcons Hgmo_perm)
  · intro h
    rw [h]
    refine ⟨by rw [Hlobp_wrel]; exact elemOfSingleton.2 rfl, Hgmo_perm.mem_iff.1 ?_⟩
    exact (AxLockAdeq.L4Mem i_A i_B k_rel k_acq w_x r_x _).2 (Or.inr (Or.inl rfl))

theorem lobSuccWrel (Hcons : rvwmoCatConsistent GD)
    (Hgmo_perm : (L4 i_A i_B k_rel k_acq w_x r_x).Perm GD.gdG.gxGmo)
    (Hlobp_wx : Axpol.lobp GD w_x = (∅ : GSet Geid))
    (Hlobp_wrel : Axpol.lobp GD (wRel i_A k_rel) = ({w_x} : GSet Geid))
    (Hlobp_acq : Axpol.lobp GD (AxLockAdeq.acq i_B k_acq) = ({wRel i_A k_rel} : GSet Geid))
    (Hlobp_rx : Axpol.lobp GD r_x = ({AxLockAdeq.acq i_B k_acq} : GSet Geid)) :
    lobSuccOf GD (wRel i_A k_rel) = ({AxLockAdeq.acq i_B k_acq} : GSet Geid) := by
  rw [setEq]
  intro e'
  rw [elemOfLobSuccOf, elemOfSingleton]
  constructor
  · rintro ⟨hin, hgmo⟩
    rcases inL4 GD i_A i_B k_rel k_acq w_x r_x Hgmo_perm e' hgmo with h | h | h | h <;>
      rw [h] at hin ⊢
    · rw [Hlobp_wx] at hin
      exact absurd hin notElemOfEmpty
    · rw [Hlobp_wrel, elemOfSingleton] at hin
      exact absurd hin.symm (L4NeWxWrel GD i_A i_B k_rel k_acq w_x r_x Hcons Hgmo_perm)
    · rw [Hlobp_rx, elemOfSingleton] at hin
      exact absurd hin (L4NeWrelAcq GD i_A i_B k_rel k_acq w_x r_x Hcons Hgmo_perm)
  · intro h
    rw [h]
    refine ⟨by rw [Hlobp_acq]; exact elemOfSingleton.2 rfl, Hgmo_perm.mem_iff.1 ?_⟩
    exact (AxLockAdeq.L4Mem i_A i_B k_rel k_acq w_x r_x _).2 (Or.inr (Or.inr (Or.inl rfl)))

theorem lobSuccAcq (Hcons : rvwmoCatConsistent GD)
    (Hgmo_perm : (L4 i_A i_B k_rel k_acq w_x r_x).Perm GD.gdG.gxGmo)
    (Hlobp_wx : Axpol.lobp GD w_x = (∅ : GSet Geid))
    (Hlobp_wrel : Axpol.lobp GD (wRel i_A k_rel) = ({w_x} : GSet Geid))
    (Hlobp_acq : Axpol.lobp GD (AxLockAdeq.acq i_B k_acq) = ({wRel i_A k_rel} : GSet Geid))
    (Hlobp_rx : Axpol.lobp GD r_x = ({AxLockAdeq.acq i_B k_acq} : GSet Geid)) :
    lobSuccOf GD (AxLockAdeq.acq i_B k_acq) = ({r_x} : GSet Geid) := by
  rw [setEq]
  intro e'
  rw [elemOfLobSuccOf, elemOfSingleton]
  constructor
  · rintro ⟨hin, hgmo⟩
    rcases inL4 GD i_A i_B k_rel k_acq w_x r_x Hgmo_perm e' hgmo with h | h | h | h <;>
      rw [h] at hin ⊢
    · rw [Hlobp_wx] at hin
      exact absurd hin notElemOfEmpty
    · rw [Hlobp_wrel, elemOfSingleton] at hin
      exact absurd hin.symm (L4NeWxAcq GD i_A i_B k_rel k_acq w_x r_x Hcons Hgmo_perm)
    · rw [Hlobp_acq, elemOfSingleton] at hin
      exact absurd hin.symm (L4NeWrelAcq GD i_A i_B k_rel k_acq w_x r_x Hcons Hgmo_perm)
  · intro h
    rw [h]
    refine ⟨by rw [Hlobp_rx]; exact elemOfSingleton.2 rfl, Hgmo_perm.mem_iff.1 ?_⟩
    exact (AxLockAdeq.L4Mem i_A i_B k_rel k_acq w_x r_x _).2 (Or.inr (Or.inr (Or.inr rfl)))

theorem lobSuccRx (Hcons : rvwmoCatConsistent GD)
    (Hgmo_perm : (L4 i_A i_B k_rel k_acq w_x r_x).Perm GD.gdG.gxGmo)
    (Hlobp_wx : Axpol.lobp GD w_x = (∅ : GSet Geid))
    (Hlobp_wrel : Axpol.lobp GD (wRel i_A k_rel) = ({w_x} : GSet Geid))
    (Hlobp_acq : Axpol.lobp GD (AxLockAdeq.acq i_B k_acq) = ({wRel i_A k_rel} : GSet Geid))
    (Hlobp_rx : Axpol.lobp GD r_x = ({AxLockAdeq.acq i_B k_acq} : GSet Geid)) :
    lobSuccOf GD r_x = (∅ : GSet Geid) := by
  rw [setEq]
  intro e'
  rw [elemOfLobSuccOf]
  constructor
  · rintro ⟨hin, hgmo⟩
    exfalso
    rcases inL4 GD i_A i_B k_rel k_acq w_x r_x Hgmo_perm e' hgmo with h | h | h | h <;>
      rw [h] at hin
    · rw [Hlobp_wx] at hin
      exact notElemOfEmpty hin
    · rw [Hlobp_wrel, elemOfSingleton] at hin
      exact L4NeWxRx GD i_A i_B k_rel k_acq w_x r_x Hcons Hgmo_perm hin.symm
    · rw [Hlobp_acq, elemOfSingleton] at hin
      exact L4NeWrelRx GD i_A i_B k_rel k_acq w_x r_x Hcons Hgmo_perm hin.symm
    · rw [Hlobp_rx, elemOfSingleton] at hin
      exact L4NeAcqRx GD i_A i_B k_rel k_acq w_x r_x Hcons Hgmo_perm hin.symm
  · intro h
    exact absurd h notElemOfEmpty

end lobSucc

/-! ### 2.3 The lock discipline, specialized to the singleton `Hh` -/

variable (x : Int) (vx : BitVec 8)

theorem HhWr (Hwx : gwritesByte GD.gdG w_x x vx) :
    ∀ p, p ∈ Hh w_x vx → gwritesByte GD.gdG p.1 x p.2 := by
  intro p hp
  unfold Hh at hp
  rw [List.mem_singleton] at hp
  subst hp
  exact Hwx

theorem HhCh : chainWith (gmoLt GD.gdG) ((Hh w_x vx).map Prod.fst) := by
  intro i w1 w2 _ hj
  simp [Hh] at hj

theorem HhOwn
    (Hdisc : ∀ w vv, gwritesByte GD.gdG w x vv → WeakRvwmoGraph.gpo GD.gdG w r_x → w = w_x) :
    ∀ w vv, gwritesByte GD.gdG w x vv → WeakRvwmoGraph.gpo GD.gdG w r_x →
      w ∈ (Hh w_x vx).map Prod.fst := by
  intro w vv hw hp
  rw [Hdisc w vv hw hp]
  simp [Hh]

theorem HhLast : (Hh w_x vx).getLast? = some (w_x, vx) := rfl

/-! ### 2.4 The `ea0`/`na0` lookups -/

section lookups
variable {GF : BundledGFunctors}

theorem na0Wx :
    get? (na0 (GF := GF) x GD i_A i_B k_rel k_acq w_x r_x vx) w_x = some iprop(emp) := by
  unfold na0
  exact lookupInsert

theorem na0Wrel (Hcons : rvwmoCatConsistent GD)
    (Hgmo_perm : (L4 i_A i_B k_rel k_acq w_x r_x).Perm GD.gdG.gxGmo) :
    get? (na0 (GF := GF) x GD i_A i_B k_rel k_acq w_x r_x vx) (wRel i_A k_rel) =
      some iprop(emp) := by
  unfold na0
  rw [lookupInsertNe (L4NeWxWrel GD i_A i_B k_rel k_acq w_x r_x Hcons Hgmo_perm)]
  exact lookupInsert

theorem na0Acq (Hcons : rvwmoCatConsistent GD)
    (Hgmo_perm : (L4 i_A i_B k_rel k_acq w_x r_x).Perm GD.gdG.gxGmo) :
    get? (na0 (GF := GF) x GD i_A i_B k_rel k_acq w_x r_x vx) (AxLockAdeq.acq i_B k_acq) =
      some iprop(emp) := by
  unfold na0
  rw [lookupInsertNe (L4NeWxAcq GD i_A i_B k_rel k_acq w_x r_x Hcons Hgmo_perm),
    lookupInsertNe (L4NeWrelAcq GD i_A i_B k_rel k_acq w_x r_x Hcons Hgmo_perm)]
  exact lookupInsert

theorem na0Rx (Hcons : rvwmoCatConsistent GD)
    (Hgmo_perm : (L4 i_A i_B k_rel k_acq w_x r_x).Perm GD.gdG.gxGmo) :
    get? (na0 (GF := GF) x GD i_A i_B k_rel k_acq w_x r_x vx) r_x =
      some iprop(⌜grfAt GD.gdG x w_x r_x ∧ ∀ t v, greadsByte GD.gdG r_x x t v → v = vx⌝) := by
  unfold na0
  rw [lookupInsertNe (L4NeWxRx GD i_A i_B k_rel k_acq w_x r_x Hcons Hgmo_perm),
    lookupInsertNe (L4NeWrelRx GD i_A i_B k_rel k_acq w_x r_x Hcons Hgmo_perm),
    lookupInsertNe (L4NeAcqRx GD i_A i_B k_rel k_acq w_x r_x Hcons Hgmo_perm)]
  exact lookupInsert

variable [AxlogG GF Hent] (γ : GName) (L : Int)

theorem ea0Wx :
    get? (AxLockAdeq.ea0 (GF := GF) γ L x GD i_A i_B k_rel k_acq w_x r_x vx) w_x =
      some (∅ : Mea GF) := by
  unfold AxLockAdeq.ea0
  exact lookupInsert

theorem ea0Wrel (Hcons : rvwmoCatConsistent GD)
    (Hgmo_perm : (L4 i_A i_B k_rel k_acq w_x r_x).Perm GD.gdG.gxGmo) :
    get? (AxLockAdeq.ea0 (GF := GF) γ L x GD i_A i_B k_rel k_acq w_x r_x vx) (wRel i_A k_rel) =
      some ({[w_x := tokTie GD γ x (Hh w_x vx) {[w_x := (1 : Qp)]}]} : Mea GF) := by
  unfold AxLockAdeq.ea0
  rw [lookupInsertNe (L4NeWxWrel GD i_A i_B k_rel k_acq w_x r_x Hcons Hgmo_perm)]
  exact lookupInsert

theorem ea0Acq (Hcons : rvwmoCatConsistent GD)
    (Hgmo_perm : (L4 i_A i_B k_rel k_acq w_x r_x).Perm GD.gdG.gxGmo) :
    get? (AxLockAdeq.ea0 (GF := GF) γ L x GD i_A i_B k_rel k_acq w_x r_x vx)
        (AxLockAdeq.acq i_B k_acq) =
      some ({[wRel i_A k_rel := histAuth γ L 1 [(wRel i_A k_rel, b0)]]} : Mea GF) := by
  unfold AxLockAdeq.ea0
  rw [lookupInsertNe (L4NeWxAcq GD i_A i_B k_rel k_acq w_x r_x Hcons Hgmo_perm),
    lookupInsertNe (L4NeWrelAcq GD i_A i_B k_rel k_acq w_x r_x Hcons Hgmo_perm)]
  exact lookupInsert

theorem ea0Rx (Hcons : rvwmoCatConsistent GD)
    (Hgmo_perm : (L4 i_A i_B k_rel k_acq w_x r_x).Perm GD.gdG.gxGmo) :
    get? (AxLockAdeq.ea0 (GF := GF) γ L x GD i_A i_B k_rel k_acq w_x r_x vx) r_x =
      some ({[AxLockAdeq.acq i_B k_acq :=
        RAcq2 γ L x GD (wRel i_A k_rel) (AxLockAdeq.acq i_B k_acq) (Hh w_x vx)]} : Mea GF) := by
  unfold AxLockAdeq.ea0
  rw [lookupInsertNe (L4NeWxRx GD i_A i_B k_rel k_acq w_x r_x Hcons Hgmo_perm),
    lookupInsertNe (L4NeWrelRx GD i_A i_B k_rel k_acq w_x r_x Hcons Hgmo_perm),
    lookupInsertNe (L4NeAcqRx GD i_A i_B k_rel k_acq w_x r_x Hcons Hgmo_perm)]
  exact lookupInsert

/-! ### 2.6 `axpolWfL`, the `dom`/`HeaLob` side conditions -/

theorem L40 : (L4 i_A i_B k_rel k_acq w_x r_x)[0]? = some w_x := rfl
theorem L41 : (L4 i_A i_B k_rel k_acq w_x r_x)[1]? = some (wRel i_A k_rel) := rfl
theorem L42 : (L4 i_A i_B k_rel k_acq w_x r_x)[2]? = some (AxLockAdeq.acq i_B k_acq) := rfl
theorem L43 : (L4 i_A i_B k_rel k_acq w_x r_x)[3]? = some r_x := rfl

theorem axpolWfL4 [Axpol]
    (Hlobp_wx : Axpol.lobp GD w_x = (∅ : GSet Geid))
    (Hlobp_wrel : Axpol.lobp GD (wRel i_A k_rel) = ({w_x} : GSet Geid))
    (Hlobp_acq : Axpol.lobp GD (AxLockAdeq.acq i_B k_acq) = ({wRel i_A k_rel} : GSet Geid))
    (Hlobp_rx : Axpol.lobp GD r_x = ({AxLockAdeq.acq i_B k_acq} : GSet Geid))
    (Hspol_wx : Axpol.sPol GD w_x ⊆ (∅ : GSet Geid))
    (Hspol_wrel : Axpol.sPol GD (wRel i_A k_rel) ⊆ ({w_x} : GSet Geid))
    (Hspol_acq_wf : Axpol.sPol GD (AxLockAdeq.acq i_B k_acq) ⊆
      (({w_x} : GSet Geid) ∪ {wRel i_A k_rel}))
    (Hspol_rx : Axpol.sPol GD r_x ⊆
      ((({w_x} : GSet Geid) ∪ {wRel i_A k_rel}) ∪ {AxLockAdeq.acq i_B k_acq})) :
    axpolWfL GD (L4 i_A i_B k_rel k_acq w_x r_x) := by
  have h1 := takeLSnoc (L4 i_A i_B k_rel k_acq w_x r_x) 0 w_x (L40 i_A i_B k_rel k_acq w_x r_x)
  have h2 := takeLSnoc (L4 i_A i_B k_rel k_acq w_x r_x) 1 _ (L41 i_A i_B k_rel k_acq w_x r_x)
  have h3 := takeLSnoc (L4 i_A i_B k_rel k_acq w_x r_x) 2 _ (L42 i_A i_B k_rel k_acq w_x r_x)
  rw [takeL0] at h1
  intro n e Hn
  rcases n with _ | _ | _ | _ | n'
  · rw [L40] at Hn
    obtain rfl := Option.some.inj Hn
    rw [takeL0]
    exact ⟨Hspol_wx, by rw [Hlobp_wx]; all_goals exact fun _ h => h⟩
  · rw [L41] at Hn
    obtain rfl := Option.some.inj Hn
    rw [h1]
    refine ⟨fun y hy => elemOfUnionL (Hspol_wrel y hy), ?_⟩
    rw [Hlobp_wrel]
    exact fun y hy => elemOfUnionL hy
  · rw [L42] at Hn
    obtain rfl := Option.some.inj Hn
    rw [h2, h1]
    refine ⟨fun y hy => ?_, ?_⟩
    · rcases elemOfUnion.1 (Hspol_acq_wf y hy) with h | h
      · exact elemOfUnionR (elemOfUnionL h)
      · exact elemOfUnionL h
    · rw [Hlobp_acq]
      exact fun y hy => elemOfUnionL hy
  · rw [L43] at Hn
    obtain rfl := Option.some.inj Hn
    rw [h3, h2, h1]
    refine ⟨fun y hy => ?_, ?_⟩
    · rcases elemOfUnion.1 (Hspol_rx y hy) with h | h
      · rcases elemOfUnion.1 h with h' | h'
        · exact elemOfUnionR (elemOfUnionR (elemOfUnionL h'))
        · exact elemOfUnionR (elemOfUnionL h')
      · exact elemOfUnionL h
    · rw [Hlobp_rx]
      exact fun y hy => elemOfUnionL hy
  · exfalso
    simp [L4] at Hn

theorem HdomEq0 :
    (FiniteMap.dom_set (AxLockAdeq.ea0 (GF := GF) γ L x GD i_A i_B k_rel k_acq w_x r_x vx) :
      GSet Geid) =
    FiniteMap.dom_set (na0 (GF := GF) x GD i_A i_B k_rel k_acq w_x r_x vx) := by
  unfold AxLockAdeq.ea0 na0
  simp only [domInsert, domEmpty]

theorem Hdom0 :
    (LawfulSet.ofList (L4 i_A i_B k_rel k_acq w_x r_x) : GSet Geid) ⊆
      FiniteMap.dom_set (na0 (GF := GF) x GD i_A i_B k_rel k_acq w_x r_x vx) := by
  intro e he
  rw [elemOfListToSet, AxLockAdeq.L4Mem] at he
  unfold na0
  simp only [domInsert, domEmpty, elemOfUnion, elemOfSingleton]
  rcases he with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))

theorem AxLockAdeq.HeaLob0 [Axpol]
    (Hlobp_wx : Axpol.lobp GD w_x = (∅ : GSet Geid))
    (Hlobp_wrel : Axpol.lobp GD (wRel i_A k_rel) = ({w_x} : GSet Geid))
    (Hlobp_acq : Axpol.lobp GD (AxLockAdeq.acq i_B k_acq) = ({wRel i_A k_rel} : GSet Geid))
    (Hlobp_rx : Axpol.lobp GD r_x = ({AxLockAdeq.acq i_B k_acq} : GSet Geid)) :
    ∀ e0 gm, get? (AxLockAdeq.ea0 (GF := GF) γ L x GD i_A i_B k_rel k_acq w_x r_x vx) e0 =
      some gm → (FiniteMap.dom_set gm : GSet Geid) ⊆ Axpol.lobp GD e0 := by
  intro e0 gm Hea
  unfold AxLockAdeq.ea0 at Hea
  by_cases h1 : w_x = e0
  · rw [← h1] at Hea ⊢
    rw [lookupInsert] at Hea
    obtain rfl := Option.some.inj Hea
    rw [domEmpty, Hlobp_wx]
    all_goals exact fun _ h => h
  rw [lookupInsertNe h1] at Hea
  by_cases h2 : wRel i_A k_rel = e0
  · rw [← h2] at Hea ⊢
    rw [lookupInsert] at Hea
    obtain rfl := Option.some.inj Hea
    rw [domSingleton, Hlobp_wrel]
    all_goals exact fun _ h => h
  rw [lookupInsertNe h2] at Hea
  by_cases h3 : AxLockAdeq.acq i_B k_acq = e0
  · rw [← h3] at Hea ⊢
    rw [lookupInsert] at Hea
    obtain rfl := Option.some.inj Hea
    rw [domSingleton, Hlobp_acq]
    all_goals exact fun _ h => h
  rw [lookupInsertNe h3] at Hea
  by_cases h4 : r_x = e0
  · rw [← h4] at Hea ⊢
    rw [lookupInsert] at Hea
    obtain rfl := Option.some.inj Hea
    rw [domSingleton, Hlobp_rx]
    all_goals exact fun _ h => h
  rw [lookupInsertNe h4, lookupEmpty] at Hea
  cases Hea

/-- Lean-only: the bag at `r_x` gives the read's pure result. -/
theorem AxLockAdeq.bagRx (Hcons : rvwmoCatConsistent GD)
    (Hgmo_perm : (L4 i_A i_B k_rel k_acq w_x r_x).Perm GD.gdG.gxGmo) :
    ([∗set] e0 ∈ (LawfulSet.ofList (L4 i_A i_B k_rel k_acq w_x r_x) : GSet Geid),
        AxWp.fromOption (fun P => P) iprop(emp)
          (get? (na0 (GF := GF) x GD i_A i_B k_rel k_acq w_x r_x vx) e0)) ⊢
      ⌜grfAt GD.gdG x w_x r_x ∧ ∀ t v, greadsByte GD.gdG r_x x t v → v = vx⌝ := by
  have hmem : r_x ∈ (LawfulSet.ofList (L4 i_A i_B k_rel k_acq w_x r_x) : GSet Geid) := by
    rw [elemOfListToSet, AxLockAdeq.L4Mem]
    exact Or.inr (Or.inr (Or.inr rfl))
  refine (BigSepS.bigSepS_elem_of hmem).trans ?_
  rw [na0Rx GD i_A i_B k_rel k_acq w_x r_x x vx Hcons Hgmo_perm]
  exact .rfl

end lookups

/-! ### 2.9 `Hwonly` — every writer to `x` in the four-event graph is `w_x` -/

theorem Hwonly (L : Int) (Hxl : x ≠ L) (Hcons : rvwmoCatConsistent GD)
    (Hgmo_perm : (L4 i_A i_B k_rel k_acq w_x r_x).Perm GD.gdG.gxGmo)
    (Hsingle_rel : ∀ a' v', gwritesByte GD.gdG (wRel i_A k_rel) a' v' → a' = L)
    (Hsingle_acq : ∀ a' v', gwritesByte GD.gdG (AxLockAdeq.acq i_B k_acq) a' v' → a' = L)
    (Hnw : gisW GD.gdG r_x = false) :
    ∀ w v, gwritesByte GD.gdG w x v → w = w_x := by
  intro w v Hw
  have Hgmo := gwritesByteGmo GD.gdG w x v Hcons.1 Hw
  rcases inL4 GD i_A i_B k_rel k_acq w_x r_x Hgmo_perm w Hgmo with h | h | h | h
  · exact h
  · rw [h] at Hw
    exact absurd (Hsingle_rel x v Hw) Hxl
  · rw [h] at Hw
    exact absurd (Hsingle_acq x v Hw) Hxl
  · rw [h] at Hw
    have hw := AxProt.gwritesByteGisW _ _ _ _ Hw
    rw [Hnw] at hw
    cases hw

theorem HhOwn2 (L : Int) (Hxl : x ≠ L) (Hcons : rvwmoCatConsistent GD)
    (Hgmo_perm : (L4 i_A i_B k_rel k_acq w_x r_x).Perm GD.gdG.gxGmo)
    (Hsingle_rel : ∀ a' v', gwritesByte GD.gdG (wRel i_A k_rel) a' v' → a' = L)
    (Hsingle_acq : ∀ a' v', gwritesByte GD.gdG (AxLockAdeq.acq i_B k_acq) a' v' → a' = L)
    (Hnw : gisW GD.gdG r_x = false) :
    ∀ w vv, gwritesByte GD.gdG w x vv → WeakRvwmoGraph.gpo GD.gdG w r_x →
      w ∈ (Hh w_x vx).map Prod.fst := by
  intro w vv Hw _
  rw [Hwonly GD i_A i_B k_rel k_acq w_x r_x x L Hxl Hcons Hgmo_perm Hsingle_rel Hsingle_acq
    Hnw w vv Hw]
  simp [Hh]

end graph

/-! ## 2.5–2.10 The iProp-level capstone -/

section capstone
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [axG : AxirisG GF] [Axpol]
  [AxlogG GF Hent] [AxLockG GF]
variable (γ γc : GName) (L x : Int) (Hxl : x ≠ L)
variable (ob_D : AxirisG.obSt GF → GSet Geid) (ob_hm : AxirisG.obSt GF → GMapF Geid (List Hent))
  (mk_ob' : GSet Geid → GMapF Geid (List Hent) → AxirisG.obSt GF)
  (Hmk_ob'_D : ∀ D hm, ob_D (mk_ob' D hm) = D)
  (Hmk_ob'_hm : ∀ D hm, ob_hm (mk_ob' D hm) = hm)
  (Hob_eq' : ∀ (GD : Gdexec) (σ : AxirisG.obSt GF) (s : GSet Geid),
    AxirisG.obStInterp GD σ s ⊣⊢ protInvLock' L x γ γc GD s (ob_D σ) (ob_hm σ))
variable (GD : Gdexec) (i_A i_B : Agent) (k_rel k_acq : Nat) (w_x r_x : Geid) (vx : BitVec 8)

include Hxl Hmk_ob'_D Hmk_ob'_hm Hob_eq'

/-- 2.9 `r_x`'s rule WITHOUT `Hsn`: the coverage wand is derived from `Hwonly` and the
deposited token (a snapshot read off its `histAuth` without consuming it). -/
theorem flowEqLockReadWl2 (Hcons : rvwmoCatConsistent GD)
    (Hwx : gwritesByte GD.gdG w_x x vx)
    (Hgmo_perm : (L4 i_A i_B k_rel k_acq w_x r_x).Perm GD.gdG.gxGmo)
    (Hsingle_rel : ∀ a' v', gwritesByte GD.gdG (wRel i_A k_rel) a' v' → a' = L)
    (Hsingle_acq : ∀ a' v', gwritesByte GD.gdG (AxLockAdeq.acq i_B k_acq) a' v' → a' = L)
    (Hnw : gisW GD.gdG r_x = false)
    (Hrd : ∃ t v, greadsByte GD.gdG r_x x t v)
    (acq_e : Geid) (s_ob0 : GSet Geid) (flowIn : Mea GF)
    (Hacq : gacqPo GD.gdG acq_e r_x) :
    (([∗map] Rin ∈ flowIn, Rin) -∗ tokTie GD γ x (Hh w_x vx) {[acq_e := (1 : Qp)]}) ⊢
      flowEqDyn GD r_x s_ob0 flowIn
        iprop(⌜grfAt GD.gdG x w_x r_x ∧ ∀ t v, greadsByte GD.gdG r_x x t v → v = vx⌝) := by
  have Hwo := Hwonly GD i_A i_B k_rel k_acq w_x r_x x L Hxl Hcons Hgmo_perm Hsingle_rel
    Hsingle_acq Hnw
  iintro Hflowin
  unfold flowEqDyn
  iintro %σ %sOb %Hsub %Hnin Hob Hflow
  ihave Htie := Hflowin $$ Hflow
  iunfold tokTie at Htie
  icases Htie with ⟨Hauth, %Htiebase⟩
  ihave Hauth := (tokSingleton γ x (Hh w_x vx) acq_e 1).1 $$ Hauth
  ihave #Hsnap := histSnapGet γ x 1 (Hh w_x vx) $$ Hauth
  ihave Hsn' : iprop(∀ w v, ⌜gwritesByte GD.gdG w x v⌝ -∗ ⌜gmoLt GD.gdG w r_x⌝ -∗
      ∃ (H' : List Hent), ⌜w ∈ H'.map Prod.fst⌝ ∗ histSnap (GF := GF) γ x H') $$ []
  · iintro %w %v %Hwb %_
    iexists (Hh w_x vx)
    isplitl []
    · ipureintro
      rw [Hwo w v Hwb]
      exact histSnapLastIn (Hh w_x vx) w_x vx (HhLast w_x vx)
    · iexact Hsnap
  ihave Htie2 : tokTie GD γ x (Hh w_x vx) {[acq_e := (1 : Qp)]} $$ [Hauth]
  · iunfold tokTie
    isplitl [Hauth]
    · iapply (tokSingleton γ x (Hh w_x vx) acq_e 1).2
      iexact Hauth
    · ipureintro
      exact Htiebase
  ihave %Hres := lockReadOwn GD γ x (Hh w_x vx) w_x acq_e r_x vx Hcons
    (HhWr GD w_x x vx Hwx) (HhCh GD w_x vx)
    (HhOwn2 GD i_A i_B k_rel k_acq w_x r_x x vx L Hxl Hcons Hgmo_perm Hsingle_rel Hsingle_acq Hnw)
    (HhLast w_x vx) Hacq Hrd $$ [$Htie2 $Hsn']
  ihave Hob := (Hob_eq' GD σ sOb).1 $$ Hob
  ihave Hob' := protInvLockReadStep2 γ γc L x Hxl ob_D ob_hm mk_ob' Hmk_ob'_D Hmk_ob'_hm Hob_eq'
    r_x sOb (ob_D σ) (ob_hm σ) GD Hnin Hnw $$ Hob
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  inext
  imod Hclose
  imodintro
  iexists σ
  isplitl [Hob']
  · iapply (Hob_eq' GD σ (({r_x} : GSet Geid) ∪ sOb)).2
    iexact Hob'
  · ipureintro
    exact Hres

/-! ### 2.5 / 2.10 The four bullets of `ordEaTodoL GD ea0 na0 L4 0` (Lean-only helpers) -/

/-- Lean-only: `w_x`'s bullet. -/
theorem AxLockAdeq.todoWx (Hcons : rvwmoCatConsistent GD)
    (Hwx : gwritesByte GD.gdG w_x x vx)
    (Hsingle_wx : ∀ a' v', gwritesByte GD.gdG w_x a' v' → a' = x)
    (Hgd_wx : graphData GD w_x = some [vx])
    (Hgmo_perm : (L4 i_A i_B k_rel k_acq w_x r_x).Perm GD.gdG.gxGmo)
    (Hlobp_wx : Axpol.lobp GD w_x = (∅ : GSet Geid))
    (Hlobp_wrel : Axpol.lobp GD (wRel i_A k_rel) = ({w_x} : GSet Geid))
    (Hlobp_acq : Axpol.lobp GD (AxLockAdeq.acq i_B k_acq) = ({wRel i_A k_rel} : GSet Geid))
    (Hlobp_rx : Axpol.lobp GD r_x = ({AxLockAdeq.acq i_B k_acq} : GSet Geid)) :
    histAuth (GF := GF) γ x 1 [] ⊢
      AxWp.fromOption (fun R0 => AxWp.fromOption (fun flowIn => flowEqEa GD w_x
          (Axpol.sPol GD w_x) flowIn (AxLockAdeq.ea0 (GF := GF) γ L x GD i_A i_B k_rel k_acq w_x r_x vx) R0)
          iprop(emp) (get? (AxLockAdeq.ea0 (GF := GF) γ L x GD i_A i_B k_rel k_acq w_x r_x vx) w_x))
        iprop(emp) (get? (na0 (GF := GF) x GD i_A i_B k_rel k_acq w_x r_x vx) w_x) := by
  rw [na0Wx, ea0Wx]
  simp only [AxWp.fromOption]
  unfold flowEqEa
  have hdep := AxLockAdeq.eaDepositOne (AxLockAdeq.ea0 (GF := GF) γ L x GD i_A i_B k_rel k_acq w_x r_x vx)
    (lobSuccOf GD w_x) w_x (wRel i_A k_rel) _ _
    (lobSuccWx GD i_A i_B k_rel k_acq w_x r_x Hcons Hgmo_perm Hlobp_wx Hlobp_wrel Hlobp_acq
      Hlobp_rx)
    (ea0Wrel GD i_A i_B k_rel k_acq w_x r_x x vx γ L Hcons Hgmo_perm) lookupSingleton
  rw [show Hh w_x vx = ([] : List Hent) ++ [(w_x, vx)] from rfl] at hdep
  iintro Hx
  ihave Hsrc := flowEqOwnedWriteX2 γ γc L x Hxl ob_D ob_hm mk_ob' Hmk_ob'_D Hmk_ob'_hm Hob_eq'
    GD w_x vx [] (Axpol.sPol GD w_x) [vx] Hwx Hsingle_wx Hgd_wx $$ Hx
  iapply AxLockAdeq.flowMono GD w_x (Axpol.sPol GD w_x) (∅ : Mea GF) _ _ $$ Hsrc
  inext
  iintro ⟨Htie, -⟩
  isplitl []
  · itrivial
  · iapply hdep.2
    iexact Htie

/-- Lean-only: `w_rel`'s bullet. -/
theorem AxLockAdeq.todoWrel (Hcons : rvwmoCatConsistent GD)
    (Hfence : gppoCat GD w_x (wRel i_A k_rel))
    (Hwb0 : gwritesByte GD.gdG (wRel i_A k_rel) L b0)
    (Hsingle_rel : ∀ a' v', gwritesByte GD.gdG (wRel i_A k_rel) a' v' → a' = L)
    (Hgmo_perm : (L4 i_A i_B k_rel k_acq w_x r_x).Perm GD.gdG.gxGmo)
    (Hlobp_wx : Axpol.lobp GD w_x = (∅ : GSet Geid))
    (Hlobp_wrel : Axpol.lobp GD (wRel i_A k_rel) = ({w_x} : GSet Geid))
    (Hlobp_acq : Axpol.lobp GD (AxLockAdeq.acq i_B k_acq) = ({wRel i_A k_rel} : GSet Geid))
    (Hlobp_rx : Axpol.lobp GD r_x = ({AxLockAdeq.acq i_B k_acq} : GSet Geid)) :
    histAuth (GF := GF) γ L 1 [] ⊢
      AxWp.fromOption (fun R0 => AxWp.fromOption (fun flowIn => flowEqEa GD (wRel i_A k_rel)
          (Axpol.sPol GD (wRel i_A k_rel)) flowIn
          (AxLockAdeq.ea0 (GF := GF) γ L x GD i_A i_B k_rel k_acq w_x r_x vx) R0)
          iprop(emp)
          (get? (AxLockAdeq.ea0 (GF := GF) γ L x GD i_A i_B k_rel k_acq w_x r_x vx) (wRel i_A k_rel)))
        iprop(emp) (get? (na0 (GF := GF) x GD i_A i_B k_rel k_acq w_x r_x vx) (wRel i_A k_rel)) := by
  have Hgob1 : gobCat GD w_x (wRel i_A k_rel) := gobCatStep GD _ _ (Or.inl Hfence)
  rw [na0Wrel GD i_A i_B k_rel k_acq w_x r_x x vx Hcons Hgmo_perm,
    ea0Wrel GD i_A i_B k_rel k_acq w_x r_x x vx γ L Hcons Hgmo_perm]
  simp only [AxWp.fromOption]
  unfold flowEqEa
  have hdep := AxLockAdeq.eaDepositOne (AxLockAdeq.ea0 (GF := GF) γ L x GD i_A i_B k_rel k_acq w_x r_x vx)
    (lobSuccOf GD (wRel i_A k_rel)) (wRel i_A k_rel) (AxLockAdeq.acq i_B k_acq) _ _
    (lobSuccWrel GD i_A i_B k_rel k_acq w_x r_x Hcons Hgmo_perm Hlobp_wx Hlobp_wrel Hlobp_acq
      Hlobp_rx)
    (ea0Acq GD i_A i_B k_rel k_acq w_x r_x x vx γ L Hcons Hgmo_perm) lookupSingleton
  rw [show [(wRel i_A k_rel, b0)] = ([] : List Hent) ++ [((i_A, k_rel), b0)] from rfl] at hdep
  iintro HL
  ihave Hsrc := flowEqReleaseWx γ γc L x Hxl ob_D ob_hm mk_ob' Hmk_ob'_D Hmk_ob'_hm Hob_eq'
    GD i_A k_rel w_x (Hh w_x vx) []
    ({[w_x := tokTie GD γ x (Hh w_x vx) {[w_x := (1 : Qp)]}]} : Mea GF) Hcons Hwb0 Hsingle_rel Hgob1 $$ HL []
  · iintro Hbag
    ihave Hbag := BigSepM.bigSepM_singleton.1 $$ Hbag
    iexact Hbag
  iapply AxLockAdeq.flowMono GD (wRel i_A k_rel) (Axpol.sPol GD (wRel i_A k_rel)) _ _ _ $$ Hsrc
  inext
  iintro HaL'
  isplitl []
  · itrivial
  · iapply hdep.2
    iexact HaL'

/-- Lean-only: `acq`'s bullet. -/
theorem AxLockAdeq.todoAcq (Hcons : rvwmoCatConsistent GD)
    (Hwb0 : gwritesByte GD.gdG (wRel i_A k_rel) L b0)
    (Hrf : grfe GD.gdG (wRel i_A k_rel) (AxLockAdeq.acq i_B k_acq))
    (Hwb1 : gwritesByte GD.gdG (AxLockAdeq.acq i_B k_acq) L b1)
    (Hsingle_acq : ∀ a' v', gwritesByte GD.gdG (AxLockAdeq.acq i_B k_acq) a' v' → a' = L)
    (Hval_acq : graphData GD (AxLockAdeq.acq i_B k_acq) = some [b1])
    (Hpol : wRel i_A k_rel ∈ Axpol.sPol GD (AxLockAdeq.acq i_B k_acq))
    (Hunclaimed : ∀ σ : AxirisG.obSt GF, wRel i_A k_rel ∉ ob_D σ)
    (Hhm : ∀ σ : AxirisG.obSt GF, get? (ob_hm σ) (wRel i_A k_rel) = some (Hh w_x vx))
    (Hgmo_perm : (L4 i_A i_B k_rel k_acq w_x r_x).Perm GD.gdG.gxGmo)
    (Hlobp_wx : Axpol.lobp GD w_x = (∅ : GSet Geid))
    (Hlobp_wrel : Axpol.lobp GD (wRel i_A k_rel) = ({w_x} : GSet Geid))
    (Hlobp_acq : Axpol.lobp GD (AxLockAdeq.acq i_B k_acq) = ({wRel i_A k_rel} : GSet Geid))
    (Hlobp_rx : Axpol.lobp GD r_x = ({AxLockAdeq.acq i_B k_acq} : GSet Geid)) :
    ⊢ AxWp.fromOption (fun R0 => AxWp.fromOption (fun flowIn => flowEqEa GD
          (AxLockAdeq.acq i_B k_acq) (Axpol.sPol GD (AxLockAdeq.acq i_B k_acq)) flowIn
          (AxLockAdeq.ea0 (GF := GF) γ L x GD i_A i_B k_rel k_acq w_x r_x vx) R0)
          iprop(emp)
          (get? (AxLockAdeq.ea0 (GF := GF) γ L x GD i_A i_B k_rel k_acq w_x r_x vx)
            (AxLockAdeq.acq i_B k_acq)))
        iprop(emp) (get? (na0 (GF := GF) x GD i_A i_B k_rel k_acq w_x r_x vx) (AxLockAdeq.acq i_B k_acq)) := by
  have Hgob2 : gobCat GD (wRel i_A k_rel) (AxLockAdeq.acq i_B k_acq) :=
    gobCatStep GD _ _ (Or.inr (Or.inr (Or.inl Hrf)))
  have Hne : Hh w_x vx ≠ [] := by unfold Hh; exact List.cons_ne_nil _ _
  rw [na0Acq GD i_A i_B k_rel k_acq w_x r_x x vx Hcons Hgmo_perm,
    ea0Acq GD i_A i_B k_rel k_acq w_x r_x x vx γ L Hcons Hgmo_perm]
  simp only [AxWp.fromOption]
  unfold flowEqEa
  have hdep := AxLockAdeq.eaDepositOne (AxLockAdeq.ea0 (GF := GF) γ L x GD i_A i_B k_rel k_acq w_x r_x vx)
    (lobSuccOf GD (AxLockAdeq.acq i_B k_acq)) (AxLockAdeq.acq i_B k_acq) r_x _ _
    (lobSuccAcq GD i_A i_B k_rel k_acq w_x r_x Hcons Hgmo_perm Hlobp_wx Hlobp_wrel Hlobp_acq
      Hlobp_rx)
    (ea0Rx GD i_A i_B k_rel k_acq w_x r_x x vx γ L Hcons Hgmo_perm) lookupSingleton
  ihave Hsrc := flowEqAmoswapAqWl γ γc L x Hxl ob_D ob_hm mk_ob' Hmk_ob'_D Hmk_ob'_hm Hob_eq'
    GD i_B k_acq (wRel i_A k_rel) (Hh w_x vx) [(wRel i_A k_rel, b0)]
    ({[wRel i_A k_rel := histAuth γ L 1 [(wRel i_A k_rel, b0)]]} : Mea GF)
    Hcons Hpol Hunclaimed Hhm Hwb0 Hwb1 Hsingle_acq Hgob2 Hval_acq Hne $$ []
  · iintro Hbag
    ihave Hbag := BigSepM.bigSepM_singleton.1 $$ Hbag
    iexact Hbag
  iapply AxLockAdeq.flowMono GD (AxLockAdeq.acq i_B k_acq) (Axpol.sPol GD (AxLockAdeq.acq i_B k_acq))
    _ _ _ $$ Hsrc
  inext
  iintro HR
  isplitl []
  · itrivial
  · iapply hdep.2
    iexact HR

/-- Lean-only: `r_x`'s bullet, through `flowEqLockReadWl` (with `Hsn`/`Hdisc`). -/
theorem AxLockAdeq.todoRx (Hcons : rvwmoCatConsistent GD)
    (Hwx : gwritesByte GD.gdG w_x x vx)
    (Hacq_po : gacqPo GD.gdG (AxLockAdeq.acq i_B k_acq) r_x)
    (Hnw : gisW GD.gdG r_x = false)
    (Hrd : ∃ t v, greadsByte GD.gdG r_x x t v)
    (Hsn : ⊢ iprop(∀ w v, ⌜gwritesByte GD.gdG w x v⌝ -∗ ⌜gmoLt GD.gdG w r_x⌝ -∗
      ∃ H', ⌜w ∈ H'.map Prod.fst⌝ ∗ histSnap (GF := GF) γ x H'))
    (Hdisc : ∀ w vv, gwritesByte GD.gdG w x vv → WeakRvwmoGraph.gpo GD.gdG w r_x → w = w_x)
    (Hgmo_perm : (L4 i_A i_B k_rel k_acq w_x r_x).Perm GD.gdG.gxGmo)
    (Hlobp_wx : Axpol.lobp GD w_x = (∅ : GSet Geid))
    (Hlobp_wrel : Axpol.lobp GD (wRel i_A k_rel) = ({w_x} : GSet Geid))
    (Hlobp_acq : Axpol.lobp GD (AxLockAdeq.acq i_B k_acq) = ({wRel i_A k_rel} : GSet Geid))
    (Hlobp_rx : Axpol.lobp GD r_x = ({AxLockAdeq.acq i_B k_acq} : GSet Geid)) :
    ⊢ AxWp.fromOption (fun R0 => AxWp.fromOption (fun flowIn => flowEqEa GD r_x
          (Axpol.sPol GD r_x) flowIn (AxLockAdeq.ea0 (GF := GF) γ L x GD i_A i_B k_rel k_acq w_x r_x vx) R0)
          iprop(emp) (get? (AxLockAdeq.ea0 (GF := GF) γ L x GD i_A i_B k_rel k_acq w_x r_x vx) r_x))
        iprop(emp) (get? (na0 (GF := GF) x GD i_A i_B k_rel k_acq w_x r_x vx) r_x) := by
  rw [na0Rx GD i_A i_B k_rel k_acq w_x r_x x vx Hcons Hgmo_perm,
    ea0Rx GD i_A i_B k_rel k_acq w_x r_x x vx γ L Hcons Hgmo_perm]
  simp only [AxWp.fromOption]
  unfold flowEqEa
  have hdep := AxLockAdeq.eaDepositNone (AxLockAdeq.ea0 (GF := GF) γ L x GD i_A i_B k_rel k_acq w_x r_x vx)
    (lobSuccOf GD r_x) r_x
    (lobSuccRx GD i_A i_B k_rel k_acq w_x r_x Hcons Hgmo_perm Hlobp_wx Hlobp_wrel Hlobp_acq
      Hlobp_rx)
  ihave Hsrc := flowEqLockReadWl γ γc L x Hxl ob_D ob_hm mk_ob' Hmk_ob'_D Hmk_ob'_hm Hob_eq'
    GD (AxLockAdeq.acq i_B k_acq) r_x (Hh w_x vx) w_x vx (Axpol.sPol GD r_x)
    ({[AxLockAdeq.acq i_B k_acq :=
      RAcq2 γ L x GD (wRel i_A k_rel) (AxLockAdeq.acq i_B k_acq) (Hh w_x vx)]} : Mea GF)
    Hcons Hnw (HhWr GD w_x x vx Hwx) (HhCh GD w_x vx) (HhOwn GD w_x r_x x vx Hdisc)
    (HhLast w_x vx) Hacq_po Hrd Hsn $$ []
  · iintro Hbag
    ihave Hbag := BigSepM.bigSepM_singleton.1 $$ Hbag
    iunfold RAcq2 at Hbag
    icases Hbag with ⟨-, Hbag⟩
    iexact Hbag
  iapply AxLockAdeq.flowMono GD r_x (Axpol.sPol GD r_x) _ _ _ $$ Hsrc
  inext
  iintro HP
  isplitl [HP]
  · iexact HP
  · iapply hdep.2
    itrivial

/-- Lean-only: `r_x`'s bullet, through the `Hsn`-free `flowEqLockReadWl2`. -/
theorem AxLockAdeq.todoRx2 (Hcons : rvwmoCatConsistent GD)
    (Hwx : gwritesByte GD.gdG w_x x vx)
    (Hsingle_rel : ∀ a' v', gwritesByte GD.gdG (wRel i_A k_rel) a' v' → a' = L)
    (Hsingle_acq : ∀ a' v', gwritesByte GD.gdG (AxLockAdeq.acq i_B k_acq) a' v' → a' = L)
    (Hacq_po : gacqPo GD.gdG (AxLockAdeq.acq i_B k_acq) r_x)
    (Hnw : gisW GD.gdG r_x = false)
    (Hrd : ∃ t v, greadsByte GD.gdG r_x x t v)
    (Hgmo_perm : (L4 i_A i_B k_rel k_acq w_x r_x).Perm GD.gdG.gxGmo)
    (Hlobp_wx : Axpol.lobp GD w_x = (∅ : GSet Geid))
    (Hlobp_wrel : Axpol.lobp GD (wRel i_A k_rel) = ({w_x} : GSet Geid))
    (Hlobp_acq : Axpol.lobp GD (AxLockAdeq.acq i_B k_acq) = ({wRel i_A k_rel} : GSet Geid))
    (Hlobp_rx : Axpol.lobp GD r_x = ({AxLockAdeq.acq i_B k_acq} : GSet Geid)) :
    ⊢ AxWp.fromOption (fun R0 => AxWp.fromOption (fun flowIn => flowEqEa GD r_x
          (Axpol.sPol GD r_x) flowIn (AxLockAdeq.ea0 (GF := GF) γ L x GD i_A i_B k_rel k_acq w_x r_x vx) R0)
          iprop(emp) (get? (AxLockAdeq.ea0 (GF := GF) γ L x GD i_A i_B k_rel k_acq w_x r_x vx) r_x))
        iprop(emp) (get? (na0 (GF := GF) x GD i_A i_B k_rel k_acq w_x r_x vx) r_x) := by
  rw [na0Rx GD i_A i_B k_rel k_acq w_x r_x x vx Hcons Hgmo_perm,
    ea0Rx GD i_A i_B k_rel k_acq w_x r_x x vx γ L Hcons Hgmo_perm]
  simp only [AxWp.fromOption]
  unfold flowEqEa
  have hdep := AxLockAdeq.eaDepositNone (AxLockAdeq.ea0 (GF := GF) γ L x GD i_A i_B k_rel k_acq w_x r_x vx)
    (lobSuccOf GD r_x) r_x
    (lobSuccRx GD i_A i_B k_rel k_acq w_x r_x Hcons Hgmo_perm Hlobp_wx Hlobp_wrel Hlobp_acq
      Hlobp_rx)
  ihave Hsrc := flowEqLockReadWl2 γ γc L x Hxl ob_D ob_hm mk_ob' Hmk_ob'_D Hmk_ob'_hm Hob_eq'
    GD i_A i_B k_rel k_acq w_x r_x vx Hcons Hwx Hgmo_perm Hsingle_rel Hsingle_acq Hnw Hrd
    (AxLockAdeq.acq i_B k_acq) (Axpol.sPol GD r_x)
    ({[AxLockAdeq.acq i_B k_acq :=
      RAcq2 γ L x GD (wRel i_A k_rel) (AxLockAdeq.acq i_B k_acq) (Hh w_x vx)]} : Mea GF) Hacq_po $$ []
  · iintro Hbag
    ihave Hbag := BigSepM.bigSepM_singleton.1 $$ Hbag
    iunfold RAcq2 at Hbag
    icases Hbag with ⟨-, Hbag⟩
    iexact Hbag
  iapply AxLockAdeq.flowMono GD r_x (Axpol.sPol GD r_x) _ _ _ $$ Hsrc
  inext
  iintro HP
  isplitl [HP]
  · iexact HP
  · iapply hdep.2
    itrivial

omit Hxl Hmk_ob'_D Hmk_ob'_hm Hob_eq' in
/-- Lean-only: the walk's empty tail. -/
theorem AxLockAdeq.todoTail :
    ⊢ ordEaTodoL GD (AxLockAdeq.ea0 (GF := GF) γ L x GD i_A i_B k_rel k_acq w_x r_x vx)
        (na0 (GF := GF) x GD i_A i_B k_rel k_acq w_x r_x vx) (L4 i_A i_B k_rel k_acq w_x r_x) 4 := by
  unfold ordEaTodoL L4
  simp only [List.drop_succ_cons, List.drop_zero]
  exact BigSepL.bigSepL_nil.2

omit Hxl Hmk_ob'_D Hmk_ob'_hm Hob_eq' in
/-- Lean-only: the initial ob-state, from the empty claimed authority. -/
theorem AxLockAdeq.obInit :
    claimedAuth γc (∅ : GSet Geid) ⊢ protInvLock' (GF := GF) L x γ γc GD ∅ ∅ ∅ := by
  iintro Hc
  iapply (protInvLockUnfold' L x γ γc GD ∅ ∅ ∅).2
  isplitl [Hc]
  · iexact Hc
  isplitl []
  · unfold protInv
    iapply BigSepS.bigSepS_empty.2
    itrivial
  · iapply BigSepS.bigSepS_empty.2
    itrivial

/-! ### The headline results, over Rocq's full Context -/

variable (Hcons : rvwmoCatConsistent GD)
  (Hwx : gwritesByte GD.gdG w_x x vx)
  (Hsingle_wx : ∀ a' v', gwritesByte GD.gdG w_x a' v' → a' = x)
  (Hgd_wx : graphData GD w_x = some [vx])
  (Hfence : gppoCat GD w_x (wRel i_A k_rel))
  (Hwb0 : gwritesByte GD.gdG (wRel i_A k_rel) L b0)
  (Hsingle_rel : ∀ a' v', gwritesByte GD.gdG (wRel i_A k_rel) a' v' → a' = L)
  (Hrf : grfe GD.gdG (wRel i_A k_rel) (AxLockAdeq.acq i_B k_acq))
  (Hwb1 : gwritesByte GD.gdG (AxLockAdeq.acq i_B k_acq) L b1)
  (Hsingle_acq : ∀ a' v', gwritesByte GD.gdG (AxLockAdeq.acq i_B k_acq) a' v' → a' = L)
  (Hval_acq : graphData GD (AxLockAdeq.acq i_B k_acq) = some [b1])
  (Hpol : wRel i_A k_rel ∈ Axpol.sPol GD (AxLockAdeq.acq i_B k_acq))
  (Hunclaimed : ∀ σ : AxirisG.obSt GF, wRel i_A k_rel ∉ ob_D σ)
  (Hhm : ∀ σ : AxirisG.obSt GF, get? (ob_hm σ) (wRel i_A k_rel) = some (Hh w_x vx))
  (Hacq_po : gacqPo GD.gdG (AxLockAdeq.acq i_B k_acq) r_x)
  (Hnw : gisW GD.gdG r_x = false)
  (Hrd : ∃ t v, greadsByte GD.gdG r_x x t v)
  (Hsn : ⊢ iprop(∀ w v, ⌜gwritesByte GD.gdG w x v⌝ -∗ ⌜gmoLt GD.gdG w r_x⌝ -∗
    ∃ H', ⌜w ∈ H'.map Prod.fst⌝ ∗ histSnap (GF := GF) γ x H'))
  (Hdisc : ∀ w vv, gwritesByte GD.gdG w x vv → WeakRvwmoGraph.gpo GD.gdG w r_x → w = w_x)
  (Hlobp_wx : Axpol.lobp GD w_x = (∅ : GSet Geid))
  (Hlobp_wrel : Axpol.lobp GD (wRel i_A k_rel) = ({w_x} : GSet Geid))
  (Hlobp_acq : Axpol.lobp GD (AxLockAdeq.acq i_B k_acq) = ({wRel i_A k_rel} : GSet Geid))
  (Hlobp_rx : Axpol.lobp GD r_x = ({AxLockAdeq.acq i_B k_acq} : GSet Geid))
  (Hspol_wx : Axpol.sPol GD w_x ⊆ (∅ : GSet Geid))
  (Hspol_wrel : Axpol.sPol GD (wRel i_A k_rel) ⊆ ({w_x} : GSet Geid))
  (Hspol_acq_wf : Axpol.sPol GD (AxLockAdeq.acq i_B k_acq) ⊆
    (({w_x} : GSet Geid) ∪ {wRel i_A k_rel}))
  (Hspol_rx : Axpol.sPol GD r_x ⊆
    ((({w_x} : GSet Geid) ∪ {wRel i_A k_rel}) ∪ {AxLockAdeq.acq i_B k_acq}))
  (Hgmo_perm : (L4 i_A i_B k_rel k_acq w_x r_x).Perm GD.gdG.gxGmo)

include Hcons Hwx Hsingle_wx Hgd_wx Hfence Hwb0 Hsingle_rel Hrf Hwb1 Hsingle_acq Hval_acq Hpol
  Hunclaimed Hhm Hacq_po Hnw Hrd Hsn Hdisc Hlobp_wx Hlobp_wrel Hlobp_acq Hlobp_rx Hspol_wx
  Hspol_wrel Hspol_acq_wf Hspol_rx Hgmo_perm

/-- 2.5 The four-way obligation, from the two fresh histories. -/
theorem lockSliceOrdEaTodo :
    ⊢ histAuth (GF := GF) γ x 1 [] -∗ histAuth γ L 1 [] -∗
      ordEaTodoL GD (AxLockAdeq.ea0 (GF := GF) γ L x GD i_A i_B k_rel k_acq w_x r_x vx)
        (na0 (GF := GF) x GD i_A i_B k_rel k_acq w_x r_x vx) (L4 i_A i_B k_rel k_acq w_x r_x) 0 := by
  iintro Hx HL
  iapply (ordEaTodoLCons GD _ _ _ 0 w_x (L40 i_A i_B k_rel k_acq w_x r_x)).2
  isplitl [Hx]
  · iapply AxLockAdeq.todoWx γ γc L x Hxl ob_D ob_hm mk_ob' Hmk_ob'_D Hmk_ob'_hm Hob_eq'
      GD i_A i_B k_rel k_acq w_x r_x vx Hcons Hwx Hsingle_wx Hgd_wx Hgmo_perm Hlobp_wx
      Hlobp_wrel Hlobp_acq Hlobp_rx $$ Hx
  iapply (ordEaTodoLCons GD _ _ _ 1 _ (L41 i_A i_B k_rel k_acq w_x r_x)).2
  isplitl [HL]
  · iapply AxLockAdeq.todoWrel γ γc L x Hxl ob_D ob_hm mk_ob' Hmk_ob'_D Hmk_ob'_hm Hob_eq'
      GD i_A i_B k_rel k_acq w_x r_x vx Hcons Hfence Hwb0 Hsingle_rel Hgmo_perm Hlobp_wx
      Hlobp_wrel Hlobp_acq Hlobp_rx $$ HL
  iapply (ordEaTodoLCons GD _ _ _ 2 _ (L42 i_A i_B k_rel k_acq w_x r_x)).2
  isplitl []
  · iapply AxLockAdeq.todoAcq γ γc L x Hxl ob_D ob_hm mk_ob' Hmk_ob'_D Hmk_ob'_hm Hob_eq'
      GD i_A i_B k_rel k_acq w_x r_x vx Hcons Hwb0 Hrf Hwb1 Hsingle_acq Hval_acq Hpol
      Hunclaimed Hhm Hgmo_perm Hlobp_wx Hlobp_wrel Hlobp_acq Hlobp_rx
  iapply (ordEaTodoLCons GD _ _ _ 3 _ (L43 i_A i_B k_rel k_acq w_x r_x)).2
  isplitl []
  · iapply AxLockAdeq.todoRx γ γc L x Hxl ob_D ob_hm mk_ob' Hmk_ob'_D Hmk_ob'_hm Hob_eq'
      GD i_A i_B k_rel k_acq w_x r_x vx Hcons Hwx Hacq_po Hnw Hrd Hsn Hdisc Hgmo_perm
      Hlobp_wx Hlobp_wrel Hlobp_acq Hlobp_rx
  · iapply AxLockAdeq.todoTail γ L x GD i_A i_B k_rel k_acq w_x r_x vx

/-- 2.7 THE PHASE-2 ADEQUACY RESULT. -/
theorem lockSliceAdequate :
    ⊢ histAuth (GF := GF) γ x 1 [] -∗ histAuth γ L 1 [] -∗ claimedAuth γc (∅ : GSet Geid) -∗
      |={⊤}[∅]▷=>^[(L4 i_A i_B k_rel k_acq w_x r_x).length]
        ∃ (σ : AxirisG.obSt GF),
          AxirisG.obStInterp GD σ (LawfulSet.ofList (L4 i_A i_B k_rel k_acq w_x r_x)) ∗
          [∗set] e0 ∈ (LawfulSet.ofList (L4 i_A i_B k_rel k_acq w_x r_x) : GSet Geid),
            AxWp.fromOption (fun P => P) iprop(emp)
              (get? (na0 (GF := GF) x GD i_A i_B k_rel k_acq w_x r_x vx) e0) := by
  iintro Hx HL Hc
  ihave Htodo := lockSliceOrdEaTodo γ γc L x Hxl ob_D ob_hm mk_ob' Hmk_ob'_D Hmk_ob'_hm Hob_eq'
    GD i_A i_B k_rel k_acq w_x r_x vx Hcons Hwx Hsingle_wx Hgd_wx Hfence Hwb0 Hsingle_rel Hrf
    Hwb1 Hsingle_acq Hval_acq Hpol Hunclaimed Hhm Hacq_po Hnw Hrd Hsn Hdisc Hlobp_wx Hlobp_wrel
    Hlobp_acq Hlobp_rx Hspol_wx Hspol_wrel Hspol_acq_wf Hspol_rx Hgmo_perm $$ Hx HL
  ihave Hob0 : AxirisG.obStInterp GD (mk_ob' ∅ ∅) ∅ $$ [Hc]
  · iapply (Hob_eq' GD (mk_ob' ∅ ∅) ∅).2
    rw [Hmk_ob'_D, Hmk_ob'_hm]
    iapply AxLockAdeq.obInit γ γc L x GD $$ Hc
  iapply adequacyOrdL GD Hcons (L4 i_A i_B k_rel k_acq w_x r_x) Hgmo_perm
    (axpolWfL4 GD i_A i_B k_rel k_acq w_x r_x Hlobp_wx Hlobp_wrel Hlobp_acq Hlobp_rx Hspol_wx
      Hspol_wrel Hspol_acq_wf Hspol_rx)
    _ _ (HdomEq0 GD i_A i_B k_rel k_acq w_x r_x x vx γ L)
    (Hdom0 GD i_A i_B k_rel k_acq w_x r_x x vx)
    (AxLockAdeq.HeaLob0 GD i_A i_B k_rel k_acq w_x r_x x vx γ L Hlobp_wx Hlobp_wrel Hlobp_acq
      Hlobp_rx)
    (mk_ob' ∅ ∅) $$ Htodo Hob0

/-- 2.8 THE FULLY REDUCED iProp-level FACT. -/
theorem lockSliceFinal :
    ⊢ histAuth (GF := GF) γ x 1 [] -∗ histAuth γ L 1 [] -∗ claimedAuth γc (∅ : GSet Geid) -∗
      |={⊤}[∅]▷=>^[4]
        ⌜grfAt GD.gdG x w_x r_x ∧ ∀ t v, greadsByte GD.gdG r_x x t v → v = vx⌝ := by
  have hadeq := lockSliceAdequate γ γc L x Hxl ob_D ob_hm mk_ob' Hmk_ob'_D Hmk_ob'_hm Hob_eq'
    GD i_A i_B k_rel k_acq w_x r_x vx Hcons Hwx Hsingle_wx Hgd_wx Hfence Hwb0 Hsingle_rel Hrf
    Hwb1 Hsingle_acq Hval_acq Hpol Hunclaimed Hhm Hacq_po Hnw Hrd Hsn Hdisc Hlobp_wx Hlobp_wrel
    Hlobp_acq Hlobp_rx Hspol_wx Hspol_wrel Hspol_acq_wf Hspol_rx Hgmo_perm
  have hlen : (L4 i_A i_B k_rel k_acq w_x r_x).length = 4 := rfl
  rw [hlen] at hadeq
  iintro Hx HL Hc
  ihave Hadeq := hadeq $$ Hx HL Hc
  iapply step_fupdN_wand $$ Hadeq
  iintro ⟨%σ, -, Hbag⟩
  iapply AxLockAdeq.bagRx GD i_A i_B k_rel k_acq w_x r_x x vx Hcons Hgmo_perm $$ Hbag

omit Hsn Hdisc in
/-- 2.10 The `Hsn`-free walk. -/
theorem lockSliceOrdEaTodo2 :
    ⊢ histAuth (GF := GF) γ x 1 [] -∗ histAuth γ L 1 [] -∗
      ordEaTodoL GD (AxLockAdeq.ea0 (GF := GF) γ L x GD i_A i_B k_rel k_acq w_x r_x vx)
        (na0 (GF := GF) x GD i_A i_B k_rel k_acq w_x r_x vx) (L4 i_A i_B k_rel k_acq w_x r_x) 0 := by
  iintro Hx HL
  iapply (ordEaTodoLCons GD _ _ _ 0 w_x (L40 i_A i_B k_rel k_acq w_x r_x)).2
  isplitl [Hx]
  · iapply AxLockAdeq.todoWx γ γc L x Hxl ob_D ob_hm mk_ob' Hmk_ob'_D Hmk_ob'_hm Hob_eq'
      GD i_A i_B k_rel k_acq w_x r_x vx Hcons Hwx Hsingle_wx Hgd_wx Hgmo_perm Hlobp_wx
      Hlobp_wrel Hlobp_acq Hlobp_rx $$ Hx
  iapply (ordEaTodoLCons GD _ _ _ 1 _ (L41 i_A i_B k_rel k_acq w_x r_x)).2
  isplitl [HL]
  · iapply AxLockAdeq.todoWrel γ γc L x Hxl ob_D ob_hm mk_ob' Hmk_ob'_D Hmk_ob'_hm Hob_eq'
      GD i_A i_B k_rel k_acq w_x r_x vx Hcons Hfence Hwb0 Hsingle_rel Hgmo_perm Hlobp_wx
      Hlobp_wrel Hlobp_acq Hlobp_rx $$ HL
  iapply (ordEaTodoLCons GD _ _ _ 2 _ (L42 i_A i_B k_rel k_acq w_x r_x)).2
  isplitl []
  · iapply AxLockAdeq.todoAcq γ γc L x Hxl ob_D ob_hm mk_ob' Hmk_ob'_D Hmk_ob'_hm Hob_eq'
      GD i_A i_B k_rel k_acq w_x r_x vx Hcons Hwb0 Hrf Hwb1 Hsingle_acq Hval_acq Hpol
      Hunclaimed Hhm Hgmo_perm Hlobp_wx Hlobp_wrel Hlobp_acq Hlobp_rx
  iapply (ordEaTodoLCons GD _ _ _ 3 _ (L43 i_A i_B k_rel k_acq w_x r_x)).2
  isplitl []
  · iapply AxLockAdeq.todoRx2 γ γc L x Hxl ob_D ob_hm mk_ob' Hmk_ob'_D Hmk_ob'_hm Hob_eq'
      GD i_A i_B k_rel k_acq w_x r_x vx Hcons Hwx Hsingle_rel Hsingle_acq Hacq_po Hnw Hrd
      Hgmo_perm Hlobp_wx Hlobp_wrel Hlobp_acq Hlobp_rx
  · iapply AxLockAdeq.todoTail γ L x GD i_A i_B k_rel k_acq w_x r_x vx

omit Hsn Hdisc in
theorem lockSliceAdequate2 :
    ⊢ histAuth (GF := GF) γ x 1 [] -∗ histAuth γ L 1 [] -∗ claimedAuth γc (∅ : GSet Geid) -∗
      |={⊤}[∅]▷=>^[(L4 i_A i_B k_rel k_acq w_x r_x).length]
        ∃ (σ : AxirisG.obSt GF),
          AxirisG.obStInterp GD σ (LawfulSet.ofList (L4 i_A i_B k_rel k_acq w_x r_x)) ∗
          [∗set] e0 ∈ (LawfulSet.ofList (L4 i_A i_B k_rel k_acq w_x r_x) : GSet Geid),
            AxWp.fromOption (fun P => P) iprop(emp)
              (get? (na0 (GF := GF) x GD i_A i_B k_rel k_acq w_x r_x vx) e0) := by
  iintro Hx HL Hc
  ihave Htodo := lockSliceOrdEaTodo2 γ γc L x Hxl ob_D ob_hm mk_ob' Hmk_ob'_D Hmk_ob'_hm Hob_eq'
    GD i_A i_B k_rel k_acq w_x r_x vx Hcons Hwx Hsingle_wx Hgd_wx Hfence Hwb0 Hsingle_rel Hrf
    Hwb1 Hsingle_acq Hval_acq Hpol Hunclaimed Hhm Hacq_po Hnw Hrd Hlobp_wx Hlobp_wrel
    Hlobp_acq Hlobp_rx Hspol_wx Hspol_wrel Hspol_acq_wf Hspol_rx Hgmo_perm $$ Hx HL
  ihave Hob0 : AxirisG.obStInterp GD (mk_ob' ∅ ∅) ∅ $$ [Hc]
  · iapply (Hob_eq' GD (mk_ob' ∅ ∅) ∅).2
    rw [Hmk_ob'_D, Hmk_ob'_hm]
    iapply AxLockAdeq.obInit γ γc L x GD $$ Hc
  iapply adequacyOrdL GD Hcons (L4 i_A i_B k_rel k_acq w_x r_x) Hgmo_perm
    (axpolWfL4 GD i_A i_B k_rel k_acq w_x r_x Hlobp_wx Hlobp_wrel Hlobp_acq Hlobp_rx Hspol_wx
      Hspol_wrel Hspol_acq_wf Hspol_rx)
    _ _ (HdomEq0 GD i_A i_B k_rel k_acq w_x r_x x vx γ L)
    (Hdom0 GD i_A i_B k_rel k_acq w_x r_x x vx)
    (AxLockAdeq.HeaLob0 GD i_A i_B k_rel k_acq w_x r_x x vx γ L Hlobp_wx Hlobp_wrel Hlobp_acq
      Hlobp_rx)
    (mk_ob' ∅ ∅) $$ Htodo Hob0

omit Hsn Hdisc in
theorem lockSliceFinal2 :
    ⊢ histAuth (GF := GF) γ x 1 [] -∗ histAuth γ L 1 [] -∗ claimedAuth γc (∅ : GSet Geid) -∗
      |={⊤}[∅]▷=>^[4]
        ⌜grfAt GD.gdG x w_x r_x ∧ ∀ t v, greadsByte GD.gdG r_x x t v → v = vx⌝ := by
  have hadeq := lockSliceAdequate2 γ γc L x Hxl ob_D ob_hm mk_ob' Hmk_ob'_D Hmk_ob'_hm Hob_eq'
    GD i_A i_B k_rel k_acq w_x r_x vx Hcons Hwx Hsingle_wx Hgd_wx Hfence Hwb0 Hsingle_rel Hrf
    Hwb1 Hsingle_acq Hval_acq Hpol Hunclaimed Hhm Hacq_po Hnw Hrd Hlobp_wx Hlobp_wrel
    Hlobp_acq Hlobp_rx Hspol_wx Hspol_wrel Hspol_acq_wf Hspol_rx Hgmo_perm
  have hlen : (L4 i_A i_B k_rel k_acq w_x r_x).length = 4 := rfl
  rw [hlen] at hadeq
  iintro Hx HL Hc
  ihave Hadeq := hadeq $$ Hx HL Hc
  iapply step_fupdN_wand $$ Hadeq
  iintro ⟨%σ, -, Hbag⟩
  iapply AxLockAdeq.bagRx GD i_A i_B k_rel k_acq w_x r_x x vx Hcons Hgmo_perm $$ Hbag

end capstone

end Weak
