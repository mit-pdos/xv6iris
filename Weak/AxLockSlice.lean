/-
Weak: **THE TWO-HART LB/AxSL LOCK-HANDOFF CAPSTONE** over abstract rows (no Sail): hart A runs
[owned write `w_x` to `x`; `fence rw,w`; release store `w_rel` to `L = 0`]; hart B runs the
SUCCESSFUL iteration of its acquire spin loop (an `.aq` RMW `acq` on `L` reading 0 from `w_rel`)
and then the owned read `r_x` of `x`.

Rocq: `iris/AxLockSlice.v` @ xxvzwolszwmp.

## The Rocq header, in substance

The capstone ties together `AxLockWp.wpReleaseStore` (A's release), `AxLockWp2.wpAmoswapAqLob`
(B's acquire, depositing the MIXED annotation along `na`/`lob`) and `AxLockWp2.flowEqLockReadLob`
(B's read, claiming the token back out via `lob` and concluding the graph-value fact).
Graph glue: `Hfence : gppoCat GD w_x w_rel` gives `gobCat GD w_x w_rel`, `Hrf : grfe … w_rel acq`
gives `gobCat GD w_rel acq` (one `gobCatStep` each, as `AxLockGraph.lockHandoffGraph`).  The gate
at `bnez` (via `AxGateAdeq2.annotPureFrame`): the mixed slot is `annotPure` w.r.t. "`w_rel` writes
0 to `L`" and extracting that fact leaves the slot intact (`gateAcqPureV0`/`gateAcqFrames`).  The
spin loop's failed iterations are NAMED, not modelled (`spinFailIterOk`; `Hspin` unused by the
proof).  The conclusion is the conjunction of the three `wpEvStep`/`flowEqDyn` judgements.

RESIDUAL hypotheses (as Rocq; all carried explicitly, none discharged here): `H_L`/`H_L'` (two
independent views of `L`'s history — adequacy premise), `Hnalloc_rel`/`Hnalloc_acq` (adequacy
premise, verbatim from the WP rules), the `obSt` bridge `ob_D`/`mk_ob`/`Hmk_ob`/`Hob_eq` (and the
primed `ob_hm`/`mk_ob'`/… for §4 — architecture wiring, not tied to `skelAxirisG`), `Hpol`/
`Hunclaimed` (adequacy), `Hfence` (hardware model: abstract ppo edge), `Hsn` (coverage-snapshot
wand), `Hhandoff` (the thin wand `flowIn ⊢ tokTie … Hh {[acq := 1]}` — an architecture gap for the
UNPRIMED `lockSliceHandoff` only; PROVEN for `lockSliceHandoff'` as `handoffWand'`, because the
primed acquire deposits the same `Hh` with no existential), `Hspin` (named, unused).

**Fetches / Stage C / Q8.** Nothing here mentions fetches: the file only calls the three WP-rule
lemmas generically, so the Q8 pin in the WP step clause is threaded (if at all) inside them.

## Deviations from Rocq

1. NAMES: camelCase (map below).  No name of this file is in `notes/weak-port-dupnames.json`.
2. SECTION VARIABLES (as `AxLockWp2` deviation 4): Rocq's `Context (γ γc) (L x)` and the bridge
   `(ob_D mk_ob Hmk_ob Hob_eq)` / `(ob_hm mk_ob' Hmk_ob'_D Hmk_ob'_hm Hob_eq')` become explicit
   leading arguments, in Rocq's order, of exactly the declarations whose statements (or
   `Proof using All` proofs) use them: `spinFailIterOk L`, `gateAcqPureV0/gateAcqFrames γ L x`,
   `RAcq γ L x`, `handoffWand' γ L x`; the two capstones take all of them (`Proof using All`;
   `lockSliceHandoff` takes only the unprimed bridge — the primed `Context` comes after it in Rocq).
3. VOCABULARY (as `AxLockWp2` deviation 2): `gd_g GD` ↦ `GD.gdG`; `<[e := R]> na` ↦
   `insert na e R`; `H.*1` ↦ `H.map Prod.fst`; `last H` ↦ `H.getLast?`; `gpo` ↦
   `WeakRvwmoGraph.gpo`; `WeakLitmus.b0/b1` ↦ `b0`/`b1`; `S k` ↦ `k + 1`; `Z` ↦ `Int`;
   `bv 8` ↦ `BitVec 8`; `gmap geid (list hent)` ↦ `GMapF Geid (List Hent)`, `hm !! e` ↦ `get? hm e`;
   `chain_with` ↦ `chainWith`.
4. `invGS_gen HasNoLc Σ` ↦ `[InvGS_gen hlc GF]` for any `hlc` (as `AxWp` deviation 6); `axlogG Σ
   hent` ↦ `[AxlogG GF Hent]`, `ax_lockG Σ` ↦ `[AxLockG GF]`.
5. STATEMENT SHAPES (as `AxWp` deviation 7): `A -∗ B -∗ …` ↦ `⊢ A -∗ B -∗ …`; the two-conjunct
   wand-free statements `A ⊢ B` stay `⊢`; pure premises `→`/binders.

**Rocq → Lean name map.**  `spin_fail_iter_ok` `spinFailIterOk`, `gate_acq_pure_v0`
`gateAcqPureV0`, `gate_acq_frames` `gateAcqFrames`, `lock_slice_handoff` `lockSliceHandoff`,
`R_acq` `RAcq`, `handoff_wand'` `handoffWand'`, `lock_slice_handoff'` `lockSliceHandoff'`.

**Not ported:** the §5 `Print Assumptions` audit (the lint's axiom check covers it).
-/
import Weak.AxLockWp
import Weak.AxLockWp2
import Weak.AxGateAdeq2

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp

/-! # 1. The spin loop's failed iterations — named, unused -/

/-- Iteration `k` of hart `i` reads a NONZERO value from `L` and deposits `emp` at its own slot
(the shape a failing retry's — as yet unbuilt — WP rule would have). -/
def spinFailIterOk {GF : BundledGFunctors} [AxirisG GF] (L : Int) (GD : Gdexec) (i : Agent)
    (k : Nat) : Prop :=
  (∃ t v, greadsByte GD.gdG (i, k) L t v ∧ v ≠ b0) ∧
  (⊢ ∀ na : Mea GF, naAtProgress GD i k na ∗ AxirisG.annotInterp na ==∗
      AxirisG.annotInterp (insert na (i, k) (iprop(emp) : IProp GF)))

/-! # 2. The gate at `bnez`, via `AxGateAdeq2` -/

section gate
variable {GF : BundledGFunctors} [AxlogG GF Hent]

theorem gateAcqPureV0 (γ : GName) (L x : Int) (GD : Gdexec) (w_rel acq : Geid) :
    annotPure
      (iprop(⌜gwritesByte GD.gdG w_rel L b0⌝ ∗
        (∃ H, tokTie GD γ x H {[acq := (1 : Qp)]})) : IProp GF)
      (gwritesByte GD.gdG w_rel L b0) := by
  unfold annotPure
  iintro ⟨%h, -⟩
  ipureintro
  exact h

theorem gateAcqFrames (γ : GName) (L x : Int) (GD : Gdexec) (w_rel acq : Geid) :
    (iprop(⌜gwritesByte GD.gdG w_rel L b0⌝ ∗
        (∃ H, tokTie GD γ x H {[acq := (1 : Qp)]})) : IProp GF) ⊢
      iprop(⌜gwritesByte GD.gdG w_rel L b0⌝ ∗
        (⌜gwritesByte GD.gdG w_rel L b0⌝ ∗
          (∃ H, tokTie GD γ x H {[acq := (1 : Qp)]}))) :=
  annotPureFrame _ _ (gateAcqPureV0 γ L x GD w_rel acq)

end gate

/-! # 3. The capstone `lockSliceHandoff` -/

section slice

variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [axG : AxirisG GF] [Axpol]
  [AxlogG GF Hent] [AxLockG GF]

theorem lockSliceHandoff (γ γc : GName) (L x : Int)
    (ob_D : AxirisG.obSt GF → GSet Geid) (mk_ob : GSet Geid → AxirisG.obSt GF)
    (Hmk_ob : ∀ D, ob_D (mk_ob D) = D)
    (Hob_eq : ∀ (GD : Gdexec) (σ : AxirisG.obSt GF) (s : GSet Geid),
      AxirisG.obStInterp GD σ s ⊣⊢ protInvLock L x γ γc GD s (ob_D σ))
    (GD : Gdexec) (i_A i_B : Agent) (k_rel k_acq : Nat)
    (w_x r_x : Geid) (vx : BitVec 8)
    (Hh H_L H_L' : List Hent) (ls'_A ls'_B : AxirisG.logTsT GF)
    (s_ob0 : GSet Geid) (flowIn : Mea GF) (Ψ_A Ψ_B : Unit → IProp GF)
    -- graph hypotheses: "a consistent graph"
    (Hcons : rvwmoCatConsistent GD)
    (_Hwx : gwritesByte GD.gdG w_x x vx)
    (Hfence : gppoCat GD w_x (i_A, k_rel))
    (Hwb0 : gwritesByte GD.gdG (i_A, k_rel) L b0)
    (Hsingle_rel : ∀ a' v', gwritesByte GD.gdG (i_A, k_rel) a' v' → a' = L)
    (Hval_rel : graphData GD (i_A, k_rel) = some [b0])
    (Hrf : grfe GD.gdG (i_A, k_rel) (i_B, k_acq))
    (Hwb1 : gwritesByte GD.gdG (i_B, k_acq) L b1)
    (Hsingle_acq : ∀ a' v', gwritesByte GD.gdG (i_B, k_acq) a' v' → a' = L)
    (Hval_acq : graphData GD (i_B, k_acq) = some [b1])
    (Hpol : (i_A, k_rel) ∈ Axpol.sPol GD (i_B, k_acq))
    (Hunclaimed : ∀ σ : AxirisG.obSt GF, (i_A, k_rel) ∉ ob_D σ)
    (Hacq_po : gacqPo GD.gdG (i_B, k_acq) r_x)
    (Hnw : gisW GD.gdG r_x = false)
    (Hrd : ∃ t v, greadsByte GD.gdG r_x x t v)
    (Hwr : ∀ p, p ∈ Hh → gwritesByte GD.gdG p.1 x p.2)
    (Hch : chainWith (gmoLt GD.gdG) (Hh.map Prod.fst))
    (Hown : ∀ w vv, gwritesByte GD.gdG w x vv → WeakRvwmoGraph.gpo GD.gdG w r_x →
      w ∈ Hh.map Prod.fst)
    (Hlast : Hh.getLast? = some (w_x, vx))
    (_Hspin : ∀ k', k' < k_acq → spinFailIterOk (GF := GF) L GD i_B k')
    -- ghost/WP capability hypotheses (RESIDUAL, see header)
    (Hnalloc_rel : ⊢ ∀ na : Mea GF, naAtProgress GD i_A k_rel na ∗ AxirisG.annotInterp na ==∗
      AxirisG.annotInterp (insert na (i_A, k_rel)
        iprop(⌜gwritesByte GD.gdG (i_A, k_rel) L b0⌝)))
    (Hnalloc_acq : ⊢ ∀ na : Mea GF, naAtProgress GD i_B k_acq na ∗ AxirisG.annotInterp na ==∗
      AxirisG.annotInterp (insert na (i_B, k_acq)
        iprop(⌜gwritesByte GD.gdG (i_A, k_rel) L b0⌝ ∗
          (∃ H, tokTie GD γ x H {[(i_B, k_acq) := (1 : Qp)]})))) :
    ⊢ histAuth γ L 1 H_L -∗
      tokTie GD γ x Hh {[w_x := (1 : Qp)]} -∗
      AxirisG.localInterp GD i_A (k_rel + 1) ls'_A -∗
      Ψ_A () -∗
      histAuth γ L 1 H_L' -∗
      AxirisG.localInterp GD i_B (k_acq + 1) ls'_B -∗
      Ψ_B () -∗
      -- the "thin wand" (RESIDUAL: OTHER, see header)
      (([∗map] Rin ∈ flowIn, Rin) -∗ tokTie GD γ x Hh {[(i_B, k_acq) := (1 : Qp)]}) -∗
      (∀ w vv, ⌜gwritesByte GD.gdG w x vv⌝ -∗ ⌜gmoLt GD.gdG w r_x⌝ -∗
        ∃ H', ⌜w ∈ H'.map Prod.fst⌝ ∗ histSnap γ x H') -∗
      (wpEvStep GD i_A k_rel (fun _ : Unit => True)
          (fun _ : Unit => graphData GD (i_A, k_rel) = some [b0]) (fun _ => k_rel + 1) Ψ_A ∗
        wpEvStep GD i_B k_acq (fun _ : Unit => True)
          (fun _ : Unit => graphData GD (i_B, k_acq) = some [b1]) (fun _ => k_acq + 1) Ψ_B ∗
        flowEqDyn GD r_x s_ob0 flowIn
          iprop(⌜grfAt GD.gdG x w_x r_x ∧ ∀ t v, greadsByte GD.gdG r_x x t v → v = vx⌝)) := by
  have Hgob1 : gobCat GD w_x (i_A, k_rel) := gobCatStep GD _ _ (Or.inl Hfence)
  have Hgob2 : gobCat GD (i_A, k_rel) (i_B, k_acq) :=
    gobCatStep GD _ _ (Or.inr (Or.inr (Or.inl Hrf)))
  iintro HaL Htie HlocA HPsiA HaL' HlocB HPsiB Hhandoff Hsn
  isplitl [HaL Htie HlocA HPsiA]
  · ihave Hc := wpReleaseStore γ γc L x ob_D mk_ob Hmk_ob Hob_eq GD i_A k_rel ls'_A w_x Hh H_L Ψ_A
      Hcons Hwb0 Hsingle_rel Hgob1 Hval_rel Hnalloc_rel $$ HaL Htie HlocA HPsiA
    iexact Hc
  isplitl [HaL' HlocB HPsiB]
  · ihave Hc := wpAmoswapAqLob γ γc L x ob_D mk_ob Hmk_ob Hob_eq GD i_B k_acq ls'_B (i_A, k_rel)
      H_L' Ψ_B Hcons Hpol Hunclaimed Hwb0 Hwb1 Hsingle_acq Hgob2 Hval_acq Hnalloc_acq
      $$ HaL' HlocB HPsiB
    iexact Hc
  · ihave Hc := flowEqLockReadLob γ γc L x ob_D mk_ob Hmk_ob Hob_eq GD (i_B, k_acq) r_x Hh w_x vx
      s_ob0 flowIn Hcons Hnw Hwr Hch Hown Hlast Hacq_po Hrd $$ Hhandoff Hsn
    iexact Hc

/-! # 4. The primed capstone `lockSliceHandoff'` — `Hhandoff` PROVEN -/

/-- The mixed slot `wpAmoswapAqLob'` deposits, made concrete (no `∃ H`). -/
def RAcq (γ : GName) (L x : Int) (GD : Gdexec) (w_rel acq : Geid) (Hh : List Hent) :
    IProp GF :=
  iprop(⌜gwritesByte GD.gdG w_rel L b0⌝ ∗ tokTie GD γ x Hh {[acq := (1 : Qp)]})

/-- THE FIX: with `flowIn := insert ∅ acq (RAcq … Hh)` the handoff wand is provable outright. -/
theorem handoffWand' (γ : GName) (L x : Int) (GD : Gdexec) (w_rel acq : Geid)
    (Hh : List Hent) :
    ([∗map] Rin ∈ insert (∅ : Mea GF) acq (RAcq γ L x GD w_rel acq Hh), Rin) ⊢
      tokTie GD γ x Hh {[acq := (1 : Qp)]} := by
  have hnone : get? (∅ : Mea GF) acq = none := lookupEmpty
  iintro H
  icases (BigSepM.bigSepM_insert (Φ := fun (_ : Geid) (R : IProp GF) => R) hnone).1 $$ H
    with ⟨HR, -⟩
  iunfold RAcq at HR
  icases HR with ⟨-, Ht⟩
  iexact Ht

theorem lockSliceHandoff' (γ γc : GName) (L x : Int)
    (ob_D : AxirisG.obSt GF → GSet Geid) (mk_ob : GSet Geid → AxirisG.obSt GF)
    (Hmk_ob : ∀ D, ob_D (mk_ob D) = D)
    (Hob_eq : ∀ (GD : Gdexec) (σ : AxirisG.obSt GF) (s : GSet Geid),
      AxirisG.obStInterp GD σ s ⊣⊢ protInvLock L x γ γc GD s (ob_D σ))
    (ob_hm : AxirisG.obSt GF → GMapF Geid (List Hent))
    (mk_ob' : GSet Geid → GMapF Geid (List Hent) → AxirisG.obSt GF)
    (Hmk_ob'_D : ∀ D hm, ob_D (mk_ob' D hm) = D)
    (Hmk_ob'_hm : ∀ D hm, ob_hm (mk_ob' D hm) = hm)
    (Hob_eq' : ∀ (GD : Gdexec) (σ : AxirisG.obSt GF) (s : GSet Geid),
      AxirisG.obStInterp GD σ s ⊣⊢ protInvLock' L x γ γc GD s (ob_D σ) (ob_hm σ))
    (GD : Gdexec) (i_A i_B : Agent) (k_rel k_acq : Nat)
    (w_x r_x : Geid) (vx : BitVec 8)
    (Hh H_L H_L' : List Hent) (ls'_A ls'_B : AxirisG.logTsT GF)
    (s_ob0 : GSet Geid) (Ψ_A Ψ_B : Unit → IProp GF)
    -- graph hypotheses: "a consistent graph"
    (Hcons : rvwmoCatConsistent GD)
    (_Hwx : gwritesByte GD.gdG w_x x vx)
    (Hfence : gppoCat GD w_x (i_A, k_rel))
    (Hwb0 : gwritesByte GD.gdG (i_A, k_rel) L b0)
    (Hsingle_rel : ∀ a' v', gwritesByte GD.gdG (i_A, k_rel) a' v' → a' = L)
    (Hval_rel : graphData GD (i_A, k_rel) = some [b0])
    (Hrf : grfe GD.gdG (i_A, k_rel) (i_B, k_acq))
    (Hwb1 : gwritesByte GD.gdG (i_B, k_acq) L b1)
    (Hsingle_acq : ∀ a' v', gwritesByte GD.gdG (i_B, k_acq) a' v' → a' = L)
    (Hval_acq : graphData GD (i_B, k_acq) = some [b1])
    (Hpol : (i_A, k_rel) ∈ Axpol.sPol GD (i_B, k_acq))
    (Hunclaimed : ∀ σ : AxirisG.obSt GF, (i_A, k_rel) ∉ ob_D σ)
    (Hhm : ∀ σ : AxirisG.obSt GF, get? (ob_hm σ) (i_A, k_rel) = some Hh)
    (Hacq_po : gacqPo GD.gdG (i_B, k_acq) r_x)
    (Hnw : gisW GD.gdG r_x = false)
    (Hrd : ∃ t v, greadsByte GD.gdG r_x x t v)
    (Hwr : ∀ p, p ∈ Hh → gwritesByte GD.gdG p.1 x p.2)
    (Hch : chainWith (gmoLt GD.gdG) (Hh.map Prod.fst))
    (Hown : ∀ w vv, gwritesByte GD.gdG w x vv → WeakRvwmoGraph.gpo GD.gdG w r_x →
      w ∈ Hh.map Prod.fst)
    (Hlast : Hh.getLast? = some (w_x, vx))
    (_Hspin : ∀ k', k' < k_acq → spinFailIterOk (GF := GF) L GD i_B k')
    -- ghost/WP capability hypotheses (RESIDUAL, see header)
    (Hnalloc_rel : ⊢ ∀ na : Mea GF, naAtProgress GD i_A k_rel na ∗ AxirisG.annotInterp na ==∗
      AxirisG.annotInterp (insert na (i_A, k_rel)
        iprop(⌜gwritesByte GD.gdG (i_A, k_rel) L b0⌝)))
    (Hnalloc_acq : ⊢ ∀ na : Mea GF, naAtProgress GD i_B k_acq na ∗ AxirisG.annotInterp na ==∗
      AxirisG.annotInterp (insert na (i_B, k_acq)
        (RAcq γ L x GD (i_A, k_rel) (i_B, k_acq) Hh))) :
    ⊢ histAuth γ L 1 H_L -∗
      tokTie GD γ x Hh {[w_x := (1 : Qp)]} -∗
      AxirisG.localInterp GD i_A (k_rel + 1) ls'_A -∗
      Ψ_A () -∗
      histAuth γ L 1 H_L' -∗
      AxirisG.localInterp GD i_B (k_acq + 1) ls'_B -∗
      Ψ_B () -∗
      -- the coverage-snapshot wand (RESIDUAL, see header)
      (∀ w vv, ⌜gwritesByte GD.gdG w x vv⌝ -∗ ⌜gmoLt GD.gdG w r_x⌝ -∗
        ∃ H', ⌜w ∈ H'.map Prod.fst⌝ ∗ histSnap γ x H') -∗
      (wpEvStep GD i_A k_rel (fun _ : Unit => True)
          (fun _ : Unit => graphData GD (i_A, k_rel) = some [b0]) (fun _ => k_rel + 1) Ψ_A ∗
        wpEvStep GD i_B k_acq (fun _ : Unit => True)
          (fun _ : Unit => graphData GD (i_B, k_acq) = some [b1]) (fun _ => k_acq + 1) Ψ_B ∗
        flowEqDyn GD r_x s_ob0
          (insert (∅ : Mea GF) (i_B, k_acq) (RAcq γ L x GD (i_A, k_rel) (i_B, k_acq) Hh))
          iprop(⌜grfAt GD.gdG x w_x r_x ∧ ∀ t v, greadsByte GD.gdG r_x x t v → v = vx⌝)) := by
  have Hgob1 : gobCat GD w_x (i_A, k_rel) := gobCatStep GD _ _ (Or.inl Hfence)
  have Hgob2 : gobCat GD (i_A, k_rel) (i_B, k_acq) :=
    gobCatStep GD _ _ (Or.inr (Or.inr (Or.inl Hrf)))
  have Hne : Hh ≠ [] := by
    intro Heq
    rw [Heq] at Hlast
    cases Hlast
  iintro HaL Htie HlocA HPsiA HaL' HlocB HPsiB Hsn
  isplitl [HaL Htie HlocA HPsiA]
  · ihave Hc := wpReleaseStore γ γc L x ob_D mk_ob Hmk_ob Hob_eq GD i_A k_rel ls'_A w_x Hh H_L Ψ_A
      Hcons Hwb0 Hsingle_rel Hgob1 Hval_rel Hnalloc_rel $$ HaL Htie HlocA HPsiA
    iexact Hc
  isplitl [HaL' HlocB HPsiB]
  · ihave Hc := wpAmoswapAqLob' γ γc L x ob_D ob_hm mk_ob' Hmk_ob'_D Hmk_ob'_hm Hob_eq' GD i_B k_acq
      ls'_B (i_A, k_rel) Hh H_L' Ψ_B Hcons Hpol Hunclaimed Hhm Hwb0 Hwb1 Hsingle_acq Hgob2
      Hval_acq Hne Hnalloc_acq $$ HaL' HlocB HPsiB
    iexact Hc
  · have Hhandoff : ⊢ ([∗map] Rin ∈ insert (∅ : Mea GF) (i_B, k_acq)
        (RAcq γ L x GD (i_A, k_rel) (i_B, k_acq) Hh), Rin) -∗
          tokTie GD γ x Hh {[(i_B, k_acq) := (1 : Qp)]} :=
      wand_intro (emp_sep.1.trans (handoffWand' γ L x GD (i_A, k_rel) (i_B, k_acq) Hh))
    ihave Hhandoff' := Hhandoff
    ihave Hc := flowEqLockReadLob γ γc L x ob_D mk_ob Hmk_ob Hob_eq GD (i_B, k_acq) r_x Hh w_x vx
      s_ob0 (insert (∅ : Mea GF) (i_B, k_acq) (RAcq γ L x GD (i_A, k_rel) (i_B, k_acq) Hh))
      Hcons Hnw Hwr Hch Hown Hlast Hacq_po Hrd $$ Hhandoff' Hsn
    iexact Hc

end slice

end Weak
