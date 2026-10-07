/-
Weak: **THE LOCK SLICE'S STEP RULES AT `wpd`** (AxSL tier, LB/AxSL lock slice): the generic
write-step rule `wpdWriteStepAll`/`wpdWriteStepAllWand`, the skip-step rule
`wpdSkipStepOfLocal`, and the lock's two write rules restated under the `wpd` prefix
(`wpdReleaseStore`, `wpdAmoswapAqLob`) by direct reuse of `AxLockWp`/`AxLockWp2`.

Rocq: `iris/AxLockWpD.v` @ xxvzwolszwmp.

## The Rocq header, in substance

HEADLINE FINDING: none of `wpReleaseStore` / `wpAmoswapAqLob` needs re-proving for `wpd`.
`wpdMPreStepDef`'s clauses (b) (every non-read program step) and (c) (the PLIC wire) are
`wpPreStepDef`'s verbatim, and the lock rules conclude a bare `wpEvStep`/`wpSkipStep` fact with
`Ψ` fully abstract — neither `wp` nor `wpd` appears.  So the `wpd*` lemmas below are the
originals applied (machine-checking "no premise changed").  THE RMW READ HALF: `wpd`'s clause
(a) ELSE branch is `wp`'s (already pinned), so no rule is built for it; the ordinary read
(clause (a) TRUE branch, now pinned) is `AxWpD`'s `wpdReadStepAllWand`, used under its own name.
Items: (1) `wpdWriteStepAll`/`wpdWriteStepAllWand`, the write-side analogue of
`AxReadAll.wpReadAll` (witness type `Unit`, so no angelic choice); (2) `wpdAmoswapAqLob`;
(3) `wpdReleaseStore`; (4) `wpdSkipStepOfLocal`, net new, closing `wpSkipStep` from a
`localInterp` witness (later introduced by `BI.later_intro`, not `inext`); (5) the plain `ld`
rule is `wpdReadStepAllWand`.  Clause (d) is never touched.

**Fetches.** Nothing here depends on instruction fetches being graph read events: the file
speaks of `wpEvStep`'s write shape, `wpSkipStep`, and the lock's write events (`gwritesByte`
over graph labels; `Lbl` has no fetch constructor).

## Deviations from Rocq

1. NAMES: camelCase (map below); none is duplicated.
2. SECTION CONTEXT: `invGS_gen HasNoLc Σ` ↦ `[InvGS_gen hlc GF]` for any `hlc` (as `AxWp`
   deviation 6); `axlogG Σ hent` ↦ `[AxlogG GF Hent]`, `ax_lockG Σ` ↦ `[AxLockG GF]`.  §3's
   section variables `γ γc L x ob_D mk_ob Hmk_ob Hob_eq` are explicit leading arguments, in that
   order (as `AxLockWp` deviation 2).
3. VOCABULARY (as `AxLockWp` deviation 3): `S k` ↦ `k + 1`; `gd_g GD` ↦ `GD.gdG`; `tt` ↦ `()`;
   `{[(i,k) := R]} ∪ na_unused ∪ na` ↦ `PartialMap.union (PartialMap.union {[(i, k) := R]}
   naUnused) na`; `bv 8` ↦ `BitVec 8`; `WeakLitmus.b0/b1` ↦ `b0`/`b1`; `Z` ↦ `Int`.
4. STATEMENT SHAPES (as `AxWp` deviation 7): `A -∗ B -∗ C` ↦ `⊢ A -∗ B -∗ C`; `P ⊢ Q` stays;
   pure and `⊢`-closed premises are `→`.

**Rocq → Lean name map.**  `wpd_write_step_all` `wpdWriteStepAll`, `wpd_write_step_all_wand`
`wpdWriteStepAllWand`, `wpd_skip_step_of_local` `wpdSkipStepOfLocal`, `wpd_release_store`
`wpdReleaseStore`, `wpd_amoswap_aq_lob` `wpdAmoswapAqLob`.

**Not ported:** the `Print Assumptions` audits (the lint's axiom check covers them).
-/
import Weak.AxWpD
import Weak.AxLockWp
import Weak.AxLockWp2

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp

/-! # 1. `wpdWriteStepAll` — the generic write-step rule -/

section wpdWriteAll

variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]

/-- THE GENERIC WRITE-STEP RULE: the write-side analogue of `AxReadAll.wpReadAll`. -/
theorem wpdWriteStepAll (GD : Gdexec) (i : Agent) (k : Nat) (data : List (BitVec 8)) (k' : Nat)
    (Ψ : Unit → IProp GF)
    (Hflow : ⊢ ∀ na : Mea GF, naAtProgress GD i k na ∗ AxirisG.annotInterp na -∗ |==> ▷ |==>
       ∃ (R : IProp GF) (naUsed naUnused : Mea GF) (ls' : AxirisG.logTsT GF),
         naSplittingWf (Axpol.lobp GD (i, k)) na naUsed naUnused ∗
         flowEqDyn GD (i, k) (Axpol.sPol GD (i, k)) naUsed
           iprop(R ∗ ⌜graphData GD (i, k) = some data⌝) ∗
         AxirisG.annotInterp (PartialMap.union (PartialMap.union {[(i, k) := R]} naUnused) na) ∗
         AxirisG.localInterp GD i k' ls')
    (Hcont : ⊢ Ψ ()) :
    ⊢ wpEvStep GD i k (fun _ : Unit => True) (fun _ : Unit => graphData GD (i, k) = some data)
        (fun _ => k') Ψ := by
  unfold wpEvStep
  iintro %na Hpg
  ihave Hf := Hflow
  imod Hf $$ %na Hpg with Hf1
  imodintro
  inext
  imod Hf1 with ⟨%R, %nu, %nuu, %ls', Hsplit, Hfe, Hna, Hloc⟩
  imodintro
  iexists (), R, nu, nuu, ls'
  isplitr
  · ipureintro
    trivial
  iframe Hsplit Hfe Hna Hloc
  ihave Hc := Hcont
  iexact Hc

/-- The wand-form twin: `Hcont` carried as a resource. -/
theorem wpdWriteStepAllWand (GD : Gdexec) (i : Agent) (k : Nat) (data : List (BitVec 8))
    (k' : Nat) (Ψ : Unit → IProp GF)
    (Hflow : ⊢ ∀ na : Mea GF, naAtProgress GD i k na ∗ AxirisG.annotInterp na -∗ |==> ▷ |==>
       ∃ (R : IProp GF) (naUsed naUnused : Mea GF) (ls' : AxirisG.logTsT GF),
         naSplittingWf (Axpol.lobp GD (i, k)) na naUsed naUnused ∗
         flowEqDyn GD (i, k) (Axpol.sPol GD (i, k)) naUsed
           iprop(R ∗ ⌜graphData GD (i, k) = some data⌝) ∗
         AxirisG.annotInterp (PartialMap.union (PartialMap.union {[(i, k) := R]} naUnused) na) ∗
         AxirisG.localInterp GD i k' ls') :
    Ψ () ⊢ wpEvStep GD i k (fun _ : Unit => True) (fun _ : Unit => graphData GD (i, k) = some data)
        (fun _ => k') Ψ := by
  unfold wpEvStep
  iintro Hcont %na Hpg
  ihave Hf := Hflow
  imod Hf $$ %na Hpg with Hf1
  imodintro
  inext
  imod Hf1 with ⟨%R, %nu, %nuu, %ls', Hsplit, Hfe, Hna, Hloc⟩
  imodintro
  iexists (), R, nu, nuu, ls'
  isplitr
  · ipureintro
    trivial
  iframe Hsplit Hfe Hna Hloc Hcont

end wpdWriteAll

/-! # 2. `wpdSkipStepOfLocal` — the fence/skip-step rule -/

section wpdSkipStep

variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF]

/-- `wpSkipStep` closes from a `localInterp` witness and `Ψ`. -/
theorem wpdSkipStepOfLocal (GD : Gdexec) (i : Agent) (k' : Nat) (ls' : AxirisG.logTsT GF)
    (Ψ : IProp GF) :
    ⊢ AxirisG.localInterp GD i k' ls' -∗ Ψ -∗ wpSkipStep GD i k' Ψ := by
  unfold wpSkipStep
  iintro Hloc HΨ %na Hna
  imodintro
  iapply BI.later_intro
  imodintro
  iexists ls'
  iframe Hna Hloc HΨ

end wpdSkipStep

/-! # 3. `wpdReleaseStore` and `wpdAmoswapAqLob` — direct reuse of the `wp` originals -/

section lockWpD

variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]
  [AxlogG GF Hent] [AxLockG GF]

/-- The release event's write step, ported (`AxLockWp.wpReleaseStore`). -/
theorem wpdReleaseStore (γ γc : GName) (L x : Int)
    (ob_D : AxirisG.obSt GF → GSet Geid) (mk_ob : GSet Geid → AxirisG.obSt GF)
    (Hmk_ob : ∀ D, ob_D (mk_ob D) = D)
    (Hob_eq : ∀ (GD : Gdexec) (σ : AxirisG.obSt GF) (s : GSet Geid),
      AxirisG.obStInterp GD σ s ⊣⊢ protInvLock L x γ γc GD s (ob_D σ))
    (GD : Gdexec) (i : Agent) (k : Nat) (ls' : AxirisG.logTsT GF)
    (e_last : Geid) (Hh H_L : List Hent) (Ψ : Unit → IProp GF)
    (Hcons : rvwmoCatConsistent GD)
    (Hwb : gwritesByte GD.gdG (i, k) L b0)
    (Hsingle : ∀ a' v', gwritesByte GD.gdG (i, k) a' v' → a' = L)
    (Hgob : gobCat GD e_last (i, k))
    (Hval : graphData GD (i, k) = some [b0])
    (Hnalloc : ⊢ ∀ na : Mea GF, naAtProgress GD i k na ∗ AxirisG.annotInterp na ==∗
       AxirisG.annotInterp (insert na (i, k) iprop(⌜gwritesByte GD.gdG (i, k) L b0⌝))) :
    ⊢ histAuth γ L 1 H_L -∗
      tokTie GD γ x Hh {[e_last := (1 : Qp)]} -∗
      AxirisG.localInterp GD i (k + 1) ls' -∗
      Ψ () -∗
      wpEvStep GD i k (fun _ : Unit => True) (fun _ : Unit => graphData GD (i, k) = some [b0])
        (fun _ => k + 1) Ψ :=
  wpReleaseStore γ γc L x ob_D mk_ob Hmk_ob Hob_eq GD i k ls' e_last Hh H_L Ψ Hcons Hwb Hsingle
    Hgob Hval Hnalloc

/-- The acquire RMW's write half, ported (`AxLockWp2.wpAmoswapAqLob`). -/
theorem wpdAmoswapAqLob (γ γc : GName) (L x : Int)
    (ob_D : AxirisG.obSt GF → GSet Geid) (mk_ob : GSet Geid → AxirisG.obSt GF)
    (Hmk_ob : ∀ D, ob_D (mk_ob D) = D)
    (Hob_eq : ∀ (GD : Gdexec) (σ : AxirisG.obSt GF) (s : GSet Geid),
      AxirisG.obStInterp GD σ s ⊣⊢ protInvLock L x γ γc GD s (ob_D σ))
    (GD : Gdexec) (i : Agent) (k : Nat) (ls' : AxirisG.logTsT GF) (w_rel : Geid)
    (H_L : List Hent) (Ψ : Unit → IProp GF)
    (Hcons : rvwmoCatConsistent GD)
    (Hpol : w_rel ∈ Axpol.sPol GD (i, k))
    (Hunclaimed : ∀ σ : AxirisG.obSt GF, w_rel ∉ ob_D σ)
    (Hwb0 : gwritesByte GD.gdG w_rel L b0)
    (Hwb1 : gwritesByte GD.gdG (i, k) L b1)
    (Hsingle : ∀ a' v', gwritesByte GD.gdG (i, k) a' v' → a' = L)
    (Hgob : gobCat GD w_rel (i, k))
    (Hval : graphData GD (i, k) = some [b1])
    (Hnalloc : ⊢ ∀ na : Mea GF, naAtProgress GD i k na ∗ AxirisG.annotInterp na ==∗
      AxirisG.annotInterp (insert na (i, k)
        iprop(⌜gwritesByte GD.gdG w_rel L b0⌝ ∗
          (∃ H, tokTie GD γ x H {[(i, k) := (1 : Qp)]})))) :
    ⊢ histAuth γ L 1 H_L -∗ AxirisG.localInterp GD i (k + 1) ls' -∗ Ψ () -∗
      wpEvStep GD i k (fun _ : Unit => True) (fun _ : Unit => graphData GD (i, k) = some [b1])
        (fun _ => k + 1) Ψ :=
  wpAmoswapAqLob γ γc L x ob_D mk_ob Hmk_ob Hob_eq GD i k ls' w_rel H_L Ψ Hcons Hpol Hunclaimed
    Hwb0 Hwb1 Hsingle Hgob Hval Hnalloc

end lockWpD

end Weak
