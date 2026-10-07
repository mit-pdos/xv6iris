/-
Weak: **THE DEMONIC READ RULE**, on top of `Weak.AxWp`/`Weak.AxWp2` (unchanged).

Rocq: `iris/AxReadAll.v` @ xxvzwolszwmp.

## The Rocq header, in substance

`wpEvStep`'s read case is an EXISTENTIAL in the value (`∃ a R naUsed naUnused ls', ⌜ok a⌝ ∗ …
∗ Ψ a`), so any proof of it picks ONE witness.  The demonic rule keeps that existential (it is
unavoidable) but puts the genuine `∀ v` burden on the caller's continuation hypothesis, UNGUARDED:
`Hcont : ⊢ ∀ v, ⌜ok v⌝ -∗ Ψ v` (no `v = x` premise).  The rule itself supplies the witness `x`;
`Hflow` is `wpEvStep`'s own per-witness bookkeeping (na-splitting, the flow equation depositing
`R` at the event, the annotation update, the local-state advance) at `x` only, and the
value-identity fact travels only through the annotation machinery, never to the continuation.
§1: `wpReadAll` (⊢-closed `Hcont`), its instantiation `wpReadStepAll` at `wpPreStepDef`'s read
case; the WAND forms `wpReadAllWand`/`wpReadStepAllWand` (`Hcont` an ordinary resource on the
left, consumed once at `x`).  §2 THE REPLAY FINDING: at `x := v0` the graph's own value
(`graphValue GD (i, k) = some v0`) the `val x` conjunct is discharged for free
(`flowEqDynMono`), so phase 1 replays the graph (`wpReadAllReplay`).

The file is generic in the read: it never mentions fetches (it speaks of `wpEvStep` and the
`aidentAdvRd id = 1` arm of `wpPreStepDef` only), so it is independent of whether instruction
fetches are graph read events.

## Deviations from Rocq

1. NAMES: the tree's camelCase (map below); `bv 8` ↦ `BitVec 8`; `agent` ↦ `Agent`; `mea Σ` ↦
   `Mea GF`; map unions ↦ `PartialMap.union` (left-nested as `AxWp`'s `wpEvStep`).
2. `invGS_gen HasNoLc Σ` ↦ `[InvGS_gen hlc GF]` for an arbitrary `hlc` (as `AxWp`, deviation 6);
   `annotDeposit`/`wpEvStepDepositVal` take no instance (Rocq's section context is unused).
3. `Hflow`/`Hcont` stay `⊢`-closed premises (`→`), `wpReadAllWand`'s statement is `P ⊢ Q` as
   Rocq.  `wpReadStepAll(Wand)`'s `st : stuckness` ↦ `st : Stuckness`.

**Rocq → Lean name map.**  `annot_deposit` `annotDeposit`, `wp_ev_step_deposit_val`
`wpEvStepDepositVal`, `wp_read_all` `wpReadAll`, `wp_read_step_all` `wpReadStepAll`,
`wp_read_all_wand` `wpReadAllWand`, `wp_read_step_all_wand` `wpReadStepAllWand`,
`wp_read_all_replay` `wpReadAllReplay`.

**Not ported:** nothing (the §3 `Print Assumptions` block is replaced by the lint).
-/
import Weak.AxWp2

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp

/-! # 0. `annotDeposit`: naming what `R` carries (documentation only) -/

section deposit
variable {GF : BundledGFunctors}

/-- `R` (the fact `wpEvStep` posts into `na` at the event) ENTAILS the pure fact `φ`. -/
def annotDeposit (R : IProp GF) (φ : Prop) : Prop := R ⊢ iprop(⌜φ⌝)

/-- `wpEvStep`'s own posted fact always satisfies its deposit. -/
theorem wpEvStepDepositVal (R : IProp GF) (φ : Prop) : iprop(R ∗ ⌜φ⌝) ⊢ iprop(⌜φ⌝) := by
  iintro ⟨_, H⟩
  iexact H

end deposit

/-! # 1. The generic demonic read rule -/

section readAll
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]

/-- THE DEMONIC READ RULE: the witness `x` is the rule's; the continuation is proved for every
admissible value, unguarded. -/
theorem wpReadAll {A : Type} (GD : Gdexec) (i : Agent) (k : Nat)
    (ok val : A → Prop) (k' : A → Nat) (Ψ : A → IProp GF) (x : A) (Hokx : ok x)
    (Hflow : ⊢ ∀ na, naAtProgress GD i k na ∗ AxirisG.annotInterp na -∗ |==> ▷ |==>
       ∃ (R : IProp GF) (naUsed naUnused : Mea GF) (ls' : AxirisG.logTsT GF),
         naSplittingWf (Axpol.lobp GD (i, k)) na naUsed naUnused ∗
         flowEqDyn GD (i, k) (Axpol.sPol GD (i, k)) naUsed iprop(R ∗ ⌜val x⌝) ∗
         AxirisG.annotInterp (PartialMap.union (PartialMap.union {[(i, k) := R]} naUnused) na) ∗
         AxirisG.localInterp GD i (k' x) ls')
    (Hcont : ⊢ ∀ v : A, ⌜ok v⌝ -∗ Ψ v) :
    ⊢ wpEvStep GD i k ok val k' Ψ := by
  unfold wpEvStep
  iintro %na Hpg
  ihave Hf := Hflow
  imod Hf $$ %na Hpg with Hf1
  imodintro
  inext
  imod Hf1 with ⟨%R, %nu, %nuu, %ls', Hsplit, Hfe, Hna, Hloc⟩
  imodintro
  iexists x, R, nu, nuu, ls'
  isplitr
  · ipureintro
    exact Hokx
  iframe Hsplit Hfe Hna Hloc
  ihave Hc := Hcont
  iapply Hc $$ %x
  ipureintro
  exact Hokx

/-- The instantiation at `wpPreStepDef`'s read case (the `aidentAdvRd id = 1` arm). -/
theorem wpReadStepAll (st : Stuckness) (GD : Gdexec) (i : Agent) (s : Athread)
    (id : AidentT) (K : List (BitVec 8) → Athread) (Φ : Athread → IProp GF)
    (x : List (BitVec 8)) (Hlen : x.length = aidentN id)
    (Hflow : ⊢ ∀ na, naAtProgress GD i s.atK na ∗ AxirisG.annotInterp na -∗ |==> ▷ |==>
       ∃ (R : IProp GF) (naUsed naUnused : Mea GF) (ls' : AxirisG.logTsT GF),
         naSplittingWf (Axpol.lobp GD (i, s.atK)) na naUsed naUnused ∗
         flowEqDyn GD (i, s.atK) (Axpol.sPol GD (i, s.atK)) naUsed
           iprop(R ∗ ⌜graphValue GD (i, s.atK) = some x⌝) ∗
         AxirisG.annotInterp
           (PartialMap.union (PartialMap.union {[(i, s.atK) := R]} naUnused) na) ∗
         AxirisG.localInterp GD i (K x).atK ls')
    (Hcont : ⊢ ∀ v : List (BitVec 8), ⌜v.length = aidentN id⌝ -∗ AxWp.wp st i (K v) Φ) :
    ⊢ wpEvStep GD i s.atK
        (fun v => v.length = aidentN id) (fun v => graphValue GD (i, s.atK) = some v)
        (fun v => (K v).atK) (fun v => AxWp.wp st i (K v) Φ) := by
  have h := @wpReadAll hlc GF _ _ _ (List (BitVec 8)) GD i s.atK (fun v => v.length = aidentN id)
    (fun v => graphValue GD (i, s.atK) = some v) (fun v => (K v).atK)
    (fun v => AxWp.wp st i (K v) Φ) x Hlen Hflow Hcont
  exact h

/-- THE WAND FORM: the continuation is an ordinary resource, specialized once at `x`. -/
theorem wpReadAllWand {A : Type} (GD : Gdexec) (i : Agent) (k : Nat)
    (ok val : A → Prop) (k' : A → Nat) (Ψ : A → IProp GF) (x : A) (Hokx : ok x)
    (Hflow : ⊢ ∀ na, naAtProgress GD i k na ∗ AxirisG.annotInterp na -∗ |==> ▷ |==>
       ∃ (R : IProp GF) (naUsed naUnused : Mea GF) (ls' : AxirisG.logTsT GF),
         naSplittingWf (Axpol.lobp GD (i, k)) na naUsed naUnused ∗
         flowEqDyn GD (i, k) (Axpol.sPol GD (i, k)) naUsed iprop(R ∗ ⌜val x⌝) ∗
         AxirisG.annotInterp (PartialMap.union (PartialMap.union {[(i, k) := R]} naUnused) na) ∗
         AxirisG.localInterp GD i (k' x) ls') :
    iprop(∀ v : A, ⌜ok v⌝ -∗ Ψ v) ⊢ wpEvStep GD i k ok val k' Ψ := by
  unfold wpEvStep
  iintro Hcont %na Hpg
  ihave Hf := Hflow
  imod Hf $$ %na Hpg with Hf1
  imodintro
  inext
  imod Hf1 with ⟨%R, %nu, %nuu, %ls', Hsplit, Hfe, Hna, Hloc⟩
  imodintro
  iexists x, R, nu, nuu, ls'
  isplitr
  · ipureintro
    exact Hokx
  iframe Hsplit Hfe Hna Hloc
  iapply Hcont $$ %x
  ipureintro
  exact Hokx

/-- The wand-form twin of `wpReadStepAll`. -/
theorem wpReadStepAllWand (st : Stuckness) (GD : Gdexec) (i : Agent) (s : Athread)
    (id : AidentT) (K : List (BitVec 8) → Athread) (Φ : Athread → IProp GF)
    (x : List (BitVec 8)) (Hlen : x.length = aidentN id)
    (Hflow : ⊢ ∀ na, naAtProgress GD i s.atK na ∗ AxirisG.annotInterp na -∗ |==> ▷ |==>
       ∃ (R : IProp GF) (naUsed naUnused : Mea GF) (ls' : AxirisG.logTsT GF),
         naSplittingWf (Axpol.lobp GD (i, s.atK)) na naUsed naUnused ∗
         flowEqDyn GD (i, s.atK) (Axpol.sPol GD (i, s.atK)) naUsed
           iprop(R ∗ ⌜graphValue GD (i, s.atK) = some x⌝) ∗
         AxirisG.annotInterp
           (PartialMap.union (PartialMap.union {[(i, s.atK) := R]} naUnused) na) ∗
         AxirisG.localInterp GD i (K x).atK ls') :
    iprop(∀ v : List (BitVec 8), ⌜v.length = aidentN id⌝ -∗ AxWp.wp st i (K v) Φ) ⊢
      wpEvStep GD i s.atK
        (fun v => v.length = aidentN id) (fun v => graphValue GD (i, s.atK) = some v)
        (fun v => (K v).atK) (fun v => AxWp.wp st i (K v) Φ) := by
  refine wpReadAllWand GD i s.atK (fun v => v.length = aidentN id)
    (fun v => graphValue GD (i, s.atK) = some v) (fun v => (K v).atK)
    (fun v => AxWp.wp st i (K v) Φ) x Hlen ?_
  exact Hflow

end readAll

/-! # 2. The replay finding: at the graph's own value the `val` conjunct is free -/

section readAllReplay
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]

theorem wpReadAllReplay (GD : Gdexec) (i : Agent) (k : Nat)
    (ok : List (BitVec 8) → Prop) (k' : List (BitVec 8) → Nat) (Ψ : List (BitVec 8) → IProp GF)
    (v0 : List (BitVec 8)) (Hokx : ok v0) (Hgv : graphValue GD (i, k) = some v0)
    (Hflow0 : ⊢ ∀ na, naAtProgress GD i k na ∗ AxirisG.annotInterp na -∗ |==> ▷ |==>
       ∃ (R : IProp GF) (naUsed naUnused : Mea GF) (ls' : AxirisG.logTsT GF),
         naSplittingWf (Axpol.lobp GD (i, k)) na naUsed naUnused ∗
         flowEqDyn GD (i, k) (Axpol.sPol GD (i, k)) naUsed R ∗
         AxirisG.annotInterp (PartialMap.union (PartialMap.union {[(i, k) := R]} naUnused) na) ∗
         AxirisG.localInterp GD i (k' v0) ls')
    (Hcont : ⊢ ∀ v : List (BitVec 8), ⌜ok v⌝ -∗ Ψ v) :
    ⊢ wpEvStep GD i k ok (fun v => graphValue GD (i, k) = some v) k' Ψ := by
  refine wpReadAll GD i k ok (fun v => graphValue GD (i, k) = some v) k' Ψ v0 Hokx ?_ Hcont
  iintro %na Hpg
  ihave Hf0 := Hflow0
  imod Hf0 $$ %na Hpg with Hf
  imodintro
  inext
  imod Hf with ⟨%R, %nu, %nuu, %ls', Hsplit, Hfe, Hna, Hloc⟩
  imodintro
  iexists R, nu, nuu, ls'
  iframe Hsplit Hna Hloc
  iapply flowEqDynMono $$ [] Hfe
  inext
  iintro HR
  iframe HR
  ipureintro
  exact Hgv

end readAllReplay

end Weak
