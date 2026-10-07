/-
Weak: **THE "SMELL TEST FIRST"** for the §7.L lock theorem (AxSL tier, LB/AxSL lock slice):
under the FIXED `AxirisG` instance the §7.L statement pins (`obStInterp := protInvLock' lr xr γ
γc`, at `D = ∅`/`hm = ∅`, every field the induction never inspects a trivial placeholder), the
racing write `wCR` of `AxLockRace.race` is UNVERIFIABLE EVEN WITH THE TRIVIAL ANNOTATION
(`flowIn = ∅`, `R = emp`): `raceWcUnverifiableTrivial`.

Rocq: `iris/AxLockSmell.v` @ xxvzwolszwmp.

## The Rocq header, in substance

`wCR` genuinely writes byte `xr` in `race` (`raceWcWritesX`).  Under `protInvLock'`, an
`x`-write's protocol content is `ΦpOwn`, which at a write unfolds to `ΦOwn` — a persistent
`∃ H, histSnap γ x H ∗ ⌜H.getLast? = some (wCR, v)⌝`.  The only primitive producing a fresh such
fact (`protInvWriteStep`, via `histAppend`) needs the exclusive `histAuth γ x 1 _`, which
`flowIn = ∅` withholds and `protInvLock'` over the empty validated set does not hold either.
Made concrete by holding a counter-resource: a fresh `γ` with `histAuth γ xr 1 []` (as
`lockInitialAlloc`); the snapshot the assumed obligation produces must be a prefix of `[]`
(`histSnapPrefix`), contradicting its own `getLast? = some (wCR, b2)`.  `False` is stripped from
the fancy-update chain by `Iris.pure_soundness`/`step_fupdN_soundness_close` (as
`lockSliceSound`).  VERDICT: refuted, not provable — had it been provable, `ΦpOwn` would not
demand the full `histAuth` and the §7.L mutual-exclusion conclusion would be false.

**Ghost state**: allocated inside the soundness continuation — the history log at `{xr}` with
empty history (`histAlloc`, `AxlogG GF Hent`) and the claimed-set authority at `∅`
(`claimedAllocEmpty`, `AxLockG GF`).  **Fetches**: none (as `AxLockRace`).

## Deviations from Rocq

1. VOCABULARY as `Weak/AxLockAdeq.lean` deviation 1 (`invGS_gen HasNoLc Σ` ↦
   `InvGS_gen .hasNoLC GF`; `step_fupdN_soundness_no_lc'` ↦ `step_fupdN_soundness_close` with
   `m = 0`; `uPred.pure_soundness` ↦ `Iris.pure_soundness`; `vmr` ↦ `decide +kernel`).
2. CONCRETE INSTANCE (as `Weak/AxLockAdeq2.lean` deviation 2): Rocq's `AxLock_inst` ↦ the
   `@[reducible] def axLockInst`, passed explicitly (`@flowEqDyn .hasNoLC GF Hinv (axLockInst γ
   γc) …`); Lean's `AxirisG` has no `ax_text` field (O2 Stage C); `unit`/`tt` ↦ `Unit`/`()`.
3. `raceWcWritesX` takes no section variables (its Rocq `Proof using All` context is unused).
4. PROOF: Rocq rewrites `{[w_c_r]} ∪ ∅ = {[w_c_r]}` and uses `big_sepS_singleton`; Lean peels
   the event with `protInvInsert` at `s = ∅` (no set equality).  Statements unchanged.

**Rocq → Lean name map.**  `AxLock_inst` `axLockInst`, `ob_st_interp_smell_unfold`
`obStInterpSmellUnfold`, `race_wc_writes_x` `raceWcWritesX`, `race_wc_unverifiable_trivial`
`raceWcUnverifiableTrivial`.

**Not ported:** the `Print Assumptions` audits (the lint's axiom check covers them).
-/
import Weak.AxLockAdeq
import Weak.AxLockRace

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp

/-! # 1. `axLockInst` — THE FIXED `AxirisG` instance -/

section axLockInstSec
variable {GF : BundledGFunctors} [AxlogG GF Hent] [AxLockG GF]

/-- The fixed instance: `obStInterp := protInvLock' lr xr γ γc` at `D = ∅`, `hm = ∅`. -/
@[reducible] def axLockInst (γ γc : GName) : AxirisG GF where
  annotInterp := fun _ => iprop(True)
  gconstInterp := fun _ => iprop(True)
  obSt := Unit
  obStInterp := fun GD0 _ s =>
    protInvLock' lr AxLockRace.xr γ γc GD0 s ∅ (∅ : GMapF Geid (List Hent))
  logTsT := Unit
  localInterp := fun _ _ _ _ => iprop(True)

theorem obStInterpSmellUnfold (γ γc : GName) (GD0 : Gdexec) (σ : Unit) (s : GSet Geid) :
    AxirisG.obStInterp (self := axLockInst (GF := GF) γ γc) GD0 σ s ⊣⊢
      protInvLock' lr AxLockRace.xr γ γc GD0 s ∅ (∅ : GMapF Geid (List Hent)) :=
  ⟨.rfl, .rfl⟩

end axLockInstSec

/-! # 2. THE SMELL TEST -/

/-- `race`'s racing write genuinely writes byte `xr`, value `b2`. -/
theorem raceWcWritesX : gwritesByte race.gdG wCR AxLockRace.xr b2 :=
  (gwbBSpec _ _ _ _).1 (by decide +kernel)

/-- THE SMELL TEST: under the fixed `axLockInst`, no choice of `Hinv`/`γ`/`γc` validates
`wCR`'s trivial flow equation. -/
theorem raceWcUnverifiableTrivial {GF : BundledGFunctors} [InvGpreS GF] [AxlogG GF Hent]
    [AxLockG GF] [Axpol]
    (Hspol_wc : Axpol.sPol race wCR ⊆ (∅ : GSet Geid)) :
    ¬ (∀ (Hinv : InvGS_gen .hasNoLC GF) (γ γc : GName),
        ⊢ @flowEqDyn .hasNoLC GF Hinv (axLockInst γ γc)
            race wCR (Axpol.sPol race wCR) (∅ : Mea GF) iprop(emp)) := by
  intro Hcontra
  apply Iris.pure_soundness (PROP := IProp GF)
  refine step_fupdN_soundness_close (hlc := .hasNoLC) (P := iprop(⌜False⌝)) 1 0
    (fun Hinv => ?_)
  have hs : iprop(|={⊤}[∅]▷=>^[0 + 1] (⌜False⌝ : IProp GF)) =
      iprop(|={⊤}[∅]▷=> (⌜False⌝ : IProp GF)) := rfl
  rw [show (1 : Nat) = 0 + 1 from rfl, hs]
  have Hisw : gisW race.gdG wCR = true :=
    WeakRvwmoGraph.gwritesByteGisW _ _ _ _ raceWcWritesX
  have hΦ : ∀ γ0 : GName, ΦpOwn (GF := GF) γ0 race wCR ⊢ ΦOwn γ0 race wCR := fun γ0 => by
    rw [AxProt.ΦpOwnW γ0 race wCR Hisw]
  have hNin : wCR ∉ (∅ : GSet Geid) := notElemOfEmpty
  iintro _
  imod histAlloc (GF := GF) ({AxLockRace.xr} : GSet Int) ([] : List Hent) with ⟨%γ0, Halloc⟩
  ihave Halloc := BigSepS.bigSepS_singleton.1 $$ Halloc
  imod claimedAllocEmpty (GF := GF) with ⟨%γc0, Hc0⟩
  have FE := Hcontra Hinv γ0 γc0
  ihave FE := FE
  iunfold flowEqDyn at FE
  ihave Hob0 : AxirisG.obStInterp (self := axLockInst (GF := GF) γ0 γc0) race () ∅ $$ [Hc0]
  · iapply (obStInterpSmellUnfold γ0 γc0 race () ∅).2
    iapply (protInvLockUnfold' lr AxLockRace.xr γ0 γc0 race ∅ ∅ ∅).2
    isplitl [Hc0]
    · iexact Hc0
    isplitl []
    · unfold protInv
      iapply BigSepS.bigSepS_empty.2
      itrivial
    · iapply BigSepS.bigSepS_empty.2
      itrivial
  ihave Hemp := (BigSepM.bigSepM_empty (Φ := fun (_ : Geid) (Rin : IProp GF) => Rin)).2 $$ []
  · itrivial
  imod FE $$ %() %(∅ : GSet Geid) %Hspol_wc %hNin Hob0 Hemp with Hstep
  imodintro
  inext
  imod Hstep with ⟨%σ', Hob', -⟩
  icases (obStInterpSmellUnfold γ0 γc0 race σ' _).1 $$ Hob' with Hob'
  icases (protInvLockUnfold' lr AxLockRace.xr γ0 γc0 race _ ∅ ∅).1 $$ Hob'
    with ⟨-, Hpo, -⟩
  icases (protInvInsert γ0 race wCR ∅ hNin).1 $$ Hpo with ⟨Hpo, -⟩
  ihave Hpo := hΦ γ0 $$ Hpo
  iunfold ΦOwn at Hpo
  icases Hpo $$ %AxLockRace.xr %b2 %raceWcWritesX with ⟨%H_c, Hsnap, %Hlast⟩
  ihave %Hpre := histSnapPrefix γ0 AxLockRace.xr 1 [] H_c $$ [$Halloc $Hsnap]
  imodintro
  ipureintro
  rw [List.prefix_nil.1 Hpre] at Hlast
  exact absurd Hlast (by simp)

end Weak
