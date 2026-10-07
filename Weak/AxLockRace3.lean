/-
Weak: **the program-proof-premised 5-event race theorem, slot `w_x..w_rel` only** (AxSL tier,
lock slice) — two full-authority owned-write obligations to `x` in one `ordEaTodoL` walk are
contradictory.

Rocq: `iris/AxLockRace3.v` @ xxvzwolszwmp.

## The Rocq header, in substance

A Prop-level `∀ GD, hyps5 → v = vx` is refuted by `AxLockRace.race`
(`raceConclusionWouldBeFalse`), so the theorem instead carries a PROGRAM-PROOF premise: the
2-slot walk `ordEaTodoL GD (ea05 γ) (na05 γ) [w_x; w_c] 0` is derivable from the initial
`histAuth γ x 1 []` under EVERY `InvGS_gen .hasNoLC`/`AxirisG` instance.  Only two slots are
peeled (`ordEaTodoLCons`): `w_x`'s flow equation deposits `tokTie GD γ x [(w_x, vx)] {[w_x := 1]}`
at its lob′-successor `w_rel5`, and `w_c`'s obligation is FIXED to the owned-write rule's output
`∃ Hl_c, histAuth γ x 1 Hl_c`; `AxLockRace.ownedWriteExcluded` collides the two.  `obStInterp`
is instantiated trivially (`AxLockRace3.axG5`, everything `True`), since the premise ranges over
every instance.

  §1  the slice `hh5`/`initialRes5`/`na05`/`ea05`/`AxLockRace3.l45`, the trivial instance, and
      the lookup facts.
  §2  `twoFullWriteObligationsContradict`: the premise implies `False` (the honest content).
  §3  `lockSliceSoundRaceVACUOUS`: the read-value wrapper, KEPT FOR THE RECORD ONLY.  VACUITY
      (Rocq, advisor 2026-09-27): the premise is unsatisfiable even for the non-racing program
      (the acquirer's token must come from `protInvLock'`, absent from the trivial instance),
      so the conclusion holds ex falso; do NOT cite it as evidence that a race is excluded.

**Fetches.** Nothing here relies on instruction fetches: pure ghost-state / walk facts.

## Deviations from Rocq

1. NAMES: camelCase (map below).  Duplicated Rocq name, file-qualified: `AxLockRace3.l45` (also
   in AxLockRace2).  Lean-only names file-qualified: `AxLockRace3.axG5` (Rocq's `Local Instance
   AxG5`; a `def`, installed with `letI` inside the proofs).
2. VOCABULARY (as AxLockRace deviation 2): `gd_g GD` ↦ `GD.gdG`; `Z` ↦ `Int`; `axlogG Σ hent` ↦
   `[AxlogG GF Hent]`; `invGpreS Σ` ↦ `[InvGpreS GF]`; `<[k := v]> m` ↦ `insert m k v`;
   `m !! k` ↦ `get? m k`; `tt` ↦ `()`; `invGS_gen HasNoLc Σ` ↦ `InvGS_gen .hasNoLC GF`;
   `s_pol` ↦ `Axpol.sPol`; `lob_succ_of` ↦ `lobSuccOf`; `step_fupdN_soundness_no_lc'` ↦
   iris-lean `step_fupdN_soundness_close` at `hlc := .hasNoLC`; `uPred.pure_soundness` ↦
   `Iris.pure_soundness` (Sbi).
3. SECTION VARIABLES: Rocq's `Context` (with `Proof using All`) becomes explicit leading
   arguments; each definition/lemma takes the section variables its statement or proof uses
   (the two main theorems take all of them, including the unused `vc`, as in Rocq).
4. The AxirisG record has no `ax_text` field in Lean (O2 Stage C), so `axG5` has six fields.
5. `lockSliceSoundRaceVACUOUS` is proved by `twoFullWriteObligationsContradict` (Rocq repeats
   the proof script verbatim); statements unchanged.

**Rocq → Lean name map.**  `Hh5` `hh5`, `initial_res5` `initialRes5`, `na05` `na05`, `ea05`
`ea05`, `L45` `AxLockRace3.l45`, `AxG5` `AxLockRace3.axG5`, `L45_0` `l45Get0`, `L45_1`
`l45Get1`, `na05_wx` `na05Wx`, `na05_wc` `na05Wc`, `ea05_wx` `ea05Wx`, `ea05_wc` `ea05Wc`,
`ea05_wrel5` `ea05Wrel5`, `two_full_write_obligations_contradict`
`twoFullWriteObligationsContradict`, `lock_slice_sound_race_VACUOUS` `lockSliceSoundRaceVACUOUS`.

**Not ported:** the `Print Assumptions` audits (the lint's axiom check covers them).
-/
import Weak.AxLockRace
import Weak.AxAdequacyL
import Weak.AxLifting
import Iris.ProofMode

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp

/-! # 1. THE 2-EVENT `na05`/`ea05`/`l45` SLICE AND THE TRIVIAL INSTANCE -/

section Race5

variable {GF : BundledGFunctors} [AxlogG GF Hent]

/-- The write history the deposited token is tied to. -/
def hh5 (w_x : Geid) (vx : BitVec 8) : List Hent := [(w_x, vx)]

/-- The ONE credential the whole argument threads. -/
def initialRes5 (x : Int) (γ : GName) : IProp GF := histAuth γ x 1 ([] : List Hent)

/-- `w_x`'s obligation is `emp`; `w_c`'s is FIXED to the owned-write rule's output shape. -/
def na05 (x : Int) (w_x w_c : Geid) (γ : GName) : Mea GF :=
  insert (insert (∅ : Mea GF) w_c iprop(∃ Hl_c : List Hent, histAuth γ x 1 Hl_c)) w_x iprop(emp)

/-- Neither write draws on an incoming deposit; `w_rel5` receives `w_x`'s tied token. -/
def ea05 (GD : Gdexec) (x : Int) (w_x w_c w_rel5 : Geid) (vx : BitVec 8) (γ : GName) : Sra GF :=
  insert
    (insert
      (insert (∅ : Sra GF) w_rel5
        (insert (∅ : Mea GF) w_x (tokTie GD γ x (hh5 w_x vx) {[w_x := (1 : Qp)]})))
      w_c (∅ : Mea GF))
    w_x (∅ : Mea GF)

def AxLockRace3.l45 (w_x w_c : Geid) : List Geid := [w_x, w_c]

/-- The TRIVIAL `AxirisG` instance (Rocq's `Local Instance AxG5`). -/
@[reducible] def AxLockRace3.axG5 : AxirisG GF where
  annotInterp := fun _ => iprop(True)
  gconstInterp := fun _ => iprop(True)
  obSt := Unit
  obStInterp := fun _ _ _ => iprop(True)
  logTsT := Unit
  localInterp := fun _ _ _ _ => iprop(True)

theorem l45Get0 (w_x w_c : Geid) : (AxLockRace3.l45 w_x w_c)[0]? = some w_x := rfl
theorem l45Get1 (w_x w_c : Geid) : (AxLockRace3.l45 w_x w_c)[1]? = some w_c := rfl

theorem na05Wx (x : Int) (w_x w_c : Geid) (γ : GName) :
    get? (na05 (GF := GF) x w_x w_c γ) w_x = some iprop(emp) := by
  unfold na05; exact lookupInsert

theorem na05Wc (x : Int) (w_x w_c : Geid) (Hne_xc : w_x ≠ w_c) (γ : GName) :
    get? (na05 (GF := GF) x w_x w_c γ) w_c =
      some iprop(∃ Hl_c : List Hent, histAuth γ x 1 Hl_c) := by
  unfold na05; rw [lookupInsertNe Hne_xc]; exact lookupInsert

theorem ea05Wx (GD : Gdexec) (x : Int) (w_x w_c w_rel5 : Geid) (vx : BitVec 8) (γ : GName) :
    get? (ea05 (GF := GF) GD x w_x w_c w_rel5 vx γ) w_x = some (∅ : Mea GF) := by
  unfold ea05; exact lookupInsert

theorem ea05Wc (GD : Gdexec) (x : Int) (w_x w_c w_rel5 : Geid) (vx : BitVec 8)
    (Hne_xc : w_x ≠ w_c) (γ : GName) :
    get? (ea05 (GF := GF) GD x w_x w_c w_rel5 vx γ) w_c = some (∅ : Mea GF) := by
  unfold ea05; rw [lookupInsertNe Hne_xc]; exact lookupInsert

theorem ea05Wrel5 (GD : Gdexec) (x : Int) (w_x w_c w_rel5 : Geid) (vx : BitVec 8)
    (Hne_x_wrel5 : w_x ≠ w_rel5) (Hne_c_wrel5 : w_c ≠ w_rel5) (γ : GName) :
    get? (ea05 (GF := GF) GD x w_x w_c w_rel5 vx γ) w_rel5 =
      some (insert (∅ : Mea GF) w_x (tokTie GD γ x (hh5 w_x vx) {[w_x := (1 : Qp)]})) := by
  unfold ea05; rw [lookupInsertNe Hne_x_wrel5, lookupInsertNe Hne_c_wrel5]; exact lookupInsert

/-! # 2. THE LEMMA THE FILE ACTUALLY PROVES: two full-authority owned-write obligations to `x`
in one `ordEaTodoL` are contradictory -/

/-- If the 2-slot walk is derivable from `initialRes5 γ` under EVERY instance, then `False`:
`w_x`'s slot deposits a FULL `tokTie` to its lob′-successor and `w_c`'s slot produces a FULL
`histAuth γ x 1 Hl_c`; `ownedWriteExcluded` collides them. -/
theorem twoFullWriteObligationsContradict [Axpol] [InvGpreS GF]
    (GD : Gdexec) (x : Int) (w_x w_c w_rel5 : Geid) (vx _vc : BitVec 8)
    (Hne_xc : w_x ≠ w_c) (Hne_x_wrel5 : w_x ≠ w_rel5) (Hne_c_wrel5 : w_c ≠ w_rel5)
    (Hsucc : w_rel5 ∈ lobSuccOf GD w_x)
    (Hspol_wx : Axpol.sPol GD w_x ⊆ (∅ : GSet Geid))
    (Hspol_wc : Axpol.sPol GD w_c ⊆ (∅ : GSet Geid))
    (Hverif : ∀ [InvGS_gen .hasNoLC GF] [AxirisG GF] (γ : GName),
      initialRes5 (GF := GF) x γ ⊢
        ordEaTodoL (hlc := .hasNoLC) GD (ea05 GD x w_x w_c w_rel5 vx γ) (na05 x w_x w_c γ)
          (AxLockRace3.l45 w_x w_c) 0) :
    False := by
  apply Iris.pure_soundness (PROP := IProp GF)
  refine step_fupdN_soundness_close (hlc := .hasNoLC) 2 0 (fun Hinv => ?_)
  letI : AxirisG GF := AxLockRace3.axG5
  simp only [initialRes5] at Hverif
  have Hnin_wx : w_x ∉ (∅ : GSet Geid) := notElemOfEmpty
  have Hsub_wc : Axpol.sPol GD w_c ⊆ (({w_x} : GSet Geid) ∪ ∅) :=
    fun y hy => (notElemOfEmpty (Hspol_wc y hy)).elim
  have Hnin_wc : w_c ∉ (({w_x} : GSet Geid) ∪ ∅) := by
    intro h
    rcases elemOfUnion.1 h with h | h
    · exact Hne_xc (elemOfSingleton.1 h).symm
    · exact notElemOfEmpty h
  rw [AxAdequacy.stepFupdNSucc, AxAdequacy.stepFupdNSucc, AxAdequacy.stepFupdNZero]
  iintro _
  ihave Halloc := histAlloc (GF := GF) ({x} : GSet Int) ([] : List Hent)
  imod Halloc with ⟨%γ, Halloc⟩
  ihave Halloc := BigSepS.bigSepS_singleton.1 $$ Halloc
  ihave Htodo := (@Hverif Hinv AxLockRace3.axG5 γ) $$ Halloc
  icases (ordEaTodoLCons GD _ _ _ 0 w_x (l45Get0 w_x w_c)).1 $$ Htodo with ⟨Hhd, Htodo⟩
  isimp only [na05Wx x w_x w_c γ, ea05Wx GD x w_x w_c w_rel5 vx γ, AxWp.fromOption] at Hhd
  iunfold flowEqEa, flowEqDyn at Hhd
  ihave Hob0 : iprop(True) $$ []
  · itrivial
  ihave Hemp0 := (BigSepM.bigSepM_empty (Φ := fun (_ : Geid) (Rin : IProp GF) => Rin)).2 $$ []
  · itrivial
  imod Hhd $$ %() %(∅ : GSet Geid) %Hspol_wx %Hnin_wx Hob0 Hemp0 with Hstep1
  imodintro
  inext
  imod Hstep1 with ⟨%σ1, -, -, Hdep⟩
  iunfold eaDeposit at Hdep
  icases (BigSepS.bigSepS_delete (Φ := fun eOut =>
    AxLifting.depAt (ea05 GD x w_x w_c w_rel5 vx γ) w_x eOut) Hsucc).1 $$ Hdep with ⟨Hpiece, -⟩
  rw [AxLifting.depAtSomeSome _ w_x w_rel5 _ _
    (ea05Wrel5 GD x w_x w_c w_rel5 vx Hne_x_wrel5 Hne_c_wrel5 γ) lookupInsert]
  imodintro
  icases (ordEaTodoLCons GD _ _ _ 1 w_c (l45Get1 w_x w_c)).1 $$ Htodo with ⟨Hhd, -⟩
  isimp only [na05Wc x w_x w_c Hne_xc γ, ea05Wc GD x w_x w_c w_rel5 vx Hne_xc γ,
    AxWp.fromOption] at Hhd
  iunfold flowEqEa, flowEqDyn at Hhd
  ihave Hob1 : iprop(True) $$ []
  · itrivial
  ihave Hemp1 := (BigSepM.bigSepM_empty (Φ := fun (_ : Geid) (Rin : IProp GF) => Rin)).2 $$ []
  · itrivial
  imod Hhd $$ %σ1 %(({w_x} : GSet Geid) ∪ ∅) %Hsub_wc %Hnin_wc Hob1 Hemp1 with Hstep2
  imodintro
  inext
  imod Hstep2 with ⟨%σ2, -, ⟨%Hl_c, Hauth⟩, -⟩
  imodintro
  iexfalso
  iapply ownedWriteExcluded GD γ x (hh5 w_x vx) w_x Hl_c
  isplitl [Hpiece]
  · iexact Hpiece
  · iexact Hauth

/-! # 3. THE READ-VALUE WRAPPER — KEPT FOR THE RECORD ONLY

VACUITY (Rocq, advisor 2026-09-27): `Hverif` quantifies over EVERY `AxirisG` instance, and
`twoFullWriteObligationsContradict` shows it is UNSATISFIABLE even for the non-racing program;
the read-value conclusion holds ex falso.  Do NOT cite this theorem (nor any
`race_not_verifiable`-shaped corollary) as evidence that a race is excluded, detected, or even
distinguishable from the non-racing case. -/

/-- The PROGRAM-PROOF premise is contradictory, so the read-value conclusion holds vacuously. -/
theorem lockSliceSoundRaceVACUOUS [Axpol] [InvGpreS GF]
    (GD : Gdexec) (x : Int) (w_x w_c w_rel5 : Geid) (vx vc : BitVec 8)
    (Hne_xc : w_x ≠ w_c) (Hne_x_wrel5 : w_x ≠ w_rel5) (Hne_c_wrel5 : w_c ≠ w_rel5)
    (Hsucc : w_rel5 ∈ lobSuccOf GD w_x)
    (Hspol_wx : Axpol.sPol GD w_x ⊆ (∅ : GSet Geid))
    (Hspol_wc : Axpol.sPol GD w_c ⊆ (∅ : GSet Geid))
    (r_x : Geid)
    (Hverif : ∀ [InvGS_gen .hasNoLC GF] [AxirisG GF] (γ : GName),
      initialRes5 (GF := GF) x γ ⊢
        ordEaTodoL (hlc := .hasNoLC) GD (ea05 GD x w_x w_c w_rel5 vx γ) (na05 x w_x w_c γ)
          (AxLockRace3.l45 w_x w_c) 0) :
    ∀ t v, greadsByte GD.gdG r_x x t v → v = vx := by
  intro t v _
  exact (twoFullWriteObligationsContradict GD x w_x w_c w_rel5 vx vc Hne_xc Hne_x_wrel5
    Hne_c_wrel5 Hsucc Hspol_wx Hspol_wc Hverif).elim

end Race5

end Weak
