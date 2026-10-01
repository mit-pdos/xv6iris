/-
**The in-logic strong noninterference instance for a quiet process**
(permit sweep T; Rocq's planned `ut_round_quiet`, design
`claude-notes/design/ni-strong-instance.md` §7 and §7.8L).

A run of trap rounds is a start record `V₀` and a list of rounds
`(scᵢ, Vᵢ₊₁)`: round `i` enters at `Vᵢ` with cause `scᵢ` and leaves at
`Vᵢ₊₁` -- each round is what `SpecUsertrap.usertrapPost` hands its
continuation at `V := Vᵢ`, `V' := Vᵢ₊₁`, with the quiet row
`utEvQuiet scᵢ Vᵢ Vᵢ₊₁` among its premises.  That round `i + 1` is entered
at round `i`'s exit record is the run's hypothesis (the closed loop,
`UserretClosedRound`, parks the residue at `V'` and re-opens it at the
next trap; uservec rewrites only trapframe words, which `ev` does not see);
this file does not restate the loop.  For a
QUIET run -- no cause is the ecall and the lazy flag is off at every entry
-- the event counter is the same at every record of the run
(`utRoundQuiet`, `utRoundQuiet_noAppend`).

The statement is for a process that is NOT KILLED: a killed process exits
through `kexit` (`UsertrapBlocks.UT_KEXIT`, no resume row, so no round of
the run), and kexit steps its counter at its `ZExit` append -- the
statement's one exception (§7, "The statement's exception"; the `Kill`
event is M3's).

Pure: no Iris, no ghost state.  Imports only `SpecUsertrap` (the row).

## Deviations from Rocq

1. **T, no Rocq counterpart** (Rocq never landed T): Rocq planned `ev ev'`
   inside `uround_ok` and `ut_round_quiet` over it; this tree states a
   separate kept row (`SpecUsertrap.utEvQuiet`, deviation 11 there) and the
   run as a list here.  `utRound` / `uroundOk` do not move.
2. **The run is pure.** The ledgers' contents (that no event labelled with
   the slot was appended) are M2's statement; this file states the fact
   about the counter and, in `utRoundQuiet_noAppend`'s docstring, the
   reading §7.7L's by-construction invariant gives it.
-/
import Xv6.SpecUsertrap

namespace Xv6

/-- **A run's rows**: every round `(sc, V')` entered at `V` carries the
quiet row `utEvQuiet sc V V'`. -/
def utRunRows : ProcPriv → List (BitVec 64 × ProcPriv) → Prop
  | _, [] => True
  | V, (sc, V') :: rs => utEvQuiet sc V V' ∧ utRunRows V' rs

/-- **A quiet run**: no round's cause is the ecall and the lazy flag is off
at every round's entry record. -/
def utRunQuiet : ProcPriv → List (BitVec 64 × ProcPriv) → Prop
  | _, [] => True
  | V, (sc, V') :: rs => sc ≠ uecallScause ∧ V.pvLazy = false ∧ utRunQuiet V' rs

/-- The record a run ends at. -/
def utRunEnd : ProcPriv → List (BitVec 64 × ProcPriv) → ProcPriv
  | V, [] => V
  | _, (_, V') :: rs => utRunEnd V' rs

/-- Every record of a run: the start and each round's exit. -/
def utRunRecs : ProcPriv → List (BitVec 64 × ProcPriv) → List ProcPriv
  | V, [] => [V]
  | V, (_, V') :: rs => V :: utRunRecs V' rs

/-- **THE IN-LOGIC STRONG INSTANCE, at the run's ends** (Rocq's planned
`ut_round_quiet`): over a quiet run whose rounds carry the quiet row, the
event counter at the end is the counter at the start. -/
theorem utRoundQuiet (V₀ : ProcPriv) (rs : List (BitVec 64 × ProcPriv)) (hrows : utRunRows V₀ rs)
    (hq : utRunQuiet V₀ rs) : (utRunEnd V₀ rs).ev = V₀.ev := by
  induction rs generalizing V₀ with
  | nil => rfl
  | cons r rs ih =>
    obtain ⟨sc, V'⟩ := r
    obtain ⟨hrow, hrows'⟩ := hrows
    obtain ⟨hsc, hlz, hq'⟩ := hq
    exact (ih V' hrows' hq').trans (hrow hsc hlz)

/-- **No append in a quiet run** (the in-logic reading, M2's input): every
record of a quiet run carries the start's event counter.

THE READING (design ni-strong-instance.md §7.7L, the invariant L3
established by construction).  Slot `pa`'s counter is the exclusive
`actCnt pa V.ev` its block holds (`actCnt_excl`: one owner); its value moves
only through `actCnt_step` (`k` to `k + 1`), one step paired with each
actor-labelled ledger append (`KAlloc`, `KNull`, `KFree`, `PAlloc`, `PFree`,
`ZReap`, `ZExit`) whose actor is `pa`, only in code running as `pa`'s own
kernel thread, never at boot (actor 0); and every contract on the cone hands
it back at a count no lower.  So the count at a record is the number of
`pa`-labelled appends made since the slot was minted at 0, and a quiet,
unkilled run -- where this theorem gives the same count at every record --
saw NO append labelled with `pa`.  What those appends' absence says about
the ledgers' contents is M2's statement; the `Kill` event (a killed quiet
process exits and appends `ZExit`) is M3's. -/
theorem utRoundQuiet_noAppend (V₀ : ProcPriv) (rs : List (BitVec 64 × ProcPriv))
    (hrows : utRunRows V₀ rs) (hq : utRunQuiet V₀ rs) : ∀ V ∈ utRunRecs V₀ rs, V.ev = V₀.ev := by
  induction rs generalizing V₀ with
  | nil =>
    intro V hV
    simp only [utRunRecs, List.mem_singleton] at hV
    rw [hV]
  | cons r rs ih =>
    obtain ⟨sc, V'⟩ := r
    obtain ⟨hrow, hrows'⟩ := hrows
    obtain ⟨hsc, hlz, hq'⟩ := hq
    intro V hV
    simp only [utRunRecs, List.mem_cons] at hV
    rcases hV with hV | hV
    · rw [hV]
    · exact (ih V' hrows' hq' V hV).trans (hrow hsc hlz)

end Xv6
