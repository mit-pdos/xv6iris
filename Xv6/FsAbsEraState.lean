/-
**THE ERA LEND READ AGAINST THE AUTHORITY** (Rocq `FsAbsEra.v` §2,
`/shared/xv6rocq/iris/FsAbsEra.v` lines 348-384 at `1900b8a43`): the three
`astate` laws of `elend` -- `elend_astate_q`, `elend_astate`, `elend_aents`.

Rocq's note: THE READING AGAINST THE AUTHORITY -- the law the era walk
exists for.  No client-held share is needed: the lent fragment agrees with
the `ghost_map_auth` the ftopN body hands out, so a consumer that opens
ftopN INSIDE the hop's `={T}=∗` reads the parent's row as an `ADir` at the
lent entry map.

A new file beside `Xv6/FsAbsEra.lean` (whose header lists §2 as DEFERRED
with FsAbs.v's iProp half, D15): `astate` is now `Xv6/FsAbsState.lean`, and
these three laws name no `nview`.  `elend_agrees`/`elend_reads` (over
FsAbs's `lend_agrees`/`nview`) stay DEFERRED with D15.

## Deviations from Rocq

1. **The proof reads the authority directly.**  Rocq routes
   `elend_astate_q` through `nview_of_frag` + `astate_q_nview_dq` (FsAbs.v
   §3's fragment, not ported, D15); here the fragment and the authority are
   combined by `ghost_map_lookup` and the row is read by
   `absView_lookup_of` + `absOf_dir` -- the same two facts those lemmas
   package.  The statements are Rocq's.
2. Vocabulary as `FsAbsEra`'s (`Nat` inums, `PartialMap.get?`, entry maps
   `Std.ExtTreeMap Fname Nat compare`); names `elend_astateQ`,
   `elend_astate`, `elend_aents`.
-/
import Xv6.FsAbsEra
import Xv6.FsAbsState

namespace Xv6

open Iris Iris.BI Iris.ProofMode Iris.Std MachCSL

section ElendState
variable {GF : BundledGFunctors} [FsTopG GF]

/-- Rocq `elend_astate_q`. -/
theorem elend_astateQ (Γ : FsViewNames GF) (q : Qp) (av : Aview) (d : Nat) (dq : DFrac)
    (ents : Std.ExtTreeMap Fname Nat compare) :
    ⊢ astateQ Γ q av -∗ elend Γ d dq ents -∗
      ⌜∃ nl : Nat, PartialMap.get? av d = some ⟨.ADir ents, nl⟩⌝ := by
  unfold astateQ elend
  iintro ⟨%I, Ha, %hav⟩ ⟨%n, Hf, %hn⟩
  unfold topFragQ
  ihave %hi := ghost_map_lookup $$ Ha Hf
  ipureintro
  obtain ⟨hd, he, hnl⟩ := hn
  refine ⟨fnNlink n, ?_⟩
  rw [hav, absView_lookup_of I d n hi, absOf_dir n hd hnl, he]

/-- Rocq `elend_astate`: ...and at the READING, any fraction. -/
theorem elend_astate (Γ : FsViewNames GF) (av : Aview) (d : Nat) (dq : DFrac)
    (ents : Std.ExtTreeMap Fname Nat compare) :
    ⊢ astate Γ av -∗ elend Γ d dq ents -∗
      ⌜∃ nl : Nat, PartialMap.get? av d = some ⟨.ADir ents, nl⟩⌝ := by
  unfold astate
  iintro ⟨%q, Hst⟩ HF
  iapply (elend_astateQ Γ q av d dq ents) $$ Hst HF

/-- Rocq `elend_aents`: the same reading, at `aents`. -/
theorem elend_aents (Γ : FsViewNames GF) (av : Aview) (d : Nat) (dq : DFrac)
    (ents : Std.ExtTreeMap Fname Nat compare) :
    ⊢ astate Γ av -∗ elend Γ d dq ents -∗ ⌜aents av d = some ents⌝ := by
  iintro Hst HF
  ihave %h := (elend_astate Γ av d dq ents) $$ Hst HF
  ipureintro
  obtain ⟨nl, hav⟩ := h
  unfold aents
  rw [hav]
  rfl

end ElendState

end Xv6
