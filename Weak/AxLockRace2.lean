/-
Weak: **lifting AxLockAdeq §5's bookkeeping from four lock events to five, and the
mutual-exclusion lemma over all four non-vacuous resting points** (AxSL tier, lock slice).

Rocq: `iris/AxLockRace2.v` @ xxvzwolszwmp.

## The Rocq header, in substance

The 5-event `ordEaTodoL` induction over `L44 ++ [w_c]` (a `na05`/`ea05` parameterised by
`w_c`'s slot) is NOT built (as Rocq; priced out in AxLockRace's header).  What IS generalised:

  §1  `inL44` ↦ `inL45`: membership in `gxGmo` splits into FIVE cases, from the weakened
      `Hgmo_perm5 : (w_c :: L44).Perm gxGmo` (a genuine fifth memory event); `Hwonly4` ↦
      `Hwonly5` (any writer to `x` is `w_x` or `w_c`); `DOf4`/`hmOf4` unchanged as functions,
      with the two preservation lemmas `DOf4PresWc`/`hmOf4PresWc` across `w_c`'s own step.
  §2  `lockExcludesRacingWrite`: one lemma over a `LockSlot` sum type covering AxLockRace's four
      non-vacuous resting points — `slotPreWx` (the raw initial `histAuth γ x 1 []`,
      `histAuthFullExcl`), `slotWxWrel`/`slotAcqRx` (`ownedWriteExcluded` at `w_x` / `acq4`),
      `slotWrelAcq` (`protInvLockWrelSlotExcl`, the token folded into `ΦLock'`).  A racing
      write's owned-write precondition `histAuth γ x 1 Hl_c` collides with the slot's resource;
      graph position never enters.  The fifth slot (gmo-after `r_x`) is vacuous and absent.
      `lockExcludesRacingWriteConclusion` is the ex-falso corollary in the read-value shape.
  §3  (smell test) re-cited, not re-proved: `AxLockRace.race` / `raceConclusionWouldBeFalse`
      / `raceWcExcludedAtWxWrelSlot`.
  §4  `lockSliceSoundAdmitsNoRacingWriter`: `lockSliceSound''` re-exported by name.

**Fetches.** Nothing here relies on instruction fetches: pure list/set bookkeeping and
ghost-state collisions.

## Deviations from Rocq

1. NAMES: camelCase (map below).  Duplicated Rocq names, file-qualified: `AxLockRace2.wRel4`,
   `AxLockRace2.acq4`, `AxLockRace2.Hh4`, `AxLockRace2.L44`, `AxLockRace2.L45`,
   `AxLockRace2.DOf4`, `AxLockRace2.hmOf4` (same bodies as `AxLockAdeq.*`; `wRel4`/`acq4`
   `abbrev`s as there).  The inductive `lock_slot` ↦ `AxLockRace2.LockSlot` with constructors
   `slotPreWx`/`slotWxWrel`/`slotWrelAcq`/`slotAcqRx`.
2. VOCABULARY (as AxLockRace deviation 2): `gd_g GD` ↦ `GD.gdG`; `gx_gmo` ↦ `gxGmo`; `≡ₚ` ↦
   `List.Perm`; `NoDup` ↦ `List.Nodup`; `hm !! w` ↦ `get? hm w`; `Z` ↦ `Int`; `{[a]}` ↦
   `({a} : GSet Geid)`; `bool_decide (a ∈ s)` ↦ `if a ∈ s`; `axlogG Σ hent` ↦
   `[AxlogG GF Hent]`; `ax_lockG Σ` ↦ `[AxLockG GF]`.
3. STATEMENT SHAPES (as AxLockRace deviation 3): `P -∗ Q -∗ R` ↦ `P ∗ Q ⊢ R`.
4. SECTION VARIABLES (as AxLockAdeq deviation 3): Rocq's `Context` (`Proof using All`) becomes
   explicit leading arguments, and each lemma takes only the section variables/hypotheses its
   statement or proof uses (a strengthening: Rocq's post-section signatures carry the whole
   Context, including the unused `γ γc`, `Hwx`, `Hsingle_wx`, `Hwc`, `Hsingle_wc`, `Hwb1`).
5. §4's `Notation` ↦ a `theorem` whose type is `type_of% @lockSliceSound''` (zero proof content).

**Rocq → Lean name map.**  `w_rel4` `AxLockRace2.wRel4`, `acq4` `AxLockRace2.acq4`, `Hh4`
`AxLockRace2.Hh4`, `L44` `AxLockRace2.L44`, `L45` `AxLockRace2.L45`, `L45_nodup` `L45Nodup`,
`L45_wc_notin_L44` `L45WcNotinL44`, `L45_ne_wc_wx` `L45NeWcWx`, `L45_ne_wc_wrel4`
`L45NeWcWrel4`, `L45_ne_wc_acq4` `L45NeWcAcq4`, `L45_ne_wc_rx` `L45NeWcRx`, `in_L45` `inL45`,
`Hwonly5` `Hwonly5`, `D_of4` `AxLockRace2.DOf4`, `hm_of4` `AxLockRace2.hmOf4`, `D_of4_pres_wc`
`DOf4PresWc`, `hm_of4_pres_wc` `hmOf4PresWc`, `lock_slot` `AxLockRace2.LockSlot`
(`SlotPreWx` … `SlotAcqRx` ↦ `slotPreWx` … `slotAcqRx`), `slot_resource` `slotResource`,
`lock_excludes_racing_write` `lockExcludesRacingWrite`,
`lock_excludes_racing_write_conclusion` `lockExcludesRacingWriteConclusion`,
`lock_slice_sound_admits_no_racing_writer` `lockSliceSoundAdmitsNoRacingWriter`.

**Dropped:** nothing (no downstream weak file uses this one; all ported).
-/
import Weak.AxLockRace
import Weak.AxLockAdeq2
import Iris.ProofMode

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp

/-! # 1. Bookkeeping generalised from 4 to 5 events -/

abbrev AxLockRace2.wRel4 (i_A : Agent) (k_rel : Nat) : Geid := (i_A, k_rel)
abbrev AxLockRace2.acq4 (i_B : Agent) (k_acq : Nat) : Geid := (i_B, k_acq)
def AxLockRace2.Hh4 (w_x : Geid) (vx : BitVec 8) : List Hent := [(w_x, vx)]
def AxLockRace2.L44 (i_A i_B : Agent) (k_rel k_acq : Nat) (w_x r_x : Geid) : List Geid :=
  [w_x, AxLockRace2.wRel4 i_A k_rel, AxLockRace2.acq4 i_B k_acq, r_x]
/-- `w_c` inserted; the "any position" is realised by `Hgmo_perm5` being a permutation. -/
def AxLockRace2.L45 (i_A i_B : Agent) (k_rel k_acq : Nat) (w_x r_x w_c : Geid) : List Geid :=
  w_c :: AxLockRace2.L44 i_A i_B k_rel k_acq w_x r_x

section bookkeeping5
variable (GD : Gdexec) (i_A i_B : Agent) (k_rel k_acq : Nat) (w_x r_x w_c : Geid)

theorem L45Nodup (Hcons : rvwmoCatConsistent GD)
    (Hgmo_perm5 : (AxLockRace2.L45 i_A i_B k_rel k_acq w_x r_x w_c).Perm GD.gdG.gxGmo) :
    (AxLockRace2.L45 i_A i_B k_rel k_acq w_x r_x w_c).Nodup :=
  Hgmo_perm5.nodup_iff.2 Hcons.1.1

theorem L45WcNotinL44 (Hcons : rvwmoCatConsistent GD)
    (Hgmo_perm5 : (AxLockRace2.L45 i_A i_B k_rel k_acq w_x r_x w_c).Perm GD.gdG.gxGmo) :
    w_c ∉ AxLockRace2.L44 i_A i_B k_rel k_acq w_x r_x :=
  (List.nodup_cons.1 (L45Nodup GD i_A i_B k_rel k_acq w_x r_x w_c Hcons Hgmo_perm5)).1

theorem L45NeWcWx (Hcons : rvwmoCatConsistent GD)
    (Hgmo_perm5 : (AxLockRace2.L45 i_A i_B k_rel k_acq w_x r_x w_c).Perm GD.gdG.gxGmo) :
    w_c ≠ w_x := by
  intro h
  apply L45WcNotinL44 GD i_A i_B k_rel k_acq w_x r_x w_c Hcons Hgmo_perm5
  simp [AxLockRace2.L44, h]

theorem L45NeWcWrel4 (Hcons : rvwmoCatConsistent GD)
    (Hgmo_perm5 : (AxLockRace2.L45 i_A i_B k_rel k_acq w_x r_x w_c).Perm GD.gdG.gxGmo) :
    w_c ≠ AxLockRace2.wRel4 i_A k_rel := by
  intro h
  apply L45WcNotinL44 GD i_A i_B k_rel k_acq w_x r_x w_c Hcons Hgmo_perm5
  simp [AxLockRace2.L44, h]

theorem L45NeWcAcq4 (Hcons : rvwmoCatConsistent GD)
    (Hgmo_perm5 : (AxLockRace2.L45 i_A i_B k_rel k_acq w_x r_x w_c).Perm GD.gdG.gxGmo) :
    w_c ≠ AxLockRace2.acq4 i_B k_acq := by
  intro h
  apply L45WcNotinL44 GD i_A i_B k_rel k_acq w_x r_x w_c Hcons Hgmo_perm5
  simp [AxLockRace2.L44, h]

theorem L45NeWcRx (Hcons : rvwmoCatConsistent GD)
    (Hgmo_perm5 : (AxLockRace2.L45 i_A i_B k_rel k_acq w_x r_x w_c).Perm GD.gdG.gxGmo) :
    w_c ≠ r_x := by
  intro h
  apply L45WcNotinL44 GD i_A i_B k_rel k_acq w_x r_x w_c Hcons Hgmo_perm5
  simp [AxLockRace2.L44, h]

theorem inL45
    (Hgmo_perm5 : (AxLockRace2.L45 i_A i_B k_rel k_acq w_x r_x w_c).Perm GD.gdG.gxGmo)
    (e : Geid) : e ∈ GD.gdG.gxGmo →
      e = w_c ∨ e = w_x ∨ e = AxLockRace2.wRel4 i_A k_rel ∨ e = AxLockRace2.acq4 i_B k_acq ∨
        e = r_x := by
  intro He
  have He' := Hgmo_perm5.mem_iff.2 He
  unfold AxLockRace2.L45 AxLockRace2.L44 at He'
  simpa only [List.mem_cons, List.not_mem_nil, or_false] using He'

/-- `Hwonly4` ↦ `Hwonly5`: two writers to `x`, not one. -/
theorem Hwonly5 (L x : Int) (Hxl : x ≠ L) (Hcons : rvwmoCatConsistent GD)
    (Hsingle_rel : ∀ a' v', gwritesByte GD.gdG (AxLockRace2.wRel4 i_A k_rel) a' v' → a' = L)
    (Hsingle_acq : ∀ a' v', gwritesByte GD.gdG (AxLockRace2.acq4 i_B k_acq) a' v' → a' = L)
    (Hnw : gisW GD.gdG r_x = false)
    (Hgmo_perm5 : (AxLockRace2.L45 i_A i_B k_rel k_acq w_x r_x w_c).Perm GD.gdG.gxGmo) :
    ∀ w v, gwritesByte GD.gdG w x v → w = w_x ∨ w = w_c := by
  intro w v Hw
  have Hgmo := gwritesByteGmo GD.gdG w x v Hcons.1 Hw
  rcases inL45 GD i_A i_B k_rel k_acq w_x r_x w_c Hgmo_perm5 w Hgmo with h | h | h | h | h
  · exact Or.inr h
  · exact Or.inl h
  · rw [h] at Hw
    exact absurd (Hsingle_rel x v Hw) Hxl
  · rw [h] at Hw
    exact absurd (Hsingle_acq x v Hw) Hxl
  · rw [h] at Hw
    have hw := AxProt.gwritesByteGisW _ _ _ _ Hw
    rw [Hnw] at hw
    cases hw

/-- `DOf4`/`hmOf4`: literally AxLockAdeq's own definitions. -/
def AxLockRace2.DOf4 (s : GSet Geid) : GSet Geid :=
  if AxLockRace2.acq4 i_B k_acq ∈ s then {AxLockRace2.wRel4 i_A k_rel} else ∅

def AxLockRace2.hmOf4 (vx : BitVec 8) (s : GSet Geid) : GMapF Geid (List Hent) :=
  if AxLockRace2.wRel4 i_A k_rel ∈ s then
    {[AxLockRace2.wRel4 i_A k_rel := AxLockRace2.Hh4 w_x vx]}
  else ∅

theorem DOf4PresWc (Hcons : rvwmoCatConsistent GD)
    (Hgmo_perm5 : (AxLockRace2.L45 i_A i_B k_rel k_acq w_x r_x w_c).Perm GD.gdG.gxGmo)
    (s : GSet Geid) :
    AxLockRace2.DOf4 i_A i_B k_rel k_acq (({w_c} : GSet Geid) ∪ s) =
      AxLockRace2.DOf4 i_A i_B k_rel k_acq s := by
  have hne := L45NeWcAcq4 GD i_A i_B k_rel k_acq w_x r_x w_c Hcons Hgmo_perm5
  unfold AxLockRace2.DOf4
  by_cases h : AxLockRace2.acq4 i_B k_acq ∈ s
  · rw [if_pos ((AxLockAdeq.memUnionNe hne).2 h), if_pos h]
  · rw [if_neg (fun h' => h ((AxLockAdeq.memUnionNe hne).1 h')), if_neg h]

theorem hmOf4PresWc (vx : BitVec 8) (Hcons : rvwmoCatConsistent GD)
    (Hgmo_perm5 : (AxLockRace2.L45 i_A i_B k_rel k_acq w_x r_x w_c).Perm GD.gdG.gxGmo)
    (s : GSet Geid) :
    AxLockRace2.hmOf4 i_A k_rel w_x vx (({w_c} : GSet Geid) ∪ s) =
      AxLockRace2.hmOf4 i_A k_rel w_x vx s := by
  have hne := L45NeWcWrel4 GD i_A i_B k_rel k_acq w_x r_x w_c Hcons Hgmo_perm5
  unfold AxLockRace2.hmOf4
  by_cases h : AxLockRace2.wRel4 i_A k_rel ∈ s
  · rw [if_pos ((AxLockAdeq.memUnionNe hne).2 h), if_pos h]
  · rw [if_neg (fun h' => h ((AxLockAdeq.memUnionNe hne).1 h')), if_neg h]

end bookkeeping5

/-! # 2. THE MUTUAL-EXCLUSION LEMMA: all four non-vacuous slots, one case split -/

/-- The four positions of `w_c` relative to `L44` where the address-`x` token `γ` is held
elsewhere; the gmo-after-`r_x` slot is vacuous and deliberately absent. -/
inductive AxLockRace2.LockSlot where
  /-- before `w_x`: the raw initial token. -/
  | slotPreWx
  /-- between `w_x` and `w_rel4`: `ownedWriteExcluded`'s own example. -/
  | slotWxWrel
  /-- between `w_rel4` and `acq4`: folded into `ΦLock'`/`protInvLock'`. -/
  | slotWrelAcq
  /-- between `acq4` and `r_x`: the token held by `acq4`. -/
  | slotAcqRx

section exclusion
variable {GF : BundledGFunctors} [AxlogG GF Hent] [AxLockG GF]

def slotResource (γ γc : GName) (L x : Int) (GD : Gdexec) (i_B : Agent) (k_acq : Nat)
    (w_x : Geid) (vx : BitVec 8) (slot : AxLockRace2.LockSlot)
    (s D : GSet Geid) (hm : GMapF Geid (List Hent)) : IProp GF :=
  match slot with
  | .slotPreWx => histAuth γ x 1 ([] : List Hent)
  | .slotWxWrel => tokTie GD γ x (AxLockRace2.Hh4 w_x vx) {[w_x := (1 : Qp)]}
  | .slotWrelAcq => protInvLock' L x γ γc GD s D hm
  | .slotAcqRx =>
      tokTie GD γ x (AxLockRace2.Hh4 w_x vx) {[AxLockRace2.acq4 i_B k_acq := (1 : Qp)]}

/-- THE LEMMA: whichever slot, a racing write's `histAuth γ x 1 Hl_c` cannot also exist. -/
theorem lockExcludesRacingWrite (γ γc : GName) (L x : Int) (GD : Gdexec) (i_A i_B : Agent)
    (k_rel k_acq : Nat) (w_x : Geid) (vx : BitVec 8)
    (Hwb0 : gwritesByte GD.gdG (AxLockRace2.wRel4 i_A k_rel) L b0)
    (slot : AxLockRace2.LockSlot) (s D : GSet Geid) (hm : GMapF Geid (List Hent))
    (Hl_c : List Hent)
    (Hin : AxLockRace2.wRel4 i_A k_rel ∈ s) (HninD : AxLockRace2.wRel4 i_A k_rel ∉ D)
    (Hhm : get? hm (AxLockRace2.wRel4 i_A k_rel) = some (AxLockRace2.Hh4 w_x vx)) :
    slotResource (GF := GF) γ γc L x GD i_B k_acq w_x vx slot s D hm ∗ histAuth γ x 1 Hl_c ⊢
      False := by
  cases slot with
  | slotPreWx => exact histAuthFullExcl γ x [] Hl_c
  | slotWxWrel => exact ownedWriteExcluded GD γ x _ w_x Hl_c
  | slotWrelAcq =>
      exact protInvLockWrelSlotExcl L x γ γc GD s D hm (AxLockRace2.wRel4 i_A k_rel)
        (AxLockRace2.Hh4 w_x vx) Hl_c Hin HninD Hhm Hwb0
  | slotAcqRx => exact ownedWriteExcluded GD γ x _ (AxLockRace2.acq4 i_B k_acq) Hl_c

/-- Ex-falso corollary in the read-value shape. -/
theorem lockExcludesRacingWriteConclusion (γ γc : GName) (L x : Int) (GD : Gdexec)
    (i_A i_B : Agent) (k_rel k_acq : Nat) (w_x r_x : Geid) (vx : BitVec 8)
    (Hwb0 : gwritesByte GD.gdG (AxLockRace2.wRel4 i_A k_rel) L b0)
    (slot : AxLockRace2.LockSlot) (s D : GSet Geid) (hm : GMapF Geid (List Hent))
    (Hl_c : List Hent)
    (Hin : AxLockRace2.wRel4 i_A k_rel ∈ s) (HninD : AxLockRace2.wRel4 i_A k_rel ∉ D)
    (Hhm : get? hm (AxLockRace2.wRel4 i_A k_rel) = some (AxLockRace2.Hh4 w_x vx)) :
    slotResource (GF := GF) γ γc L x GD i_B k_acq w_x vx slot s D hm ∗ histAuth γ x 1 Hl_c ⊢
      ⌜∀ t v, greadsByte GD.gdG r_x x t v → v = vx⌝ :=
  (lockExcludesRacingWrite γ γc L x GD i_A i_B k_rel k_acq w_x vx Hwb0 slot s D hm Hl_c
    Hin HninD Hhm).trans false_elim

end exclusion

/-! # 4. THE POSITIVE COROLLARY: `lockSliceSound''`, re-exported by name -/

theorem lockSliceSoundAdmitsNoRacingWriter : type_of% @lockSliceSound'' := @lockSliceSound''

end Weak
