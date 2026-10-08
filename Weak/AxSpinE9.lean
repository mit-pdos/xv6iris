/-
Weak: **a boolean CHECKER for `AxSpinE3.FirstRd`** (concrete states), and its transfer to every
register file agreeing off the pins.

Rocq: `iris/AxSpinE9.v` @ xxvzwolszwmp.

## The Rocq header, in substance

`frb img p q m t`: walks the tree `m` from `t` the way `FirstRd` does — register reads answered
from `t` (BOTH answers of every pin read), register writes applied, silent nodes skipped — and at
the FIRST plain RAM read checks `p` on its (address, width); a return checks `q`.
`frbSound`: `frb img p q m t = true → FirstRd img (fun a n => p a n = true) (fun t' => q t' = true)
m t`.  `frbAgree`: with `q` constant, the verdict does not depend on `t`'s pins / memory / device
state.  Intended for the off-row twin certificate (AxSpinE8d): the REAL fetch node after mycpu's
c.ret, at a concrete state, by `decide +kernel`.

## Deviations from Rocq

1. O2 STAGE C (as `AxSpinE3` deviation 1): `frb` takes the image `img` first.  A FETCH
   (`akIfetch = true`, not a device address) is not a first read: with image bytes it CONTINUES
   with them (`FirstRd.frIf`), without image bytes it is accepted (`frNf`: no pinned step).  Only
   non-fetch RAM reads are checked against `p` (`frMrd` takes `akIfetch = false`).
2. THE PINS (`AxRunClose` deviation 1): `seip_reg` ↦ `AxRunClose.pinReg` (`sig_seip` or
   `sig_meip`).  A pin read is answered both-0 then both-1 (as `AxSymEngine2.evb`): the
   continuation gets `((t.regs.set .sig_seip b).set .sig_meip b) r`; a pin write fails.
   `frbAgree` takes `regsAgree AxRunClose.pinReg t'.regs t.regs`.
3. Q7: an `instrAnnounce` whose word is an sfence.vma (`sfAnnB n w = true`) fails (`frIa` takes
   `sfAnnB n w = false`).
4. LEAN-SAIL: `frb` is on `SailM Unit`; a failure node `.impure (.error _) _` is ACCEPTED (it has
   no step: `FirstRd.frExt`; Rocq's `M` has no such node).  Types as `AxSpinE3` deviation 5
   (`mstate` ↦ `ExecSt`, `register_lookup r s.(sregs)` ↦ `s.regs r`, `set_reg` ↦ `setReg`,
   `N.to_nat n` ↦ `n`).

**Rocq → Lean name map.**  `frb` `frb`, `frb_sound` `frbSound`, `frb_agree` `frbAgree`,
`FirstRd_mono` `FirstRdMono`.  Lean-only (file-qualified): `AxSpinE9.pinsSetAgree`.

**Dropped:** nothing (Rocq 4 definitions/lemmas; Lean 4 + 1 Lean-only).
**Not ported:** the `Print Assumptions` lines (the lint's axiom check covers them).
-/
import Weak.AxSpinE3
import Weak.AxSymEngine2

namespace Weak

open MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-- **The boolean `FirstRd` checker** (deviations 1–4). -/
def frb (img : Image) (p : Int → Nat → Bool) (q : ExecSt → Bool) : SailM Unit → ExecSt → Bool
  | .pure _, t => q t
  | .impure (.error _) _, _ => true
  | .impure (.ok o) k, t =>
    match o, k with
    | .regRead r, k =>
      if r = .sig_seip ∨ r = .sig_meip then
        frb img p q (k (((t.regs.set .sig_seip 0#1).set .sig_meip 0#1) r)) t &&
        frb img p q (k (((t.regs.set .sig_seip 1#1).set .sig_meip 1#1) r)) t
      else frb img p q (k (t.regs r)) t
    | .regWrite r v, k =>
      if r = .sig_seip ∨ r = .sig_meip then false else frb img p q (k PUnit.unit) (t.setReg r v)
    | .memRead n _ req, k =>
      if devAddr req.pa then false
      else if (classify req.access_kind).akIfetch then
        match imgBytes img (paZ req.pa) n with
        | some vs => frb img p q (k (.Ok (wordOfBytes n vs, none))) t
        | none => true
      else if (classify req.access_kind).akLatest then false
      else p (paZ req.pa) n
    | .instrAnnounce n w, k => if sfAnnB n w then false else frb img p q (k ()) t
    | .branchAnnounce _ _, k => frb img p q (k ()) t
    | .cacheOp _, k => frb img p q (k ()) t
    | .tlbi _, k => frb img p q (k ()) t
    | .takeException _, k => frb img p q (k ()) t
    | .returnException _, k => frb img p q (k ()) t
    | .translationStart _, k => frb img p q (k ()) t
    | .translationEnd _, k => frb img p q (k ()) t
    | .cycleCount, k => frb img p q (k ()) t
    | .message _, k => frb img p q (k ()) t
    | .getCycleCount, k => frb img p q (k (0 : Nat)) t
    | _, _ => false

theorem frbSound (img : Image) (p : Int → Nat → Bool) (q : ExecSt → Bool) (m : SailM Unit) :
    ∀ t, frb img p q m t = true →
      FirstRd img (fun a n => p a n = true) (fun t' => q t' = true) m t := by
  induction m with
  | pure y => intro t hb; exact .frRet _ hb
  | impure call k ih =>
    intro t hb
    cases call with
    | error e => exact .frExt e k t
    | ok o =>
      cases o
      case regRead r =>
        simp only [frb] at hb
        refine .frRd r k t ?_ ?_
        · intro hp v
          have hp' : r = .sig_seip ∨ r = .sig_meip := hp
          rw [if_pos hp', Bool.and_eq_true] at hb
          rcases hp with rfl | rfl <;> rcases bv1_cases v with rfl | rfl
          · exact ih _ _ (by simpa [RegFile.set_same, RegFile.set_other] using hb.1)
          · exact ih _ _ (by simpa [RegFile.set_same, RegFile.set_other] using hb.2)
          · exact ih _ _ (by simpa [RegFile.set_same] using hb.1)
          · exact ih _ _ (by simpa [RegFile.set_same] using hb.2)
        · intro hp
          have hp' : ¬ (r = .sig_seip ∨ r = .sig_meip) := hp
          rw [if_neg hp'] at hb
          exact ih _ _ hb
      case regWrite r v =>
        simp only [frb] at hb
        by_cases hp : r = .sig_seip ∨ r = .sig_meip
        · rw [if_pos hp] at hb; cases hb
        · rw [if_neg hp] at hb
          exact .frWr r v k t hp (ih _ _ hb)
      case memRead n va req =>
        simp only [frb] at hb
        cases hd : devAddr req.pa
        · cases hf : (classify req.access_kind).akIfetch
          · cases hl : (classify req.access_kind).akLatest
            · simp only [hd, hf, hl, Bool.false_eq_true, ↓reduceIte] at hb
              exact .frMrd n va req k t hd hl hf hb
            · simp [hd, hf, hl] at hb
          · cases hv : imgBytes img (paZ req.pa) n with
            | none => exact .frNf n va req k t hd hf hv
            | some vs =>
              simp only [hd, hf, hv, Bool.false_eq_true, ↓reduceIte] at hb
              exact .frIf n va req k t vs hd hf hv (ih _ _ hb)
        · simp [hd] at hb
      case instrAnnounce n w =>
        simp only [frb] at hb
        cases hs : sfAnnB n w
        · simp only [hs, Bool.false_eq_true, ↓reduceIte] at hb
          exact .frIa n w k t hs (ih _ _ hb)
        · simp [hs] at hb
      case branchAnnounce n a => exact .frBa n a k t (ih _ _ hb)
      case cacheOp c => exact .frCo c k t (ih _ _ hb)
      case tlbi c => exact .frTl c k t (ih _ _ hb)
      case takeException c => exact .frTe c k t (ih _ _ hb)
      case returnException c => exact .frRx c k t (ih _ _ hb)
      case translationStart c => exact .frTs c k t (ih _ _ hb)
      case translationEnd c => exact .frTx c k t (ih _ _ hb)
      case cycleCount => exact .frCc k t (ih _ _ hb)
      case message c => exact .frMsg c k t (ih _ _ hb)
      case getCycleCount => exact .frGcc k t (ih _ _ hb)
      all_goals simp [frb] at hb

/-- (Lean-only) Setting both pins erases the difference between two files agreeing off the
pins. -/
theorem AxSpinE9.pinsSetAgree (rs rs' : RegFile) (b : BitVec 1)
    (Hag : regsAgree AxRunClose.pinReg rs' rs) (r : Register) :
    ((rs.set .sig_seip b).set .sig_meip b) r = ((rs'.set .sig_seip b).set .sig_meip b) r := by
  by_cases hm : r = .sig_meip
  · subst hm; rw [RegFile.set_same, RegFile.set_same]
  · rw [RegFile.set_other _ _ _ _ hm, RegFile.set_other _ _ _ _ hm]
    by_cases hs : r = .sig_seip
    · subst hs; rw [RegFile.set_same, RegFile.set_same]
    · rw [RegFile.set_other _ _ _ _ hs, RegFile.set_other _ _ _ _ hs]
      exact (Hag r (fun h => h.elim hs hm)).symm

/-- With a constant `q`, the verdict depends only on the registers off the pins. -/
theorem frbAgree (img : Image) (p : Int → Nat → Bool) (q : Bool) (m : SailM Unit) :
    ∀ t t' : ExecSt, regsAgree AxRunClose.pinReg t'.regs t.regs →
      frb img p (fun _ => q) m t = frb img p (fun _ => q) m t' := by
  induction m with
  | pure y => intro t t' _; rfl
  | impure call k ih =>
    intro t t' Hag
    cases call with
    | error e => rfl
    | ok o =>
      cases o
      case regRead r =>
        simp only [frb]
        by_cases hp : r = .sig_seip ∨ r = .sig_meip
        · rw [if_pos hp, if_pos hp, AxSpinE9.pinsSetAgree t.regs t'.regs 0#1 Hag r,
            AxSpinE9.pinsSetAgree t.regs t'.regs 1#1 Hag r, ih _ t t' Hag, ih _ t t' Hag]
        · rw [if_neg hp, if_neg hp, Hag r hp]
          exact ih _ t t' Hag
      case regWrite r v =>
        simp only [frb]
        by_cases hp : r = .sig_seip ∨ r = .sig_meip
        · rw [if_pos hp, if_pos hp]
        · rw [if_neg hp, if_neg hp]
          apply ih
          simp only [ExecSt.setReg_regs]
          exact regsAgreeSet _ _ _ r v Hag
      case memRead n va req =>
        simp only [frb]
        cases hd : devAddr req.pa
        · cases hf : (classify req.access_kind).akIfetch
          · rfl
          · cases hv : imgBytes img (paZ req.pa) n with
            | none => rfl
            | some vs => simp only [Bool.false_eq_true, ↓reduceIte]; exact ih _ t t' Hag
        · rfl
      case instrAnnounce n w =>
        simp only [frb]
        cases sfAnnB n w
        · simp only [Bool.false_eq_true, ↓reduceIte]; exact ih _ t t' Hag
        · rfl
      case branchAnnounce n a => exact ih _ t t' Hag
      case cacheOp c => exact ih _ t t' Hag
      case tlbi c => exact ih _ t t' Hag
      case takeException c => exact ih _ t t' Hag
      case returnException c => exact ih _ t t' Hag
      case translationStart c => exact ih _ t t' Hag
      case translationEnd c => exact ih _ t t' Hag
      case cycleCount => exact ih _ t t' Hag
      case message c => exact ih _ t t' Hag
      case getCycleCount => exact ih _ t t' Hag
      all_goals rfl

theorem FirstRdMono (img : Image) (P P' : Int → Nat → Prop) (Q Q' : ExecSt → Prop)
    (m : SailM Unit) (t : ExecSt) :
    (∀ a n, P a n → P' a n) → (∀ t', Q t' → Q' t') →
      FirstRd img P Q m t → FirstRd img P' Q' m t := by
  intro HP HQ h
  induction h with
  | frRet t hq => exact .frRet t (HQ t hq)
  | frRd r k t _ _ ih1 ih2 => exact .frRd r k t (fun hp v => ih1 hp v) (fun hp => ih2 hp)
  | frWr r v k t hp _ ih => exact .frWr r v k t hp ih
  | frMrd n va req k t hd hl hf hP => exact .frMrd n va req k t hd hl hf (HP _ _ hP)
  | frIf n va req k t vs hd hf hv _ ih => exact .frIf n va req k t vs hd hf hv ih
  | frNf n va req k t hd hf hv => exact .frNf n va req k t hd hf hv
  | frIa n w k t hs _ ih => exact .frIa n w k t hs ih
  | frBa n a k t _ ih => exact .frBa n a k t ih
  | frCo c k t _ ih => exact .frCo c k t ih
  | frTl c k t _ ih => exact .frTl c k t ih
  | frTe f k t _ ih => exact .frTe f k t ih
  | frRx a k t _ ih => exact .frRx a k t ih
  | frTs a k t _ ih => exact .frTs a k t ih
  | frTx a k t _ ih => exact .frTx a k t ih
  | frCc k t _ ih => exact .frCc k t ih
  | frMsg a k t _ ih => exact .frMsg a k t ih
  | frGcc k t _ ih => exact .frGcc k t ih
  | frExt e k t => exact .frExt e k t

end Weak
