/-
Weak/Prom: **SchedAD — track (a)'s concurrent language over E-c's A/D machine variant** (owner ruling [OWN.P14];
G4-review3.md §5 A-2, §6 item 2; plan rev 7 `~/dev/weak-orch/promising/plan.md` §3 "Schedule lemma" rev 5,
"`stage`, defined once", "Claim (frontier)", "Why A/D messages are excluded"; machine: AdMachine.lean, M20).

OwnALang.lean's language with the variant's memory half `Ad.memStepV`:

* `stageGeV M σ s` — plan §3 verbatim: "`stage` is the largest k such that every NON-A/D timestamp ≤ k has completed
  its fulfil".  An A/D timestamp (`Ad.adAt`, class `WCad`) is never required: `stage` EXCLUDES A/D messages.
* `fOkV` — the frontier claim `WF(h) ≥ s ⊢ stage ≥ s` over `stageGeV` ("restated over the hart's next non-A/D
  fulfil", plan §3).
* `cstepV` — one hart step against the fixed `M`: a machine-v2 label `.v l` (including the variant's fetch arm,
  `fetchViewV`/`ownDoneV`), GUARDED by `fOkV` after the step, exactly as `cstep`; an A/D update `.ad` (M20 (2),
  (3): `ws` unchanged, the promise consumed), NOT GUARDED: "A/D fulfils of h, wherever they fall, do not enter the
  argument" (plan §3).  The A/D step adds no entry to the hart's (v2-label) trace in the shared state: `fulAt`
  therefore sees only non-A/D fulfils, the only ones `stage` counts.  The value step as `cstep.fin`.
* `adExactV`, `PO_adV` — CoreDefs.lean's `adExact`/`PO_ad` with the variant's A/D test `isAdV m := m.cls =
  PClass.ad` in place of v2's constantly-false `PMsg.isAd` (CoreDefs.lean §3 "the definitions are the extension
  point").
* View facts: `floorsV_mono` (no arm lowers `WF`; the A/D and fetch arms keep it), `memStepV_v_some` (a `.v`
  fulfil is a machine-v2 fulfil, so `floor_lt_ts`/`post_floor_le` apply), `memStepV_ad_at` (an A/D fulfil's
  timestamp is an A/D message).
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.OwnAAdeq
import Weak.Prom.NfrAd

namespace Weak.Prom.OAd

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.PF Weak.Prom.OA
open PLabel
open Iris Iris.ProgramLogic

variable {P D V : Type}

/-! ## 1. The A/D vocabulary of the variant (CoreDefs.lean §3 with the variant's class test) -/

/-- An A/D message of the variant (M20 (5) class `WCad`, AdMachine.lean `PClass.ad`). -/
def isAdV (m : PMsg) : Prop := m.cls = PClass.ad

/-- `adExact img M` (plan §0) for the variant: A/D messages are determined by `M`. -/
def adExactV (img : Image) (M : List PMsg) : Prop :=
  ∀ t m, 1 ≤ t → t ≤ M.length → msgAt M t = some m → isAdV m → adData img M t m.pa m.data

/-- `PO_ad π img M` (plan §0, NA-14b) for the variant: the protocols are closed under the A/D updates. -/
def PO_adV (π : Proto) (img : Image) (M : List PMsg) : Prop :=
  ∀ t m, 1 ≤ t → t ≤ M.length → msgAt M t = some m → isAdV m → Valid π img M (t - 1) →
    adData img M t m.pa m.data → π.okMsg m

theorem adAt_msgAt {M : List PMsg} {t : Nat} (h1 : 1 ≤ t) : Ad.adAt M t ↔ ∃ m, msgAt M t = some m ∧ isAdV m := by
  obtain ⟨k, rfl⟩ : ∃ k, t = k + 1 := ⟨t - 1, by omega⟩
  simp [Ad.adAt, msgAt, isAdV]

/-- PO-ad and adExact give `protoOk` of every A/D timestamp (plan §3: "an A/D t is valid by PO-ad from Valid(t−1),
whether or not it has been fulfilled yet"). -/
theorem protoOk_ad {π : Proto} {img : Image} {M : List PMsg} (had : PO_adV π img M) (hex : adExactV img M)
    {t : Nat} (h1 : 1 ≤ t) (h2 : t ≤ M.length) (hat : Ad.adAt M t) : protoOk π img M t := by
  obtain ⟨m0, hm0, hc0⟩ := (adAt_msgAt h1).1 hat
  intro m hm hv
  rw [hm0] at hm; cases hm
  exact had t m0 h1 h2 hm0 hc0 hv (hex t m0 h1 h2 hm0 hc0)

/-! ## 2. `stage` over non-A/D timestamps, the frontier claim -/

/-- `stage ≥ s` (plan §3 "`stage`, defined once"): every NON-A/D timestamp `t ≤ s` is fulfilled. -/
def stageGeV (M : List PMsg) (σ : CSt) (s : Nat) : Prop :=
  ∀ t, 1 ≤ t → t ≤ M.length → t ≤ s → ¬ Ad.adAt M t → fulAt σ t

/-- THE FRONTIER CLAIM of hart `h` (plan §3, restated over non-A/D fulfils): `WF(h) ≥ s ⊢ stage ≥ s`. -/
def fOkV (M : List PMsg) (σ : CSt) (h : Nat) : Prop := stageGeV M σ (wfr (σ h).1)

theorem stageGeV_updS {M : List PMsg} {σ : CSt} {h : Nat} {ws' : PState} {pr' : GSet Nat} {e : PEv} {s : Nat}
    (hs : stageGeV M σ s) : stageGeV M (updS σ h (ws', pr', (σ h).2.2 ++ [e])) s :=
  fun t h1 h2 h3 h4 => fulAt_updS (hs t h1 h2 h3 h4)

/-- A step that changes no trace keeps every fulfilled timestamp. -/
theorem fulAt_updS_keep {σ : CSt} {h : Nat} {ws' : PState} {pr' : GSet Nat} {t : Nat} :
    fulAt (updS σ h (ws', pr', (σ h).2.2)) t ↔ fulAt σ t := by
  constructor
  · rintro ⟨k, e, he, ht⟩
    by_cases hk : k = h
    · subst hk; rw [updS_self] at he; exact ⟨k, e, he, ht⟩
    · rw [updS_ne σ _ hk] at he; exact ⟨k, e, he, ht⟩
  · rintro ⟨k, e, he, ht⟩
    by_cases hk : k = h
    · subst hk; exact ⟨k, e, by rw [updS_self]; exact he, ht⟩
    · exact ⟨k, e, by rw [updS_ne σ _ hk]; exact he, ht⟩

/-! ## 3. The concurrent language over the variant -/

/-- THE HART'S WORLD over the variant: the program half emits `Ad.VLabel`s. -/
structure HWV (P D V : Type) where
  pstep : P → D → Ad.VLabel → P → D → Prop
  pdone : P → Option V
  img : Image
  M : List PMsg
  h : Nat

/-- The thread expression. -/
inductive CExprV (P D V : Type) where
  | run (w : HWV P D V) (s : P)
  | ret (v : V)

/-- ONE HART STEP over the variant (plan §3): a v2 label, guarded by the frontier claim after the step; an A/D
update, unguarded, which consumes its promise and changes neither `ws` nor the (v2-label) trace; the value step. -/
inductive cstepV : CExprV P D V × CSt → List Unit → CExprV P D V × CSt × List (CExprV P D V) → Prop
  | lab (w : HWV P D V) (s : P) (σ : CSt) (l : PLabel) (ots : Option Nat) (s' : P) (ws' : PState)
      (pr' : GSet Nat) (d d' : D) :
      w.pstep s d (.v l) s' d' → Ad.memStepV w.img w.M w.h (σ w.h).2.1 (σ w.h).1 (.v l) ots ws' pr' →
      fOkV w.M (updS σ w.h (ws', pr', (σ w.h).2.2 ++ [(l, ots)])) w.h →
      cstepV (.run w s, σ) [] (.run w s', updS σ w.h (ws', pr', (σ w.h).2.2 ++ [(l, ots)]), [])
  | ad (w : HWV P D V) (s : P) (σ : CSt) (b : Int) (tvs : List (Nat × BitVec 8)) (data : List (BitVec 8))
      (ots : Option Nat) (s' : P) (pr' : GSet Nat) (d d' : D) :
      w.pstep s d (.ad b tvs data) s' d' →
      Ad.memStepV w.img w.M w.h (σ w.h).2.1 (σ w.h).1 (.ad b tvs data) ots (σ w.h).1 pr' →
      cstepV (.run w s, σ) [] (.run w s', updS σ w.h ((σ w.h).1, pr', (σ w.h).2.2), [])
  | fin (w : HWV P D V) (s : P) (σ : CSt) (v : V) :
      w.pdone s = some v → cstepV (.run w s, σ) [] (.ret v, σ, [])

instance : PrimStep (CExprV P D V) CSt (List Unit) := ⟨cstepV⟩

/-- The value of an expression. -/
def CExprV.toV : CExprV P D V → Option V
  | .ret v => some v
  | .run _ _ => none

instance : ToVal (CExprV P D V) V where
  toVal := CExprV.toV
  ofVal v := .ret v
  coe_of_toVal_eq_some {e v} h := by
    cases e with
    | run => cases h
    | ret v' => cases h; rfl
  toVal_coe _ := rfl

instance : Language (CExprV P D V) CSt Unit V where
  val_stuck h := by cases h <;> rfl

/-! ## 4. View facts of the variant's arms -/

section views

variable {img : Image} {log : List PMsg} {i : Nat} {prom : GSet Nat} {ws : PState} {ots : Option Nat}
  {ws' : PState} {prom' : GSet Nat}

/-- No arm lowers the write frontier (the fetch and A/D arms keep it: M20 (3), no view effect). -/
theorem floorsV_mono {l : Ad.VLabel} (h : Ad.memStepV img log i prom ws l ots ws' prom') :
    stFloor ws ≤ stFloor ws' := by
  cases h with
  | v2 _ _ _ _ hm _ => exact floors_mono hm
  | fetch => exact Nat.le_refl _
  | ad => exact Nat.le_refl _

/-- A `.v` fulfil is a machine-v2 fulfil (the variant's fetch arm fulfils nothing). -/
theorem memStepV_v_some {l : PLabel} {t : Nat} (h : Ad.memStepV img log i prom ws (.v l) (some t) ws' prom') :
    memStep img log i prom ws l (some t) ws' prom' := by
  cases h with
  | v2 _ _ _ _ hm _ => exact hm

/-- The timestamp an A/D update fulfils is an A/D message. -/
theorem memStepV_ad_at {b : Int} {tvs : List (Nat × BitVec 8)} {d : List (BitVec 8)} {t : Nat}
    (h : Ad.memStepV img log i prom ws (.ad b tvs d) (some t) ws' prom') : Ad.adAt log t := by
  obtain ⟨ts, hts, -, -, -, -, -, hm, -⟩ := Ad.memStepV_ad_inv h
  cases hts
  exact ⟨_, hm, rfl⟩

end views

end Weak.Prom.OAd
