/-
Weak/Prom: **track (a), the concurrent language over the timestamp schedule** (stage S4a; plan rev 7
`~/dev/weak-orch/promising/plan.md` §3 "Schedule lemma", "`stage`, defined once", "Claim (frontier)"; §2 "A0 is per
hart, so the tracks need more" [R2.s11]).

Track (a)'s frontier rule and its invariants need cross-hart schedule knowledge, so its adequacy is CONCURRENT: one
iris-lean thread per hart, all in one Iris world, over a shared language state.

* `CSt` — the shared state: every hart's exact `(ws, P, τ)` (plan §2 `hartSt h ws P τ`).
* `wfr ws = stFloor ws = max vcap vwNew` — the hart's WRITE FRONTIER `WF(h) := max(vwNew, vcap)` (plan §3 "Claim
  (frontier)").
* `fulAt σ t` — timestamp `t` is fulfilled: some hart's trace has a fulfil entry at `t`.  On machine v2 every message
  is non-A/D (no A/D class, [OWN.P3]), so the plan's "stage ≥ s" is "every `t ≤ s` is fulfilled": `stageGe σ s`.
* `fOk M σ h` — THE FRONTIER CLAIM of hart `h` (plan §3): `WF(h) ≥ s ⊢ stage ≥ s`, i.e. every timestamp `t ≤ WF(h)`
  (`t ≤ |M|`) is fulfilled.
* `cstep` — ONE HART STEP of the concurrent language: one machine-v2 state step of hart `w.h` against the fixed log
  `M` (as `hstep`, CoreWp.lean), allowed only if the hart's frontier claim holds AFTER the step (`fOk`).  The
  schedule lemma (OwnASched.lean) shows that every valid run is an execution of this guarded language: the
  timestamp-ordered schedule keeps every hart's claim; the claim is the plan's "stage" invariant, stated
  as a property of the state (the guard), so the Iris model is NOT run-parameterised (R-a2).
* `post_floor_le`, `floor_le_fulPv` — the two view facts the schedule needs: a fulfil's pre-view contains the
  frontier (`fulfilVpre` contains `vcap ⊔ vwNew`, plan §3), and the frontier after a fulfil at `t` is at most `t`.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.CoreKitV

namespace Weak.Prom.OA

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.PF
open PLabel
open Iris Iris.ProgramLogic

variable {P D V : Type}

/-! ## 1. The shared state, the frontier, the claim -/

/-- THE SHARED STATE of the concurrent language: every hart's exact state, promise set and trace. -/
abbrev CSt : Type := Nat → HSt

/-- Update one hart's component. -/
def updS (σ : CSt) (h : Nat) (x : HSt) : CSt := fun k => if k = h then x else σ k

theorem updS_self (σ : CSt) (h : Nat) (x : HSt) : updS σ h x h = x := by simp [updS]

theorem updS_same (σ : CSt) (h : Nat) : updS σ h (σ h) = σ := by
  funext k; by_cases hk : k = h <;> simp [updS, hk]

theorem updS_ne (σ : CSt) {h k : Nat} (x : HSt) (hk : k ≠ h) : updS σ h x k = σ k := by simp [updS, hk]

/-- THE WRITE FRONTIER `WF(h) := max(vwNew, vcap)` (plan §3 "Claim (frontier)"). -/
abbrev wfr (ws : PState) : Nat := stFloor ws

/-- Timestamp `t` is FULFILLED in `σ`: some hart's trace has a fulfil entry at `t`. -/
def fulAt (σ : CSt) (t : Nat) : Prop := ∃ h, ∃ e ∈ (σ h).2.2, e.2 = some t

/-- `stage ≥ s` (plan §3 "`stage`, defined once": the largest `k` with every non-A/D `t ≤ k` fulfilled; machine v2
has no A/D class, so every message counts). -/
def stageGe (M : List PMsg) (σ : CSt) (s : Nat) : Prop := ∀ t, 1 ≤ t → t ≤ M.length → t ≤ s → fulAt σ t

/-- THE FRONTIER CLAIM of hart `h` (plan §3): `WF(h) ≥ s ⊢ stage ≥ s`. -/
def fOk (M : List PMsg) (σ : CSt) (h : Nat) : Prop := stageGe M σ (wfr (σ h).1)

theorem stageGe_mono {M : List PMsg} {σ : CSt} {s s' : Nat} (h : stageGe M σ s) (hs : s' ≤ s) : stageGe M σ s' :=
  fun t h1 h2 h3 => h t h1 h2 (Nat.le_trans h3 hs)

/-- A hart step only adds a trace entry: fulfilled timestamps stay fulfilled. -/
theorem fulAt_updS {σ : CSt} {h : Nat} {ws' : PState} {pr' : GSet Nat} {e : PEv} {t : Nat} (hf : fulAt σ t) :
    fulAt (updS σ h (ws', pr', (σ h).2.2 ++ [e])) t := by
  obtain ⟨k, e', he', ht⟩ := hf
  refine ⟨k, e', ?_, ht⟩
  by_cases hk : k = h
  · subst hk; rw [updS_self]; exact List.mem_append_left _ he'
  · rw [updS_ne σ _ hk]; exact he'

theorem stageGe_updS {M : List PMsg} {σ : CSt} {h : Nat} {ws' : PState} {pr' : GSet Nat} {e : PEv} {s : Nat}
    (hs : stageGe M σ s) : stageGe M (updS σ h (ws', pr', (σ h).2.2 ++ [e])) s :=
  fun t h1 h2 h3 => fulAt_updS (hs t h1 h2 h3)

/-! ## 2. The concurrent language -/

/-- The thread expression: a running hart (its world, hence its index `w.h`, and program state), or a value. -/
inductive CExpr (P D V : Type) where
  | run (w : HW P D V) (s : P)
  | ret (v : V)

/-- ONE HART STEP of the concurrent language (plan §3): hart `w.h`'s machine-v2 state step against `M`, with the
label its program half emits (any fabric values), appending the trace entry; allowed only if the hart's frontier
claim holds after the step.  Or the step to the hart's value. -/
inductive cstep : CExpr P D V × CSt → List Unit → CExpr P D V × CSt × List (CExpr P D V) → Prop
  | lab (w : HW P D V) (s : P) (σ : CSt) (l : PLabel) (ots : Option Nat) (s' : P) (ws' : PState)
      (pr' : GSet Nat) (d d' : D) :
      w.pstep s d l s' d' → memStep w.img w.M w.h (σ w.h).2.1 (σ w.h).1 l ots ws' pr' →
      fOk w.M (updS σ w.h (ws', pr', (σ w.h).2.2 ++ [(l, ots)])) w.h →
      cstep (.run w s, σ) [] (.run w s', updS σ w.h (ws', pr', (σ w.h).2.2 ++ [(l, ots)]), [])
  | fin (w : HW P D V) (s : P) (σ : CSt) (v : V) :
      w.pdone s = some v → cstep (.run w s, σ) [] (.ret v, σ, [])

instance : PrimStep (CExpr P D V) CSt (List Unit) := ⟨cstep⟩

/-- The value of an expression. -/
def CExpr.toV : CExpr P D V → Option V
  | .ret v => some v
  | .run _ _ => none

instance : ToVal (CExpr P D V) V where
  toVal := CExpr.toV
  ofVal v := .ret v
  coe_of_toVal_eq_some {e v} h := by
    cases e with
    | run => cases h
    | ret v' => cases h; rfl
  toVal_coe _ := rfl

instance : Language (CExpr P D V) CSt Unit V where
  val_stuck h := by cases h <;> rfl

/-! ## 3. The two view facts of the schedule -/

/-- A fulfil's pre-view contains the frontier (plan §3: "Its pre-view contains `vcap ⊔ vwNew` (`fulfilVpre`)"). -/
theorem floor_le_fulPv {img : Image} {log : List PMsg} {i : Nat} {prom : GSet Nat} {ws : PState} {l : PLabel}
    {t : Nat} {ws' : PState} {prom' : GSet Nat} (h : memStep img log i prom ws l (some t) ws' prom') :
    stFloor ws ≤ fulPv ws l := by
  cases h with
  | store aq rl _ _ asrc vsrc =>
    obtain ⟨_, _, h3, h4, _⟩ := PF.stPreA_ge ws aq rl (srcsView ws asrc) (srcsView ws vsrc)
    simp only [fulPv]; unfold stFloor; omega
  | rmw aq rl base tvs _ asrc vsrc =>
    have h1 := loadRun_floor ws aq false (srcsView ws asrc) base tvs
    obtain ⟨_, _, h3, h4, _⟩ := PF.stPre_ge (loadRun ws aq false (srcsView ws asrc) base tvs) rl
      (srcsView ws asrc) (srcsView ws vsrc)
    simp only [fulPv]; unfold stFloor at h1 ⊢; omega
  | amoSt rl _ _ asrc vsrc =>
    obtain ⟨_, _, h3, h4, _⟩ := PF.stPre_ge ws rl (srcsView ws asrc) (srcsView ws vsrc)
    simp only [fulPv]; unfold stFloor; omega
  | sc aq rl _ _ asrc vsrc _ R hR =>
    obtain ⟨_, _, h3, h4, _⟩ := PF.stPreA_ge ws aq rl (srcsView ws asrc) (srcsView ws vsrc)
    simp only [fulPv, hR]; unfold stFloor; omega
  | cmo _ _ _ asrc =>
    obtain ⟨_, _, h3, h4, _⟩ := PF.stPre_ge ws false (srcsView ws asrc) 0
    simp only [fulPv]; unfold stFloor; omega

/-- The frontier before a fulfil at `t` is below `t` (EXT through `floor_le_fulPv`). -/
theorem floor_lt_ts {img : Image} {log : List PMsg} {i : Nat} {prom : GSet Nat} {ws : PState} {l : PLabel}
    {t : Nat} {ws' : PState} {prom' : GSet Nat} (h : memStep img log i prom ws l (some t) ws' prom') :
    stFloor ws < t :=
  Nat.lt_of_le_of_lt (floor_le_fulPv h) (fulPv_lt h)

/-- THE FRONTIER AFTER A FULFIL AT `t` IS AT MOST `t`: the post-state's `vcap` and `vwNew` are the pre-view's, raised
at most to `t` (an acquire's `acqPost`/`amoPost`, M0 (i)). -/
theorem post_floor_le {img : Image} {log : List PMsg} {i : Nat} {prom : GSet Nat} {ws : PState} {l : PLabel}
    {t : Nat} {ws' : PState} {prom' : GSet Nat} (h : memStep img log i prom ws l (some t) ws' prom') :
    stFloor ws' ≤ t := by
  have hlt := floor_lt_ts h
  have hpv := fulPv_lt h
  cases h with
  | store aq rl base data asrc vsrc =>
    obtain ⟨_, _, _, _, h5, h6, _⟩ := storeRun_mono ws rl (srcsView ws asrc)
      (max (srcsView ws asrc) (srcsView ws vsrc)) base data.length t
    have h1 := PF.stPreA_ge ws aq rl (srcsView ws asrc) (srcsView ws vsrc)
    simp only [fulPv] at hpv
    unfold stFloor at hlt ⊢
    unfold acqPost; simp only
    rw [h6]
    split
    · rw [h5]; omega
    · rw [h5]; omega
  | rmw aq rl base tvs data asrc vsrc =>
    obtain ⟨_, _, _, _, h5, h6, _⟩ := storeRun_mono (loadRun ws aq false (srcsView ws asrc) base tvs) rl
      (srcsView ws asrc) t base data.length t
    have h2 := (PF.stPre_ge (loadRun ws aq false (srcsView ws asrc) base tvs) rl (srcsView ws asrc)
      (srcsView ws vsrc))
    have h3 : (loadRun ws aq false (srcsView ws asrc) base tvs).wVwNew ≤
        stPre (loadRun ws aq false (srcsView ws asrc) base tvs) rl (srcsView ws asrc) (srcsView ws vsrc) := by
      unfold stPre; split <;> omega
    simp only [fulPv] at hpv
    unfold stFloor
    unfold amoPost; simp only
    rw [h6]
    split
    · rw [h5]; omega
    · rw [h5]; omega
  | amoSt rl base data asrc vsrc R =>
    obtain ⟨_, _, _, _, h5, h6, _⟩ := storeRun_mono ws rl (srcsView ws asrc) t base data.length t
    have h2 := (PF.stPre_ge ws rl (srcsView ws asrc) (srcsView ws vsrc))
    simp only [fulPv] at hpv
    unfold stFloor at hlt ⊢
    unfold amoPost; simp only
    rw [h6]
    split
    · rw [h5]; omega
    · rw [h5]; omega
  | sc aq rl base data asrc vsrc _ R hR =>
    obtain ⟨_, _, _, _, h5, h6, _⟩ := storeRun_mono ws rl (srcsView ws asrc) t base data.length t
    have h1 := PF.stPreA_ge ws aq rl (srcsView ws asrc) (srcsView ws vsrc)
    simp only [fulPv, hR] at hpv
    unfold stFloor at hlt ⊢
    unfold acqPost; simp only
    rw [h6]
    split
    · rw [h5]; omega
    · rw [h5]; omega
  | cmo k base len asrc =>
    have := cohRaise_floor ws base len t
    have h2 := (PF.stPre_ge ws false (srcsView ws asrc) 0)
    simp only [fulPv] at hpv
    unfold stFloor at hlt ⊢
    unfold cmoPost; simp only
    omega

end Weak.Prom.OA
