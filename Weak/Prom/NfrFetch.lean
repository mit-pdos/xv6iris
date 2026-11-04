/-
Weak/Prom: **E-b — the NF_R lemma WITHOUT (P2) `fetchBounded`, through a PROPHECY-FED FETCH ARM** (G4 deciding
experiment E-b, owner ruling [OWN.P11] "G4. Do B"; G4-review.md §4(1), §5 B-1, §6; plan rev 7 §4 "NF_R lemma").

NfrRun.lean's `nfR` needs (P2) `fetchBounded` because its schedule runs a hart's release-free segment against the
prefix `M[..r)` below the hart's next release `r`, and a fetch may read above `r` (zifencei.adoc:67–69: a fetch may
be STALE — and nothing in Machine.lean bounds a fetch source from above but the fetch floor).  This file removes the
premise by changing what a replayed fetch is checked against: in the NF run shape `nfStepsF … M` a fetch step may be
admissible against the FINAL memory `M` (constructor `fet`, `fetchByteOk c.pcImg M`), not the prefix.  Nothing else
reads a fetched timestamp:

* the fetch moves only `wIfr` (fed only to the FENCE.I floor `wIfl`, Machine.lean `fenceIPost`; `wIfl` feeds only
  `fetchByteOk`) and `wIfv` (fed to `ldPre`/`stPre` of later accesses, reset at `LInstr`);
* so the schedule's self bound drops `wIfr`: `bndF ws := vrOld ⊔ vwOld` bounds every NON-fetch read and every
  fulfil (`memStep_selfF`), with the one invariant `fwdB` (forwarded timestamps are below `bndF`), and a
  release-class write at `r` has `bndF < r` by its class alone (`RCOk.lt_`).  A large `wIfv` raises a later
  access's pre-view, hence its post-view, hence `bndF` — so an instruction that both fetches above the next release
  and accesses memory before it is impossible in the segment without any argument about the fetch.

Checked against the review's sketch (G4-review.md §4(1)): "the FENCE.I window inside the prefix since wIfl ≤ bnd" is
FALSE once fetches are unbounded (`wIfl ⊔= vrOld ⊔ vwOld ⊔ wIfr` absorbs a prophecy-fed `wIfr`); it is not needed —
the replayed fetch reads its FENCE.I window in `M` too, exactly as the hart's solo run against `M` did.  The fetch
view `fetchView` exempts own fulfilled stores (`ownDone`); computed against the prefix and the cut promise set it
equals the solo run's (`fetchView_cut`: an own message above the prefix is still promised).

The schedule is generic in the release class `RC` (`RCOk`: no-timestamp steps are not in it, its writes are above
`vrOld ⊔ vwOld`, its reads are below its timestamp); instances: plan §3's `relClass` (`rcOk_plan`) and S4b3's
`relClassPre` (`rcOk_pre`).  `nfRF` / `nfRF_pre`: EVERY valid run of machine v2 (`D = Unit`), no premise, has an NF
run (`nfRunF`) with the same final configuration and per-hart traces.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.NfrPre

namespace Weak.Prom.Nfr.F

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.Nfr
open PLabel

/-! ## 1. Definitions -/

/-- THE SELF BOUND WITHOUT FETCHES: the load and store maxima. -/
def bndF (ws : PState) : Nat := max ws.wVrOld ws.wVwOld

/-- The forward bank's timestamps lie within `bndF` (the only bound the schedule needs besides `bndF` itself). -/
def fwdB (ws : PState) : Prop := ∀ a tf vf, get? ws.wFwd a = some (tf, vf) → tf ≤ bndF ws

/-- A fetch label. -/
def isFetch (l : PLabel) : Prop := ∃ b tvs, l = LIFetch b tvs

/-- Machine.lean's fetch post (arm `fetch`) with the fetch view computed against log `L` and promise set `prom`. -/
def fetchPost (L : List PMsg) (i : Nat) (prom : GSet Nat) (ws : PState) (base : Int) (tvs : List (Nat × BitVec 8)) :
    PState :=
  { ws with
    wIfr := max ws.wIfr (bytesMax (fun _ t => t) base tvs)
    wIfv := max ws.wIfv (fetchView L i prom base tvs) }

/-! ## 2. Step facts -/

theorem fwdB_psInit : fwdB psInit := by
  intro a tf vf h; simp [psInit, lookupEmpty] at h

theorem bytesAll_all {Pr : Int → Nat → BitVec 8 → Prop} (h : ∀ a t v, Pr a t v) :
    ∀ (base : Int) (tvs : List (Nat × BitVec 8)), bytesAll Pr base tvs
  | _, [] => trivial
  | a, (t, v) :: r => ⟨h a t v, bytesAll_all h (a + 1) r⟩

theorem ownTs_gt {M : List PMsg} {i t : Nat} (ht : M.length < t) : ¬ ownTs M i t := by
  rintro ⟨m, hm, _⟩
  rw [List.getElem?_eq_none (by omega)] at hm
  cases hm

/-- THE FETCH VIEW OF A REPLAYED FETCH: against the prefix `L` and the promise set cut at `|L|` it is the solo
run's (against `M`, full promise set `P`), provided every own message above `L` is still promised. -/
theorem fetchView_cut {L M : List PMsg} {i : Nat} {P Q : GSet Nat} (hpre : L <+: M)
    (hQ : ∀ t, t ∈ Q ↔ t ∈ P ∧ t ≤ L.length) (hfut : ∀ t, L.length < t → ownTs M i t → t ∈ P)
    (base : Int) (tvs : List (Nat × BitVec 8)) : fetchView M i P base tvs = fetchView L i Q base tvs := by
  unfold fetchView
  refine bytesMax_congr base tvs (bytesAll_all (fun a t _ => ?_) base tvs)
  by_cases ht : t ≤ L.length
  · rw [ownDone_ext hpre ht (fun t' ht' => by rw [hQ t']; exact ⟨fun h => ⟨h, ht'⟩, fun h => h.1⟩)]
  · have h1 : ownDone L i Q t = false := by
      unfold ownDone; rw [List.getElem?_eq_none (by omega)]
    have h2 : ownDone M i P t = false := by
      unfold ownDone
      cases hm : M[t - 1]? with
      | none => rfl
      | some m =>
        by_cases ht' : m.tid = some i
        · have := hfut t (by omega) ⟨m, hm, ht'⟩
          simp [this]
        · simp [ht']
    rw [h1, h2]

theorem memStep_fetch_inv {img : Image} {M : List PMsg} {i : Nat} {prom : GSet Nat} {ws : PState} {b : Int}
    {tvs : List (Nat × BitVec 8)} {ots : Option Nat} {ws' : PState} {prom' : GSet Nat}
    (hm : memStep img M i prom ws (LIFetch b tvs) ots ws' prom') :
    bytesAll (fetchByteOk img M ws) b tvs ∧ ots = none ∧ ws' = fetchPost M i prom ws b tvs ∧ prom' = prom := by
  cases hm with
  | fetch => exact ⟨‹_›, rfl, rfl, rfl⟩

theorem reads_le_ofF {ws : PState} (hb : fwdB ws) {aq : Bool} {V : Nat} {base : Int}
    {tvs : List (Nat × BitVec 8)} (hv : bytesAll (fun a t _ => fwdView ws aq a t ≤ V) base tvs) :
    bytesAll (fun _ t _ => t ≤ max V (bndF ws)) base tvs := by
  refine bytesAll_mono (fun a t _ h => ?_) base tvs hv
  rcases le_fwdView ws aq a t with e | ⟨vf, e⟩
  · omega
  · have := hb a t vf e; omega

theorem storeRun_fwd {ws : PState} {rl : Bool} {va fv : Nat} {base : Int} {n ts : Nat} {a : Int} {tf vf : Nat}
    (hg : get? (storeRun ws rl va fv base n ts).wFwd a = some (tf, vf)) : get? ws.wFwd a = some (tf, vf) ∨ tf = ts := by
  have e : (storeRun ws rl va fv base n ts).wFwd = (storeBytes ws base n ts fv).wFwd := rfl
  rw [e, Mach.storeBytes_fwd] at hg
  split at hg
  · simp only [Option.some.injEq, Prod.mk.injEq] at hg; exact .inr hg.1.symm
  · exact .inl hg

theorem cohRaise_fwd : ∀ (ws : PState) (a : Int) (n ts : Nat), (cohRaise ws a n ts).wFwd = ws.wFwd
  | _, _, 0, _ => rfl
  | ws, a, n + 1, ts => by simp only [cohRaise]; exact cohRaise_fwd _ (a + 1) n ts

/-- A step's forward bank: old entries, or the step's own fulfil timestamp. -/
theorem memStep_fwd {img : Image} {M : List PMsg} {i : Nat} {prom : GSet Nat} {ws : PState} {l : PLabel}
    {ots : Option Nat} {ws' : PState} {prom' : GSet Nat} (h : memStep img M i prom ws l ots ws' prom') :
    ∀ a tf vf, get? ws'.wFwd a = some (tf, vf) → get? ws.wFwd a = some (tf, vf) ∨ ots = some tf := by
  intro a tf vf hg
  cases h with
  | load aq rl base tvs asrc _ vi _ =>
    exact .inl (by rw [← (loadRunV_keep ws aq rl (srcsView ws asrc) vi base tvs).1]; exact hg)
  | lr aq rl base tvs asrc _ vi _ =>
    exact .inl (by rw [← (loadRunV_keep ws aq rl (srcsView ws asrc) vi base tvs).1]; exact hg)
  | amoLd aq base tvs asrc _ vi _ =>
    exact .inl (by rw [← (loadRunV_keep ws aq false (srcsView ws asrc) vi base tvs).1]; exact hg)
  | rmw aq rl base tvs data asrc vsrc ts _ _ _ _ _ _ _ vi _ _ =>
    have hg' : get? (storeRun (loadRunV ws aq false (srcsView ws asrc) vi base tvs) rl (srcsView ws asrc) ts base
        data.length ts).wFwd a = some (tf, vf) := hg
    rcases storeRun_fwd hg' with e | e
    · exact .inl (by rw [← (loadRunV_keep ws aq false (srcsView ws asrc) vi base tvs).1]; exact e)
    · exact .inr (by rw [e])
  | store aq rl base data asrc vsrc ts =>
    have hg' : get? (storeRun ws rl (srcsView ws asrc) (max (srcsView ws asrc) (srcsView ws vsrc)) base
        data.length ts).wFwd a = some (tf, vf) := hg
    rcases storeRun_fwd hg' with e | e
    · exact .inl e
    · exact .inr (by rw [e])
  | amoSt rl base data asrc vsrc ts R =>
    have hg' : get? (storeRun ws rl (srcsView ws asrc) ts base data.length ts).wFwd a = some (tf, vf) := hg
    rcases storeRun_fwd hg' with e | e
    · exact .inl e
    · exact .inr (by rw [e])
  | sc aq rl base data asrc vsrc ts R =>
    have hg' : get? (storeRun ws rl (srcsView ws asrc) ts base data.length ts).wFwd a = some (tf, vf) := hg
    rcases storeRun_fwd hg' with e | e
    · exact .inl e
    · exact .inr (by rw [e])
  | cmo k base len asrc ts =>
    exact .inl (by rw [← cohRaise_fwd ws base len ts]; exact hg)
  | silent => exact .inl hg
  | fence => exact .inl hg
  | fenceI => exact .inl hg
  | dev => exact .inl hg
  | regW => exact .inl hg
  | ctrl => exact .inl hg
  | instr => exact .inl hg
  | scFail => exact .inl hg
  | fetch => exact .inl hg

/-- `vrOld` grows. -/
theorem memStep_vr {img : Image} {M : List PMsg} {i : Nat} {prom : GSet Nat} {ws : PState} {l : PLabel}
    {ots : Option Nat} {ws' : PState} {prom' : GSet Nat} (h : memStep img M i prom ws l ots ws' prom') :
    ws.wVrOld ≤ ws'.wVrOld := by
  cases h with
  | load aq rl base tvs asrc _ vi _ => exact (loadRunV_keep ws aq rl (srcsView ws asrc) vi base tvs).2.2.2.1
  | lr aq rl base tvs asrc _ vi _ => exact (loadRunV_keep ws aq rl (srcsView ws asrc) vi base tvs).2.2.2.1
  | amoLd aq base tvs asrc _ vi _ => exact (loadRunV_keep ws aq false (srcsView ws asrc) vi base tvs).2.2.2.1
  | rmw aq rl base tvs data asrc vsrc ts _ _ _ _ _ _ _ vi _ _ =>
    have i4 := (loadRunV_keep ws aq false (srcsView ws asrc) vi base tvs).2.2.2.1
    have j1 := (storeRun_keep (loadRunV ws aq false (srcsView ws asrc) vi base tvs) rl (srcsView ws asrc) ts base
      data.length ts).1
    simp only [amoPost]; rw [j1]; omega
  | store aq rl base data asrc vsrc ts =>
    have j1 := (storeRun_keep ws rl (srcsView ws asrc) (max (srcsView ws asrc) (srcsView ws vsrc)) base
      data.length ts).1
    simp only [acqPost]; rw [j1]; exact Nat.le_refl _
  | amoSt rl base data asrc vsrc ts R =>
    have j1 := (storeRun_keep ws rl (srcsView ws asrc) ts base data.length ts).1
    simp only [amoPost]; rw [j1]; omega
  | sc aq rl base data asrc vsrc ts R =>
    have j1 := (storeRun_keep ws rl (srcsView ws asrc) ts base data.length ts).1
    simp only [acqPost]; rw [j1]; exact Nat.le_refl _
  | cmo k base len asrc ts =>
    have j1 := (cohRaise_keep ws base len ts).1
    simp only [cmoPost]; rw [j1]; exact Nat.le_refl _
  | _ => exact Nat.le_refl _

/-- THE SELF BOUND WITHOUT FETCHES: every NON-fetch read and every fulfil of a step is at most `bndF` of its
post-state; `bndF` grows; `fwdB` is kept. -/
theorem memStep_selfF {img : Image} {M : List PMsg} {i : Nat} {prom : GSet Nat} {ws : PState} {l : PLabel}
    {ots : Option Nat} {ws' : PState} {prom' : GSet Nat} (h : memStep img M i prom ws l ots ws' prom')
    (hb : fwdB ws) :
    bndF ws ≤ bndF ws' ∧ (¬ isFetch l → readsLe l (bndF ws')) ∧ (∀ ts, ots = some ts → ts ≤ bndF ws') ∧
      fwdB ws' := by
  have hvw := memStep_vw h
  have hvr := memStep_vr h
  have hle : bndF ws ≤ bndF ws' := by unfold bndF; omega
  refine ⟨hle, ?_, fun ts e => by have := hvw.2 ts e; unfold bndF; omega, fun a tf vf hg => ?_⟩
  · intro hnf b tvs hl
    have key : ∀ {aq : Bool} {V : Nat}, bytesAll (fun a t _ => fwdView ws aq a t ≤ V) b tvs → V ≤ bndF ws' →
        bytesAll (fun _ t _ => t ≤ bndF ws') b tvs := fun hv hV =>
      bytesAll_mono (fun _ _ _ u => by omega) _ _ (reads_le_ofF hb hv)
    cases h with
    | load aq rl base tvs' asrc _ vi _ =>
      have i5 := (loadRunV_keep ws aq rl (srcsView ws asrc) vi base tvs').2.2.2.2
      simp only [labelReads, Option.some.injEq, Prod.mk.injEq] at hl; obtain ⟨rfl, rfl⟩ := hl
      exact key i5 (Nat.le_max_left _ _)
    | lr aq rl base tvs' asrc _ vi _ =>
      have i5 := (loadRunV_keep ws aq rl (srcsView ws asrc) vi base tvs').2.2.2.2
      simp only [labelReads, Option.some.injEq, Prod.mk.injEq] at hl; obtain ⟨rfl, rfl⟩ := hl
      exact key i5 (Nat.le_max_left _ _)
    | amoLd aq base tvs' asrc _ vi _ =>
      have i5 := (loadRunV_keep ws aq false (srcsView ws asrc) vi base tvs').2.2.2.2
      simp only [labelReads, Option.some.injEq, Prod.mk.injEq] at hl; obtain ⟨rfl, rfl⟩ := hl
      exact key i5 (Nat.le_max_left _ _)
    | rmw aq rl base tvs' data asrc vsrc ts _ _ _ _ _ _ _ vi _ _ =>
      have i5 := (loadRunV_keep ws aq false (srcsView ws asrc) vi base tvs').2.2.2.2
      have j1 := (storeRun_keep (loadRunV ws aq false (srcsView ws asrc) vi base tvs') rl (srcsView ws asrc) ts base
        data.length ts).1
      simp only [labelReads, Option.some.injEq, Prod.mk.injEq] at hl; obtain ⟨rfl, rfl⟩ := hl
      refine key i5 ?_
      unfold bndF; simp only [amoPost]; rw [j1]; omega
    | fetch base tvs' _ => exact absurd (show ∃ b' t', LIFetch base tvs' = LIFetch b' t' from ⟨_, _, rfl⟩) hnf
    | silent => cases hl
    | store => cases hl
    | amoSt => cases hl
    | fence => cases hl
    | fenceI => cases hl
    | dev => cases hl
    | regW => cases hl
    | ctrl => cases hl
    | instr => cases hl
    | sc => cases hl
    | scFail => cases hl
    | cmo => cases hl
  · rcases memStep_fwd h a tf vf hg with e | e
    · exact Nat.le_trans (hb a tf vf e) hle
    · have := hvw.2 tf e; unfold bndF; omega

/-- The reads of a write step are below the post-read `vrOld`, or forwarded (below `bndF`). -/
theorem memStep_reads_wrF {img : Image} {M : List PMsg} {i : Nat} {prom : GSet Nat} {ws : PState} {l : PLabel}
    {ts : Nat} {ws' : PState} {prom' : GSet Nat} (h : memStep img M i prom ws l (some ts) ws' prom')
    (hb : fwdB ws) : readsLe l (max (wrState ws l).wVrOld (bndF ws)) := by
  intro base tvs hl
  cases h with
  | rmw aq rl b r data asrc vsrc ts _ _ _ hok =>
    simp only [labelReads, Option.some.injEq, Prod.mk.injEq] at hl; obtain ⟨rfl, rfl⟩ := hl
    exact reads_le_ofF hb (loadRun_keep ws aq false (srcsView ws asrc) _ _).2.2.2.2
  | _ => cases hl

/-! ## 3. The release class, abstractly -/

/-- WHAT THE SCHEDULE NEEDS OF A RELEASE CLASS `RC` (a property of the machine step, plan §3): a step with no
fulfil is not in it; its write is above `vrOld ⊔ vwOld`; every byte it reads is at most its timestamp. -/
structure RCOk (RC : PState → PLabel → Prop) : Prop where
  none_ : ∀ {img : Image} {M : List PMsg} {i : Nat} {prom : GSet Nat} {ws : PState} {l : PLabel} {ws' : PState}
    {prom' : GSet Nat}, memStep img M i prom ws l none ws' prom' → ¬ RC ws l
  lt_ : ∀ {img : Image} {M : List PMsg} {i : Nat} {prom : GSet Nat} {ws : PState} {l : PLabel} {ts : Nat}
    {ws' : PState} {prom' : GSet Nat}, memStep img M i prom ws l (some ts) ws' prom' → RC ws l →
    max ws.wVrOld ws.wVwOld < ts
  reads_ : ∀ {img : Image} {M : List PMsg} {i : Nat} {prom : GSet Nat} {ws : PState} {l : PLabel} {ts : Nat}
    {ws' : PState} {prom' : GSet Nat}, memStep img M i prom ws l (some ts) ws' prom' → RC ws l → fwdB ws →
    readsLe l ts

/-- Plan §3's release class (NfrStep.lean `relClass`). -/
theorem rcOk_plan : RCOk relClass where
  none_ h := not_relClass_none h
  lt_ h hr := relClass_lt h hr
  reads_ := @fun img M i prom ws l ts ws' prom' h hr hb => by
    intro b tvs e
    have hrd := memStep_reads_wrF h hb b tvs e
    obtain ⟨⟨pv, hpv, hlt⟩, _⟩ := memStep_write h
    obtain ⟨pv', hpv', hle'⟩ := hr
    rw [hpv] at hpv'; cases hpv'
    obtain ⟨hw1, hw2⟩ := wrState_le ws l
    exact bytesAll_mono (fun _ _ _ u => by unfold bndF at u; omega) _ _ hrd

/-- S4b3's pre-state release class (NfrPre.lean `relClassPre`). -/
theorem rcOk_pre : RCOk Pre.relClassPre where
  none_ h := Pre.not_relClassPre_none h
  lt_ h hr := Pre.relClassPre_lt h hr
  reads_ h _ _ := fun b tvs e => bytesAll_mono (fun _ _ _ u => Nat.le_of_lt u) _ _ (Pre.memStep_reads_lt h b tvs e)

/-! ## 4. Solo runs -/

/-- No side condition. -/
def QT : PState → PLabel → Option Nat → Prop := fun _ _ _ => True

/-- "Every `RC` write is above `n`". -/
def QG (RC : PState → PLabel → Prop) (n : Nat) : PState → PLabel → Option Nat → Prop :=
  fun ws l ots => RC ws l → ∀ r, ots = some r → n < r

/-- Not in `RC`. -/
def QNR (RC : PState → PLabel → Prop) : PState → PLabel → Option Nat → Prop := fun ws l _ => ¬ RC ws l

section soloF

variable {P : Type} {pstep : P → Unit → PLabel → P → Unit → Prop} {img : Image} {M : List PMsg} {i : Nat}
variable {RC : PState → PLabel → Prop}

theorem soloSteps_QT : ∀ {x y τ}, soloSteps pstep img M i x τ y → soloQ pstep img M i QT x τ y := by
  intro x y τ h
  induction h with
  | refl => exact .refl _
  | step x l ots p' ws' prom' tr y hp hm _ ih => exact .step _ _ _ _ _ _ _ _ trivial hp hm ih

/-- RAISING THE FLOOR (no fetch premise): every `RC` write of a run from `x` is above `x`'s `vwOld`. -/
theorem soloQ_raiseF (hRC : RCOk RC) {n : Nat} : ∀ {x y τ}, soloQ pstep img M i QT x τ y →
    n ≤ x.2.1.wVwOld → soloQ pstep img M i (QG RC n) x τ y := by
  intro x y τ h
  induction h with
  | refl => intro _; exact .refl _
  | step x l ots p' ws' prom' tr y _ hp hm _ ih =>
    intro hn
    refine .step _ _ _ _ _ _ _ _ (fun hr r hots => ?_) hp hm (ih (Nat.le_trans hn (memStep_vw hm).1))
    subst hots
    have := hRC.lt_ hm hr
    omega

theorem soloQ_QN_QG {n : Nat} {x y τ} (h : soloQ pstep img M i (QNR RC) x τ y) :
    soloQ pstep img M i (QG RC n) x τ y :=
  soloQ_mono (fun _ _ _ hq hr => absurd hr hq) h

theorem soloQ_QG_anti {n m : Nat} (hmn : m ≤ n) {x y τ} (h : soloQ pstep img M i (QG RC n) x τ y) :
    soloQ pstep img M i (QG RC m) x τ y :=
  soloQ_mono (fun _ _ _ hq hr r hr' => by have := hq hr r hr'; omega) h

theorem soloQ_bndF {Q : PState → PLabel → Option Nat → Prop} :
    ∀ {x y τ}, soloQ pstep img M i Q x τ y → fwdB x.2.1 → bndF x.2.1 ≤ bndF y.2.1 ∧ fwdB y.2.1 := by
  intro x y τ h
  induction h with
  | refl => intro hb; exact ⟨Nat.le_refl _, hb⟩
  | step x l ots p' ws' prom' tr y _ _ hm _ ih =>
    intro hb
    have hs := memStep_selfF hm hb
    have := ih hs.2.2.2
    exact ⟨Nat.le_trans hs.1 this.1, this.2⟩

/-- THE SPLIT AT THE FIRST `RC` WRITE. -/
theorem soloQ_splitF (hRC : RCOk RC) {n : Nat} : ∀ {x y τ}, soloQ pstep img M i (QG RC n) x τ y →
    soloQ pstep img M i (QNR RC) x τ y ∨
    ∃ τ1 z l r p' ws' prom' τ2, soloQ pstep img M i (QNR RC) x τ1 z ∧ RC z.2.1 l ∧ n < r ∧
      pstep z.1 () l p' () ∧ memStep img M i z.2.2 z.2.1 l (some r) ws' prom' ∧
      soloQ pstep img M i QT (p', ws', prom') τ2 y ∧ τ = τ1 ++ (l, some r) :: τ2 := by
  intro x y τ h
  induction h with
  | refl => exact .inl (.refl _)
  | step x l ots p' ws' prom' tr y hq hp hm hrest ih =>
    by_cases hr : RC x.2.1 l
    · cases ots with
      | none => exact absurd hr (hRC.none_ hm)
      | some r =>
        exact .inr ⟨[], x, l, r, p', ws', prom', tr, .refl _, hr, hq hr r rfl, hp, hm,
          soloQ_mono (fun _ _ _ _ => trivial) hrest, rfl⟩
    · rcases ih with ih | ⟨τ1, z, l', r, p'', ws'', prom'', τ2, k1, k2, k3, k4, k5, k6, k7⟩
      · exact .inl (.step _ _ _ _ _ _ _ _ hr hp hm ih)
      · refine .inr ⟨(l, ots) :: τ1, z, l', r, p'', ws'', prom'', τ2, .step _ _ _ _ _ _ _ _ hr hp hm k1, k2, k3,
          k4, k5, k6, ?_⟩
        rw [k7]; rfl

end soloF

/-! ## 5. The run shape NF_R with prophecy-fed fetches -/

section nf

variable {P D : Type} (RC : PState → PLabel → Prop) (pstep : P → D → PLabel → P → D → Prop) (M : List PMsg)

/-- THE RUN SHAPE NF_R WITH PROPHECY-FED FETCHES: NfrRun.lean's `nfSteps` (constructors `prom`, `st`, `rel`, for a
release class `RC`) plus `fet` — a fetch step of agent `i` whose bytes are admissible against the FINAL memory `M`
(not the current log), with Machine.lean's fetch post computed against the current log and promise set. -/
inductive nfStepsF : PCfg P D → List PEvt → PCfg P D → Prop
  | refl (c : PCfg P D) : nfStepsF c [] c
  | prom (c c1 : PCfg P D) (i : Nat) (m : PMsg) (es : List PEvt) (c2 : PCfg P D) :
      pmStep pstep c (.prom i m) c1 → nfStepsF c1 es c2 → nfStepsF c (.prom i m :: es) c2
  | st (c c1 : PCfg P D) (i : Nat) (ag : PAgent P) (l : PLabel) (ots : Option Nat) (es : List PEvt)
      (c2 : PCfg P D) :
      c.pcAgs[i]? = some ag → ¬ RC ag.paWs l → pmStep pstep c (.st i l ots) c1 → nfStepsF c1 es c2 →
      nfStepsF c (.st i l ots :: es) c2
  | rel (c c1 c2 : PCfg P D) (i : Nat) (m : PMsg) (ag : PAgent P) (l : PLabel) (r : Nat) (es : List PEvt)
      (c3 : PCfg P D) :
      pmStep pstep c (.prom i m) c1 → c1.pcAgs[i]? = some ag → RC ag.paWs l → r = c1.pcLog.length →
      pmStep pstep c1 (.st i l (some r)) c2 → nfStepsF c2 es c3 →
      nfStepsF c (.prom i m :: .st i l (some r) :: es) c3
  | fet (c : PCfg P D) (i : Nat) (ag : PAgent P) (b : Int) (tvs : List (Nat × BitVec 8)) (st' : P) (d' : D)
      (es : List PEvt) (c2 : PCfg P D) :
      c.pcAgs[i]? = some ag → pstep ag.paSt c.pcDev (LIFetch b tvs) st' d' →
      bytesAll (fetchByteOk c.pcImg M ag.paWs) b tvs →
      nfStepsF ⟨c.pcImg, c.pcLog, d', c.pcAgs.set i ⟨st', fetchPost c.pcLog i ag.paProm ag.paWs b tvs, ag.paProm⟩⟩
        es c2 →
      nfStepsF c (.st i (LIFetch b tvs) none :: es) c2

/-- An NF_R VALID RUN with prophecy-fed fetches. -/
def nfRunF (img : Image) (d0 : D) (ps : List P) (evs : List PEvt) (cfg : PCfg P D) : Prop :=
  nfStepsF RC pstep M (pmInit img d0 ps) evs cfg ∧ noPromises cfg

variable {RC pstep M}

theorem nfStepsF_append {c c1 c2 : PCfg P D} {es1 es2 : List PEvt} (h1 : nfStepsF RC pstep M c es1 c1)
    (h2 : nfStepsF RC pstep M c1 es2 c2) : nfStepsF RC pstep M c (es1 ++ es2) c2 := by
  induction h1 with
  | refl => exact h2
  | prom c c1 i m es c2' h _ ih => exact .prom _ _ _ _ _ _ h (ih h2)
  | st c c1 i ag l ots es c2' ha hn h _ ih => exact .st _ _ _ _ _ _ _ _ ha hn h (ih h2)
  | rel c c1 c2' i m ag l r es c3 h ha hr hl h' _ ih => exact .rel _ _ _ _ _ _ _ _ _ _ h ha hr hl h' (ih h2)
  | fet c i ag b tvs st' d' es c2' ha hp hok _ ih => exact .fet _ _ _ _ _ _ _ _ _ ha hp hok (ih h2)

theorem pmStep_prefix {c c' : PCfg P D} {e : PEvt} (h : pmStep pstep c e c') : c.pcLog <+: c'.pcLog :=
  pmSteps_prefix (.step _ _ _ _ _ h (.refl _))

/-- The log only grows along an NF run. -/
theorem nfStepsF_prefix {c c' : PCfg P D} {es : List PEvt} (h : nfStepsF RC pstep M c es c') :
    c.pcLog <+: c'.pcLog := by
  induction h with
  | refl => exact List.prefix_refl _
  | prom c c1 i m es c2 h1 _ ih => exact List.IsPrefix.trans (pmStep_prefix h1) ih
  | st c c1 i ag l ots es c2 _ _ h1 _ ih => exact List.IsPrefix.trans (pmStep_prefix h1) ih
  | rel c c1 c2 i m ag l r es c3 h1 _ _ _ h2 _ ih =>
    exact List.IsPrefix.trans (pmStep_prefix h1) (List.IsPrefix.trans (pmStep_prefix h2) ih)
  | fet c i ag b tvs st' d' es c2 _ _ _ _ ih => exact ih

end nf

/-! ## 6. The schedule (NfrRun.lean §4 with `bndF`/`fwdB` for `bnd`/`psBounded`, no fetch premise, and the
prophecy-fed fetch for every fetch step) -/

section sched

variable {P : Type} {pstep : P → Unit → PLabel → P → Unit → Prop} {img : Image} {M : List PMsg} {N : Nat}
variable {RC : PState → PLabel → Prop}

/-- One hart's part of the invariant at log length `n`. -/
def hartInvF (RC : PState → PLabel → Prop) (pstep : P → Unit → PLabel → P → Unit → Prop) (img : Image)
    (M : List PMsg) (c : PCfg P Unit) (n : Nat) (h : Nat) (j : Job P) : Prop :=
  ∃ Q, c.pcAgs[h]? = some ⟨j.x.1, j.x.2.1, Q⟩ ∧ (∀ t, t ∈ Q ↔ t ∈ j.x.2.2 ∧ t ≤ n) ∧
    soloQ pstep img M h (QG RC n) j.x j.τ j.y ∧ promWf M h j.x.2.2 ∧ (∀ t, n < t → ownTs M h t → t ∈ j.x.2.2) ∧
    fwdB j.x.2.1

/-- THE SCHEDULE INVARIANT. -/
def InvF (RC : PState → PLabel → Prop) (pstep : P → Unit → PLabel → P → Unit → Prop) (img : Image)
    (M : List PMsg) (N : Nat) (c : PCfg P Unit) (J : Fin N → Job P) (n : Nat) : Prop :=
  c.pcImg = img ∧ c.pcLog = M.take n ∧ n ≤ M.length ∧ c.pcAgs.length = N ∧
    ∀ h : Fin N, hartInvF RC pstep img M c n h (J h)

/-- ONE PROMISE: append `M[n]` by its author. -/
theorem promOneF (hmsg : ∀ m ∈ M, msgOk N m) {c : PCfg P Unit} {J : Fin N → Job P} {n : Nat}
    (hI : InvF RC pstep img M N c J n) (hn : n < M.length)
    (hq : ∀ h : Fin N, soloQ pstep img M h (QG RC (n + 1)) (J h).x (J h).τ (J h).y) :
    ∃ i m c', M[n]? = some m ∧ m.tid = some i ∧ pmStep pstep c (.prom i m) c' ∧
      InvF RC pstep img M N c' J (n + 1) := by
  obtain ⟨himg, hlog, hle, hlen, hh⟩ := hI
  have hmn : M[n]? = some M[n] := List.getElem?_eq_getElem hn
  obtain ⟨hnt, i, htid, hiN⟩ := hmsg M[n] (List.getElem_mem hn)
  obtain ⟨Qi, hagi, hQi, _, _, hfut, _⟩ := hh ⟨i, hiN⟩
  have hclen : c.pcLog.length = n := by rw [hlog]; exact take_length_of hle
  have hst := pmStep.promise (pstep := pstep) c i _ M[n] hagi hnt htid
  refine ⟨i, M[n], _, hmn, htid, hst, himg, ?_, by omega, by simp [hlen], fun h => ?_⟩
  · simp only; rw [hlog, take_succ_of hmn]
  · obtain ⟨Q, hag, hQ, _, hw, hf, hb⟩ := hh h
    by_cases hih : (h : Nat) = i
    · have e : h = ⟨i, hiN⟩ := Fin.ext hih
      subst e
      rw [hagi] at hag
      cases hag
      refine ⟨{c.pcLog.length + 1} ∪ Qi, ?_, fun t => ?_, hq _, hw, fun t ht ho => hf t (by omega) ho, hb⟩
      · simp only; exact getElem?_set_eq_of hagi
      · rw [elemOfUnion, elemOfSingleton, hQi t, hclen]
        have hin : n + 1 ∈ (J ⟨i, hiN⟩).x.2.2 := hfut (n + 1) (by omega) ⟨M[n], by simp [hmn], htid⟩
        constructor
        · rintro (e | ⟨h1, h2⟩)
          · subst e; exact ⟨hin, Nat.le_refl _⟩
          · exact ⟨h1, by omega⟩
        · rintro ⟨h1, h2⟩
          by_cases e : t = n + 1
          · exact .inl e
          · exact .inr ⟨h1, by omega⟩
    · refine ⟨Q, ?_, fun t => ?_, hq h, hw, fun t ht ho => hf t (by omega) ho, hb⟩
      · simp only; rw [List.getElem?_set_ne (Ne.symm hih)]; exact hag
      · rw [hQ t]
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨h1, by omega⟩
        · rintro ⟨h1, h2⟩
          refine ⟨h1, ?_⟩
          by_cases e : t = n + 1
          · subst e
            obtain ⟨_, _, m', hm', ht'⟩ := hw _ h1
            simp only [Nat.add_sub_cancel] at hm'
            rw [hmn] at hm'
            cases hm'
            rw [htid] at ht'
            cases ht'
            exact absurd rfl hih
          · omega

/-- PROMISES UP TO `k`. -/
theorem promsUpToF (hmsg : ∀ m ∈ M, msgOk N m) {k : Nat} :
    ∀ (d : Nat) {c : PCfg P Unit} {J : Fin N → Job P} {n : Nat}, n + d = k → InvF RC pstep img M N c J n →
      k ≤ M.length → (∀ h : Fin N, soloQ pstep img M h (QG RC k) (J h).x (J h).τ (J h).y) →
      ∃ es c', nfStepsF RC pstep M c es c' ∧ InvF RC pstep img M N c' J k ∧ ∀ h, traceOf h es = [] := by
  intro d
  induction d with
  | zero =>
    intro c J n hk hI _ _
    rw [Nat.add_zero] at hk; subst hk
    exact ⟨[], c, .refl _, hI, fun _ => rfl⟩
  | succ d ih =>
    intro c J n hk hI hkM hq
    obtain ⟨i, m, c', _, _, hst, hI'⟩ := promOneF hmsg hI (by omega)
      (fun h => soloQ_QG_anti (by omega) (hq h))
    obtain ⟨es, c'', h1, h2, h3⟩ := ih (n := n + 1) (by omega) hI' hkM hq
    exact ⟨.prom i m :: es, c'', .prom _ _ _ _ _ _ hst h1, h2, fun h => by simp only [traceOf]; exact h3 h⟩

/-- RUNNING ONE HART'S `RC`-FREE SEGMENT against the current prefix: non-fetch steps by restriction
(`memStep_restrict`, bounds by `memStep_selfF`), fetch steps by the prophecy-fed arm `fet` (`fetchView_cut`). -/
theorem runSegF {A : Nat} :
    ∀ {x z : P × PState × GSet Nat} {τ1 : List (PLabel × Option Nat)}, soloQ pstep img M A (QNR RC) x τ1 z →
      ∀ (c : PCfg P Unit) (Q : GSet Nat), c.pcImg = img → c.pcLog <+: M → c.pcAgs[A]? = some ⟨x.1, x.2.1, Q⟩ →
      (∀ t, t ∈ Q ↔ t ∈ x.2.2 ∧ t ≤ c.pcLog.length) → fwdB x.2.1 →
      (∀ t, c.pcLog.length < t → ownTs M A t → t ∈ x.2.2) →
      (bndF z.2.1 ≤ c.pcLog.length ∨ M.length ≤ c.pcLog.length) →
      ∃ Q', nfStepsF RC pstep M c (stEvs A τ1) ⟨c.pcImg, c.pcLog, c.pcDev, c.pcAgs.set A ⟨z.1, z.2.1, Q'⟩⟩ ∧
        (∀ t, t ∈ Q' ↔ t ∈ z.2.2 ∧ t ≤ c.pcLog.length) ∧ fwdB z.2.1 ∧
        (∀ t, c.pcLog.length < t → t ∈ x.2.2 → t ∈ z.2.2) ∧ (∀ t, t ∈ z.2.2 → t ∈ x.2.2) := by
  intro x z τ1 h
  induction h with
  | refl x =>
    intro c Q _ _ hag hQ hb _ _
    refine ⟨Q, ?_, hQ, hb, fun _ _ h => h, fun _ h => h⟩
    rw [set_of_get hag]
    exact .refl _
  | step x l ots p' ws' prom' tr z hq hp hm hrest ih =>
    intro c Q himg hpre hag hQ hb hfut hfit
    have hs := memStep_selfF hm hb
    have hz : bndF ws' ≤ bndF z.2.1 := (soloQ_bndF hrest hs.2.2.2).1
    have eset : ∀ (ag1 ag2 : PAgent P),
        (⟨c.pcImg, c.pcLog, (), (c.pcAgs.set A ag1).set A ag2⟩ : PCfg P Unit) =
          ⟨c.pcImg, c.pcLog, c.pcDev, c.pcAgs.set A ag2⟩ := by
      intro ag1 ag2; rw [List.set_set]
    by_cases hfe : isFetch l
    · -- THE PROPHECY-FED FETCH
      obtain ⟨b, tvs, rfl⟩ := hfe
      obtain ⟨hok, rfl, rfl, rfl⟩ := memStep_fetch_inv hm
      have hws : fetchPost M A x.2.2 x.2.1 b tvs = fetchPost c.pcLog A Q x.2.1 b tvs := by
        unfold fetchPost; rw [fetchView_cut hpre hQ hfut b tvs]
      rw [hws] at ih hrest hs hz
      obtain ⟨Q', h1, h2, h3, h4, h5⟩ := ih ⟨c.pcImg, c.pcLog, (), c.pcAgs.set A ⟨p', fetchPost c.pcLog A Q x.2.1 b tvs, Q⟩⟩
        Q himg hpre (getElem?_set_eq_of hag) hQ hs.2.2.2 hfut hfit
      refine ⟨Q', ?_, h2, h3, h4, h5⟩
      rw [← eset ⟨p', fetchPost c.pcLog A Q x.2.1 b tvs, Q⟩ ⟨z.1, z.2.1, Q'⟩]
      exact .fet c A ⟨x.1, x.2.1, Q⟩ b tvs p' () _ _ hag hp (himg ▸ hok) h1
    · have hr : readsLe l c.pcLog.length ∧ ∀ ts, ots = some ts → ts ≤ c.pcLog.length := by
        rcases hfit with hf | hf
        · exact ⟨fun b t hl => bytesAll_mono (fun _ _ _ h => by omega) _ _ (hs.2.1 hfe b t hl),
            fun ts e => by have := hs.2.2.1 ts e; omega⟩
        · have hl := memStep_len hm
          exact ⟨fun b t e => bytesAll_mono (fun _ _ _ h => by omega) _ _ (hl.1 b t e),
            fun ts e => by have := hl.2 ts e; omega⟩
      obtain ⟨Q1, hm1, hQ1⟩ := memStep_restrict Q hm hpre
        (fun _ => hfit.elim (fun hf => .inl (by unfold bndF at hz hf; omega)) .inr) hr.1 hr.2 hQ
      have hst : pmStep pstep c (.st A l ots) ⟨c.pcImg, c.pcLog, (), c.pcAgs.set A ⟨p', ws', Q1⟩⟩ :=
        pmStep.state c A _ l ots p' () ws' Q1 hag hp (himg ▸ hm1)
      have hfut' : ∀ t, c.pcLog.length < t → ownTs M A t → t ∈ prom' := by
        intro t ht ho
        rcases memStep_prom hm with ⟨_, e⟩ | ⟨ts, e1, _, e2⟩
        · rw [e]; exact hfut t ht ho
        · rw [e2, elemOfDifference, elemOfSingleton]
          refine ⟨hfut t ht ho, fun e => ?_⟩
          subst e
          have := hr.2 _ e1
          omega
      obtain ⟨Q', h1, h2, h3, h4, h5⟩ := ih ⟨c.pcImg, c.pcLog, (), c.pcAgs.set A ⟨p', ws', Q1⟩⟩ Q1 himg hpre
        (getElem?_set_eq_of hag) hQ1 hs.2.2.2 hfut' hfit
      refine ⟨Q', ?_, h2, h3, fun t ht hx => h4 t ht ?_, fun t ht => ?_⟩
      · rw [← eset ⟨p', ws', Q1⟩ ⟨z.1, z.2.1, Q'⟩]
        exact .st _ _ _ _ _ _ _ _ hag hq hst h1
      · rcases memStep_prom hm with ⟨_, e⟩ | ⟨ts, e1, _, e2⟩
        · rw [e]; exact hx
        · rw [e2, elemOfDifference, elemOfSingleton]
          refine ⟨hx, fun e => ?_⟩
          subst e
          have := hr.2 _ e1
          omega
      · have := h5 t ht
        rcases memStep_prom hm with ⟨_, e⟩ | ⟨ts, _, _, e2⟩
        · rw [← e]; exact this
        · rw [e2] at this; exact (elemOfDifference.1 this).1

/-- THE FINAL PHASE: with the whole of `M` in the log and no `RC` write left, run the harts `0, …, k−1`. -/
theorem runAllF {c : PCfg P Unit} {J : Fin N → Job P}
    (himg : c.pcImg = img) (hlog : c.pcLog = M) (hlen : c.pcAgs.length = N)
    (hh : ∀ h : Fin N, ∃ Q, c.pcAgs[(h : Nat)]? = some ⟨(J h).x.1, (J h).x.2.1, Q⟩ ∧
      (∀ t, t ∈ Q ↔ t ∈ (J h).x.2.2 ∧ t ≤ M.length) ∧ soloQ pstep img M h (QNR RC) (J h).x (J h).τ (J h).y ∧
      fwdB (J h).x.2.1) :
    ∀ k, k ≤ N → ∃ es c', nfStepsF RC pstep M c es c' ∧ c'.pcImg = img ∧ c'.pcLog = M ∧ c'.pcAgs.length = N ∧
      (∀ h : Fin N, ∃ Q, (h < k → c'.pcAgs[(h : Nat)]? = some ⟨(J h).y.1, (J h).y.2.1, Q⟩ ∧
          ∀ t, t ∈ Q ↔ t ∈ (J h).y.2.2 ∧ t ≤ M.length) ∧
        (k ≤ h → c'.pcAgs[(h : Nat)]? = some ⟨(J h).x.1, (J h).x.2.1, Q⟩ ∧
          ∀ t, t ∈ Q ↔ t ∈ (J h).x.2.2 ∧ t ≤ M.length)) ∧
      ∀ h, traceOf h es = if hN : h < N then (if h < k then (J ⟨h, hN⟩).τ else []) else [] := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨[], c, .refl _, himg, hlog, hlen, fun h => ?_, fun h => ?_⟩
    · obtain ⟨Q, h1, h2, _⟩ := hh h
      exact ⟨Q, fun e => absurd e (Nat.not_lt_zero _), fun _ => ⟨h1, h2⟩⟩
    · simp only [Nat.not_lt_zero, if_false, dite_eq_ite, ite_self]; rfl
  | succ k ih =>
    intro hk
    obtain ⟨es, c', h1, h2, h3, h4, h5, h6⟩ := ih (by omega)
    obtain ⟨A, hAk⟩ : ∃ A : Fin N, (A : Nat) = k := ⟨⟨k, by omega⟩, rfl⟩
    obtain ⟨Q, _, hA⟩ := h5 A
    obtain ⟨hag, hQ⟩ := hA (by omega)
    obtain ⟨_, _, _, hrun, hb⟩ := hh A
    rw [← h3] at hQ
    obtain ⟨Q', g1, g2, _, _, _⟩ := runSegF hrun c' Q h2 (by rw [h3]; exact List.prefix_refl _) hag hQ hb
      (fun t ht ho => absurd ho (ownTs_gt (by rw [h3] at ht; exact ht))) (.inr (by rw [h3]; exact Nat.le_refl _))
    refine ⟨es ++ stEvs A (J A).τ, _, nfStepsF_append h1 g1, h2, h3, by simp [h4], fun h => ?_, fun h => ?_⟩
    · by_cases e : (h : Nat) = k
      · have e' : h = A := Fin.ext (by omega)
        subst e'
        refine ⟨Q', fun _ => ⟨?_, by rw [← h3]; exact g2⟩, fun hle => absurd hle (by omega)⟩
        simp only; exact getElem?_set_eq_of hag
      · obtain ⟨Q0, k1, k2⟩ := h5 h
        have e2 : (A : Nat) ≠ (h : Nat) := by omega
        refine ⟨Q0, fun hl => ?_, fun hl => ?_⟩
        · obtain ⟨u1, u2⟩ := k1 (by omega)
          refine ⟨?_, u2⟩
          simp only; rw [List.getElem?_set_ne e2]; exact u1
        · obtain ⟨u1, u2⟩ := k2 (by omega)
          refine ⟨?_, u2⟩
          simp only; rw [List.getElem?_set_ne e2]; exact u1
    · rw [traceOf_append, h6 h, traceOf_stEvs]
      by_cases hN : h < N
      · simp only [hN, dif_pos]
        by_cases e : h = k
        · subst e
          have e' : (⟨h, hN⟩ : Fin N) = A := Fin.ext (by show h = (A : Nat); omega)
          rw [e']
          simp [hAk]
        · by_cases hlt : h < k
          · simp [hlt, e, hAk, show h < k + 1 by omega]
          · simp [hlt, e, hAk, show ¬ h < k + 1 by omega]
      · have e : ¬ h = (A : Nat) := by omega
        simp [hN, e]

/-- THE SCHEDULE (no fetch premise), by induction on `|M| − n`. -/
theorem scheduleF (hRC : RCOk RC) (hmsg : ∀ m ∈ M, msgOk N m) :
    ∀ (d : Nat) {c : PCfg P Unit} {J : Fin N → Job P} {n : Nat}, M.length - n ≤ d → InvF RC pstep img M N c J n →
      ∃ es c', nfStepsF RC pstep M c es c' ∧ Final img M N c' J ∧
        ∀ h, traceOf h es = if hN : h < N then (J ⟨h, hN⟩).τ else [] := by
  intro d
  induction d using Nat.strongRecOn with
  | _ d ihd =>
  intro c J n hd hI
  classical
  -- the first `RC` write of each hart, if any
  let S : Nat → Prop := fun r => ∃ h : Fin N, ∃ τ1 z l p' ws' prom' τ2,
    soloQ pstep img M h (QNR RC) (J h).x τ1 z ∧ RC z.2.1 l ∧ n < r ∧
    pstep z.1 () l p' () ∧ memStep img M h z.2.2 z.2.1 l (some r) ws' prom' ∧
    soloQ pstep img M h QT (p', ws', prom') τ2 (J h).y ∧ (J h).τ = τ1 ++ (l, some r) :: τ2
  obtain ⟨himg, hlog, hle, hlen, hh⟩ := hI
  have hsplit : ∀ h : Fin N, soloQ pstep img M h (QNR RC) (J h).x (J h).τ (J h).y ∨ ∃ r, S r ∧
      ∃ τ1 z l p' ws' prom' τ2,
      soloQ pstep img M h (QNR RC) (J h).x τ1 z ∧ RC z.2.1 l ∧ n < r ∧
      pstep z.1 () l p' () ∧ memStep img M h z.2.2 z.2.1 l (some r) ws' prom' ∧
      soloQ pstep img M h QT (p', ws', prom') τ2 (J h).y ∧ (J h).τ = τ1 ++ (l, some r) :: τ2 := by
    intro h
    obtain ⟨_, _, _, hq, _⟩ := hh h
    rcases soloQ_splitF hRC hq with e | ⟨τ1, z, l, r, p', ws', prom', τ2, k1, k2, k3, k4, k5, k6, k7⟩
    · exact .inl e
    · exact .inr ⟨r, ⟨h, τ1, z, l, p', ws', prom', τ2, k1, k2, k3, k4, k5, k6, k7⟩,
        τ1, z, l, p', ws', prom', τ2, k1, k2, k3, k4, k5, k6, k7⟩
  by_cases hS : ∃ r, S r
  · -- an `RC` write remains: process the least one
    obtain ⟨r, hSr, hmin⟩ := exists_min S hS
    obtain ⟨A, τ1, z, l, p', ws', prom', τ2, k1, k2, k4, k5, k6, k7, k8⟩ := hSr
    obtain ⟨⟨pv, hpv, hpvlt⟩, m, hm, hmt⟩ := memStep_write k6
    have hrM : r ≤ M.length := by have := (List.getElem?_eq_some_iff.1 hm).1; omega
    -- every other hart's `RC` writes are above `r`
    have hother : ∀ h : Fin N, h ≠ A → soloQ pstep img M h (QG RC r) (J h).x (J h).τ (J h).y := by
      intro h hne
      rcases hsplit h with e | ⟨rh, hSh, τ1', z', l', p'', ws'', prom'', τ2', j1, j2, j4, j5, j6, j7, j8⟩
      · exact soloQ_QN_QG e
      · have hrh : r ≤ rh := by
          by_cases hc : rh < r
          · exact absurd hSh (hmin rh hc)
          · omega
        have hne' : rh ≠ r := by
          intro e; subst e
          obtain ⟨_, m', hm', hmt'⟩ := memStep_write j6
          rw [hm] at hm'; cases hm'
          exact hne (Fin.ext (Option.some.inj (hmt'.symm.trans hmt)))
        rw [j8]
        refine soloQ_append (soloQ_QN_QG j1) (.step _ _ _ _ _ _ _ _ (fun _ r' e => ?_) j5 j6
          (soloQ_raiseF hRC j7 (Nat.le_trans (by omega) ((memStep_vw j6).2 rh rfl))))
        cases e; omega
    -- hart `A`'s whole run, above `r − 1`
    have hAq : soloQ pstep img M A (QG RC (r - 1)) (J A).x (J A).τ (J A).y := by
      rw [k8]
      exact soloQ_append (soloQ_QN_QG k1) (.step _ _ _ _ _ _ _ _ (fun _ r' e => by cases e; omega)
        k5 k6 (soloQ_raiseF hRC k7 (Nat.le_trans (by omega) ((memStep_vw k6).2 r rfl))))
    have hall : ∀ h : Fin N, soloQ pstep img M h (QG RC (r - 1)) (J h).x (J h).τ (J h).y := by
      intro h
      by_cases e : h = A
      · subst e; exact hAq
      · exact soloQ_QG_anti (by omega) (hother h e)
    -- 1. promises up to `r − 1`
    obtain ⟨es1, c1, n1, i1, n1tr⟩ := promsUpToF hmsg (r - 1 - n) (k := r - 1) (by omega)
      ⟨himg, hlog, hle, hlen, hh⟩ (by omega) hall
    obtain ⟨g1, g2, g3, g4, g5⟩ := i1
    have hc1len : c1.pcLog.length = r - 1 := by rw [g2]; exact take_length_of (by omega)
    -- 2. hart `A`'s segment up to its `RC` write
    obtain ⟨QA, hagA, hQA, _, hwA, hfA, hbA⟩ := g5 A
    have hbz : bndF z.2.1 < r := hRC.lt_ k6 k2
    obtain ⟨Qz, s1, s2, s3, s4, s5⟩ := runSegF k1 c1 QA g1 (by rw [g2]; exact take_prefix M _) hagA
      (by rw [hc1len]; exact hQA) hbA (fun t ht ho => hfA t (by omega) ho) (.inl (by omega))
    -- 3. the release: promise `M[r − 1]`, then fulfil it in place
    let c2 : PCfg P Unit := ⟨c1.pcImg, c1.pcLog, c1.pcDev, c1.pcAgs.set A ⟨z.1, z.2.1, Qz⟩⟩
    have hag2 : c2.pcAgs[(A : Nat)]? = some ⟨z.1, z.2.1, Qz⟩ := getElem?_set_eq_of hagA
    have hmr : M[r - 1]? = some m := hm
    obtain ⟨hnt, _⟩ := hmsg m (List.mem_of_getElem? hm)
    have hpst := pmStep.promise (pstep := pstep) c2 A _ m hag2 hnt hmt
    let c3 : PCfg P Unit := ⟨c2.pcImg, c2.pcLog ++ [m], c2.pcDev,
      c2.pcAgs.set A ⟨z.1, z.2.1, {c2.pcLog.length + 1} ∪ Qz⟩⟩
    have hc2len : c2.pcLog.length = r - 1 := hc1len
    have hlog3 : c3.pcLog = M.take r := by
      show c1.pcLog ++ [m] = M.take r
      rw [g2]
      have := take_succ_of hmr
      rw [show r - 1 + 1 = r by omega] at this
      exact this.symm
    have hr_in : r ∈ z.2.2 := by
      rcases memStep_prom k6 with ⟨e, _⟩ | ⟨ts, e1, e2, _⟩
      · cases e
      · cases e1; exact e2
    have hQ3 : ∀ t, t ∈ ({c2.pcLog.length + 1} ∪ Qz : GSet Nat) ↔ t ∈ z.2.2 ∧ t ≤ c3.pcLog.length := by
      intro t
      rw [hlog3, take_length_of hrM, elemOfUnion, elemOfSingleton, s2 t, hc1len]
      constructor
      · rintro (e | ⟨u1, u2⟩)
        · subst e; exact ⟨by rw [show r - 1 + 1 = r by omega]; exact hr_in, by omega⟩
        · exact ⟨u1, by omega⟩
      · rintro ⟨u1, u2⟩
        by_cases e : t = r
        · left; omega
        · right; exact ⟨u1, by omega⟩
    have hrd : readsLe l c3.pcLog.length := by
      rw [hlog3, take_length_of hrM]
      exact hRC.reads_ k6 k2 s3
    obtain ⟨Q4, hm4, hQ4⟩ := memStep_restrict _ k6 (by rw [hlog3]; exact take_prefix M r) (fun h => by cases h) hrd
      (fun ts e => by cases e; rw [hlog3, take_length_of hrM]; exact Nat.le_refl _) hQ3
    have hag3 : c3.pcAgs[(A : Nat)]? = some ⟨z.1, z.2.1, {c2.pcLog.length + 1} ∪ Qz⟩ := getElem?_set_eq_of hag2
    let c4 : PCfg P Unit := ⟨c3.pcImg, c3.pcLog, (), c3.pcAgs.set A ⟨p', ws', Q4⟩⟩
    have himg3 : c3.pcImg = img := g1
    have hrst := pmStep.state (pstep := pstep) c3 A _ l (some r) p' () ws' Q4 hag3 k5 (himg3 ▸ hm4)
    have hr3 : r = c3.pcLog.length := by rw [hlog3, take_length_of hrM]
    -- the invariant after the release
    let J' : Fin N → Job P := fun h => if h = A then ⟨(p', ws', prom'), τ2, (J A).y⟩ else J h
    have hself := memStep_selfF k6 s3
    have hI4 : InvF RC pstep img M N c4 J' r := by
      refine ⟨g1, hlog3, hrM, by simp [c4, c3, c2, g4], fun h => ?_⟩
      by_cases e : h = A
      · subst e
        simp only [J', if_true]
        refine ⟨Q4, getElem?_set_eq_of hag3, fun t => by rw [hQ4 t, hlog3, take_length_of hrM],
          soloQ_raiseF hRC k7 ((memStep_vw k6).2 r rfl), ?_, fun t ht ho => ?_, hself.2.2.2⟩
        · intro t ht
          rcases memStep_prom k6 with ⟨e, _⟩ | ⟨ts, _, _, e2⟩
          · cases e
          · rw [e2] at ht; exact hwA t (s5 t (elemOfDifference.1 ht).1)
        · rcases memStep_prom k6 with ⟨e, _⟩ | ⟨ts, e1, _, e2⟩
          · cases e
          · cases e1
            rw [e2, elemOfDifference, elemOfSingleton]
            exact ⟨s4 t (by omega) (hfA t (by omega) ho), by omega⟩
      · simp only [J', e, if_false]
        obtain ⟨Q, u1, u2, _, u4, u5, u6⟩ := g5 h
        have hne : (h : Nat) ≠ (A : Nat) := fun e' => e (Fin.ext e')
        refine ⟨Q, ?_, fun t => ?_, hother h e, u4, fun t ht ho => u5 t (by omega) ho, u6⟩
        · show (((c1.pcAgs.set A _).set A _).set A _)[(h : Nat)]? = _
          rw [List.getElem?_set_ne (Ne.symm hne), List.getElem?_set_ne (Ne.symm hne),
            List.getElem?_set_ne (Ne.symm hne)]
          exact u1
        · rw [u2 t]
          constructor
          · rintro ⟨v1, v2⟩; exact ⟨v1, by omega⟩
          · rintro ⟨v1, v2⟩
            refine ⟨v1, ?_⟩
            by_cases et : t = r
            · subst et
              obtain ⟨_, _, m', hm', ht'⟩ := u4 _ v1
              rw [hm] at hm'; cases hm'
              exact absurd (Option.some.inj (ht'.symm.trans hmt)) hne
            · omega
    obtain ⟨es4, c5, n4, f4, t4⟩ := ihd (M.length - r) (by omega) (Nat.le_refl _) hI4
    refine ⟨es1 ++ (stEvs A τ1 ++ (.prom A m :: .st A l (some r) :: es4)), c5,
      nfStepsF_append n1 (nfStepsF_append s1 (.rel _ _ _ _ _ _ _ _ _ _ hpst hag3 k2 hr3 hrst n4)), ?_, ?_⟩
    · obtain ⟨f1, f2, f3, f4⟩ := f4
      refine ⟨f1, f2, f3, fun h => ?_⟩
      obtain ⟨Q, v1, v2⟩ := f4 h
      by_cases e : h = A
      · subst e; simp only [J', if_true] at v1 v2; exact ⟨Q, v1, v2⟩
      · simp only [J', e, if_false] at v1 v2; exact ⟨Q, v1, v2⟩
    · intro h
      rw [traceOf_append, traceOf_append, n1tr h, traceOf_stEvs, List.nil_append]
      simp only [traceOf]
      rw [t4 h]
      by_cases hN : h < N
      · simp only [hN, dif_pos]
        by_cases e : h = (A : Nat)
        · have e' : (⟨h, hN⟩ : Fin N) = A := Fin.ext e
          rw [e']
          simp only [J', if_true, e, if_true, k8]
        · have e' : (⟨h, hN⟩ : Fin N) ≠ A := fun e'' => e (congrArg Fin.val e'')
          have e2 : ¬ (A : Nat) = h := fun e'' => e e''.symm
          simp only [J', e', e, e2, if_false, List.nil_append]
      · have e : ¬ (A : Nat) = h := fun e'' => hN (e'' ▸ A.isLt)
        have e2 : ¬ h = (A : Nat) := fun e'' => e e''.symm
        simp [hN, e, e2]
  · -- no `RC` write remains: the final phase
    have hN : ∀ h : Fin N, soloQ pstep img M h (QNR RC) (J h).x (J h).τ (J h).y := by
      intro h
      rcases hsplit h with e | ⟨r, hSr, _⟩
      · exact e
      · exact absurd ⟨r, hSr⟩ hS
    obtain ⟨es1, c1, n1, i1, n1tr⟩ := promsUpToF hmsg (M.length - n) (k := M.length) (by omega)
      ⟨himg, hlog, hle, hlen, hh⟩ (Nat.le_refl _) (fun h => soloQ_QN_QG (hN h))
    obtain ⟨g1, g2, _, g4, g5⟩ := i1
    have hlogM : c1.pcLog = M := by rw [g2]; exact List.take_length
    obtain ⟨es2, c2, n2, f1, f2, f3, f5, f6⟩ := runAllF g1 hlogM g4 (fun h => by
      obtain ⟨Q, u1, u2, _, _, _, u6⟩ := g5 h
      exact ⟨Q, u1, u2, hN h, u6⟩) N (Nat.le_refl _)
    refine ⟨es1 ++ es2, c2, nfStepsF_append n1 n2, ⟨f1, f2, f3, fun h => ?_⟩, fun h => ?_⟩
    · obtain ⟨Q, u1, _⟩ := f5 h
      obtain ⟨v1, v2⟩ := u1 h.isLt
      refine ⟨Q, v1, fun t => ?_⟩
      rw [v2 t]
      obtain ⟨_, _, _, _, w4, _, _⟩ := g5 h
      have hy := soloQ_solo (hN h)
      constructor
      · exact fun u => u.1
      · intro u
        refine ⟨u, ?_⟩
        have : ∀ {x y τ}, soloSteps pstep img M h x τ y → ∀ t, t ∈ y.2.2 → t ∈ x.2.2 := by
          intro x y τ hs
          induction hs with
          | refl => exact fun _ h => h
          | step x l ots p' ws' prom' tr y _ hm _ ih =>
            intro t ht
            have := ih t ht
            rcases memStep_prom hm with ⟨_, e⟩ | ⟨ts, _, _, e2⟩
            · rw [← e]; exact this
            · rw [e2] at this; exact (elemOfDifference.1 this).1
        exact (w4 t (this hy t u)).2.1
    · rw [traceOf_append, n1tr h, f6 h, List.nil_append]
      by_cases hN' : h < N
      · simp [hN']
      · simp [hN']

end sched

/-! ## 7. THE NF_R LEMMA WITHOUT (P2) -/

/-- **THE NF_R LEMMA WITH PROPHECY-FED FETCHES** (E-b; plan §4, program-agnostic; machine v2, no device fabric),
for any release class satisfying `RCOk`.  Every valid run — NO fetch-boundedness premise — can be rescheduled
into an NF run (`nfRunF`: releases in place, fetches admissible against the final memory) with the same final
configuration and the same per-hart traces. -/
theorem nfRF_gen {RC : PState → PLabel → Prop} (hRC : RCOk RC) {P : Type} {pstep : P → Unit → PLabel → P → Unit → Prop}
    {img : Image} {ps : List P} {evs : List PEvt} {cfg : PCfg P Unit} (hv : validRun pstep img () ps evs cfg) :
    ∃ evs', nfRunF RC pstep cfg.pcLog img () ps evs' cfg ∧ ∀ h, traceOf h evs' = traceOf h evs := by
  classical
  let M := cfg.pcLog
  let N := ps.length
  have hwf := pmSteps_wf hv.1 (pmInit_wf img () ps)
  have hlenN : cfg.pcAgs.length = N := by rw [pmSteps_len hv.1]; simp [pmInit, N]
  have hmsg : ∀ m ∈ M, msgOk N m := fun m hm => by rw [← hlenN]; exact hwf.2 m hm
  have hsolo := validRun_solo hv
  have hps : ∀ h : Fin N, ps[(h : Nat)]? = some ps[(h : Nat)] := fun h => List.getElem?_eq_getElem h.isLt
  have hjob : ∀ h : Fin N, ∃ ag : PAgent P, cfg.pcAgs[(h : Nat)]? = some ag ∧ ∃ P0 : GSet Nat,
      (∀ t, t ∈ P0 ↔ 0 < t ∧ ownTs M h t) ∧
      soloSteps pstep img M h (ps[(h : Nat)], psInit, P0) (traceOf h evs) (ag.paSt, ag.paWs, ag.paProm) :=
    fun h => hsolo h _ (hps h)
  let ag : Fin N → PAgent P := fun h => Classical.choose (hjob h)
  have hag : ∀ h : Fin N, cfg.pcAgs[(h : Nat)]? = some (ag h) := fun h => (Classical.choose_spec (hjob h)).1
  let P0 : Fin N → GSet Nat := fun h => Classical.choose (Classical.choose_spec (hjob h)).2
  have hP0 : ∀ h : Fin N, (∀ t, t ∈ P0 h ↔ 0 < t ∧ ownTs M h t) ∧
      soloSteps pstep img M h (ps[(h : Nat)], psInit, P0 h) (traceOf h evs) ((ag h).paSt, (ag h).paWs, (ag h).paProm) :=
    fun h => Classical.choose_spec (Classical.choose_spec (hjob h)).2
  let J : Fin N → Job P := fun h => ⟨(ps[(h : Nat)], psInit, P0 h), traceOf h evs, ((ag h).paSt, (ag h).paWs, (ag h).paProm)⟩
  have hI : InvF RC pstep img M N (pmInit img () ps) J 0 := by
    refine ⟨rfl, by simp [pmInit], Nat.zero_le _, by simp [pmInit, N], fun h => ?_⟩
    obtain ⟨h1, h2⟩ := hP0 h
    refine ⟨∅, by simp [pmInit, hps h, J], fun t => ?_, ?_, fun t ht => ?_, fun t _ ho => ?_, fwdB_psInit⟩
    · constructor
      · intro u; exact absurd u notElemOfEmpty
      · rintro ⟨u1, u2⟩
        have := ((h1 t).1 u1).1
        omega
    · exact soloQ_raiseF hRC (soloSteps_QT h2) (Nat.zero_le _)
    · obtain ⟨u1, m, hm, hmt⟩ := (h1 t).1 ht
      exact ⟨u1, by have := (List.getElem?_eq_some_iff.1 hm).1; omega, m, hm, hmt⟩
    · exact (h1 t).2 ⟨by omega, ho⟩
  obtain ⟨es, c', hnf, ⟨f1, f2, f3, f4⟩, htr⟩ := scheduleF hRC hmsg (M.length - 0) (Nat.le_refl _) hI
  have hc : c' = cfg := by
    have hags : c'.pcAgs = cfg.pcAgs := by
      apply List.ext_getElem?
      intro j
      by_cases hj : j < N
      · obtain ⟨Q, u1, u2⟩ := f4 ⟨j, hj⟩
        rw [u1, hag ⟨j, hj⟩]
        have : Q = (ag ⟨j, hj⟩).paProm := setEq.2 u2
        subst this
        rfl
      · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
    cases c'; cases cfg
    simp only at f1 f2 hags
    have himg := PF.validRun_img hv
    simp only at himg
    subst f1 f2 hags himg
    rfl
  subst hc
  refine ⟨es, ⟨hnf, hv.2⟩, fun h => ?_⟩
  rw [htr h]
  by_cases hN : h < N
  · simp only [hN, dif_pos]; rfl
  · simp only [hN, dif_neg, not_false_eq_true]
    exact (PF.validRun_traceNone hv (List.getElem?_eq_none (by omega))).symm

/-- **NF_R WITHOUT (P2), PLAN §3's RELEASE CLASS** (the class the G4 targets (1a), (1c), (2), (2′), (4) use). -/
theorem nfRF {P : Type} {pstep : P → Unit → PLabel → P → Unit → Prop} {img : Image} {ps : List P}
    {evs : List PEvt} {cfg : PCfg P Unit} (hv : validRun pstep img () ps evs cfg) :
    ∃ evs', nfRunF relClass pstep cfg.pcLog img () ps evs' cfg ∧ ∀ h, traceOf h evs' = traceOf h evs :=
  nfRF_gen rcOk_plan hv

/-- **NF_R WITHOUT (P2), S4b3's PRE-STATE RELEASE CLASS** (the class G4 (1b) uses, NfrPre.lean). -/
theorem nfRF_pre {P : Type} {pstep : P → Unit → PLabel → P → Unit → Prop} {img : Image} {ps : List P}
    {evs : List PEvt} {cfg : PCfg P Unit} (hv : validRun pstep img () ps evs cfg) :
    ∃ evs', nfRunF Pre.relClassPre pstep cfg.pcLog img () ps evs' cfg ∧ ∀ h, traceOf h evs' = traceOf h evs :=
  nfRF_gen rcOk_pre hv

end Weak.Prom.Nfr.F
