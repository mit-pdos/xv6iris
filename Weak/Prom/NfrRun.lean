/-
Weak/Prom: **the NF_R lemma for machine v2** (stage S4b, track (b); plan rev 7 §4 "Run shape NF_R ('releases in
place')", "NF_R lemma (to prove, program-agnostic, S4b)").

* `nfSteps` — THE RUN SHAPE NF_R: a run in which every release-class write step (`relClass`, NfrStep.lean) is
  immediately preceded by the promise of its own message, which is then the LAST message of the log (constructor
  `rel`); every other state step is not release-class (`st`); other promises are unconstrained (`prom`).  Memory is
  always a prefix of the final memory (the log only grows, `pmSteps_prefix`).
* `nfR` — THE NF_R LEMMA: every valid run of machine v2 (no device fabric, `D = Unit`) whose final memory has no
  invalidate-class CMO (`invalFree`) and which is FETCH-BOUNDED (`fetchBounded`, the plan's premise (P2)) can be
  rescheduled into an NF_R run with the SAME final configuration and the same per-hart traces.
  Premises (plan §4): (P1) `latFreeProg` holds of every v2 run by construction (`LLoad` has no `lat` field, SR-31);
  (P3) walk-bounded and (P4) A/D-bounded are vacuous (machine v2 has no walk and no A/D arm, [OWN.P3]); (P2) is
  `fetchBounded`; `invalFree` is the extra premise found here (NfrStep.lean header, PROGRESS-S4b.md R-b5).
* `fetchBounded_ofImg` — PO-fetch for programs that fetch only the image (every fetched byte has timestamp 0, PA-0):
  the G4 targets' discharge (plan §4 "For the G4 litmus targets they are dischargeable").

The construction is the plan's: process the release messages in timestamp order; before release `r` by hart `A`,
append every message below `r` as a promise, run `A` up to its fulfil of `r` against that prefix (restriction,
`memStep_restrict`; bounds by `memStep_self`), promise `r` and fulfil it; finally append the rest and run every hart
to its end.  Proof: an invariant `Inv` between the current NF configuration and every hart's remaining solo run
against `M` (MachSolo.lean), by induction on `|M| − |log|`.  The release chosen at each round is the least
first-release timestamp over all harts (`exists_min`).

No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.NfrStep
import Weak.Prom.CoreRun

namespace Weak.Prom.Nfr

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom
open PLabel

/-! ## 1. Solo runs with a per-step side condition -/

section soloq

variable {P : Type} (pstep : P → Unit → PLabel → P → Unit → Prop) (img : Image) (M : List PMsg) (i : Nat)

/-- A solo run of agent `i` against `M` (MachSolo.lean `soloSteps`) in which every step satisfies `Q` of its
pre-state, label and timestamp. -/
inductive soloQ (Q : PState → PLabel → Option Nat → Prop) :
    P × PState × GSet Nat → List (PLabel × Option Nat) → P × PState × GSet Nat → Prop
  | refl (x : P × PState × GSet Nat) : soloQ Q x [] x
  | step (x : P × PState × GSet Nat) (l : PLabel) (ots : Option Nat) (p' : P) (ws' : PState) (prom' : GSet Nat)
      (tr : List (PLabel × Option Nat)) (y : P × PState × GSet Nat) :
      Q x.2.1 l ots → pstep x.1 () l p' () → memStep img M i x.2.2 x.2.1 l ots ws' prom' →
      soloQ Q (p', ws', prom') tr y → soloQ Q x ((l, ots) :: tr) y

end soloq

/-- (P2) at one step: a release-class write at `r` has every earlier fetch source below `r` (`wIfr` is the maximum
fetch source so far). -/
def QF : PState → PLabel → Option Nat → Prop :=
  fun ws l ots => relClass ws l → ∀ r, ots = some r → ws.wIfr < r

/-- (P2) and "every release-class write is above `n`". -/
def QFG (n : Nat) : PState → PLabel → Option Nat → Prop :=
  fun ws l ots => relClass ws l → ∀ r, ots = some r → ws.wIfr < r ∧ n < r

/-- Not release-class. -/
def QN : PState → PLabel → Option Nat → Prop := fun ws l _ => ¬ relClass ws l

section soloqLemmas

variable {P : Type} {pstep : P → Unit → PLabel → P → Unit → Prop} {img : Image} {M : List PMsg} {i : Nat}

theorem soloQ_mono {Q1 Q2 : PState → PLabel → Option Nat → Prop} (hQ : ∀ ws l ots, Q1 ws l ots → Q2 ws l ots) :
    ∀ {x y τ}, soloQ pstep img M i Q1 x τ y → soloQ pstep img M i Q2 x τ y := by
  intro x y τ h
  induction h with
  | refl => exact .refl _
  | step x l ots p' ws' prom' tr y hq hp hm _ ih => exact .step _ _ _ _ _ _ _ _ (hQ _ _ _ hq) hp hm ih

theorem soloQ_solo {Q : PState → PLabel → Option Nat → Prop} :
    ∀ {x y τ}, soloQ pstep img M i Q x τ y → soloSteps pstep img M i x τ y := by
  intro x y τ h
  induction h with
  | refl => exact .refl _
  | step x l ots p' ws' prom' tr y _ hp hm _ ih => exact .step _ _ _ _ _ _ _ _ hp hm ih

theorem soloQ_append {Q : PState → PLabel → Option Nat → Prop} :
    ∀ {x z y τ1 τ2}, soloQ pstep img M i Q x τ1 z → soloQ pstep img M i Q z τ2 y →
      soloQ pstep img M i Q x (τ1 ++ τ2) y := by
  intro x z y τ1 τ2 h1 h2
  induction h1 with
  | refl => exact h2
  | step x l ots p' ws' prom' tr y' hq hp hm _ ih => exact .step _ _ _ _ _ _ _ _ hq hp hm (ih h2)

/-- RAISING THE FLOOR: in a fetch-bounded run from `x`, every release-class write is above `x`'s `vwOld`. -/
theorem soloQ_raise {n : Nat} : ∀ {x y τ}, soloQ pstep img M i QF x τ y → n ≤ x.2.1.wVwOld →
    soloQ pstep img M i (QFG n) x τ y := by
  intro x y τ h
  induction h with
  | refl => intro _; exact .refl _
  | step x l ots p' ws' prom' tr y hq hp hm _ ih =>
    intro hn
    refine .step _ _ _ _ _ _ _ _ (fun hr r hots => ?_) hp hm (ih (Nat.le_trans hn (memStep_vw hm).1))
    subst hots
    have := relClass_lt hm hr
    exact ⟨hq hr r rfl, by omega⟩

theorem soloQ_QN_QFG {n : Nat} {x y τ} (h : soloQ pstep img M i QN x τ y) : soloQ pstep img M i (QFG n) x τ y :=
  soloQ_mono (fun _ _ _ hq hr => absurd hr hq) h

theorem soloQ_QFG_QF {n : Nat} {x y τ} (h : soloQ pstep img M i (QFG n) x τ y) : soloQ pstep img M i QF x τ y :=
  soloQ_mono (fun _ _ _ hq hr r hr' => (hq hr r hr').1) h

theorem soloQ_QFG_anti {n m : Nat} (hmn : m ≤ n) {x y τ} (h : soloQ pstep img M i (QFG n) x τ y) :
    soloQ pstep img M i (QFG m) x τ y :=
  soloQ_mono (fun _ _ _ hq hr r hr' => ⟨(hq hr r hr').1, by have := (hq hr r hr').2; omega⟩) h

/-- The self bound along a run. -/
theorem soloQ_bnd {Q : PState → PLabel → Option Nat → Prop} :
    ∀ {x y τ}, soloQ pstep img M i Q x τ y → psBounded x.2.1 (bnd x.2.1) →
      bnd x.2.1 ≤ bnd y.2.1 ∧ psBounded y.2.1 (bnd y.2.1) := by
  intro x y τ h
  induction h with
  | refl => intro hb; exact ⟨Nat.le_refl _, hb⟩
  | step x l ots p' ws' prom' tr y _ _ hm _ ih =>
    intro hb
    have hs := memStep_self hm hb
    have := ih hs.2.2.2
    exact ⟨Nat.le_trans hs.1 this.1, this.2⟩

/-- THE SPLIT AT THE FIRST RELEASE: a run either has no release-class write, or is a release-free prefix, a
release-class write at `r > n`, and a fetch-bounded rest. -/
theorem soloQ_split {n : Nat} : ∀ {x y τ}, soloQ pstep img M i (QFG n) x τ y →
    soloQ pstep img M i QN x τ y ∨
    ∃ τ1 z l r p' ws' prom' τ2, soloQ pstep img M i QN x τ1 z ∧ relClass z.2.1 l ∧ z.2.1.wIfr < r ∧ n < r ∧
      pstep z.1 () l p' () ∧ memStep img M i z.2.2 z.2.1 l (some r) ws' prom' ∧
      soloQ pstep img M i QF (p', ws', prom') τ2 y ∧ τ = τ1 ++ (l, some r) :: τ2 := by
  intro x y τ h
  induction h with
  | refl => exact .inl (.refl _)
  | step x l ots p' ws' prom' tr y hq hp hm hrest ih =>
    by_cases hr : relClass x.2.1 l
    · cases ots with
      | none => exact absurd hr (not_relClass_none hm)
      | some r =>
        obtain ⟨h1, h2⟩ := hq hr r rfl
        exact .inr ⟨[], x, l, r, p', ws', prom', tr, .refl _, hr, h1, h2, hp, hm, soloQ_QFG_QF hrest, rfl⟩
    · rcases ih with ih | ⟨τ1, z, l', r, p'', ws'', prom'', τ2, k1, k2, k3, k4, k5, k6, k7, k8⟩
      · exact .inl (.step _ _ _ _ _ _ _ _ hr hp hm ih)
      · refine .inr ⟨(l, ots) :: τ1, z, l', r, p'', ws'', prom'', τ2, .step _ _ _ _ _ _ _ _ hr hp hm k1, k2, k3,
          k4, k5, k6, k7, ?_⟩
        rw [k8]; rfl

end soloqLemmas

/-! ## 2. The run shape NF_R -/

section nf

variable {P D : Type} (pstep : P → D → PLabel → P → D → Prop)

/-- THE RUN SHAPE NF_R (plan §4): every release-class write step is IMMEDIATELY preceded by the promise of its own
message and fulfils the last message of the log (`rel`); no other state step is release-class (`st`). -/
inductive nfSteps : PCfg P D → List PEvt → PCfg P D → Prop
  | refl (c : PCfg P D) : nfSteps c [] c
  | prom (c c1 : PCfg P D) (i : Nat) (m : PMsg) (es : List PEvt) (c2 : PCfg P D) :
      pmStep pstep c (.prom i m) c1 → nfSteps c1 es c2 → nfSteps c (.prom i m :: es) c2
  | st (c c1 : PCfg P D) (i : Nat) (ag : PAgent P) (l : PLabel) (ots : Option Nat) (es : List PEvt)
      (c2 : PCfg P D) :
      c.pcAgs[i]? = some ag → ¬ relClass ag.paWs l → pmStep pstep c (.st i l ots) c1 → nfSteps c1 es c2 →
      nfSteps c (.st i l ots :: es) c2
  | rel (c c1 c2 : PCfg P D) (i : Nat) (m : PMsg) (ag : PAgent P) (l : PLabel) (r : Nat) (es : List PEvt)
      (c3 : PCfg P D) :
      pmStep pstep c (.prom i m) c1 → c1.pcAgs[i]? = some ag → relClass ag.paWs l → r = c1.pcLog.length →
      pmStep pstep c1 (.st i l (some r)) c2 → nfSteps c2 es c3 →
      nfSteps c (.prom i m :: .st i l (some r) :: es) c3

/-- An NF_R VALID RUN: an NF_R run from the initial configuration that ends with no outstanding promise. -/
def nfRun (img : Image) (d0 : D) (ps : List P) (evs : List PEvt) (cfg : PCfg P D) : Prop :=
  nfSteps pstep (pmInit img d0 ps) evs cfg ∧ noPromises cfg

variable {pstep}

theorem nfSteps_pm {c c' : PCfg P D} {es : List PEvt} (h : nfSteps pstep c es c') : pmSteps pstep c es c' := by
  induction h with
  | refl => exact .refl _
  | prom c c1 i m es c2 h1 _ ih => exact .step _ _ _ _ _ h1 ih
  | st c c1 i ag l ots es c2 _ _ h1 _ ih => exact .step _ _ _ _ _ h1 ih
  | rel c c1 c2 i m ag l r es c3 h1 _ _ _ h2 _ ih => exact .step _ _ _ _ _ h1 (.step _ _ _ _ _ h2 ih)

theorem nfSteps_append {c c1 c2 : PCfg P D} {es1 es2 : List PEvt} (h1 : nfSteps pstep c es1 c1)
    (h2 : nfSteps pstep c1 es2 c2) : nfSteps pstep c (es1 ++ es2) c2 := by
  induction h1 with
  | refl => exact h2
  | prom c c1 i m es c2' h _ ih => exact .prom _ _ _ _ _ _ h (ih h2)
  | st c c1 i ag l ots es c2' ha hn h _ ih => exact .st _ _ _ _ _ _ _ _ ha hn h (ih h2)
  | rel c c1 c2' i m ag l r es c3 h ha hr hl h' _ ih => exact .rel _ _ _ _ _ _ _ _ _ _ h ha hr hl h' (ih h2)

theorem nfRun_valid {img : Image} {d0 : D} {ps : List P} {evs : List PEvt} {cfg : PCfg P D}
    (h : nfRun pstep img d0 ps evs cfg) : validRun pstep img d0 ps evs cfg :=
  ⟨nfSteps_pm h.1, h.2⟩

end nf

/-! ## 3. Event and list bookkeeping -/

/-- The state events of agent `A` for a trace. -/
def stEvs (A : Nat) (τ : List (PLabel × Option Nat)) : List PEvt := τ.map (fun e => PEvt.st A e.1 e.2)

theorem traceOf_stEvs (h A : Nat) : ∀ τ : List (PLabel × Option Nat),
    traceOf h (stEvs A τ) = if h = A then τ else []
  | [] => by simp [stEvs, traceOf]
  | e :: τ => by
    have ih := traceOf_stEvs h A τ
    simp only [stEvs, List.map_cons] at ih ⊢
    simp only [traceOf]
    by_cases hh : A = h
    · subst hh; simp only [if_true] at ih ⊢; rw [ih]
    · have hh' : ¬ h = A := fun e => hh e.symm
      simp only [hh, hh', if_false] at ih ⊢; exact ih

theorem set_of_get {α : Type} {l : List α} {i : Nat} {a : α} (h : l[i]? = some a) : l.set i a = l := by
  apply List.ext_getElem?
  intro j
  rw [List.getElem?_set]
  split
  · split
    · rename_i h1 _; subst h1; exact h.symm
    · rename_i h1 h2; subst h1; exact absurd (List.getElem?_eq_some_iff.1 h).1 h2
  · rfl

theorem exists_min (p : Nat → Prop) (h : ∃ n, p n) : ∃ n, p n ∧ ∀ m, m < n → ¬ p m := by
  obtain ⟨n, hn⟩ := h
  induction n using Nat.strongRecOn with
  | _ n ih =>
    by_cases hc : ∃ m, m < n ∧ p m
    · obtain ⟨m, hm, hpm⟩ := hc
      exact ih m hm hpm
    · exact ⟨n, hn, fun m hm hpm => hc ⟨m, hm, hpm⟩⟩

theorem take_succ_of {M : List PMsg} {n : Nat} {m : PMsg} (h : M[n]? = some m) :
    M.take (n + 1) = M.take n ++ [m] := by
  rw [List.take_add_one, h]; rfl

theorem take_prefix (M : List PMsg) (n : Nat) : M.take n <+: M := List.take_prefix n M

theorem take_length_of {M : List PMsg} {n : Nat} (h : n ≤ M.length) : (M.take n).length = n := by
  simp [List.length_take]; omega

/-- Read and fulfil timestamps of a step against `M` are within `M`. -/
theorem memStep_len {img : Image} {M : List PMsg} {i : Nat} {prom : GSet Nat} {ws : PState} {l : PLabel}
    {ots : Option Nat} {ws' : PState} {prom' : GSet Nat} (h : memStep img M i prom ws l ots ws' prom') :
    readsLe l M.length ∧ ∀ ts, ots = some ts → ts ≤ M.length := by
  have hts : ∀ ts, ots = some ts → ts ≤ M.length := by
    intro ts e
    subst e
    obtain ⟨_, m, hm, _⟩ := memStep_write h
    have := (List.getElem?_eq_some_iff.1 hm).1
    omega
  refine ⟨?_, hts⟩
  intro base tvs hl
  cases h with
  | load aq rl b r asrc hok =>
    simp only [labelReads, Option.some.injEq, Prod.mk.injEq] at hl; obtain ⟨rfl, rfl⟩ := hl; exact loadOk_ts hok
  | lr aq rl b r asrc hok =>
    simp only [labelReads, Option.some.injEq, Prod.mk.injEq] at hl; obtain ⟨rfl, rfl⟩ := hl; exact loadOk_ts hok
  | amoLd aq b r asrc hok =>
    simp only [labelReads, Option.some.injEq, Prod.mk.injEq] at hl; obtain ⟨rfl, rfl⟩ := hl; exact loadOk_ts hok
  | rmw aq rl b r data asrc vsrc ts _ _ _ hok =>
    simp only [labelReads, Option.some.injEq, Prod.mk.injEq] at hl; obtain ⟨rfl, rfl⟩ := hl; exact loadOk_ts hok
  | fetch b r hok =>
    simp only [labelReads, Option.some.injEq, Prod.mk.injEq] at hl; obtain ⟨rfl, rfl⟩ := hl
    exact bytesAll_mono (fun _ _ _ hp => memByte_le hp.1) _ _ hok
  | _ => cases hl

/-- The reads of a write step are below the post-read `vrOld`, or own fulfilled stores. -/
theorem memStep_reads_wr {img : Image} {M : List PMsg} {i : Nat} {prom : GSet Nat} {ws : PState} {l : PLabel}
    {ts : Nat} {ws' : PState} {prom' : GSet Nat} (h : memStep img M i prom ws l (some ts) ws' prom')
    (hb : psBounded ws (bnd ws)) : readsLe l (max (wrState ws l).wVrOld (bnd ws)) := by
  intro base tvs hl
  cases h with
  | rmw aq rl b r data asrc vsrc ts _ _ _ hok =>
    simp only [labelReads, Option.some.injEq, Prod.mk.injEq] at hl; obtain ⟨rfl, rfl⟩ := hl
    exact reads_le_of hb (loadRun_keep ws aq false (srcsView ws asrc) _ _).2.2.2.2
  | _ => cases hl

/-! ## 4. The schedule -/

/-- A hart's remaining work: its current solo state, its remaining trace, its final state. -/
structure Job (P : Type) where
  x : P × PState × GSet Nat
  τ : List (PLabel × Option Nat)
  y : P × PState × GSet Nat

section sched

variable {P : Type} {pstep : P → Unit → PLabel → P → Unit → Prop} {img : Image} {M : List PMsg} {N : Nat}

/-- One hart's part of the invariant at log length `n`. -/
def hartInv (pstep : P → Unit → PLabel → P → Unit → Prop) (img : Image) (M : List PMsg) (c : PCfg P Unit)
    (n : Nat) (h : Nat) (j : Job P) : Prop :=
  ∃ Q, c.pcAgs[h]? = some ⟨j.x.1, j.x.2.1, Q⟩ ∧ (∀ t, t ∈ Q ↔ t ∈ j.x.2.2 ∧ t ≤ n) ∧
    soloQ pstep img M h (QFG n) j.x j.τ j.y ∧ promWf M h j.x.2.2 ∧ (∀ t, n < t → ownTs M h t → t ∈ j.x.2.2) ∧
    psBounded j.x.2.1 (bnd j.x.2.1)

/-- THE SCHEDULE INVARIANT: the NF configuration `c` has log `M[..n]`, and every hart `h < N` sits at the start of
its remaining solo run against `M`, with its promise set cut at `n`. -/
def Inv (pstep : P → Unit → PLabel → P → Unit → Prop) (img : Image) (M : List PMsg) (N : Nat)
    (c : PCfg P Unit) (J : Fin N → Job P) (n : Nat) : Prop :=
  c.pcImg = img ∧ c.pcLog = M.take n ∧ n ≤ M.length ∧ c.pcAgs.length = N ∧
    ∀ h : Fin N, hartInv pstep img M c n h (J h)

/-- The end of the schedule: the log is `M` and every hart is at its final state. -/
def Final (img : Image) (M : List PMsg) (N : Nat) (c : PCfg P Unit) (J : Fin N → Job P) : Prop :=
  c.pcImg = img ∧ c.pcLog = M ∧ c.pcAgs.length = N ∧
    ∀ h : Fin N, ∃ Q, c.pcAgs[(h : Nat)]? = some ⟨(J h).y.1, (J h).y.2.1, Q⟩ ∧ ∀ t, t ∈ Q ↔ t ∈ (J h).y.2.2

/-- ONE PROMISE: append `M[n]` by its author. -/
theorem promOne (hmsg : ∀ m ∈ M, msgOk N m) {c : PCfg P Unit} {J : Fin N → Job P} {n : Nat}
    (hI : Inv pstep img M N c J n) (hn : n < M.length)
    (hq : ∀ h : Fin N, soloQ pstep img M h (QFG (n + 1)) (J h).x (J h).τ (J h).y) :
    ∃ i m c', M[n]? = some m ∧ m.tid = some i ∧ pmStep pstep c (.prom i m) c' ∧ Inv pstep img M N c' J (n + 1) := by
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

/-- PROMISES UP TO `k`: append `M[n..k)`. -/
theorem promsUpTo (hmsg : ∀ m ∈ M, msgOk N m) {k : Nat} :
    ∀ (d : Nat) {c : PCfg P Unit} {J : Fin N → Job P} {n : Nat}, n + d = k → Inv pstep img M N c J n →
      k ≤ M.length → (∀ h : Fin N, soloQ pstep img M h (QFG k) (J h).x (J h).τ (J h).y) →
      ∃ es c', nfSteps pstep c es c' ∧ Inv pstep img M N c' J k ∧ ∀ h, traceOf h es = [] := by
  intro d
  induction d with
  | zero =>
    intro c J n hk hI _ _
    rw [Nat.add_zero] at hk; subst hk
    exact ⟨[], c, .refl _, hI, fun _ => rfl⟩
  | succ d ih =>
    intro c J n hk hI hkM hq
    obtain ⟨i, m, c', _, _, hst, hI'⟩ := promOne hmsg hI (by omega)
      (fun h => soloQ_QFG_anti (by omega) (hq h))
    obtain ⟨es, c'', h1, h2, h3⟩ := ih (n := n + 1) (by omega) hI' hkM hq
    exact ⟨.prom i m :: es, c'', .prom _ _ _ _ _ _ hst h1, h2, fun h => by simp only [traceOf]; exact h3 h⟩

/-- RUNNING ONE HART'S RELEASE-FREE SEGMENT against the current prefix (restriction). -/
theorem runSeg (hinv : invalFree M) {A : Nat} :
    ∀ {x z : P × PState × GSet Nat} {τ1 : List (PLabel × Option Nat)}, soloQ pstep img M A QN x τ1 z →
      ∀ (c : PCfg P Unit) (Q : GSet Nat), c.pcImg = img → c.pcLog <+: M → c.pcAgs[A]? = some ⟨x.1, x.2.1, Q⟩ →
      (∀ t, t ∈ Q ↔ t ∈ x.2.2 ∧ t ≤ c.pcLog.length) → psBounded x.2.1 (bnd x.2.1) →
      (bnd z.2.1 ≤ c.pcLog.length ∨ M.length ≤ c.pcLog.length) →
      ∃ Q', nfSteps pstep c (stEvs A τ1) ⟨c.pcImg, c.pcLog, c.pcDev, c.pcAgs.set A ⟨z.1, z.2.1, Q'⟩⟩ ∧
        (∀ t, t ∈ Q' ↔ t ∈ z.2.2 ∧ t ≤ c.pcLog.length) ∧ psBounded z.2.1 (bnd z.2.1) ∧
        (∀ t, c.pcLog.length < t → t ∈ x.2.2 → t ∈ z.2.2) ∧ (∀ t, t ∈ z.2.2 → t ∈ x.2.2) := by
  intro x z τ1 h
  induction h with
  | refl x =>
    intro c Q _ _ hag hQ hb _
    refine ⟨Q, ?_, hQ, hb, fun _ _ h => h, fun _ h => h⟩
    rw [set_of_get hag]
    exact .refl _
  | step x l ots p' ws' prom' tr z hq hp hm hrest ih =>
    intro c Q himg hpre hag hQ hb hfit
    have hs := memStep_self hm hb
    have hz : bnd ws' ≤ bnd z.2.1 := (soloQ_bnd hrest hs.2.2.2).1
    have hr : readsLe l c.pcLog.length ∧ ∀ ts, ots = some ts → ts ≤ c.pcLog.length := by
      rcases hfit with hf | hf
      · exact ⟨fun b t hl => bytesAll_mono (fun _ _ _ h => by omega) _ _ (hs.2.1 b t hl),
          fun ts e => by have := hs.2.2.1 ts e; omega⟩
      · have hl := memStep_len hm
        exact ⟨fun b t e => bytesAll_mono (fun _ _ _ h => by omega) _ _ (hl.1 b t e),
          fun ts e => by have := hl.2 ts e; omega⟩
    obtain ⟨Q1, hm1, hQ1⟩ := memStep_restrict Q hm hpre hinv hr.1 hr.2 hQ
    have hst : pmStep pstep c (.st A l ots) ⟨c.pcImg, c.pcLog, (), c.pcAgs.set A ⟨p', ws', Q1⟩⟩ :=
      pmStep.state c A _ l ots p' () ws' Q1 hag hp (himg ▸ hm1)
    obtain ⟨Q', h1, h2, h3, h4, h5⟩ := ih ⟨c.pcImg, c.pcLog, (), c.pcAgs.set A ⟨p', ws', Q1⟩⟩ Q1 himg hpre
      (getElem?_set_eq_of hag) hQ1 hs.2.2.2 hfit
    refine ⟨Q', ?_, h2, h3, fun t ht hx => h4 t ht ?_, fun t ht => ?_⟩
    · have e : (⟨c.pcImg, c.pcLog, (), (c.pcAgs.set A ⟨p', ws', Q1⟩).set A ⟨z.1, z.2.1, Q'⟩⟩ : PCfg P Unit) =
          ⟨c.pcImg, c.pcLog, c.pcDev, c.pcAgs.set A ⟨z.1, z.2.1, Q'⟩⟩ := by
        rw [List.set_set]
      rw [← e]
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

/-- THE FINAL PHASE: with the whole of `M` in the log and no release left, run the harts `0, …, k−1` to their
ends. -/
theorem runAll (hinv : invalFree M) {c : PCfg P Unit} {J : Fin N → Job P}
    (himg : c.pcImg = img) (hlog : c.pcLog = M) (hlen : c.pcAgs.length = N)
    (hh : ∀ h : Fin N, ∃ Q, c.pcAgs[(h : Nat)]? = some ⟨(J h).x.1, (J h).x.2.1, Q⟩ ∧
      (∀ t, t ∈ Q ↔ t ∈ (J h).x.2.2 ∧ t ≤ M.length) ∧ soloQ pstep img M h QN (J h).x (J h).τ (J h).y ∧
      psBounded (J h).x.2.1 (bnd (J h).x.2.1)) :
    ∀ k, k ≤ N → ∃ es c', nfSteps pstep c es c' ∧ c'.pcImg = img ∧ c'.pcLog = M ∧ c'.pcAgs.length = N ∧
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
    obtain ⟨Q', g1, g2, _, _, _⟩ := runSeg hinv hrun c' Q h2 (by rw [h3]; exact List.prefix_refl _) hag hQ hb
      (.inr (by rw [h3]; exact Nat.le_refl _))
    refine ⟨es ++ stEvs A (J A).τ, _, nfSteps_append h1 g1, h2, h3, by simp [h4], fun h => ?_, fun h => ?_⟩
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

/-- THE SCHEDULE (plan §4's construction), by induction on `|M| − n`. -/
theorem schedule (hmsg : ∀ m ∈ M, msgOk N m) (hinv : invalFree M) :
    ∀ (d : Nat) {c : PCfg P Unit} {J : Fin N → Job P} {n : Nat}, M.length - n ≤ d → Inv pstep img M N c J n →
      ∃ es c', nfSteps pstep c es c' ∧ Final img M N c' J ∧
        ∀ h, traceOf h es = if hN : h < N then (J ⟨h, hN⟩).τ else [] := by
  intro d
  induction d using Nat.strongRecOn with
  | _ d ihd =>
  intro c J n hd hI
  classical
  -- the first release of each hart, if any
  let S : Nat → Prop := fun r => ∃ h : Fin N, ∃ τ1 z l p' ws' prom' τ2,
    soloQ pstep img M h QN (J h).x τ1 z ∧ relClass z.2.1 l ∧ z.2.1.wIfr < r ∧ n < r ∧
    pstep z.1 () l p' () ∧ memStep img M h z.2.2 z.2.1 l (some r) ws' prom' ∧
    soloQ pstep img M h QF (p', ws', prom') τ2 (J h).y ∧ (J h).τ = τ1 ++ (l, some r) :: τ2
  obtain ⟨himg, hlog, hle, hlen, hh⟩ := hI
  have hsplit : ∀ h : Fin N, soloQ pstep img M h QN (J h).x (J h).τ (J h).y ∨ ∃ r, S r ∧
      ∃ τ1 z l p' ws' prom' τ2,
      soloQ pstep img M h QN (J h).x τ1 z ∧ relClass z.2.1 l ∧ z.2.1.wIfr < r ∧ n < r ∧
      pstep z.1 () l p' () ∧ memStep img M h z.2.2 z.2.1 l (some r) ws' prom' ∧
      soloQ pstep img M h QF (p', ws', prom') τ2 (J h).y ∧ (J h).τ = τ1 ++ (l, some r) :: τ2 := by
    intro h
    obtain ⟨_, _, _, hq, _⟩ := hh h
    rcases soloQ_split hq with e | ⟨τ1, z, l, r, p', ws', prom', τ2, k1, k2, k3, k4, k5, k6, k7, k8⟩
    · exact .inl e
    · exact .inr ⟨r, ⟨h, τ1, z, l, p', ws', prom', τ2, k1, k2, k3, k4, k5, k6, k7, k8⟩,
        τ1, z, l, p', ws', prom', τ2, k1, k2, k3, k4, k5, k6, k7, k8⟩
  by_cases hS : ∃ r, S r
  · -- a release remains: process the least one
    obtain ⟨r, hSr, hmin⟩ := exists_min S hS
    obtain ⟨A, τ1, z, l, p', ws', prom', τ2, k1, k2, k3, k4, k5, k6, k7, k8⟩ := hSr
    obtain ⟨⟨pv, hpv, hpvlt⟩, m, hm, hmt⟩ := memStep_write k6
    have hrM : r ≤ M.length := by have := (List.getElem?_eq_some_iff.1 hm).1; omega
    -- every other hart's releases are above `r`
    have hother : ∀ h : Fin N, h ≠ A → soloQ pstep img M h (QFG r) (J h).x (J h).τ (J h).y := by
      intro h hne
      rcases hsplit h with e | ⟨rh, hSh, τ1', z', l', p'', ws'', prom'', τ2', j1, j2, j3, j4, j5, j6, j7, j8⟩
      · exact soloQ_QN_QFG e
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
        refine soloQ_append (soloQ_QN_QFG j1) (.step _ _ _ _ _ _ _ _ (fun _ r' e => ?_) j5 j6
          (soloQ_raise j7 (Nat.le_trans (by omega) ((memStep_vw j6).2 rh rfl))))
        cases e; exact ⟨j3, by omega⟩
    -- hart `A`'s whole run, above `r − 1`
    have hAq : soloQ pstep img M A (QFG (r - 1)) (J A).x (J A).τ (J A).y := by
      rw [k8]
      exact soloQ_append (soloQ_QN_QFG k1) (.step _ _ _ _ _ _ _ _ (fun _ r' e => by cases e; exact ⟨k3, by omega⟩)
        k5 k6 (soloQ_raise k7 (Nat.le_trans (by omega) ((memStep_vw k6).2 r rfl))))
    have hall : ∀ h : Fin N, soloQ pstep img M h (QFG (r - 1)) (J h).x (J h).τ (J h).y := by
      intro h
      by_cases e : h = A
      · subst e; exact hAq
      · exact soloQ_QFG_anti (by omega) (hother h e)
    -- 1. promises up to `r − 1`
    obtain ⟨es1, c1, n1, i1, n1tr⟩ := promsUpTo hmsg (r - 1 - n) (k := r - 1) (by omega)
      ⟨himg, hlog, hle, hlen, hh⟩ (by omega) hall
    obtain ⟨g1, g2, g3, g4, g5⟩ := i1
    have hc1len : c1.pcLog.length = r - 1 := by rw [g2]; exact take_length_of (by omega)
    -- 2. hart `A`'s segment up to its release
    obtain ⟨QA, hagA, hQA, _, hwA, hfA, hbA⟩ := g5 A
    have hbz : bnd z.2.1 < r := by
      have h1 := relClass_lt k6 k2
      unfold bnd; omega
    obtain ⟨Qz, s1, s2, s3, s4, s5⟩ := runSeg hinv k1 c1 QA g1 (by rw [g2]; exact take_prefix M _) hagA
      (by rw [hc1len]; exact hQA) hbA (.inl (by omega))
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
      intro b t e
      have := memStep_reads_wr k6 s3 b t e
      obtain ⟨pv', hpv', hle'⟩ := k2
      rw [hpv] at hpv'; cases hpv'
      rw [hlog3, take_length_of hrM]
      exact bytesAll_mono (fun _ _ _ u => by omega) _ _ this
    obtain ⟨Q4, hm4, hQ4⟩ := memStep_restrict _ k6 (by rw [hlog3]; exact take_prefix M r) hinv hrd
      (fun ts e => by cases e; rw [hlog3, take_length_of hrM]; exact Nat.le_refl _) hQ3
    have hag3 : c3.pcAgs[(A : Nat)]? = some ⟨z.1, z.2.1, {c2.pcLog.length + 1} ∪ Qz⟩ := getElem?_set_eq_of hag2
    let c4 : PCfg P Unit := ⟨c3.pcImg, c3.pcLog, (), c3.pcAgs.set A ⟨p', ws', Q4⟩⟩
    have himg3 : c3.pcImg = img := g1
    have hrst := pmStep.state (pstep := pstep) c3 A _ l (some r) p' () ws' Q4 hag3 k5 (himg3 ▸ hm4)
    have hr3 : r = c3.pcLog.length := by rw [hlog3, take_length_of hrM]
    -- the invariant after the release
    let J' : Fin N → Job P := fun h => if h = A then ⟨(p', ws', prom'), τ2, (J A).y⟩ else J h
    have hself := memStep_self k6 s3
    have hI4 : Inv pstep img M N c4 J' r := by
      refine ⟨g1, hlog3, hrM, by simp [c4, c3, c2, g4], fun h => ?_⟩
      by_cases e : h = A
      · subst e
        simp only [J', if_true]
        refine ⟨Q4, getElem?_set_eq_of hag3, fun t => by rw [hQ4 t, hlog3, take_length_of hrM],
          soloQ_raise k7 ((memStep_vw k6).2 r rfl), ?_, fun t ht ho => ?_, hself.2.2.2⟩
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
      nfSteps_append n1 (nfSteps_append s1 (.rel _ _ _ _ _ _ _ _ _ _ hpst hag3 k2 hr3 hrst n4)), ?_, ?_⟩
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
  · -- no release remains: the final phase
    have hN : ∀ h : Fin N, soloQ pstep img M h QN (J h).x (J h).τ (J h).y := by
      intro h
      rcases hsplit h with e | ⟨r, hSr, _⟩
      · exact e
      · exact absurd ⟨r, hSr⟩ hS
    obtain ⟨es1, c1, n1, i1, n1tr⟩ := promsUpTo hmsg (M.length - n) (k := M.length) (by omega)
      ⟨himg, hlog, hle, hlen, hh⟩ (Nat.le_refl _) (fun h => soloQ_QN_QFG (hN h))
    obtain ⟨g1, g2, _, g4, g5⟩ := i1
    have hlogM : c1.pcLog = M := by rw [g2]; exact List.take_length
    obtain ⟨es2, c2, n2, f1, f2, f3, f5, f6⟩ := runAll hinv g1 hlogM g4 (fun h => by
      obtain ⟨Q, u1, u2, _, _, _, u6⟩ := g5 h
      exact ⟨Q, u1, u2, hN h, u6⟩) N (Nat.le_refl _)
    refine ⟨es1 ++ es2, c2, nfSteps_append n1 n2, ⟨f1, f2, f3, fun h => ?_⟩, fun h => ?_⟩
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
        -- the final promise set is a subset of the initial one, which `promWf` bounds
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

/-! ## 5. The NF_R lemma -/

/-- (P2) FETCH-BOUNDED (plan §4, premise of NF_R): in every hart's solo run (the run's trace from its initial
state, against the final memory `M`), every release-class write at `r` has every earlier fetch source below `r`. -/
def fetchBounded {P : Type} (pstep : P → Unit → PLabel → P → Unit → Prop) (img : Image) (ps : List P)
    (M : List PMsg) (evs : List PEvt) : Prop :=
  ∀ h p (P0 : GSet Nat) y, ps[h]? = some p → (∀ t, t ∈ P0 ↔ 0 < t ∧ ownTs M h t) →
    soloSteps pstep img M h (p, psInit, P0) (traceOf h evs) y →
    soloQ pstep img M h QF (p, psInit, P0) (traceOf h evs) y

/-- THE NF_R LEMMA (plan §4, program-agnostic; machine v2, no device fabric).  Every valid run whose final memory
has no invalidate-class CMO and which is fetch-bounded (P2) can be rescheduled into an NF_R run (`nfRun`) with the
same final configuration (memory, program states, hart states, empty promise sets) and the same per-hart traces.
(P1) holds of every v2 run by construction; (P3), (P4) are vacuous on v2 (no walk, no A/D arm). -/
theorem nfR {P : Type} {pstep : P → Unit → PLabel → P → Unit → Prop} {img : Image} {ps : List P}
    {evs : List PEvt} {cfg : PCfg P Unit} (hv : validRun pstep img () ps evs cfg)
    (hfb : fetchBounded pstep img ps cfg.pcLog evs) (hinv : invalFree cfg.pcLog) :
    ∃ evs', nfRun pstep img () ps evs' cfg ∧ ∀ h, traceOf h evs' = traceOf h evs := by
  classical
  let M := cfg.pcLog
  let N := ps.length
  have hwf := pmSteps_wf hv.1 (pmInit_wf img () ps)
  have hlenN : cfg.pcAgs.length = N := by rw [pmSteps_len hv.1]; simp [pmInit, N]
  have hmsg : ∀ m ∈ M, msgOk N m := fun m hm => by rw [← hlenN]; exact hwf.2 m hm
  have hsolo := validRun_solo hv
  have hps : ∀ h : Fin N, ps[(h : Nat)]? = some ps[(h : Nat)] := fun h => List.getElem?_eq_getElem h.isLt
  -- the jobs: every hart's solo run against `M`
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
  have hI : Inv pstep img M N (pmInit img () ps) J 0 := by
    refine ⟨rfl, by simp [pmInit], Nat.zero_le _, by simp [pmInit, N], fun h => ?_⟩
    obtain ⟨h1, h2⟩ := hP0 h
    refine ⟨∅, by simp [pmInit, hps h, J], fun t => ?_, ?_, fun t ht => ?_, fun t _ ho => ?_, psInit_bnd _⟩
    · constructor
      · intro u; exact absurd u notElemOfEmpty
      · rintro ⟨u1, u2⟩
        have := ((h1 t).1 u1).1
        omega
    · exact soloQ_raise (hfb h _ _ _ (hps h) h1 h2) (Nat.zero_le _)
    · obtain ⟨u1, m, hm, hmt⟩ := (h1 t).1 ht
      exact ⟨u1, by have := (List.getElem?_eq_some_iff.1 hm).1; omega, m, hm, hmt⟩
    · exact (h1 t).2 ⟨by omega, ho⟩
  obtain ⟨es, c', hnf, ⟨f1, f2, f3, f4⟩, htr⟩ := schedule hmsg hinv (M.length - 0) (Nat.le_refl _) hI
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

/-! ## 6. PO-fetch for programs that fetch only the image (the G4 targets) -/

/-- Every fetch of the trace reads the image (timestamp 0): plan §4 "every fetch reads the image (PA-0)". -/
def fetchImgOnly (τ : List (PLabel × Option Nat)) : Prop :=
  ∀ e ∈ τ, ∀ base tvs, e.1 = LIFetch base tvs → ∀ tv ∈ tvs, tv.1 = 0

theorem bytesMax_zero : ∀ (a : Int) (tvs : List (Nat × BitVec 8)), (∀ tv ∈ tvs, tv.1 = 0) →
    bytesMax (fun _ t => t) a tvs = 0
  | _, [], _ => rfl
  | a, (t, v) :: r, h => by
    simp only [bytesMax]
    have h1 := h (t, v) (List.mem_cons_self ..)
    have h2 := bytesMax_zero (a + 1) r (fun tv htv => h tv (List.mem_cons_of_mem _ htv))
    simp only at h1
    omega

theorem soloQ_ofImg {P : Type} {pstep : P → Unit → PLabel → P → Unit → Prop} {img : Image} {M : List PMsg}
    {i : Nat} : ∀ {x y τ}, soloSteps pstep img M i x τ y → x.2.1.wIfr = 0 → fetchImgOnly τ →
      soloQ pstep img M i QF x τ y := by
  intro x y τ h
  induction h with
  | refl => intro _ _; exact .refl _
  | step x l ots p' ws' prom' tr y hp hm _ ih =>
    intro h0 hf
    refine .step _ _ _ _ _ _ _ _ (fun hr r e => ?_) hp hm (ih ?_ (fun e he => hf e (List.mem_cons_of_mem _ he)))
    · subst e; have := relClass_lt hm hr; omega
    · cases hm with
      | fetch base tvs hok =>
        show max x.2.1.wIfr (bytesMax (fun _ t => t) base tvs) = 0
        rw [bytesMax_zero base tvs (hf _ (List.mem_cons_self ..) base tvs rfl), h0]; rfl
      | load => simp only [loadRun]; rw [(loadBytes_keep _ _ _ _ _).2.2.1]; exact h0
      | lr => simp only [loadRun]; rw [(loadBytes_keep _ _ _ _ _).2.2.1]; exact h0
      | amoLd => simp only [loadRun]; rw [(loadBytes_keep _ _ _ _ _).2.2.1]; exact h0
      | rmw =>
        simp only [amoPost]; rw [(storeRun_keep _ _ _ _ _ _ _).2.2, (loadRun_keep _ _ _ _ _ _).2.2.1]; exact h0
      | store => simp only [acqPost]; rw [(storeRun_keep _ _ _ _ _ _ _).2.2]; exact h0
      | amoSt => simp only [amoPost]; rw [(storeRun_keep _ _ _ _ _ _ _).2.2]; exact h0
      | sc => simp only [acqPost]; rw [(storeRun_keep _ _ _ _ _ _ _).2.2]; exact h0
      | cmo => simp only [cmoPost]; rw [(cohRaise_keep _ _ _ _).2.2]; exact h0
      | _ => exact h0

/-- PO-FETCH for programs that fetch only the image: fetch-boundedness (P2) holds. -/
theorem fetchBounded_ofImg {P : Type} {pstep : P → Unit → PLabel → P → Unit → Prop} {img : Image} {ps : List P}
    {M : List PMsg} {evs : List PEvt} (h : ∀ hh, fetchImgOnly (traceOf hh evs)) :
    fetchBounded pstep img ps M evs :=
  fun hh _ _ _ _ _ hs => soloQ_ofImg hs rfl (h hh)

end Weak.Prom.Nfr
