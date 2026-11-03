/-
Weak/Prom: **machine lemmas of valid runs used by A0** (stage S2; plan rev 7 §0 A0 (iii), (v) and the per-hart
projection of §2 "Run shape (regime A)").  No logic: facts about machine v2 (`Weak/Prom/Machine.lean`) only.

* `sepD`/`validRun_soloD` — the device-general form of MachSolo.lean's hart separation: every valid run gives, for
  every hart, a SOLO RUN against the final memory over the program half `anyFab pstep` ("some fabric values make the
  step").  No device premise is needed for this direction: the solo run forgets which fabric values occurred.
* `soloSteps_take` — every prefix of a solo run is a solo run (A0 (ii) speaks of every prefix).
* `solo_fulfils` — a solo run's fulfil list is duplicate-free and is exactly the promises it discharged.
* `validRun_partition` — A0 (iii) (plan §2 "The partition").
* `validRun_traceWf` — A0 (v) (plan §2 `run.traceWf M`, [R7.s4]).
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.CoreDefs

namespace Weak.Prom.PF

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom
open PLabel

variable {P D : Type}

/-! ## 1. Hart separation over any fabric -/

/-- The program half with the fabric forgotten: some fabric values make the step (plan §2: each hart's state-phase
run depends only on `M` and its own state once the fabric's values are quantified). -/
def anyFab (pstep : P → D → PLabel → P → D → Prop) : P → Unit → PLabel → P → Unit → Prop :=
  fun p _ l p' _ => ∃ d d', pstep p d l p' d'

/-- HART SEPARATION for any fabric (MachSolo.lean `sep`, device-general). -/
theorem sepD {pstep : P → D → PLabel → P → D → Prop} {M : List PMsg} :
    ∀ {c c'' : PCfg P D} {sts : List PEvt}, pmSteps pstep c sts c'' → (∀ e ∈ sts, e.isSt = true) →
      c.pcLog = M → ∀ h ag, c.pcAgs[h]? = some ag → ∃ ag'', c''.pcAgs[h]? = some ag'' ∧
        soloSteps (anyFab pstep) c.pcImg M h (ag.paSt, ag.paWs, ag.paProm) (traceOf h sts)
          (ag''.paSt, ag''.paWs, ag''.paProm) := by
  intro c c'' sts hrun
  induction hrun with
  | refl => intro _ _ h ag hag; exact ⟨ag, hag, .refl _⟩
  | step c0 c1 c2 e es hst hrest ih =>
    intro hst' hM h ag hag
    cases hst with
    | promise => exact absurd (hst' _ (List.mem_cons_self ..)) (by simp [PEvt.isSt])
    | state i ag0 l ots st' d' ws' prom' hag0 hp hm =>
      have hst1 : ∀ e ∈ es, e.isSt = true := fun e he => hst' e (List.mem_cons_of_mem _ he)
      by_cases hih : i = h
      · subst hih
        rw [hag] at hag0
        cases hag0
        obtain ⟨ag'', h1, h2⟩ := ih hst1 hM i ⟨st', ws', prom'⟩ (getElem?_set_eq_of hag)
        refine ⟨ag'', h1, ?_⟩
        simp only [traceOf, if_true]
        exact .step _ l ots st' ws' prom' _ _ ⟨_, _, hp⟩ (hM ▸ hm) h2
      · obtain ⟨ag'', h1, h2⟩ := ih hst1 hM h ag (by simp only [List.getElem?_set_ne hih]; exact hag)
        refine ⟨ag'', h1, ?_⟩
        simp only [traceOf, if_neg hih]
        exact h2

/-- EVERY VALID RUN SEPARATES, any fabric (MachSolo.lean `validRun_solo`, device-general). -/
theorem validRun_soloD {pstep : P → D → PLabel → P → D → Prop} {img : Image} {d0 : D} {ps : List P}
    {evs : List PEvt} {cfg : PCfg P D} (h : Weak.Prom.validRun pstep img d0 ps evs cfg) :
    ∀ hh p, ps[hh]? = some p → ∃ ag, cfg.pcAgs[hh]? = some ag ∧ ∃ P0 : GSet Nat,
      (∀ t, t ∈ P0 ↔ 0 < t ∧ ownTs cfg.pcLog hh t) ∧
      soloSteps (anyFab pstep) img cfg.pcLog hh (p, psInit, P0) (traceOf hh evs) (ag.paSt, ag.paWs, ag.paProm) := by
  intro hh p hp
  obtain ⟨c0, himg, hlog, _, hags, hs⟩ := validRun_statePhase h
  obtain ⟨ag0, h1, h2, h3, h4⟩ := hags hh p hp
  obtain ⟨ag'', k1, k2⟩ := sepD hs (filter_isSt evs) hlog hh ag0 h1
  refine ⟨ag'', k1, ag0.paProm, h4, ?_⟩
  rw [himg, h2, h3, traceOf_filter] at k2
  exact k2

/-! ## 2. Harts outside the domain, image, lengths -/

theorem traceOf_none {pstep : P → D → PLabel → P → D → Prop} {h : Nat} :
    ∀ {c c' : PCfg P D} {evs : List PEvt}, pmSteps pstep c evs c' → c.pcAgs[h]? = none → traceOf h evs = [] := by
  intro c c' evs hrun
  induction hrun with
  | refl => intro _; rfl
  | step c0 c1 c2 e es hst _ ih =>
    intro hn
    cases hst with
    | promise i ag m hag _ _ =>
      have hih : i ≠ h := by intro e; subst e; rw [hag] at hn; cases hn
      simp only [traceOf]
      exact ih (by simp only [List.getElem?_set_ne hih]; exact hn)
    | state i ag l ots st' d' ws' prom' hag _ _ =>
      have hih : i ≠ h := by intro e; subst e; rw [hag] at hn; cases hn
      simp only [traceOf, if_neg hih]
      exact ih (by simp only [List.getElem?_set_ne hih]; exact hn)

theorem pmSteps_img {pstep : P → D → PLabel → P → D → Prop} :
    ∀ {c c' : PCfg P D} {evs : List PEvt}, pmSteps pstep c evs c' → c'.pcImg = c.pcImg := by
  intro c c' evs hrun
  induction hrun with
  | refl => rfl
  | step c0 c1 c2 e es hst _ ih => rw [ih]; cases hst <;> rfl

theorem validRun_len {pstep : P → D → PLabel → P → D → Prop} {img : Image} {d0 : D} {ps : List P}
    {evs : List PEvt} {cfg : PCfg P D} (h : Weak.Prom.validRun pstep img d0 ps evs cfg) :
    cfg.pcAgs.length = ps.length := by
  rw [pmSteps_len h.1]; simp [pmInit]

theorem validRun_traceNone {pstep : P → D → PLabel → P → D → Prop} {img : Image} {d0 : D} {ps : List P}
    {evs : List PEvt} {cfg : PCfg P D} (h : Weak.Prom.validRun pstep img d0 ps evs cfg) {hh : Nat}
    (hn : ps[hh]? = none) : traceOf hh evs = [] :=
  traceOf_none h.1 (by simp [pmInit, hn])

theorem validRun_img {pstep : P → D → PLabel → P → D → Prop} {img : Image} {d0 : D} {ps : List P}
    {evs : List PEvt} {cfg : PCfg P D} (h : Weak.Prom.validRun pstep img d0 ps evs cfg) : cfg.pcImg = img :=
  pmSteps_img h.1

/-! ## 3. Solo runs: prefixes and fulfils -/

theorem soloSteps_take {pst : P → Unit → PLabel → P → Unit → Prop} {img : Image} {M : List PMsg} {i : Nat} :
    ∀ {x y : P × PState × GSet Nat} {tr : List (PLabel × Option Nat)}, soloSteps pst img M i x tr y →
      ∀ k, ∃ z, soloSteps pst img M i x (tr.take k) z ∧ soloSteps pst img M i z (tr.drop k) y := by
  intro x y tr h
  induction h with
  | refl x => intro k; exact ⟨x, by simp; exact .refl _, by simp; exact .refl _⟩
  | step x l ots p' ws' prom' tr y hp hm hrest ih =>
    intro k
    cases k with
    | zero => exact ⟨x, .refl _, .step _ _ _ _ _ _ _ _ hp hm hrest⟩
    | succ k =>
      obtain ⟨z, h1, h2⟩ := ih k
      exact ⟨z, by simpa using soloSteps.step _ _ _ _ _ _ _ _ hp hm h1, by simpa using h2⟩

/-- A solo run's fulfil list is duplicate-free and is exactly the promises it discharged. -/
theorem solo_fulfils {pst : P → Unit → PLabel → P → Unit → Prop} {img : Image} {M : List PMsg} {i : Nat} :
    ∀ {x y : P × PState × GSet Nat} {tr : List (PLabel × Option Nat)}, soloSteps pst img M i x tr y →
      (tr.filterMap (fun e => e.2)).Nodup ∧
      (∀ t, t ∈ tr.filterMap (fun e => e.2) ↔ t ∈ x.2.2 ∧ t ∉ y.2.2) ∧ (∀ t, t ∈ y.2.2 → t ∈ x.2.2) := by
  intro x y tr h
  induction h with
  | refl x => exact ⟨List.nodup_nil, fun t => by simp, fun t ht => ht⟩
  | step x l ots p' ws' prom' tr y hp hm hrest ih =>
    obtain ⟨ihn, ihm, ihs⟩ := ih
    rcases memStep_prom hm with ⟨he, hpr⟩ | ⟨ts, he, hts, hpr⟩
    · subst he hpr
      simp only [List.filterMap_cons]
      exact ⟨ihn, ihm, ihs⟩
    · subst he hpr
      simp only [List.filterMap_cons]
      refine ⟨List.nodup_cons.2 ⟨fun hin => ?_, ihn⟩, fun t => ?_, fun t ht => ?_⟩
      · exact (elemOfDifference.1 ((ihm ts).1 hin).1).2 (elemOfSingleton.2 rfl)
      · constructor
        · intro ht
          rcases List.mem_cons.1 ht with rfl | ht
          · exact ⟨hts, fun hy => (elemOfDifference.1 (ihs _ hy)).2 (elemOfSingleton.2 rfl)⟩
          · exact ⟨(elemOfDifference.1 ((ihm t).1 ht).1).1, ((ihm t).1 ht).2⟩
        · rintro ⟨h1, h2⟩
          by_cases e : t = ts
          · subst e; exact List.mem_cons_self ..
          · exact List.mem_cons_of_mem _
              ((ihm t).2 ⟨elemOfDifference.2 ⟨h1, fun hs => e (elemOfSingleton.1 hs)⟩, h2⟩)
      · exact (elemOfDifference.1 (ihs t ht)).1

/-! ## 4. A0 (iii): the partition -/

/-- The fulfils of a hart of the domain are exactly its own messages (`noPromises` at the end). -/
theorem validRun_fulfils_iff {pstep : P → D → PLabel → P → D → Prop} {img : Image} {d0 : D} {ps : List P}
    {evs : List PEvt} {cfg : PCfg P D} (h : Weak.Prom.validRun pstep img d0 ps evs cfg) {hh : Nat} {p : P}
    (hp : ps[hh]? = some p) :
    (fulfilsOf hh evs).Nodup ∧ ∀ t, t ∈ fulfilsOf hh evs ↔ 0 < t ∧ ownTs cfg.pcLog hh t := by
  obtain ⟨ag, hag, P0, hP0, hs⟩ := validRun_soloD h hh p hp
  obtain ⟨hn, hm, _⟩ := solo_fulfils hs
  have he : ag.paProm = ∅ := h.2 hh ag hag
  refine ⟨hn, fun t => ?_⟩
  unfold fulfilsOf
  rw [hm t, ← hP0 t]
  simp only [he]
  exact ⟨fun h => h.1, fun h => ⟨h, notElemOfEmpty⟩⟩

/-- **A0 (iii)** (plan §2 "The partition"): every timestamp of `M` is fulfilled by exactly one hart, its author,
and no hart fulfils a timestamp twice. -/
theorem validRun_partition {pstep : P → D → PLabel → P → D → Prop} {img : Image} {d0 : D} {ps : List P}
    {M : List PMsg} {run : PFRun P D} (h : validRun pstep img d0 ps M run) :
    (∀ t, 1 ≤ t → t ≤ M.length → exU (fun hh => t ∈ run.fulfils hh ∧ tidAt M t = some hh)) ∧
    (∀ hh, (run.fulfils hh).Nodup) := by
  obtain ⟨hv, hM⟩ := h
  subst hM
  have hdom : ∀ hh : Nat, (∃ p, ps[hh]? = some p) ∨ ps[hh]? = none := fun hh => by
    cases ps[hh]? <;> simp
  refine ⟨fun t h1 h2 => ?_, fun hh => ?_⟩
  · have hk : t - 1 < run.cfg.pcLog.length := by omega
    obtain ⟨m, hm⟩ : ∃ m, run.cfg.pcLog[t - 1]? = some m := ⟨_, List.getElem?_eq_getElem hk⟩
    have hmsg : msgAt run.cfg.pcLog t = some m := by
      cases t with
      | zero => omega
      | succ k => exact hm
    have hwf := pmSteps_wf hv.1 (pmInit_wf img d0 ps)
    obtain ⟨_, i, hti, hil⟩ := hwf.2 m (List.mem_of_getElem? hm)
    rw [validRun_len hv] at hil
    obtain ⟨p, hp⟩ : ∃ p, ps[i]? = some p := ⟨_, List.getElem?_eq_getElem hil⟩
    have htid : tidAt run.cfg.pcLog t = some i := by simp [tidAt, hmsg, hti]
    refine ⟨i, ⟨((validRun_fulfils_iff hv hp).2 t).2 ⟨by omega, m, hm, hti⟩, htid⟩, ?_⟩
    rintro j ⟨hj, _⟩
    rcases hdom j with ⟨q, hq⟩ | hq
    · obtain ⟨_, m', hm', hti'⟩ := ((validRun_fulfils_iff hv hq).2 t).1 hj
      rw [hm] at hm'; cases hm'
      rw [hti] at hti'; cases hti'; rfl
    · have : fulfilsOf j run.evs = [] := by unfold fulfilsOf; rw [validRun_traceNone hv hq]; rfl
      exact absurd hj (by unfold PFRun.fulfils; rw [this]; simp)
  · rcases hdom hh with ⟨q, hq⟩ | hq
    · exact (validRun_fulfils_iff hv hq).1
    · unfold PFRun.fulfils fulfilsOf; rw [validRun_traceNone hv hq]; exact List.nodup_nil

/-! ## 5. A0 (v): trace well-formedness -/

/-- One state step's trace entry is well-formed against the memory it ran against. -/
theorem memStep_entryWf {img : Image} {log : List PMsg} {i : Nat} {prom : GSet Nat} {ws : PState} {l : PLabel}
    {ots : Option Nat} {ws' : PState} {prom' : GSet Nat} (h : memStep img log i prom ws l ots ws' prom') :
    traceWf img log i [(l, ots)] := by
  intro e he
  rw [List.mem_singleton] at he
  subst he
  have rd : ∀ {vpre : Nat} {base : Int} {tvs : List (Nat × BitVec 8)}, loadOk img log ws vpre base tvs →
      bytesAll (fun a t v => memByte img log t a = some v) base tvs :=
    fun hl => bytesAll_mono (fun _ _ _ hp => hp.1) _ _ hl
  cases h with
  | silent => exact ⟨fun _ _ h => (by cases h), trivial⟩
  | load _ _ _ _ _ hl => exact ⟨fun b t h => (by cases h; exact rd hl), trivial⟩
  | store _ _ _ _ _ _ ts _ hm => exact ⟨fun _ _ h => (by cases h), ⟨_, hm, rfl, rfl, rfl⟩⟩
  | rmw _ _ _ _ _ _ _ ts _ _ hm hl => exact ⟨fun b t h => (by cases h; exact rd hl), ⟨_, hm, rfl, rfl, rfl⟩⟩
  | amoLd _ _ _ _ hl => exact ⟨fun b t h => (by cases h; exact rd hl), trivial⟩
  | amoSt _ _ _ _ _ ts _ _ _ _ _ hm => exact ⟨fun _ _ h => (by cases h), ⟨_, hm, rfl, rfl, rfl⟩⟩
  | fence => exact ⟨fun _ _ h => (by cases h), trivial⟩
  | fenceI => exact ⟨fun _ _ h => (by cases h), trivial⟩
  | dev => exact ⟨fun _ _ h => (by cases h), trivial⟩
  | regW => exact ⟨fun _ _ h => (by cases h), trivial⟩
  | ctrl => exact ⟨fun _ _ h => (by cases h), trivial⟩
  | instr => exact ⟨fun _ _ h => (by cases h), trivial⟩
  | lr _ _ _ _ _ hl => exact ⟨fun b t h => (by cases h; exact rd hl), trivial⟩
  | sc _ _ _ _ _ _ ts _ _ _ hm => exact ⟨fun _ _ h => (by cases h), ⟨_, hm, rfl, rfl, rfl⟩⟩
  | scFail => exact ⟨fun _ _ h => (by cases h), trivial⟩
  | fetch _ _ hf =>
    exact ⟨fun b t h => (by cases h; exact bytesAll_mono (fun _ _ _ hp => hp.1) _ _ hf), trivial⟩
  | cmo _ _ _ _ ts _ hm => exact ⟨fun _ _ h => (by cases h), ⟨_, hm, rfl, rfl, rfl⟩⟩

theorem solo_traceWf {pst : P → Unit → PLabel → P → Unit → Prop} {img : Image} {M : List PMsg} {i : Nat} :
    ∀ {x y : P × PState × GSet Nat} {tr : List (PLabel × Option Nat)}, soloSteps pst img M i x tr y →
      traceWf img M i tr := by
  intro x y tr h
  induction h with
  | refl => intro e he; cases he
  | step x l ots p' ws' prom' tr y hp hm hrest ih =>
    intro e he
    rcases List.mem_cons.1 he with rfl | he
    · exact memStep_entryWf hm _ (List.mem_singleton_self _)
    · exact ih e he

/-- **A0 (v)** (plan §2 `run.traceWf M`): every hart's trace is well-formed against the final memory. -/
theorem validRun_traceWf {pstep : P → D → PLabel → P → D → Prop} {img : Image} {d0 : D} {ps : List P}
    {M : List PMsg} {run : PFRun P D} (h : validRun pstep img d0 ps M run) : run.traceWf M := by
  obtain ⟨hv, hM⟩ := h
  subst hM
  intro hh
  rw [validRun_img hv]
  unfold PFRun.trace
  cases hq : ps[hh]? with
  | none => rw [validRun_traceNone hv hq]; intro e he; cases he
  | some p =>
    obtain ⟨_, _, _, _, hs⟩ := validRun_soloD hv hh p hq
    exact solo_traceWf hs

end Weak.Prom.PF
