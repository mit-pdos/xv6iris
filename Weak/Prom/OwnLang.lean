/-
Weak/Prom: **track (b)'s concurrent language** (stage S4b; plan rev 7 §4 "Pull rule": "Promise steps are steps of a
separate *promise agent* thread.  It has no program, and its wp is the invariant, so hart wps keep exactly one ▷ per
label").

One iris-lean `Language` whose thread pool is the N harts plus ONE PROMISE-AGENT thread, over a prophecy world
`OW` holding the final memory `M` of the run being verified.  The language state `OSt` holds the current log length
`n` (the log is `M.take n`, always a prefix of `M`), every hart's promise set, and the values of the harts that
finished.  A hart thread carries its own exact machine state (`PState`, trace) in its expression.

* a hart step is ONE machine-v2 state step of NF_R (NfrRun.lean `nfSteps`): a non-release-class step against the
  current prefix (`hstepO.plain`), or a release-class write that appends its own message `M[n]` and fulfils it in
  place (`hstepO.rel`, the `rel` pair of `nfSteps` as one atomic step);
* the agent step appends `M[n]` as a promise of its author (`ostep.ag`);
* a hart that reached a value and has no outstanding promise may stop (`ostep.fin`), recording its value.

`validRun_lang`: every valid, fetch-bounded run (MachFix-R-b5: no `invalFree`) of machine v2 (`D = Unit`) is an execution of this
language from the initial pool, ending with log `M`, no promise, and every finished hart's value recorded — through
the NF_R lemma `nfR` (NfrRun.lean) and the simulation `nf_sim`.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.NfrRun
import Iris.ProgramLogic.Language

namespace Weak.Prom.Own

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.Nfr
open PLabel
open Iris.ProgramLogic Iris.ProgramLogic.Language

/-- The prophecy world: program half, value map, image, final memory. -/
structure OW (P V : Type) where
  pstep : P → Unit → PLabel → P → Unit → Prop
  pdone : P → Option V
  img : Image
  M : List PMsg

/-- A thread: a hart (index, program state, exact machine state, trace), the promise agent, or a value. -/
inductive OExpr (P V : Type) where
  | hart (w : OW P V) (h : Nat) (s : P) (ws : PState) (τ : List (PLabel × Option Nat))
  | agent (w : OW P V)
  | ret (v : V)

/-- The shared state: log length, promise sets, recorded values. -/
structure OSt (V : Type) where
  n : Nat
  pr : Nat → GSet Nat
  done : Nat → Option V

/-- Point update of a function. -/
def upd {α : Type} (f : Nat → α) (h : Nat) (x : α) : Nat → α := fun j => if j = h then x else f j

theorem upd_eq {α : Type} (f : Nat → α) (h : Nat) (x : α) : upd f h x h = x := by simp [upd]
theorem upd_ne {α : Type} (f : Nat → α) {h j : Nat} (x : α) (e : j ≠ h) : upd f h x j = f j := by simp [upd, e]

variable {P V : Type}

/-- The author of `M[n]`. -/
def authorAt (M : List PMsg) (n : Nat) : Option Nat := (M[n]?).bind PMsg.tid

/-- ONE HART STEP of NF_R. -/
inductive hstepO (w : OW P V) (h : Nat) : OSt V → P → PState → PLabel → Option Nat → P → PState → OSt V → Prop
  | plain (σ : OSt V) (s : P) (ws : PState) (l : PLabel) (ots : Option Nat) (s' : P) (ws' : PState)
      (pr' : GSet Nat) :
      w.pstep s () l s' () → memStep w.img (w.M.take σ.n) h (σ.pr h) ws l ots ws' pr' → ¬ relClass ws l →
      hstepO w h σ s ws l ots s' ws' { σ with pr := upd σ.pr h pr' }
  | rel (σ : OSt V) (s : P) (ws : PState) (l : PLabel) (s' : P) (ws' : PState) (pr' : GSet Nat) :
      σ.n < w.M.length → authorAt w.M σ.n = some h → relClass ws l → w.pstep s () l s' () →
      memStep w.img (w.M.take (σ.n + 1)) h ({σ.n + 1} ∪ σ.pr h) ws l (some (σ.n + 1)) ws' pr' →
      hstepO w h σ s ws l (some (σ.n + 1)) s' ws' { σ with n := σ.n + 1, pr := upd σ.pr h pr' }
  /-- [E-b] THE PROPHECY-FED FETCH (G4 experiment E-b, NfrFetch.lean): an instruction fetch whose bytes are admissible
  against the FINAL memory `M` (`fetchByteOk w.img w.M`: value and FENCE.I window read in `M`), not the prefix; the
  post is Machine.lean's fetch post with the fetch view computed against the prefix and the hart's promise set
  (equal to the machine's, NfrFetch.lean `fetchView_cut`).  No language-state change. -/
  | fetch (σ : OSt V) (s : P) (ws : PState) (base : Int) (tvs : List (Nat × BitVec 8)) (s' : P) :
      w.pstep s () (LIFetch base tvs) s' () → bytesAll (fetchByteOk w.img w.M ws) base tvs →
      hstepO w h σ s ws (LIFetch base tvs) none s'
        { ws with
          wIfr := max ws.wIfr (bytesMax (fun _ t => t) base tvs)
          wIfv := max ws.wIfv (fetchView (w.M.take σ.n) h (σ.pr h) base tvs) } σ

/-- THE AGENT STEP: append `M[n]` as a promise of its author. -/
def agentStep (w : OW P V) (σ σ' : OSt V) : Prop :=
  ∃ i, σ.n < w.M.length ∧ authorAt w.M σ.n = some i ∧
    σ' = { σ with n := σ.n + 1, pr := upd σ.pr i ({σ.n + 1} ∪ σ.pr i) }

inductive ostep : OExpr P V × OSt V → List Unit → OExpr P V × OSt V × List (OExpr P V) → Prop
  | hst (w : OW P V) (h : Nat) (s : P) (ws : PState) (τ : List (PLabel × Option Nat)) (σ : OSt V) (l : PLabel)
      (ots : Option Nat) (s' : P) (ws' : PState) (σ' : OSt V) :
      hstepO w h σ s ws l ots s' ws' σ' →
      ostep (.hart w h s ws τ, σ) [] (.hart w h s' ws' (τ ++ [(l, ots)]), σ', [])
  | fin (w : OW P V) (h : Nat) (s : P) (ws : PState) (τ : List (PLabel × Option Nat)) (σ : OSt V) (v : V) :
      w.pdone s = some v → σ.pr h = ∅ →
      ostep (.hart w h s ws τ, σ) [] (.ret v, { σ with done := upd σ.done h (some v) }, [])
  | ag (w : OW P V) (σ σ' : OSt V) : agentStep w σ σ' → ostep (.agent w, σ) [] (.agent w, σ', [])

instance : PrimStep (OExpr P V) (OSt V) (List Unit) := ⟨ostep⟩

def OExpr.toV : OExpr P V → Option V
  | .ret v => some v
  | _ => none

instance : ToVal (OExpr P V) V where
  toVal := OExpr.toV
  ofVal v := .ret v
  coe_of_toVal_eq_some {e v} h := by
    cases e with
    | ret v' => cases h; rfl
    | _ => cases h
  toVal_coe _ := rfl

instance : Language (OExpr P V) (OSt V) Unit V where
  val_stuck h := by cases h <;> rfl

/-! ## The simulation of NF_R runs -/

/-- The initial pool: the harts `k, k+1, …` at their initial states. -/
def hartsFrom (w : OW P V) : Nat → List P → List (OExpr P V)
  | _, [] => []
  | k, p :: ps => .hart w k p psInit [] :: hartsFrom w (k + 1) ps

theorem hartsFrom_length (w : OW P V) : ∀ (k : Nat) (ps : List P), (hartsFrom w k ps).length = ps.length
  | _, [] => rfl
  | k, _ :: ps => by simp [hartsFrom, hartsFrom_length w (k + 1) ps]

theorem hartsFrom_get (w : OW P V) : ∀ (k : Nat) (ps : List P) (j : Nat) (p : P), ps[j]? = some p →
    (hartsFrom w k ps)[j]? = some (.hart w (k + j) p psInit [])
  | _, [], _, _, h => by cases h
  | k, q :: ps, 0, p, h => by simp at h; subst h; rfl
  | k, q :: ps, j + 1, p, h => by
    simp only [hartsFrom, List.getElem?_cons_succ]
    rw [hartsFrom_get w (k + 1) ps j p (by simpa using h)]
    congr 2; omega

/-- The initial language state. -/
def σ0 : OSt V := ⟨0, fun _ => ∅, fun _ => none⟩

/-- THE SIMULATION RELATION between an NF_R configuration and a language configuration. -/
def Sim (w : OW P V) (N : Nat) (c : PCfg P Unit) (tp : List (OExpr P V)) (σ : OSt V) : Prop :=
  c.pcImg = w.img ∧ c.pcLog = w.M.take σ.n ∧ σ.n ≤ w.M.length ∧ c.pcAgs.length = N ∧ tp.length = N + 1 ∧
    tp[N]? = some (.agent w) ∧ (∀ h, N ≤ h → σ.pr h = ∅) ∧
    (∀ h, h < N → ∃ ag τ, c.pcAgs[h]? = some ag ∧ tp[h]? = some (.hart w h ag.paSt ag.paWs τ) ∧
      σ.pr h = ag.paProm) ∧ σ.done = fun _ => none

theorem take_length' {M : List PMsg} {n : Nat} (h : n ≤ M.length) : (M.take n).length = n := by
  simp [List.length_take]; omega

theorem nsteps_one {tp tp' : List (OExpr P V)} {σ σ' : OSt V} (h : Step (tp, σ) [] (tp', σ')) :
    NSteps 1 (tp, σ) [] (tp', σ') := by
  have := NSteps.cons h (NSteps.refl (tp', σ'))
  simpa using this

theorem nsteps_trans' {k1 k2 : Nat} {ρ1 ρ2 ρ3 : List (OExpr P V) × OSt V} {o1 o2 : List Unit}
    (h1 : NSteps k1 ρ1 o1 ρ2) (h2 : NSteps k2 ρ2 o2 ρ3) : NSteps (k1 + k2) ρ1 (o1 ++ o2) ρ3 := by
  induction h1 with
  | refl => simpa using h2
  | cons hs _ ih =>
    have := NSteps.cons hs (ih h2)
    simpa [Nat.add_right_comm, List.append_assoc] using this

theorem nsteps_trans {k1 k2 : Nat} {ρ1 ρ2 ρ3 : List (OExpr P V) × OSt V}
    (h1 : NSteps k1 ρ1 [] ρ2) (h2 : NSteps k2 ρ2 [] ρ3) : NSteps (k1 + k2) ρ1 [] ρ3 := by
  simpa using nsteps_trans' h1 h2

/-- ONE NF_R EVENT GROUP IS ONE OR TWO LANGUAGE STEPS. -/
theorem nf_sim {w : OW P V} {N : Nat} :
    ∀ {c c' : PCfg P Unit} {es : List PEvt}, nfSteps w.pstep c es c' → c'.pcLog <+: w.M →
      ∀ (tp : List (OExpr P V)) (σ : OSt V), Sim w N c tp σ →
      ∃ k tp' σ', NSteps k (tp, σ) [] (tp', σ') ∧ Sim w N c' tp' σ' := by
  intro c c' es h
  induction h with
  | refl c => intro _ tp σ hs; exact ⟨0, tp, σ, .refl _, hs⟩
  | prom c c1 i m es c2 hst hrest ih =>
    intro hpre tp σ hs
    obtain ⟨himg, hlog, hle, hlen, htp, hag, hprN, hh, hdone⟩ := hs
    cases hst with
    | promise _ ag _ hagi hnt htid =>
    have hpre1 : c.pcLog ++ [m] <+: w.M := List.IsPrefix.trans (List.prefix_refl _)
      (List.IsPrefix.trans (pmSteps_prefix (nfSteps_pm hrest)) hpre)
    have hiN : i < N := by rw [← hlen]; exact (List.getElem?_eq_some_iff.1 hagi).1
    have hclen : c.pcLog.length = σ.n := by rw [hlog]; exact take_length' hle
    have hMn : w.M[σ.n]? = some m := by
      obtain ⟨t, ht⟩ := hpre1
      rw [← ht, List.getElem?_append_left (by simp [hclen])]
      simp [hclen]
    have hnM : σ.n < w.M.length := (List.getElem?_eq_some_iff.1 hMn).1
    let σ' : OSt V := { σ with n := σ.n + 1, pr := upd σ.pr i ({σ.n + 1} ∪ σ.pr i) }
    have hstep : Step (tp, σ) [] (tp, σ') := by
      have := step_update_of_getElem? (Λ := (inferInstance : Language (OExpr P V) (OSt V) Unit V))
        (e := OExpr.agent w) (e' := OExpr.agent w) (i := N) (obs := []) (efs := []) σ σ' hag
        (ostep.ag w σ σ' ⟨i, hnM, by simp [authorAt, hMn, htid], rfl⟩)
      rw [set_of_get hag, List.append_nil] at this
      exact this
    obtain ⟨k, tp', σ'', h1, h2⟩ := ih hpre tp σ' (by
      refine ⟨himg, ?_, hnM, by simp [hlen], htp, hag, fun h hN => ?_, fun h hN => ?_, hdone⟩
      · show c.pcLog ++ [m] = w.M.take (σ.n + 1)
        rw [hlog, take_succ_of hMn]
      · have e : h ≠ i := by omega
        simp only [σ', upd_ne _ _ e]; exact hprN h hN
      · obtain ⟨ag', τ, a1, a2, a3⟩ := hh h hN
        by_cases e : h = i
        · subst e
          rw [hagi] at a1; cases a1
          refine ⟨_, τ, getElem?_set_eq_of hagi, a2, ?_⟩
          simp only [σ', upd_eq, a3, hclen]
        · refine ⟨ag', τ, ?_, a2, ?_⟩
          · simp only; rw [List.getElem?_set_ne (Ne.symm e)]; exact a1
          · simp only [σ', upd_ne _ _ e]; exact a3)
    exact ⟨1 + k, tp', σ'', nsteps_trans (nsteps_one hstep) h1, h2⟩
  | st c c1 i ag l ots es c2 hag hnr hst hrest ih =>
    intro hpre tp σ hs
    obtain ⟨himg, hlog, hle, hlen, htp, hagN, hprN, hh, hdone⟩ := hs
    cases hst with
    | state _ ag0 _ _ st' d' ws' prom' hag0 hp hm =>
    rw [hag] at hag0; cases hag0
    have hiN : i < N := by rw [← hlen]; exact (List.getElem?_eq_some_iff.1 hag).1
    obtain ⟨ag', τ, a1, a2, a3⟩ := hh i hiN
    rw [hag] at a1; cases a1
    let σ' : OSt V := { σ with pr := upd σ.pr i prom' }
    have hm' : memStep w.img (w.M.take σ.n) i (σ.pr i) ag.paWs l ots ws' prom' := by
      rw [← hlog, a3, ← himg]; exact hm
    have hstep : Step (tp, σ) [] (tp.set i (.hart w i st' ws' (τ ++ [(l, ots)])), σ') := by
      have := step_update_of_getElem? (Λ := (inferInstance : Language (OExpr P V) (OSt V) Unit V))
        (obs := []) (efs := []) σ σ' a2
        (ostep.hst w i ag.paSt ag.paWs τ σ l ots st' ws' σ' (.plain σ _ _ l ots st' ws' prom' hp hm' hnr))
      rw [List.append_nil] at this
      exact this
    have hiN' : i ≠ N := by omega
    obtain ⟨k, tp', σ'', h1, h2⟩ := ih hpre (tp.set i (.hart w i st' ws' (τ ++ [(l, ots)]))) σ' (by
      refine ⟨himg, hlog, hle, by rw [List.length_set]; exact hlen, by rw [List.length_set]; exact htp, ?_, fun h hN => ?_, fun h hN => ?_, hdone⟩
      · rw [List.getElem?_set_ne hiN']; exact hagN
      · have e : h ≠ i := by omega
        simp only [σ', upd_ne _ _ e]; exact hprN h hN
      · by_cases e : h = i
        · subst e
          refine ⟨_, τ ++ [(l, ots)], getElem?_set_eq_of hag, getElem?_set_eq_of a2, ?_⟩
          simp only [σ', upd_eq]
        · obtain ⟨ag', τ', b1, b2, b3⟩ := hh h hN
          refine ⟨ag', τ', ?_, ?_, ?_⟩
          · simp only; rw [List.getElem?_set_ne (Ne.symm e)]; exact b1
          · rw [List.getElem?_set_ne (Ne.symm e)]; exact b2
          · simp only [σ', upd_ne _ _ e]; exact b3)
    exact ⟨1 + k, tp', σ'', nsteps_trans (nsteps_one hstep) h1, h2⟩
  | rel c c1 c2 i m ag l r es c3 hpst hag1 hrc hr hst hrest ih =>
    intro hpre tp σ hs
    obtain ⟨himg, hlog, hle, hlen, htp, hagN, hprN, hh, hdone⟩ := hs
    cases hpst with
    | promise _ ag0 _ hag0 hnt htid =>
    cases hst with
    | state _ ag1 _ _ st' d' ws' prom' hag1' hp hm =>
    rw [hag1] at hag1'; cases hag1'
    simp only at hag1
    rw [getElem?_set_eq_of hag0] at hag1; cases hag1
    have hpre1 : c.pcLog ++ [m] <+: w.M := List.IsPrefix.trans (List.prefix_refl _)
      (List.IsPrefix.trans (pmSteps_prefix (nfSteps_pm hrest)) hpre)
    have hiN : i < N := by rw [← hlen]; exact (List.getElem?_eq_some_iff.1 hag0).1
    have hclen : c.pcLog.length = σ.n := by rw [hlog]; exact take_length' hle
    have hMn : w.M[σ.n]? = some m := by
      obtain ⟨t, ht⟩ := hpre1
      rw [← ht, List.getElem?_append_left (by simp [hclen])]
      simp [hclen]
    have hnM : σ.n < w.M.length := (List.getElem?_eq_some_iff.1 hMn).1
    obtain ⟨ag', τ, a1, a2, a3⟩ := hh i hiN
    rw [hag0] at a1; cases a1
    have hr' : r = σ.n + 1 := by rw [hr]; simp [hclen]
    subst hr'
    let σ' : OSt V := { σ with n := σ.n + 1, pr := upd σ.pr i prom' }
    have hm' : memStep w.img (w.M.take (σ.n + 1)) i ({σ.n + 1} ∪ σ.pr i) ag0.paWs l (some (σ.n + 1)) ws' prom' := by
      have hm2 := hm
      simp only at hm2
      rw [hclen] at hm2
      rw [a3, take_succ_of hMn, ← hlog, ← himg]; exact hm2
    have hstep : Step (tp, σ) [] (tp.set i (.hart w i st' ws' (τ ++ [(l, some (σ.n + 1))])), σ') := by
      have := step_update_of_getElem? (Λ := (inferInstance : Language (OExpr P V) (OSt V) Unit V))
        (obs := []) (efs := []) σ σ' a2
        (ostep.hst w i ag0.paSt ag0.paWs τ σ l (some (σ.n + 1)) st' ws' σ'
          (.rel σ _ _ l st' ws' prom' hnM (by simp [authorAt, hMn, htid]) hrc hp hm'))
      rw [List.append_nil] at this
      exact this
    have hiN' : i ≠ N := by omega
    obtain ⟨k, tp', σ'', h1, h2⟩ := ih hpre (tp.set i (.hart w i st' ws' (τ ++ [(l, some (σ.n + 1))]))) σ' (by
      refine ⟨himg, ?_, hnM, by rw [List.length_set, List.length_set]; exact hlen,
        by rw [List.length_set]; exact htp, ?_, fun h hN => ?_, fun h hN => ?_, hdone⟩
      · show c.pcLog ++ [m] = w.M.take (σ.n + 1)
        rw [hlog, take_succ_of hMn]
      · rw [List.getElem?_set_ne hiN']; exact hagN
      · have e : h ≠ i := by omega
        simp only [σ', upd_ne _ _ e]; exact hprN h hN
      · by_cases e : h = i
        · subst e
          refine ⟨⟨st', ws', prom'⟩, τ ++ [(l, some (σ.n + 1))], ?_, getElem?_set_eq_of a2, ?_⟩
          · simp only; rw [List.set_set]; exact getElem?_set_eq_of hag0
          · simp only [σ', upd_eq]
        · obtain ⟨ag', τ', b1, b2, b3⟩ := hh h hN
          refine ⟨ag', τ', ?_, ?_, ?_⟩
          · simp only; rw [List.getElem?_set_ne (Ne.symm e), List.getElem?_set_ne (Ne.symm e)]; exact b1
          · rw [List.getElem?_set_ne (Ne.symm e)]; exact b2
          · simp only [σ', upd_ne _ _ e]; exact b3)
    exact ⟨1 + k, tp', σ'', nsteps_trans (nsteps_one hstep) h1, h2⟩

/-- The final value map of a configuration. -/
def doneOf (w : OW P V) (N : Nat) (c : PCfg P Unit) : Nat → Option V :=
  fun h => if h < N then (c.pcAgs[h]?).bind (fun ag => w.pdone ag.paSt) else none

/-- THE FIN STEPS: every hart whose final program state has a value stops (harts `0, …, k−1`). -/
theorem fin_steps {w : OW P V} {N : Nat} {c : PCfg P Unit} {tp : List (OExpr P V)} {σ : OSt V}
    (hs : Sim w N c tp σ) (hno : ∀ h, h < N → σ.pr h = ∅) :
    ∀ k, k ≤ N → ∃ j tp', NSteps j (tp, σ) [] (tp', { σ with done := fun h => if h < k then doneOf w N c h else none })
      ∧ tp'.length = tp.length ∧ ∀ h, k ≤ h → tp'[h]? = tp[h]? := by
  obtain ⟨_, _, _, _, htp, _, _, hh, hdone⟩ := hs
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨0, tp, ?_, rfl, fun _ _ => rfl⟩
    have e : (fun h => if h < 0 then doneOf w N c h else none) = σ.done := by rw [hdone]; funext h; simp
    rw [e]
    exact .refl _
  | succ k ih =>
    intro hk
    obtain ⟨j, tp1, h1, hl1, he1⟩ := ih (by omega)
    obtain ⟨ag, τ, a1, a2, _⟩ := hh k (by omega)
    have hk1 : tp1[k]? = some (.hart w k ag.paSt ag.paWs τ) := by rw [he1 k (Nat.le_refl _)]; exact a2
    cases hv : w.pdone ag.paSt with
    | none =>
      refine ⟨j, tp1, ?_, hl1, fun h hh' => he1 h (by omega)⟩
      have e : (fun h => if h < k + 1 then doneOf w N c h else none) =
          (fun h => if h < k then doneOf w N c h else none) := by
        funext h
        by_cases e1 : h < k
        · simp [e1, show h < k + 1 by omega]
        · by_cases e2 : h = k
          · subst e2; simp [doneOf, show h < N by omega, a1, hv]
          · simp [e1, show ¬ h < k + 1 by omega]
      rw [e]; exact h1
    | some v =>
      let σ1 : OSt V := { σ with done := fun h => if h < k then doneOf w N c h else none }
      have hstep := step_update_of_getElem? (Λ := (inferInstance : Language (OExpr P V) (OSt V) Unit V))
        (obs := []) (efs := []) σ1 { σ1 with done := upd σ1.done k (some v) } hk1
        (ostep.fin w k ag.paSt ag.paWs τ σ1 v hv (hno k (by omega)))
      rw [List.append_nil] at hstep
      refine ⟨j + 1, tp1.set k (.ret v), ?_, by simp [hl1], fun h hh' => ?_⟩
      · have e : ({ σ1 with done := upd σ1.done k (some v) } : OSt V) =
            { σ with done := fun h => if h < k + 1 then doneOf w N c h else none } := by
          simp only [σ1]
          congr 1
          funext h
          by_cases e2 : h = k
          · subst e2; simp [upd, doneOf, show h < N by omega, a1, hv]
          · by_cases e1 : h < k
            · simp [upd, e2, e1, show h < k + 1 by omega]
            · simp [upd, e2, e1, show ¬ h < k + 1 by omega]
        rw [← e]
        exact nsteps_trans h1 (nsteps_one hstep)
      · rw [List.getElem?_set_ne (by omega)]; exact he1 h (by omega)

end Weak.Prom.Own
