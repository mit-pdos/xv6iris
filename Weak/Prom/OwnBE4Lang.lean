/-
Weak/Prom: **E-b4, B-0 — track (b)'s concurrent language WITH PER-HART TRACES IN THE STATE** (stage E-b4; owner
ruling [OWN.P16], context.md item 24; G4-review3.md §5 B-0 "export per-hart traces for unfinished harts").

RE-TYPINGS ONLY (every lemma tagged `-- [retype <Old.name>]`).  OwnLang.lean's language (plan rev 7 §4 "Pull rule")
has no traces in its state `OSt` and its simulation `Sim` leaves each hart's trace `τ` existential, so its adequacy
can only export final values of FINISHED harts (`φ σ.done`).  Here:
* `TExpr` — OwnLang's `OExpr` without the trace argument;
* `TSt` — OwnLang's `OSt` (reused unchanged, so `hstepO` and `agentStep` are REUSED verbatim) PLUS the memory-event
  trace of every hart (`tr h`, CoreKit.lean `memEv`: entries with a timestamp or a non-quiet label);
* `tstep` — OwnLang's `ostep` minus `fin`: a hart step is ONE `hstepO` step and records its entry in `tr h`
  (`recE`); the agent step is OwnLang's `agentStep`;
* `SimT` / `nf_simT` — OwnLang's `Sim` / OwnWpF.lean's `nf_simF` with the extra clause
  `σ.tr h = memEv (traceOf h es)` for the events `es` replayed so far.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.OwnWpF
import Weak.Prom.CoreKit

namespace Weak.Prom.OB.E4

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.Nfr Weak.Prom.Nfr.F
open Weak.Prom.Own (OW OSt hstepO agentStep authorAt upd upd_eq upd_ne take_length')
open Weak.Prom.PF (memEv keepE Trace PEv)
open PLabel
open Iris.ProgramLogic Iris.ProgramLogic.Language

/-- A thread: a hart (index, program state, exact machine state), the promise agent, or a value. -/
inductive TExpr (P V : Type) where   -- [retype Own.OExpr]
  | hart (w : OW P V) (h : Nat) (s : P) (ws : PState)
  | agent (w : OW P V)
  | ret (v : V)

/-- The shared state: OwnLang's state and every hart's memory-event trace. -/
structure TSt (V : Type) where   -- [retype Own.OSt]
  o : OSt V
  tr : Nat → Trace

/-- Record a trace entry if `memEv` keeps it. -/
def recE (τ : Trace) (e : PEv) : Trace := if keepE e then τ ++ [e] else τ

variable {P V : Type}

inductive tstep : TExpr P V × TSt V → List Unit → TExpr P V × TSt V × List (TExpr P V) → Prop   -- [retype Own.ostep]
  | hst (w : OW P V) (h : Nat) (s : P) (ws : PState) (σ : TSt V) (l : PLabel) (ots : Option Nat) (s' : P)
      (ws' : PState) (o' : OSt V) :
      hstepO w h σ.o s ws l ots s' ws' o' →
      tstep (.hart w h s ws, σ) [] (.hart w h s' ws', ⟨o', upd σ.tr h (recE (σ.tr h) (l, ots))⟩, [])
  | ag (w : OW P V) (σ : TSt V) (o' : OSt V) : agentStep w σ.o o' → tstep (.agent w, σ) [] (.agent w, ⟨o', σ.tr⟩, [])

instance : PrimStep (TExpr P V) (TSt V) (List Unit) := ⟨tstep⟩

def TExpr.toV : TExpr P V → Option V   -- [retype Own.OExpr.toV]
  | .ret v => some v
  | _ => none

instance : ToVal (TExpr P V) V where
  toVal := TExpr.toV
  ofVal v := .ret v
  coe_of_toVal_eq_some {e v} h := by
    cases e with
    | ret v' => cases h; rfl
    | _ => cases h
  toVal_coe _ := rfl

instance : Language (TExpr P V) (TSt V) Unit V where
  val_stuck h := by cases h <;> rfl

/-! ## The simulation of NF runs, traces included -/

/-- The initial pool. -/
def hartsFromT (w : OW P V) : Nat → List P → List (TExpr P V)   -- [retype Own.hartsFrom]
  | _, [] => []
  | k, p :: ps => .hart w k p psInit :: hartsFromT w (k + 1) ps

theorem hartsFromT_length (w : OW P V) : ∀ (k : Nat) (ps : List P), (hartsFromT w k ps).length = ps.length   -- [retype Own.hartsFrom_length]
  | _, [] => rfl
  | k, _ :: ps => by simp [hartsFromT, hartsFromT_length w (k + 1) ps]

theorem hartsFromT_get (w : OW P V) : ∀ (k : Nat) (ps : List P) (j : Nat) (p : P), ps[j]? = some p →   -- [retype Own.hartsFrom_get]
    (hartsFromT w k ps)[j]? = some (.hart w (k + j) p psInit)
  | _, [], _, _, h => by cases h
  | k, q :: ps, 0, p, h => by simp at h; subst h; rfl
  | k, q :: ps, j + 1, p, h => by
    simp only [hartsFromT, List.getElem?_cons_succ]
    rw [hartsFromT_get w (k + 1) ps j p (by simpa using h)]
    congr 2; omega

/-- The initial state. -/
def σT0 : TSt V := ⟨⟨0, fun _ => ∅, fun _ => none⟩, fun _ => []⟩   -- [retype Own.σ0]

/-- THE SIMULATION RELATION, with the traces of the events `es` replayed so far. -/
def SimT (w : OW P V) (N : Nat) (c : PCfg P Unit) (tp : List (TExpr P V)) (σ : TSt V) (es : List PEvt) : Prop :=   -- [retype Own.Sim]
  c.pcImg = w.img ∧ c.pcLog = w.M.take σ.o.n ∧ σ.o.n ≤ w.M.length ∧ c.pcAgs.length = N ∧ tp.length = N + 1 ∧
    tp[N]? = some (.agent w) ∧ (∀ h, N ≤ h → σ.o.pr h = ∅) ∧
    (∀ h, h < N → ∃ ag, c.pcAgs[h]? = some ag ∧ tp[h]? = some (.hart w h ag.paSt ag.paWs) ∧
      σ.o.pr h = ag.paProm) ∧ ∀ h, σ.tr h = memEv (traceOf h es)

theorem nsteps_oneT {tp tp' : List (TExpr P V)} {σ σ' : TSt V} (h : Step (tp, σ) [] (tp', σ')) :   -- [retype Own.nsteps_one]
    NSteps 1 (tp, σ) [] (tp', σ') := by
  have := NSteps.cons h (NSteps.refl (tp', σ'))
  simpa using this

theorem nsteps_transT' {k1 k2 : Nat} {ρ1 ρ2 ρ3 : List (TExpr P V) × TSt V} {o1 o2 : List Unit}   -- [retype Own.nsteps_trans']
    (h1 : NSteps k1 ρ1 o1 ρ2) (h2 : NSteps k2 ρ2 o2 ρ3) : NSteps (k1 + k2) ρ1 (o1 ++ o2) ρ3 := by
  induction h1 with
  | refl => simpa using h2
  | cons hs _ ih =>
    have := NSteps.cons hs (ih h2)
    simpa [Nat.add_right_comm, List.append_assoc] using this

theorem nsteps_transT {k1 k2 : Nat} {ρ1 ρ2 ρ3 : List (TExpr P V) × TSt V}   -- [retype Own.nsteps_trans]
    (h1 : NSteps k1 ρ1 [] ρ2) (h2 : NSteps k2 ρ2 [] ρ3) : NSteps (k1 + k2) ρ1 [] ρ3 := by
  simpa using nsteps_transT' h1 h2

/-- A promise event adds nothing to any trace. -/
theorem tr_prom (es0 : List PEvt) (i : Nat) (m : PMsg) (h : Nat) :
    memEv (traceOf h (es0 ++ [.prom i m])) = memEv (traceOf h es0) := by
  rw [traceOf_append]; simp [traceOf]

/-- A state event of hart `i` records its entry in `i`'s trace only. -/
theorem tr_st (es0 : List PEvt) (i : Nat) (l : PLabel) (ots : Option Nat) (tr : Nat → Trace)
    (htr : ∀ h, tr h = memEv (traceOf h es0)) (h : Nat) :
    upd tr i (recE (tr i) (l, ots)) h = memEv (traceOf h (es0 ++ [.st i l ots])) := by
  rw [traceOf_append]
  by_cases e : h = i
  · subst e
    simp only [upd_eq, traceOf, if_true, recE, htr, memEv, List.filter_append]
    split <;> simp_all
  · rw [upd_ne _ _ e, htr]
    simp [traceOf, Ne.symm e]

/-- ONE NF EVENT GROUP IS ONE OR TWO LANGUAGE STEPS, the traces following the events. -/
theorem nf_simT {w : OW P V} {N : Nat} :   -- [retype Own.nf_simF]
    ∀ {c c' : PCfg P Unit} {es : List PEvt}, nfStepsF relClass w.pstep w.M c es c' → c'.pcLog <+: w.M →
      ∀ (tp : List (TExpr P V)) (σ : TSt V) (es0 : List PEvt), SimT w N c tp σ es0 →
      ∃ k tp' σ', NSteps k (tp, σ) [] (tp', σ') ∧ SimT w N c' tp' σ' (es0 ++ es) := by
  intro c c' es h
  induction h with
  | refl c => intro _ tp σ es0 hs; exact ⟨0, tp, σ, .refl _, by simpa using hs⟩
  | prom c c1 i m es c2 hst hrest ih =>
    intro hpre tp σ es0 hs
    obtain ⟨himg, hlog, hle, hlen, htp, hag, hprN, hh, htr⟩ := hs
    cases hst with
    | promise _ ag _ hagi hnt htid =>
    have hpre1 : c.pcLog ++ [m] <+: w.M := List.IsPrefix.trans (List.prefix_refl _)
      (List.IsPrefix.trans (nfStepsF_prefix hrest) hpre)
    have hiN : i < N := by rw [← hlen]; exact (List.getElem?_eq_some_iff.1 hagi).1
    have hclen : c.pcLog.length = σ.o.n := by rw [hlog]; exact take_length' hle
    have hMn : w.M[σ.o.n]? = some m := by
      obtain ⟨t, ht⟩ := hpre1
      rw [← ht, List.getElem?_append_left (by simp [hclen])]
      simp [hclen]
    have hnM : σ.o.n < w.M.length := (List.getElem?_eq_some_iff.1 hMn).1
    let o' : OSt V := { σ.o with n := σ.o.n + 1, pr := upd σ.o.pr i ({σ.o.n + 1} ∪ σ.o.pr i) }
    have hstep : Step (tp, σ) [] (tp, ⟨o', σ.tr⟩) := by
      have := step_update_of_getElem? (Λ := (inferInstance : Language (TExpr P V) (TSt V) Unit V))
        (e := TExpr.agent w) (e' := TExpr.agent w) (i := N) (obs := []) (efs := []) σ ⟨o', σ.tr⟩ hag
        (tstep.ag w σ o' ⟨i, hnM, by simp [authorAt, hMn, htid], rfl⟩)
      rw [set_of_get hag, List.append_nil] at this
      exact this
    obtain ⟨k, tp', σ'', h1, h2⟩ := ih hpre tp ⟨o', σ.tr⟩ (es0 ++ [.prom i m]) (by
      refine ⟨himg, ?_, hnM, by simp [hlen], htp, hag, fun h hN => ?_, fun h hN => ?_,
        fun h => by rw [tr_prom]; exact htr h⟩
      · show c.pcLog ++ [m] = w.M.take (σ.o.n + 1)
        rw [hlog, take_succ_of hMn]
      · have e : h ≠ i := by omega
        simp only [o', upd_ne _ _ e]; exact hprN h hN
      · obtain ⟨ag', a1, a2, a3⟩ := hh h hN
        by_cases e : h = i
        · subst e
          rw [hagi] at a1; cases a1
          refine ⟨_, getElem?_set_eq_of hagi, a2, ?_⟩
          simp only [o', upd_eq, a3, hclen]
        · refine ⟨ag', ?_, a2, ?_⟩
          · simp only; rw [List.getElem?_set_ne (Ne.symm e)]; exact a1
          · simp only [o', upd_ne _ _ e]; exact a3)
    exact ⟨1 + k, tp', σ'', nsteps_transT (nsteps_oneT hstep) h1, by simpa using h2⟩
  | st c c1 i ag l ots es c2 hag hnr hst hrest ih =>
    intro hpre tp σ es0 hs
    obtain ⟨himg, hlog, hle, hlen, htp, hagN, hprN, hh, htr⟩ := hs
    cases hst with
    | state _ ag0 _ _ st' d' ws' prom' hag0 hp hm =>
    rw [hag] at hag0; cases hag0
    have hiN : i < N := by rw [← hlen]; exact (List.getElem?_eq_some_iff.1 hag).1
    obtain ⟨ag', a1, a2, a3⟩ := hh i hiN
    rw [hag] at a1; cases a1
    let o' : OSt V := { σ.o with pr := upd σ.o.pr i prom' }
    let σ' : TSt V := ⟨o', upd σ.tr i (recE (σ.tr i) (l, ots))⟩
    have hm' : memStep w.img (w.M.take σ.o.n) i (σ.o.pr i) ag.paWs l ots ws' prom' := by
      rw [← hlog, a3, ← himg]; exact hm
    have hstep : Step (tp, σ) [] (tp.set i (.hart w i st' ws'), σ') := by
      have := step_update_of_getElem? (Λ := (inferInstance : Language (TExpr P V) (TSt V) Unit V))
        (obs := []) (efs := []) σ σ' a2
        (tstep.hst w i ag.paSt ag.paWs σ l ots st' ws' o' (.plain σ.o _ _ l ots st' ws' prom' hp hm' hnr))
      rw [List.append_nil] at this
      exact this
    have hiN' : i ≠ N := by omega
    obtain ⟨k, tp', σ'', h1, h2⟩ := ih hpre (tp.set i (.hart w i st' ws')) σ' (es0 ++ [.st i l ots]) (by
      refine ⟨himg, hlog, hle, by rw [List.length_set]; exact hlen, by rw [List.length_set]; exact htp, ?_,
        fun h hN => ?_, fun h hN => ?_, fun h => tr_st es0 i l ots σ.tr htr h⟩
      · rw [List.getElem?_set_ne hiN']; exact hagN
      · have e : h ≠ i := by omega
        simp only [σ', o', upd_ne _ _ e]; exact hprN h hN
      · by_cases e : h = i
        · subst e
          refine ⟨_, getElem?_set_eq_of hag, getElem?_set_eq_of a2, ?_⟩
          simp only [σ', o', upd_eq]
        · obtain ⟨ag', b1, b2, b3⟩ := hh h hN
          refine ⟨ag', ?_, ?_, ?_⟩
          · simp only; rw [List.getElem?_set_ne (Ne.symm e)]; exact b1
          · rw [List.getElem?_set_ne (Ne.symm e)]; exact b2
          · simp only [σ', o', upd_ne _ _ e]; exact b3)
    exact ⟨1 + k, tp', σ'', nsteps_transT (nsteps_oneT hstep) h1, by simpa using h2⟩
  | rel c c1 c2 i m ag l r es c3 hpst hag1 hrc hr hst hrest ih =>
    intro hpre tp σ es0 hs
    obtain ⟨himg, hlog, hle, hlen, htp, hagN, hprN, hh, htr⟩ := hs
    cases hpst with
    | promise _ ag0 _ hag0 hnt htid =>
    cases hst with
    | state _ ag1 _ _ st' d' ws' prom' hag1' hp hm =>
    rw [hag1] at hag1'; cases hag1'
    simp only at hag1
    rw [getElem?_set_eq_of hag0] at hag1; cases hag1
    have hpre1 : c.pcLog ++ [m] <+: w.M := List.IsPrefix.trans (List.prefix_refl _)
      (List.IsPrefix.trans (nfStepsF_prefix hrest) hpre)
    have hiN : i < N := by rw [← hlen]; exact (List.getElem?_eq_some_iff.1 hag0).1
    have hclen : c.pcLog.length = σ.o.n := by rw [hlog]; exact take_length' hle
    have hMn : w.M[σ.o.n]? = some m := by
      obtain ⟨t, ht⟩ := hpre1
      rw [← ht, List.getElem?_append_left (by simp [hclen])]
      simp [hclen]
    have hnM : σ.o.n < w.M.length := (List.getElem?_eq_some_iff.1 hMn).1
    obtain ⟨ag', a1, a2, a3⟩ := hh i hiN
    rw [hag0] at a1; cases a1
    have hr' : r = σ.o.n + 1 := by rw [hr]; simp [hclen]
    subst hr'
    let o' : OSt V := { σ.o with n := σ.o.n + 1, pr := upd σ.o.pr i prom' }
    let σ' : TSt V := ⟨o', upd σ.tr i (recE (σ.tr i) (l, some (σ.o.n + 1)))⟩
    have hm' : memStep w.img (w.M.take (σ.o.n + 1)) i ({σ.o.n + 1} ∪ σ.o.pr i) ag0.paWs l (some (σ.o.n + 1)) ws'
        prom' := by
      have hm2 := hm
      simp only at hm2
      rw [hclen] at hm2
      rw [a3, take_succ_of hMn, ← hlog, ← himg]; exact hm2
    have hstep : Step (tp, σ) [] (tp.set i (.hart w i st' ws'), σ') := by
      have := step_update_of_getElem? (Λ := (inferInstance : Language (TExpr P V) (TSt V) Unit V))
        (obs := []) (efs := []) σ σ' a2
        (tstep.hst w i ag0.paSt ag0.paWs σ l (some (σ.o.n + 1)) st' ws' o'
          (.rel σ.o _ _ l st' ws' prom' hnM (by simp [authorAt, hMn, htid]) hrc hp hm'))
      rw [List.append_nil] at this
      exact this
    have hiN' : i ≠ N := by omega
    obtain ⟨k, tp', σ'', h1, h2⟩ := ih hpre (tp.set i (.hart w i st' ws')) σ'
        (es0 ++ [.prom i m, .st i l (some (σ.o.n + 1))]) (by
      refine ⟨himg, ?_, hnM, by rw [List.length_set, List.length_set]; exact hlen,
        by rw [List.length_set]; exact htp, ?_, fun h hN => ?_, fun h hN => ?_, fun h => ?_⟩
      · show c.pcLog ++ [m] = w.M.take (σ.o.n + 1)
        rw [hlog, take_succ_of hMn]
      · rw [List.getElem?_set_ne hiN']; exact hagN
      · have e : h ≠ i := by omega
        simp only [σ', o', upd_ne _ _ e]; exact hprN h hN
      · by_cases e : h = i
        · subst e
          refine ⟨⟨st', ws', prom'⟩, ?_, getElem?_set_eq_of a2, ?_⟩
          · simp only; rw [List.set_set]; exact getElem?_set_eq_of hag0
          · simp only [σ', o', upd_eq]
        · obtain ⟨ag', b1, b2, b3⟩ := hh h hN
          refine ⟨ag', ?_, ?_, ?_⟩
          · simp only; rw [List.getElem?_set_ne (Ne.symm e), List.getElem?_set_ne (Ne.symm e)]; exact b1
          · rw [List.getElem?_set_ne (Ne.symm e)]; exact b2
          · simp only [σ', o', upd_ne _ _ e]; exact b3
      · have e2 : es0 ++ [PEvt.prom i m, .st i l (some (σ.o.n + 1))] = (es0 ++ [.prom i m]) ++ [.st i l (some (σ.o.n + 1))] := by
          simp
        rw [e2]
        exact tr_st _ i l _ σ.tr (fun h => by rw [tr_prom]; exact htr h) h)
    exact ⟨1 + k, tp', σ'', nsteps_transT (nsteps_oneT hstep) h1, by simpa using h2⟩
  | fet c i ag b tvs st' d' es c2 hag hp hok hrest ih =>
    intro hpre tp σ es0 hs
    obtain ⟨himg, hlog, hle, hlen, htp, hagN, hprN, hh, htr⟩ := hs
    have hiN : i < N := by rw [← hlen]; exact (List.getElem?_eq_some_iff.1 hag).1
    obtain ⟨ag', a1, a2, a3⟩ := hh i hiN
    rw [hag] at a1; cases a1
    have hws : fetchPost c.pcLog i ag.paProm ag.paWs b tvs =
        { ag.paWs with
          wIfr := max ag.paWs.wIfr (bytesMax (fun _ t => t) b tvs)
          wIfv := max ag.paWs.wIfv (fetchView (w.M.take σ.o.n) i (σ.o.pr i) b tvs) } := by
      unfold fetchPost; rw [hlog, a3]
    have hf : hstepO w i σ.o ag.paSt ag.paWs (LIFetch b tvs) none st'
        (fetchPost c.pcLog i ag.paProm ag.paWs b tvs) σ.o := by
      rw [hws]; exact .fetch σ.o _ _ b tvs st' hp (himg ▸ hok)
    let σ' : TSt V := ⟨σ.o, upd σ.tr i (recE (σ.tr i) (LIFetch b tvs, none))⟩
    have hstep : Step (tp, σ) [] (tp.set i (.hart w i st' (fetchPost c.pcLog i ag.paProm ag.paWs b tvs)), σ') := by
      have := step_update_of_getElem? (Λ := (inferInstance : Language (TExpr P V) (TSt V) Unit V))
        (obs := []) (efs := []) σ σ' a2
        (tstep.hst w i ag.paSt ag.paWs σ (LIFetch b tvs) none st' _ σ.o hf)
      rw [List.append_nil] at this
      exact this
    have hiN' : i ≠ N := by omega
    obtain ⟨k, tp', σ'', h1, h2⟩ := ih hpre
      (tp.set i (.hart w i st' (fetchPost c.pcLog i ag.paProm ag.paWs b tvs))) σ'
        (es0 ++ [.st i (LIFetch b tvs) none]) (by
      refine ⟨himg, hlog, hle, by rw [List.length_set]; exact hlen, by rw [List.length_set]; exact htp, ?_,
        hprN, fun h hN => ?_, fun h => tr_st es0 i _ _ σ.tr htr h⟩
      · rw [List.getElem?_set_ne hiN']; exact hagN
      · by_cases e : h = i
        · subst e
          exact ⟨_, getElem?_set_eq_of hag, getElem?_set_eq_of a2, a3⟩
        · obtain ⟨ag', b1, b2, b3⟩ := hh h hN
          refine ⟨ag', ?_, ?_, b3⟩
          · simp only; rw [List.getElem?_set_ne (Ne.symm e)]; exact b1
          · rw [List.getElem?_set_ne (Ne.symm e)]; exact b2)
    exact ⟨1 + k, tp', σ'', nsteps_transT (nsteps_oneT hstep) h1, by simpa using h2⟩

end Weak.Prom.OB.E4
