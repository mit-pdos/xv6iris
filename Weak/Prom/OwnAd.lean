/-
Weak/Prom: **E-c — track (b)'s language and adequacy for the A/D variant** (G4 deciding experiment E-c, owner
ruling [OWN.P13]; G4-review2.md §7).  The counterpart of OwnLang.lean + OwnWpF.lean (`ownAdequacyF`) for
AdMachine.lean's variant, through `Ad.nfRAd` (NfrAd.lean).

What changes against OwnLang.lean (state `OSt` REUSED unchanged — no new bookkeeping):
* `hstepA.plain` / `rel` / `fetch`: OwnLang's three hart arms over `VLabel` (the plain arm also covers an A/D update
  whose timestamp is in the prefix: an ordinary fulfil of the hart's own promise);
* `hstepA.adF` (NEW): an A/D update whose timestamp is ABOVE the prefix, admissible against the prophecy world's `M`,
  with NO change of the language state (the hart's state and promise set are unchanged; nothing is recorded);
* `agentStepA` (one NEW disjunct): the agent may append an A/D-class message `M[n]` with no promise owner.
The client obligations of `ownAdequacyAd` have OwnWpF.lean's `ownAdequacyF` shape exactly (a state interpretation
`X`, the agent obligation for every `agentStepA`, the hart wps, the final extraction); no premise on the run.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.NfrAd
import Weak.Prom.OwnWp

namespace Weak.Prom.Ad

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.Nfr Weak.Prom.Nfr.F
open Weak.Prom.Own (OSt upd upd_eq upd_ne authorAt σ0 take_length')
open PLabel
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode
open Iris.ProgramLogic.Language Iris.ProgramLogic.Language.Notation

/-- The prophecy world (OwnLang.lean `OW` over `VLabel`). -/
structure OWA (P V : Type) where
  pstep : P → Unit → VLabel → P → Unit → Prop
  pdone : P → Option V
  img : Image
  M : List PMsg

/-- A thread: a hart, the promise agent, or a value. -/
inductive OExprA (P V : Type) where
  | hart (w : OWA P V) (h : Nat) (s : P) (ws : PState) (τ : List (VLabel × Option Nat))
  | agent (w : OWA P V)
  | ret (v : V)

variable {P V : Type}

/-- ONE HART STEP. -/
inductive hstepA (w : OWA P V) (h : Nat) : OSt V → P → PState → VLabel → Option Nat → P → PState → OSt V → Prop
  | plain (σ : OSt V) (s : P) (ws : PState) (l : VLabel) (ots : Option Nat) (s' : P) (ws' : PState)
      (pr' : GSet Nat) :
      w.pstep s () l s' () → memStepV w.img (w.M.take σ.n) h (σ.pr h) ws l ots ws' pr' → ¬ RCV relClass ws l →
      hstepA w h σ s ws l ots s' ws' { σ with pr := upd σ.pr h pr' }
  | rel (σ : OSt V) (s : P) (ws : PState) (l : PLabel) (s' : P) (ws' : PState) (pr' : GSet Nat) :
      σ.n < w.M.length → authorAt w.M σ.n = some h → relClass ws l → w.pstep s () (.v l) s' () →
      memStepV w.img (w.M.take (σ.n + 1)) h ({σ.n + 1} ∪ σ.pr h) ws (.v l) (some (σ.n + 1)) ws' pr' →
      hstepA w h σ s ws (.v l) (some (σ.n + 1)) s' ws' { σ with n := σ.n + 1, pr := upd σ.pr h pr' }
  | fetch (σ : OSt V) (s : P) (ws : PState) (base : Int) (tvs : List (Nat × BitVec 8)) (s' : P) :
      w.pstep s () (.v (LIFetch base tvs)) s' () → bytesAll (fetchByteOk w.img w.M ws) base tvs →
      hstepA w h σ s ws (.v (LIFetch base tvs)) none s' (fetchPostV (w.M.take σ.n) h (σ.pr h) ws base tvs) σ
  /-- [E-c] THE PROPHECY-FED A/D UPDATE: timestamp above the prefix, admissible against `M`, no state change. -/
  | adF (σ : OSt V) (s : P) (ws : PState) (b : Int) (tvs : List (Nat × BitVec 8)) (d : List (BitVec 8)) (ts : Nat)
      (s' : P) :
      w.pstep s () (.ad b tvs d) s' () → σ.n < ts → tvs.length = d.length →
      w.M[ts - 1]? = some ⟨b, d, some h, PClass.ad⟩ → bytesAll (adReadOk w.img w.M ts) b tvs →
      hstepA w h σ s ws (.ad b tvs d) (some ts) s' ws σ

/-- THE AGENT STEP: append `M[n]` as a promise of its author, or — [E-c] — an A/D message with no promise owner. -/
def agentStepA (w : OWA P V) (σ σ' : OSt V) : Prop :=
  ∃ i, σ.n < w.M.length ∧ authorAt w.M σ.n = some i ∧
    (σ' = { σ with n := σ.n + 1, pr := upd σ.pr i ({σ.n + 1} ∪ σ.pr i) } ∨
     ((∃ m, w.M[σ.n]? = some m ∧ m.cls = PClass.ad) ∧ σ' = { σ with n := σ.n + 1 }))

inductive ostepA : OExprA P V × OSt V → List Unit → OExprA P V × OSt V × List (OExprA P V) → Prop
  | hst (w : OWA P V) (h : Nat) (s : P) (ws : PState) (τ : List (VLabel × Option Nat)) (σ : OSt V) (l : VLabel)
      (ots : Option Nat) (s' : P) (ws' : PState) (σ' : OSt V) :
      hstepA w h σ s ws l ots s' ws' σ' →
      ostepA (.hart w h s ws τ, σ) [] (.hart w h s' ws' (τ ++ [(l, ots)]), σ', [])
  | fin (w : OWA P V) (h : Nat) (s : P) (ws : PState) (τ : List (VLabel × Option Nat)) (σ : OSt V) (v : V) :
      w.pdone s = some v → σ.pr h = ∅ →
      ostepA (.hart w h s ws τ, σ) [] (.ret v, { σ with done := upd σ.done h (some v) }, [])
  | ag (w : OWA P V) (σ σ' : OSt V) : agentStepA w σ σ' → ostepA (.agent w, σ) [] (.agent w, σ', [])

instance : PrimStep (OExprA P V) (OSt V) (List Unit) := ⟨ostepA⟩

def OExprA.toV : OExprA P V → Option V
  | .ret v => some v
  | _ => none

instance : ToVal (OExprA P V) V where
  toVal := OExprA.toV
  ofVal v := .ret v
  coe_of_toVal_eq_some {e v} h := by
    cases e with
    | ret v' => cases h; rfl
    | _ => cases h
  toVal_coe _ := rfl

instance : Language (OExprA P V) (OSt V) Unit V where
  val_stuck h := by cases h <;> rfl

/-! ## The simulation of NF runs -/

/-- The initial pool. -/
def hartsFromA (w : OWA P V) : Nat → List P → List (OExprA P V)
  | _, [] => []
  | k, p :: ps => .hart w k p psInit [] :: hartsFromA w (k + 1) ps

theorem hartsFromA_length (w : OWA P V) : ∀ (k : Nat) (ps : List P), (hartsFromA w k ps).length = ps.length
  | _, [] => rfl
  | k, _ :: ps => by simp [hartsFromA, hartsFromA_length w (k + 1) ps]

theorem hartsFromA_get (w : OWA P V) : ∀ (k : Nat) (ps : List P) (j : Nat) (p : P), ps[j]? = some p →
    (hartsFromA w k ps)[j]? = some (.hart w (k + j) p psInit [])
  | _, [], _, _, h => by cases h
  | k, q :: ps, 0, p, h => by simp at h; subst h; rfl
  | k, q :: ps, j + 1, p, h => by
    simp only [hartsFromA, List.getElem?_cons_succ]
    rw [hartsFromA_get w (k + 1) ps j p (by simpa using h)]
    congr 2; omega

/-- THE SIMULATION RELATION (OwnLang.lean `Sim`). -/
def SimA (w : OWA P V) (N : Nat) (c : PCfg P Unit) (tp : List (OExprA P V)) (σ : OSt V) : Prop :=
  c.pcImg = w.img ∧ c.pcLog = w.M.take σ.n ∧ σ.n ≤ w.M.length ∧ c.pcAgs.length = N ∧ tp.length = N + 1 ∧
    tp[N]? = some (.agent w) ∧ (∀ h, N ≤ h → σ.pr h = ∅) ∧
    (∀ h, h < N → ∃ ag τ, c.pcAgs[h]? = some ag ∧ tp[h]? = some (.hart w h ag.paSt ag.paWs τ) ∧
      σ.pr h = ag.paProm) ∧ σ.done = fun _ => none

theorem nstepsA_trans' {k1 k2 : Nat} {ρ1 ρ2 ρ3 : List (OExprA P V) × OSt V} {o1 o2 : List Unit}
    (h1 : NSteps k1 ρ1 o1 ρ2) (h2 : NSteps k2 ρ2 o2 ρ3) : NSteps (k1 + k2) ρ1 (o1 ++ o2) ρ3 := by
  induction h1 with
  | refl => simpa using h2
  | cons hs _ ih =>
    have := NSteps.cons hs (ih h2)
    simpa [Nat.add_right_comm, List.append_assoc] using this

theorem nstepsA_trans {k1 k2 : Nat} {ρ1 ρ2 ρ3 : List (OExprA P V) × OSt V}
    (h1 : NSteps k1 ρ1 [] ρ2) (h2 : NSteps k2 ρ2 [] ρ3) : NSteps (k1 + k2) ρ1 [] ρ3 := by
  simpa using nstepsA_trans' h1 h2

/-- One thread step of the pool, from a configuration where thread `j` is `e`. -/
theorem stepA_at {tp : List (OExprA P V)} {σ σ' : OSt V} {j : Nat} {e e' : OExprA P V} (hj : tp[j]? = some e)
    (h : ostepA (e, σ) [] (e', σ', [])) : NSteps 1 (tp, σ) [] (tp.set j e', σ') := by
  have := step_update_of_getElem? (Λ := (inferInstance : Language (OExprA P V) (OSt V) Unit V))
    (obs := []) (efs := []) σ σ' hj h
  rw [List.append_nil] at this
  have := NSteps.cons this (NSteps.refl (tp.set j e', σ'))
  simpa using this

/-- A HART STEP keeps the simulation (the common part of the `st`, `rel`, `fet`, `adF` cases). -/
theorem simA_hart {w : OWA P V} {N : Nat} {c : PCfg P Unit} {tp : List (OExprA P V)} {σ : OSt V}
    (hs : SimA w N c tp σ) {i : Nat} {ag : PAgent P} (hag : c.pcAgs[i]? = some ag) {l : VLabel}
    {ots : Option Nat} {st' : P} {ws' : PState} {prom' : GSet Nat} {log' : List PMsg} {σ' : OSt V}
    (hlog : log' = w.M.take σ'.n) (hle : σ'.n ≤ w.M.length) (hpr : σ'.pr = upd σ.pr i prom')
    (hdone : σ'.done = σ.done) (hst : hstepA w i σ ag.paSt ag.paWs l ots st' ws' σ') :
    ∃ tp', NSteps 1 (tp, σ) [] (tp', σ') ∧
      SimA w N ⟨c.pcImg, log', (), c.pcAgs.set i ⟨st', ws', prom'⟩⟩ tp' σ' := by
  obtain ⟨himg, _, _, hlen, htp, hagN, hprN, hh, hd⟩ := hs
  have hiN : i < N := by rw [← hlen]; exact (List.getElem?_eq_some_iff.1 hag).1
  obtain ⟨ag', τ, a1, a2, a3⟩ := hh i hiN
  rw [hag] at a1; cases a1
  refine ⟨_, stepA_at a2 (.hst w i _ _ τ σ l ots st' ws' σ' hst), himg, hlog, hle, by simp [hlen],
    by simp [htp], by rw [List.getElem?_set_ne (by omega)]; exact hagN, fun h hN => ?_, fun h hN => ?_,
    by rw [hdone]; exact hd⟩
  · rw [hpr, upd_ne _ _ (by omega)]; exact hprN h hN
  · by_cases e : h = i
    · subst e
      exact ⟨_, τ ++ [(l, ots)], getElem?_set_eq_of hag, getElem?_set_eq_of a2, by rw [hpr, upd_eq]⟩
    · obtain ⟨ag', τ', b1, b2, b3⟩ := hh h hN
      refine ⟨ag', τ', ?_, ?_, by rw [hpr, upd_ne _ _ e]; exact b3⟩
      · simp only; rw [List.getElem?_set_ne (Ne.symm e)]; exact b1
      · rw [List.getElem?_set_ne (Ne.symm e)]; exact b2

theorem msg_at {w : OWA P V} {c : PCfg P Unit} {σ : OSt V} {m : PMsg} (hlog : c.pcLog = w.M.take σ.n)
    (hle : σ.n ≤ w.M.length) (hpre : c.pcLog ++ [m] <+: w.M) :
    c.pcLog.length = σ.n ∧ w.M[σ.n]? = some m ∧ c.pcLog ++ [m] = w.M.take (σ.n + 1) := by
  have hclen : c.pcLog.length = σ.n := by rw [hlog]; exact take_length' hle
  have hMn : w.M[σ.n]? = some m := by
    obtain ⟨t, ht⟩ := hpre
    rw [← ht, List.getElem?_append_left (by simp [hclen])]
    simp [hclen]
  exact ⟨hclen, hMn, by rw [hlog, take_succ_of hMn]⟩

/-- ONE NF EVENT GROUP (`Ad.nfStepsV`, plan §3's class) IS ONE OR TWO LANGUAGE STEPS. -/
theorem nf_simA {w : OWA P V} {N : Nat} :
    ∀ {c c' : PCfg P Unit} {es : List VEvt}, nfStepsV relClass w.pstep w.M c es c' → c'.pcLog <+: w.M →
      ∀ (tp : List (OExprA P V)) (σ : OSt V), SimA w N c tp σ →
      ∃ k tp' σ', NSteps k (tp, σ) [] (tp', σ') ∧ SimA w N c' tp' σ' := by
  intro c c' es h
  induction h with
  | refl c => intro _ tp σ hs; exact ⟨0, tp, σ, .refl _, hs⟩
  | prom c c1 i m es c2 hst hrest ih =>
    intro hpre tp σ hs
    obtain ⟨himg, hlog, hle, hlen, htp, hag, hprN, hh, hdone⟩ := hs
    cases hst with
    | promise _ ag _ hagi hnt htid =>
    have hiN : i < N := by rw [← hlen]; exact (List.getElem?_eq_some_iff.1 hagi).1
    obtain ⟨hclen, hMn, hlog1⟩ := msg_at hlog hle
      (List.IsPrefix.trans (List.prefix_refl _) (List.IsPrefix.trans (nfStepsV_prefix hrest) hpre))
    have hnM : σ.n < w.M.length := (List.getElem?_eq_some_iff.1 hMn).1
    let σ' : OSt V := { σ with n := σ.n + 1, pr := upd σ.pr i ({σ.n + 1} ∪ σ.pr i) }
    have hstep := stepA_at hag (ostepA.ag w σ σ' ⟨i, hnM, by simp [authorAt, hMn, htid], .inl rfl⟩)
    rw [set_of_get hag] at hstep
    obtain ⟨k, tp', σ'', h1, h2⟩ := ih hpre tp σ' (by
      refine ⟨himg, hlog1, hnM, by simp [hlen], htp, hag, fun h hN => ?_, fun h hN => ?_, hdone⟩
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
    exact ⟨1 + k, tp', σ'', nstepsA_trans hstep h1, h2⟩
  | promF c i ag m es c2 hagi _ htid hcls hrest ih =>
    -- [E-c] an A/D message appended with no promise owner
    intro hpre tp σ hs
    obtain ⟨himg, hlog, hle, hlen, htp, hag, hprN, hh, hdone⟩ := hs
    obtain ⟨_, hMn, hlog1⟩ := msg_at hlog hle
      (List.IsPrefix.trans (List.prefix_refl _) (List.IsPrefix.trans (nfStepsV_prefix hrest) hpre))
    have hnM : σ.n < w.M.length := (List.getElem?_eq_some_iff.1 hMn).1
    let σ' : OSt V := { σ with n := σ.n + 1 }
    have hstep := stepA_at hag (ostepA.ag w σ σ' ⟨i, hnM, by simp [authorAt, hMn, htid], .inr ⟨⟨m, hMn, hcls⟩, rfl⟩⟩)
    rw [set_of_get hag] at hstep
    obtain ⟨k, tp', σ'', h1, h2⟩ := ih hpre tp σ' ⟨himg, hlog1, hnM, hlen, htp, hag, hprN, hh, hdone⟩
    exact ⟨1 + k, tp', σ'', nstepsA_trans hstep h1, h2⟩
  | st c c1 i ag l ots es c2 hag hnr hst hrest ih =>
    intro hpre tp σ hs
    cases hst with
    | state _ ag0 _ _ st' d' ws' prom' hag0 hp hm =>
    rw [hag] at hag0; cases hag0
    obtain ⟨himg, hlog, hle, hlen, _, _, _, hh, _⟩ := id hs
    have hiN : i < N := by rw [← hlen]; exact (List.getElem?_eq_some_iff.1 hag).1
    obtain ⟨ag', τ, a1, _, a3⟩ := hh i hiN
    rw [hag] at a1; cases a1
    have hm' : memStepV w.img (w.M.take σ.n) i (σ.pr i) ag.paWs l ots ws' prom' := by
      rw [← hlog, a3, ← himg]; exact hm
    obtain ⟨tp1, hstep, hs1⟩ := simA_hart hs hag (σ' := { σ with pr := upd σ.pr i prom' }) hlog hle rfl rfl
      (.plain σ _ _ l ots st' ws' prom' hp hm' hnr)
    obtain ⟨k, tp', σ'', h1, h2⟩ := ih hpre tp1 _ hs1
    exact ⟨1 + k, tp', σ'', nstepsA_trans hstep h1, h2⟩
  | rel c c1 c2 i m ag l r es c3 hpst hag1 hrc hr hst hrest ih =>
    intro hpre tp σ hs
    cases hpst with
    | promise _ ag0 _ hag0 hnt htid =>
    cases hst with
    | state _ ag1 _ _ st' d' ws' prom' hag1' hp hm =>
    rw [hag1] at hag1'; cases hag1'
    simp only at hag1
    rw [getElem?_set_eq_of hag0] at hag1; cases hag1
    obtain ⟨himg, hlog, hle, hlen, _, _, _, hh, _⟩ := id hs
    obtain ⟨hclen, hMn, hlog1⟩ := msg_at hlog hle
      (List.IsPrefix.trans (List.prefix_refl _) (List.IsPrefix.trans (nfStepsV_prefix hrest) hpre))
    have hnM : σ.n < w.M.length := (List.getElem?_eq_some_iff.1 hMn).1
    have hiN : i < N := by rw [← hlen]; exact (List.getElem?_eq_some_iff.1 hag0).1
    obtain ⟨ag', τ, a1, _, a3⟩ := hh i hiN
    rw [hag0] at a1; cases a1
    have hr' : r = σ.n + 1 := by rw [hr]; simp [hclen]
    subst hr'
    have hm' : memStepV w.img (w.M.take (σ.n + 1)) i ({σ.n + 1} ∪ σ.pr i) ag0.paWs (.v l) (some (σ.n + 1)) ws'
        prom' := by
      have hm2 := hm
      simp only at hm2
      rw [hclen] at hm2
      rw [a3, ← hlog1, ← himg]; exact hm2
    obtain ⟨tp1, hstep, hs1⟩ := simA_hart hs hag0 (σ' := { σ with n := σ.n + 1, pr := upd σ.pr i prom' })
      hlog1 hnM rfl rfl (.rel σ _ _ l st' ws' prom' hnM (by simp [authorAt, hMn, htid]) hrc hp hm')
    obtain ⟨k, tp', σ'', h1, h2⟩ := ih hpre tp1 _ (by simpa [List.set_set] using hs1)
    exact ⟨1 + k, tp', σ'', nstepsA_trans hstep h1, h2⟩
  | fet c i ag b tvs st' d' es c2 hag hp hok hrest ih =>
    intro hpre tp σ hs
    obtain ⟨himg, hlog, hle, hlen, _, _, _, hh, hdone⟩ := id hs
    have hiN : i < N := by rw [← hlen]; exact (List.getElem?_eq_some_iff.1 hag).1
    obtain ⟨ag', τ, a1, _, a3⟩ := hh i hiN
    rw [hag] at a1; cases a1
    have hws : fetchPostV c.pcLog i ag.paProm ag.paWs b tvs = fetchPostV (w.M.take σ.n) i (σ.pr i) ag.paWs b tvs := by
      rw [hlog, a3]
    obtain ⟨tp1, hstep, hs1⟩ := simA_hart hs hag (σ' := σ) (prom' := ag.paProm)
      (ws' := fetchPostV c.pcLog i ag.paProm ag.paWs b tvs) hlog hle
      (by funext j; by_cases e : j = i <;> simp [upd, e, a3]) rfl
      (by rw [hws]; exact .fetch σ _ _ b tvs st' hp (himg ▸ hok))
    obtain ⟨k, tp', σ'', h1, h2⟩ := ih hpre tp1 _ hs1
    exact ⟨1 + k, tp', σ'', nstepsA_trans hstep h1, h2⟩
  | adF c i ag b tvs d ts st' d' es c2 hag hp hlt hlen' hm hrd hrest ih =>
    -- [E-c] the prophecy-fed A/D update: no language-state change
    intro hpre tp σ hs
    obtain ⟨himg, hlog, hle, hlen, _, _, _, hh, hdone⟩ := id hs
    have hiN : i < N := by rw [← hlen]; exact (List.getElem?_eq_some_iff.1 hag).1
    obtain ⟨ag', τ, a1, _, a3⟩ := hh i hiN
    rw [hag] at a1; cases a1
    have hclen : c.pcLog.length = σ.n := by rw [hlog]; exact take_length' hle
    obtain ⟨tp1, hstep, hs1⟩ := simA_hart hs hag (σ' := σ) (prom' := ag.paProm) hlog hle
      (by funext j; by_cases e : j = i <;> simp [upd, e, a3]) rfl
      (.adF σ _ _ b tvs d ts st' hp (by omega) hlen' hm (himg ▸ hrd))
    obtain ⟨k, tp', σ'', h1, h2⟩ := ih hpre tp1 _ hs1
    exact ⟨1 + k, tp', σ'', nstepsA_trans hstep h1, h2⟩

/-- The final value map of a configuration. -/
def doneOfA (w : OWA P V) (N : Nat) (c : PCfg P Unit) : Nat → Option V :=
  fun h => if h < N then (c.pcAgs[h]?).bind (fun ag => w.pdone ag.paSt) else none

/-- THE FIN STEPS (OwnLang.lean `fin_steps`). -/
theorem fin_stepsA {w : OWA P V} {N : Nat} {c : PCfg P Unit} {tp : List (OExprA P V)} {σ : OSt V}
    (hs : SimA w N c tp σ) (hno : ∀ h, h < N → σ.pr h = ∅) :
    ∀ k, k ≤ N → ∃ j tp', NSteps j (tp, σ) [] (tp', { σ with done := fun h => if h < k then doneOfA w N c h else none })
      ∧ tp'.length = tp.length ∧ ∀ h, k ≤ h → tp'[h]? = tp[h]? := by
  obtain ⟨_, _, _, _, htp, _, _, hh, hdone⟩ := hs
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨0, tp, ?_, rfl, fun _ _ => rfl⟩
    have e : (fun h => if h < 0 then doneOfA w N c h else none) = σ.done := by rw [hdone]; funext h; simp
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
      have e : (fun h => if h < k + 1 then doneOfA w N c h else none) =
          (fun h => if h < k then doneOfA w N c h else none) := by
        funext h
        by_cases e1 : h < k
        · simp [e1, show h < k + 1 by omega]
        · by_cases e2 : h = k
          · subst e2; simp [doneOfA, show h < N by omega, a1, hv]
          · simp [e1, show ¬ h < k + 1 by omega]
      rw [e]; exact h1
    | some v =>
      let σ1 : OSt V := { σ with done := fun h => if h < k then doneOfA w N c h else none }
      have hstep := stepA_at hk1 (ostepA.fin w k ag.paSt ag.paWs τ σ1 v hv (hno k (by omega)))
      refine ⟨j + 1, tp1.set k (.ret v), ?_, by simp [hl1], fun h hh' => ?_⟩
      · have e : ({ σ1 with done := upd σ1.done k (some v) } : OSt V) =
            { σ with done := fun h => if h < k + 1 then doneOfA w N c h else none } := by
          simp only [σ1]
          congr 1
          funext h
          by_cases e2 : h = k
          · subst e2; simp [upd, doneOfA, show h < N by omega, a1, hv]
          · by_cases e1 : h < k
            · simp [upd, e2, e1, show h < k + 1 by omega]
            · simp [upd, e2, e1, show ¬ h < k + 1 by omega]
        rw [← e]
        exact nstepsA_trans h1 hstep
      · rw [List.getElem?_set_ne (by omega)]; exact he1 h (by omega)

/-! ## The weakest precondition and adequacy -/

variable {hlc : HasLC} {GF : BundledGFunctors}

/-- The `IrisGS` of the pool under the client's state interpretation `X` (OwnWp.lean `oIrisGS`). -/
@[reducible] def aIrisGS [InvGS_gen hlc GF] (X : OSt V → IProp GF) : IrisGS_gen hlc (OExprA P V) GF where
  toStateInterp := ⟨fun σ _ _ _ => X σ⟩
  invGS := inferInstance
  numLatersPerStep _ := 0
  forkPost _ := iprop(True)
  stateInterp_mono _ _ _ _ := by iintro $

/-- **`wpA X e Φ`**: the WP of a thread (OwnWp.lean `wpO`). -/
def wpA [InvGS_gen hlc GF] (X : OSt V → IProp GF) (e : OExprA P V) (Φ : V → IProp GF) : IProp GF :=
  letI : IrisGS_gen hlc (OExprA P V) GF := aIrisGS X
  WP e @ Stuckness.MaybeStuck; ⊤ {{ Φ }}

theorem aStateI_eq [InvGS_gen hlc GF] (X : OSt V → IProp GF) (σ : OSt V) (ns : Nat) (obs : List Unit) (nt : Nat) :
    @stateInterp (OSt V) Unit GF ((aIrisGS (P := P) X).toStateInterp) σ ns obs nt = X σ := rfl

/-- **THE PROMISE AGENT'S WP IS THE INVARIANT** (OwnWp.lean `wpO_agent`), for `agentStepA`. -/
theorem wpA_agent [InvGS_gen hlc GF] {X : OSt V → IProp GF} {w : OWA P V} :
    □ (∀ σ σ', ⌜agentStepA w σ σ'⌝ -∗ X σ -∗ |={⊤}=> X σ') ⊢
      wpA X (.agent w : OExprA P V) (fun _ => iprop(True)) := by
  letI : IrisGS_gen hlc (OExprA P V) GF := aIrisGS X
  show _ ⊢ WP (OExprA.agent w : OExprA P V) @ Stuckness.MaybeStuck; ⊤ {{ fun _ => iprop(True) }}
  iintro #Hag
  iloeb as IH
  iapply wp_lift_step (rfl : toVal (OExprA.agent w : OExprA P V) = none)
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  rw [aStateI_eq]
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplit
  · ipureintro; trivial
  inext
  iintro %e₂ %σ₂ %eₜ %Hstep _
  change ostepA _ _ _ at Hstep
  cases Hstep with
  | ag _ _ σ' ha =>
    imod Hclose
    imod Hag $$ %σ₁ %_ %ha Hσ with Hσ
    imodintro
    rw [aStateI_eq]
    iframe Hσ
    isplitl
    · iexact IH
    · exact BigSepL.bigSepL_nil_intro

/-- **THE ADEQUACY OF TRACK (b)'s LOGIC FOR THE A/D VARIANT** (E-c): OwnWpF.lean's `ownAdequacyF` — same client
premise shape, the agent obligation now over `agentStepA` — and NO premise on the run: `φ` of the final value map of
EVERY valid run of the variant (`D = Unit`), through `nfRAd` and `nf_simA`. -/
theorem ownAdequacyAd [InvGpreS GF] {w : OWA P V} {ps : List P} (φ : (Nat → Option V) → Prop)
    (Hwp : ∀ [InvGS_gen hlc GF], ⊢@{IProp GF} |={⊤}=> ∃ X : OSt V → IProp GF,
      X σ0 ∗ □ (∀ σ σ', ⌜agentStepA w σ σ'⌝ -∗ X σ -∗ |={⊤}=> X σ') ∗
      ([∗list] e ∈ hartsFromA w 0 ps, wpA X e (fun _ => iprop(True))) ∗
      (∀ σ, ⌜σ.n = w.M.length ∧ ∀ h, σ.pr h = ∅⌝ -∗ X σ -∗ |={⊤,∅}=> ⌜φ σ.done⌝))
    {evs : List VEvt} {cfg : PCfg P Unit} (hv : validRunV w.pstep w.img () ps evs cfg) (hM : cfg.pcLog = w.M) :
    φ (doneOfA w ps.length cfg) := by
  obtain ⟨evs', ⟨hnf, hno⟩, _⟩ := nfRAd hv
  rw [hM] at hnf
  let N := ps.length
  have hs0 : SimA w N (pmInit w.img () ps) (hartsFromA w 0 ps ++ [OExprA.agent w]) σ0 := by
    refine ⟨rfl, by simp [pmInit, σ0], Nat.zero_le _, by simp [pmInit, N], by simp [hartsFromA_length, N], ?_,
      fun _ _ => rfl, fun h hN => ?_, rfl⟩
    · rw [List.getElem?_append_right (by simp [hartsFromA_length, N])]
      simp [hartsFromA_length, N]
    · have hp : ps[h]? = some ps[h] := List.getElem?_eq_getElem hN
      refine ⟨⟨ps[h], psInit, ∅⟩, [], by simp [pmInit, hp], ?_, rfl⟩
      rw [List.getElem?_append_left (by simp [hartsFromA_length]; exact hN), hartsFromA_get w 0 ps h _ hp]
      simp
  obtain ⟨k, tp1, σ1, hk, hs1⟩ := nf_simA hnf (by rw [hM]; exact List.prefix_refl _) _ _ hs0
  have hno' : ∀ h, h < N → σ1.pr h = ∅ := by
    intro h hN
    obtain ⟨ag, _, a1, _, a3⟩ := hs1.2.2.2.2.2.2.2.1 h hN
    rw [a3]; exact hno h ag a1
  obtain ⟨j, tp2, hj, _, _⟩ := fin_stepsA hs1 hno' N (Nat.le_refl _)
  have hn1 : σ1.n = w.M.length := by
    have e := hs1.2.1
    rw [hM] at e
    have := congrArg List.length e
    rw [take_length' hs1.2.2.1] at this
    omega
  have hdone : (fun h => if h < N then doneOfA w N cfg h else none) = doneOfA w N cfg := by
    funext h; by_cases e : h < N <;> simp [e, doneOfA]
  rw [hdone] at hj
  have hsteps := nstepsA_trans hk hj
  refine wp_strong_adequacy_gen (hlc := hlc) (GF := GF) Stuckness.MaybeStuck
    (hartsFromA w 0 ps ++ [OExprA.agent w]) σ0 (k + j) [] tp2 { σ1 with done := doneOfA w N cfg }
    (φ (doneOfA w N cfg)) (fun _ => 0) ?_ hsteps
  intro Hinv
  have hw := @Hwp Hinv
  dsimp only [wpA] at hw
  iintro
  imod hw with ⟨%X, HX, #Hag, Hharts, Hfin⟩
  imodintro
  iexists (fun σ _ _ _ => X σ), List.replicate (N + 1) (fun _ => iprop(True)),
    (fun _ => iprop(True)), (fun _ _ _ _ => fupd_intro)
  dsimp only
  iframe HX
  isplitl [Hharts]
  · have hl : (hartsFromA w 0 ps).length = N := hartsFromA_length w 0 ps
    rw [List.replicate_succ', ← hl]
    iapply (BigSepL2.bigSepL2_append (.inl (by simp))).2
    isplitl [Hharts]
    · iapply BigSepL2.bigSepL2_replicate_right.2
      iexact Hharts
    · iapply BigSepL2.bigSepL2_singleton.2
      ihave Ha := wpA_agent (hlc := hlc) (X := X) (w := w) $$ Hag
      dsimp only [wpA]
      iexact Ha
  iintro %es' %t2' %_ %_ %_ Hσ _ _
  iapply Hfin $$ %({ σ1 with done := doneOfA w N cfg } : OSt V) %⟨hn1, fun h => ?_⟩ Hσ
  by_cases hN : h < N
  · exact hno' h hN
  · exact hs1.2.2.2.2.2.2.1 h (by omega)

end Weak.Prom.Ad
