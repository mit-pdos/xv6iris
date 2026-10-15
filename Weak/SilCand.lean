/-
Weak: **(c) [OWN.100] — the SILENT EQUAL-VALUE AMO, increment 1: the candidate-level twin step**
(`PROGRESS-W10spike.md`, `PROGRESS-W10N2p.md`).  Lean-only, no Rocq twin.  A PRIMED TWIN: the registered
machine (`mstep`, `execWf`, `srvwmoConsistent`) is untouched.

`SilCand.stepS` is `mstep` plus ONE arm, the SILENT AMO: an AMO whose written bytes EQUAL its read bytes
(and that is not `rl`) may complete WITHOUT a message.  Per byte it reads the latest message as of an
earlier log position `q` — its write's virtual place, co-immediately after its source — subject to the
write's own ordering constraints:

  * `q` is at least the hart's coherence view of every byte (riscv.cat coherence), the fulfil pre-view
    `fulfilVpre` (fences with a write successor, control/address dependencies: ppo rules 4, 9–11), and the
    position of the hart's own earlier `aq` AMO writes (`SilCand.St.aqw`: ppo rule 5 — the registered
    machine needs no such view because its writes always append);
  * the read is an ordinary `rdOk` read (load readability: rules 1–3, 5) and no write of the byte lies in
    `(t, q]` (atomicity: rmw ∩ (fre;coe) = ∅ with the write placed right after `q`);
  * afterwards the hart's views are those of an RMW written at `q` (`storePostRun … q`), raised to `q` when
    `aq` (later events follow the AMO).

Faithful (riscv.cat): each silent AMO corresponds to an RVWMO AMO whose write sits in co immediately after
its source (equal value, so invisible to every read), placed in gmo at `q`.  xv6's failed
`amoswap.w.aq` (reads 1, writes 1) qualifies, which makes the cross-spin shape realizable
(`CertZ35.crossSpinNo` shows the registered target cannot).

  §1  the twin state `SilCand.St`, `silentOk`, `silentPost`, **`SilCand.stepS`**;
  §2  the twin run `SilCand.ExecS`/`execWfS` and the EMBEDDING **`SilCand.execWfOfOld`** (every registered
      run is a twin run); the log facts (`stepSLog`: a step keeps the log or appends one message).
-/
import Weak.CertZ35

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std

/-! # 1. The twin step -/

/-- The twin machine state: the registered state plus, per agent, the position of its latest own
`aq` AMO write. -/
structure SilCand.St where
  ms : Mstate
  aqw : Nat → Nat

/-- The side conditions of a SILENT AMO of agent `i` at position `q`. -/
def SilCand.silentOk (σ : Mstate) (aqw : Nat → Nat) (i : Nat) (aq : Bool) (base : Int)
    (ts : List Nat) (rvs wvs : List (BitVec 8)) (q : Nat) : Prop :=
  wvs = rvs ∧ wvs ≠ [] ∧ wvs.length = ts.length ∧
  rdOk σ.msImg σ.msLog (σ.msWs i) aq base ts rvs ∧
  q ≤ σ.msLog.length ∧
  (∀ (j t : Nat), ts[j]? = some t → t ≤ q ∧ ¬ writesIn σ.msLog (accAddr base j) t q) ∧
  (∀ j, j < ts.length → coh (σ.msWs i) (accAddr base j) ≤ q) ∧
  fulfilVpre (σ.msWs i) false ≤ q ∧ aqw i ≤ q

/-- An `aq` AMO's raise of the read and write-ordering views to its write position. -/
def SilCand.aqRaise (ws : Wstate) (q : Nat) : Wstate :=
  { ws with wVrOld := max ws.wVrOld q, wVrNew := max ws.wVrNew q, wVwNew := max ws.wVwNew q }

/-- The views after a silent AMO written (virtually) at `q`. -/
def SilCand.silentPost (ws : Wstate) (aq : Bool) (base : Int) (ts : List Nat) (n q : Nat) :
    Wstate :=
  storePostRun
    (if aq then SilCand.aqRaise (loadPostRun ws aq base ts) q else loadPostRun ws aq base ts)
    false base n q

def SilCand.updAqw (f : Nat → Nat) (i v : Nat) : Nat → Nat :=
  fun j => if j = i then max (f j) v else f j

/-- The `aq`-AMO view after an ordinary step. -/
def SilCand.aqwPost (σ : Mstate) (f : Nat → Nat) (i : Nat) (l : Lbl) : Nat → Nat :=
  match l with
  | .LRmw true _ _ _ _ _ _ => SilCand.updAqw f i (σ.msLog.length + 1)
  | _ => f

/-- **THE TWIN STEP**: an ordinary step, or a SILENT AMO. -/
inductive SilCand.stepS (S : SilCand.St) (i : Nat) : Lbl → SilCand.St → Prop where
  | old (l : Lbl) (σ' : Mstate) :
      mstep S.ms i l σ' → SilCand.stepS S i l ⟨σ', SilCand.aqwPost S.ms S.aqw i l⟩
  | silent (aq : Bool) (base : Int) (ts : List Nat) (rvs wvs : List (BitVec 8)) (k : WmClass)
      (q : Nat) :
      SilCand.silentOk S.ms S.aqw i aq base ts rvs wvs q →
      SilCand.stepS S i (.LRmw aq false base ts rvs wvs k)
        ⟨⟨S.ms.msImg, S.ms.msLog,
            updWs S.ms.msWs i (SilCand.silentPost (S.ms.msWs i) aq base ts wvs.length q)⟩,
          if aq then SilCand.updAqw S.aqw i q else S.aqw⟩

/-- A step keeps the log (a silent AMO, a load, a fence, an I/O step) or appends one message. -/
theorem SilCand.stepSLog (S S' : SilCand.St) (i : Nat) (l : Lbl) :
    SilCand.stepS S i l S' →
    S'.ms.msImg = S.ms.msImg ∧ (S'.ms.msLog = S.ms.msLog ∨ ∃ m, S'.ms.msLog = S.ms.msLog ++ [m]) := by
  intro h
  cases h with
  | old l σ' hm =>
    cases hm with
    | MStepLoad => exact ⟨rfl, .inl rfl⟩
    | MStepStore => exact ⟨rfl, .inr ⟨_, rfl⟩⟩
    | MStepFence => exact ⟨rfl, .inl rfl⟩
    | MStepRmw => exact ⟨rfl, .inr ⟨_, rfl⟩⟩
    | MStepIo => exact ⟨rfl, .inl rfl⟩
  | silent => exact ⟨rfl, .inl rfl⟩

/-! # 2. The twin run and the embedding -/

structure SilCand.ExecS where
  exSt : List SilCand.St
  exTr : List Estep

/-- **A TWIN RUN**: as `execWf`, at the twin step, from an empty log, initial views and no `aq` view. -/
def SilCand.execWfS (E : SilCand.ExecS) : Prop :=
  E.exSt.length = E.exTr.length + 1 ∧
  (∀ S0, E.exSt[0]? = some S0 → S0.ms.msLog = [] ∧ (∀ i, S0.ms.msWs i = wsInit) ∧
    ∀ i, S0.aqw i = 0) ∧
  (∀ k s S S', E.exTr[k]? = some s → E.exSt[k]? = some S →
    E.exSt[k + 1]? = some S' → SilCand.stepS S s.esAg s.esLb S')

/-- The registered run's states, with the `aq` view threaded along. -/
def SilCand.liftSt : List Mstate → List Estep → (Nat → Nat) → List SilCand.St
  | [], _, _ => []
  | σ :: σs, tr, f =>
    ⟨σ, f⟩ :: match tr with
      | [] => SilCand.liftSt σs [] f
      | s :: tr' => SilCand.liftSt σs tr' (SilCand.aqwPost σ f s.esAg s.esLb)

theorem SilCand.liftLen : ∀ (σs : List Mstate) (tr : List Estep) (f : Nat → Nat),
    (SilCand.liftSt σs tr f).length = σs.length := by
  intro σs
  induction σs with
  | nil => intro _ _; rfl
  | cons σ σs ih =>
    intro tr f
    cases tr with
    | nil => simp [SilCand.liftSt, ih]
    | cons s tr' => simp [SilCand.liftSt, ih]

theorem SilCand.liftHead (σ : Mstate) (σs : List Mstate) (tr : List Estep) (f : Nat → Nat) :
    (SilCand.liftSt (σ :: σs) tr f)[0]? = some ⟨σ, f⟩ := by
  cases tr <;> rfl

theorem SilCand.liftLook : ∀ (σs : List Mstate) (tr : List Estep) (f : Nat → Nat) (k : Nat)
    (s : Estep) (σ σ' : Mstate),
    tr[k]? = some s → σs[k]? = some σ → σs[k + 1]? = some σ' →
    ∃ fk, (SilCand.liftSt σs tr f)[k]? = some ⟨σ, fk⟩ ∧
      (SilCand.liftSt σs tr f)[k + 1]? = some ⟨σ', SilCand.aqwPost σ fk s.esAg s.esLb⟩ := by
  intro σs
  induction σs with
  | nil => intro _ _ _ _ _ _ _ h; simp at h
  | cons σ0 σs ih =>
    intro tr f k s σ σ' hs hσ hσ'
    cases tr with
    | nil => simp at hs
    | cons s0 tr' =>
      cases k with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hs hσ
        subst hs hσ
        simp only [List.getElem?_cons_succ] at hσ'
        cases σs with
        | nil => simp at hσ'
        | cons σ1 σs' =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hσ'
          subst hσ'
          refine ⟨f, rfl, ?_⟩
          show (SilCand.liftSt (σ1 :: σs') tr' (SilCand.aqwPost σ0 f s0.esAg s0.esLb))[0]? = _
          exact SilCand.liftHead _ _ _ _
      | succ k =>
        simp only [List.getElem?_cons_succ] at hs hσ hσ'
        obtain ⟨fk, h1, h2⟩ := ih tr' (SilCand.aqwPost σ0 f s0.esAg s0.esLb) k s σ σ' hs hσ hσ'
        exact ⟨fk, by simpa [SilCand.liftSt] using h1, by simpa [SilCand.liftSt] using h2⟩

/-- **THE EMBEDDING**: every registered run is a twin run (no silent step, the `aq` view threaded). -/
theorem SilCand.execWfOfOld (E : Exec) :
    execWf E → SilCand.execWfS ⟨SilCand.liftSt E.exSt E.exTr (fun _ => 0), E.exTr⟩ := by
  rintro ⟨hlen, h0, hstep⟩
  refine ⟨by rw [SilCand.liftLen]; exact hlen, fun S0 hS0 => ?_, fun k s S S' hs hS hS' => ?_⟩
  · cases hst : E.exSt with
    | nil => rw [hst] at hlen; simp at hlen
    | cons σ0 σs =>
      have h1 : (SilCand.liftSt E.exSt E.exTr (fun _ => 0))[0]? = some ⟨σ0, fun _ => 0⟩ := by
        rw [hst]; exact SilCand.liftHead _ _ _ _
      rw [h1, Option.some.injEq] at hS0
      subst hS0
      obtain ⟨hl, hw⟩ := h0 σ0 (by rw [hst]; rfl)
      exact ⟨hl, hw, fun _ => rfl⟩
  · have hk : k < E.exTr.length := lookup_lt_Some hs
    obtain ⟨σ, hσ⟩ : ∃ σ, E.exSt[k]? = some σ := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨σ', hσ'⟩ : ∃ σ', E.exSt[k + 1]? = some σ' := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨fk, h1, h2⟩ := SilCand.liftLook E.exSt E.exTr (fun _ => 0) k s σ σ' hs hσ hσ'
    rw [h1, Option.some.injEq] at hS
    rw [h2, Option.some.injEq] at hS'
    subst hS hS'
    exact .old s.esLb σ' (hstep k s σ σ' hs hσ hσ')

end Weak
