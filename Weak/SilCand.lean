/-
Weak: **(c) [OWN.100] — the SILENT EQUAL-VALUE AMO, increment 1: the candidate-level twin step**
(`PROGRESS-W10spike.md`, `PROGRESS-W10N2p.md`).  Lean-only, no Rocq twin.  A PRIMED TWIN: the registered
machine (`mstep`, `execWf`, `srvwmoConsistent`) is untouched.

`SilCand.stepS` is `mstep` plus ONE arm, the SILENT AMO: an AMO whose written bytes EQUAL its read bytes
(and that is not `rl`) may complete WITHOUT a message.  Per byte it reads the latest message as of an
earlier log position `q` — its write's virtual place, co-immediately after its source — subject to the
write's own ordering constraints:

  * `q` is at least — at the views AFTER the read half, where the write node evaluates them — the
    hart's coherence view of every byte (riscv.cat coherence), the write-ordering view `wVwNew` (fences
    with a write successor, `aq`: ppo rules 4/5), and the log position of the hart's own latest EXCLUSIVE
    (AMO) message (`SilCand.ownExcl`: ppo rule 5 for an earlier `aq` AMO; conservative for a non-`aq` one —
    xv6's only AMO is `amoswap.w.aq`) — the registered machine needs no such bound because its writes
    always append.  The DEPENDENCY part of the bound (control / address / data dependencies, ppo rules
    9–11/13, and the reservation) is not visible at this level (the candidate tracks no registers): the
    pf / Iris machines check `SilCand.depView ≤ q` (PARM's exclusive-store fulfil pre-view), and the twin
    program data (`SilReplay.progOkD`) carries it through the dependency shadow;
  * the read is an ordinary `rdOk` read and no write of the byte lies in `(t, q]` (atomicity:
    rmw ∩ (fre;coe) = ∅ with the write placed right after `q`);
  * afterwards the hart's views are those of an RMW written at `q` (`storePostRun … q`), its read and
    write-ordering views raised to `q` (`aqRaise`: later events follow the AMO; conservative when not `aq`).
    An earlier SILENT AMO is covered by that raise (`wVwNew`), so no extra state is needed —
    the same bound is computable at the WP-verified machine (WeakEvLang's `WGState`).

Faithful (riscv.cat): each silent AMO corresponds to an RVWMO AMO whose write sits in co immediately after
its source (equal value, so invisible to every read), placed in gmo at `q`.  xv6's failed
`amoswap.w.aq` (reads 1, writes 1) qualifies, which makes the cross-spin shape realizable
(`CertZ35.crossSpinNo` shows the registered target cannot).

  §1  `SilCand.ownExcl`, `silentOk`, `aqRaise`, `silentPost`, **`SilCand.stepS`**, `stepSLog`;
  §2  the twin run `SilCand.ExecS`/`execWfS` and the EMBEDDING **`SilCand.execWfOfOld`** (every registered
      run is a twin run).
-/
import Weak.CertZ35

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std

/-! # 1. The twin step -/

/-- The log position (1-based) of agent `i`'s latest EXCLUSIVE message (0 if none). -/
def SilCand.ownExcl (log : List Wmsg) (i : Nat) : Nat :=
  (log.zipIdx.filterMap (fun p =>
    if p.1.wmTid = some i ∧ p.1.wmAk = .WCexcl then some (p.2 + 1) else none)).foldr max 0

/-- The silent write's candidate-level ORDERING bound: after every fence- / `aq`-ordered predecessor.
(The dependency part is `SilCand.depView`, at the pf / Iris levels.) -/
def SilCand.ordOk (ws : Wstate) (q : Nat) : Prop := ws.wVwNew ≤ q

theorem SilCand.ordOkEqr (w1 w2 : Wstate) (q : Nat) :
    wsEqr w1 w2 → SilCand.ordOk w1 q → SilCand.ordOk w2 q := by
  rintro ⟨-, -, -, -, h4, -⟩ a
  show w2.wVwNew ≤ q
  rw [← h4]; exact a

/-- The silent write's DEPENDENCY bound at the pf / Iris levels: PARM's exclusive-store fulfil
pre-view (not `rl`) — `wVwNew` (fences, `aq`: ppo rules 4/5), `wVcap` (control dependencies), the
address and data dependencies of the write (`asrc`, `vsrc`: rules 9–11), the reservation's view. -/
def SilCand.depView (ws : Wstate) (asrc vsrc : List Dsrc) : Nat :=
  fulfilVpreD ws false (max (max (srcsView ws asrc) (srcsView ws vsrc)) (resView ws))

/-- The side conditions of a SILENT AMO of agent `i` at position `q`. -/
def SilCand.silentOk (σ : Mstate) (i : Nat) (aq : Bool) (base : Int)
    (ts : List Nat) (rvs wvs : List (BitVec 8)) (q : Nat) : Prop :=
  wvs = rvs ∧ wvs ≠ [] ∧ wvs.length = ts.length ∧
  rdOk σ.msImg σ.msLog (σ.msWs i) aq base ts rvs ∧
  q ≤ σ.msLog.length ∧
  (∀ (j t : Nat), ts[j]? = some t → t ≤ q ∧ ¬ writesIn σ.msLog (accAddr base j) t q) ∧
  (∀ j, j < ts.length → coh (loadPostRun (σ.msWs i) aq base ts) (accAddr base j) ≤ q) ∧
  SilCand.ordOk (loadPostRun (σ.msWs i) aq base ts) q ∧ SilCand.ownExcl σ.msLog i ≤ q

/-- The raise of the read and write-ordering views to the silent write's position. -/
def SilCand.aqRaise (ws : Wstate) (q : Nat) : Wstate :=
  { ws with wVrOld := max ws.wVrOld q, wVrNew := max ws.wVrNew q, wVwNew := max ws.wVwNew q }

/-- The views after a silent AMO written (virtually) at `q`. -/
def SilCand.silentPost (ws : Wstate) (aq : Bool) (base : Int) (ts : List Nat) (n q : Nat) :
    Wstate :=
  storePostRun (SilCand.aqRaise (loadPostRun ws aq base ts) q) false base n q

/-- The silent AMO's post-state. -/
def SilCand.silentNext (σ : Mstate) (i : Nat) (aq : Bool) (base : Int) (ts : List Nat)
    (wvs : List (BitVec 8)) (q : Nat) : Mstate :=
  ⟨σ.msImg, σ.msLog, updWs σ.msWs i (SilCand.silentPost (σ.msWs i) aq base ts wvs.length q)⟩

/-- **THE TWIN STEP**: an ordinary step, or a SILENT AMO. -/
inductive SilCand.stepS (σ : Mstate) (i : Nat) : Lbl → Mstate → Prop where
  | old (l : Lbl) (σ' : Mstate) : mstep σ i l σ' → SilCand.stepS σ i l σ'
  | silent (aq : Bool) (base : Int) (ts : List Nat) (rvs wvs : List (BitVec 8)) (k : WmClass)
      (q : Nat) :
      SilCand.silentOk σ i aq base ts rvs wvs q →
      SilCand.stepS σ i (.LRmw aq false base ts rvs wvs k) (SilCand.silentNext σ i aq base ts wvs q)

/-- A step keeps the log (a silent AMO, a load, a fence, an I/O step) or appends one message. -/
theorem SilCand.stepSLog (σ σ' : Mstate) (i : Nat) (l : Lbl) :
    SilCand.stepS σ i l σ' →
    σ'.msImg = σ.msImg ∧ (σ'.msLog = σ.msLog ∨ ∃ m, σ'.msLog = σ.msLog ++ [m]) := by
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

/-- **A TWIN RUN**: as `execWf`, at the twin step. -/
def SilCand.execWfS (E : Exec) : Prop :=
  E.exSt.length = E.exTr.length + 1 ∧
  (∀ σ0, E.exSt[0]? = some σ0 → σ0.msLog = [] ∧ ∀ i, σ0.msWs i = wsInit) ∧
  (∀ k s σ σ', E.exTr[k]? = some s → E.exSt[k]? = some σ →
    E.exSt[k + 1]? = some σ' → SilCand.stepS σ s.esAg s.esLb σ')

/-- **THE EMBEDDING**: every registered run is a twin run. -/
theorem SilCand.execWfOfOld (E : Exec) : execWf E → SilCand.execWfS E :=
  fun ⟨hlen, h0, hstep⟩ =>
    ⟨hlen, h0, fun k s σ σ' hs hσ hσ' => .old s.esLb σ' (hstep k s σ σ' hs hσ hσ')⟩

end Weak
