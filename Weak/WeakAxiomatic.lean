/-
Weak: **the axiomatic characterization of the promise-free machine** (W4 of the
M6 robustness effort, SLICE 1).

Rocq: `iris/WeakAxiomatic.v` @ xxvzwolszwmp (1cc222280).

The Rocq header, in substance: the conjectured characterization

    promise-free machine  ≡  RVWMO ∧ acyclic(po ∪ rf) ∧ (po ∩ W×W) ⊆ gmo

(`claude-notes/design/weak-memory-m6-robustness.md` §6).  THIS FILE IS SLICE 1:
the event vocabulary, the axioms as definitions, and the SOUNDNESS direction
(every promise-free machine execution induces an axiomatic execution
satisfying the axioms).  Completeness is slice 2/3 (`WeakAxiomatic2`,
`WeakAxiomatic3`).  SCOPE: the axiomatic side is "RVWMO minus ppo 9–13";
syntactic dependencies are NOT modelled (design Decision 3).  DELIBERATELY
DEPENDENCY-FREE, like `WeakMem`: no Iris, no Sail.

WHY THERE IS A MACHINE DEFINITION IN THIS FILE AT ALL: `WeakMem` defines the
memory model's STEP FUNCTIONS (`loadPostRun`, `storePostRun`, `fencePost`) and
their side conditions (`readable`, `latest`) but no whole-machine step
relation; an axiomatic characterization needs a notion of "execution", so this
file supplies the minimal one: an EVENT-LABELLED transition system whose labels
are exactly the memory-model-visible effects and whose steps are exactly
`WeakMem`'s rules.  Every modelling choice is flagged `MODELLING CHOICE` in a
comment (the Rocq comments are kept on the corresponding definitions).

**Deviations from Rocq.**

1. NAMES: as `Weak/WeakMem.lean` deviation 1 (lowerCamelCase; types
   UpperCamelCase; record fields lowerCamelCase; inductive constructors keep
   their Rocq spelling).  Rocq → Lean map of the types and fields:
   `lbl` ↦ `Lbl` (constructors `LLoad`/`LStore`/`LFence`/`LRmw` kept),
   `estep` ↦ `Estep` (`EStep i l` ↦ `⟨i, l⟩`; `es_ag`/`es_lb` ↦ `esAg`/`esLb`),
   `mstate` ↦ `Mstate` (`MSt img log ws` ↦ `⟨img, log, ws⟩`; `ms_img`/`ms_log`/
   `ms_ws` ↦ `msImg`/`msLog`/`msWs`), `exec` ↦ `Exec` (`Exec st tr` ↦
   `⟨st, tr⟩`; `ex_st`/`ex_tr` ↦ `exSt`/`exTr`), `ev` ↦ `Ev` (constructors
   `ev_init`/`ev_at` kept), the Prop inductive `mstep` keeps its lower-case
   name (as `WeakPromise.wpstep`) with constructors `MStepLoad` … `MStepRmw`.
   A segment already in camelCase keeps it with its first letter raised:
   `is_W` ↦ `isW`, `is_Wb` ↦ `isWb`, `is_W_lt` ↦ `isWLt`, `wr_b` ↦ `wrB`,
   `ev_ts_S`-style names likewise; `pub_w_vwOld` ↦ `pubWVwOld`,
   `load_post_run_vrOld_aq` ↦ `loadPostRunVrOldAq`.
2. VOCABULARY: as `WeakMem` deviation 2; `prefix_of` ↦ `List.IsPrefix`
   (`<+:`), `tc` ↦ `MachCSL.tc` (core `Relation.TransGen`), `relation A` ↦
   `A → A → Prop`, `Z.of_nat j` ↦ `(j : Int)`, `is_Some o` ↦ `o.isSome`,
   `Forall P l` ↦ `∀ x ∈ l, P x`.
3. Rocq's `default ms_junk (ex_st E !! k)` is `(E.exSt[k]?).getD msJunk`;
   `exec_st_len`/`exec_tr_lookup` conclude `(l[k]?).isSome` (Rocq `is_Some`).
4. `ev_eq_dec` is `deriving DecidableEq` on `Ev`; `Lbl`/`Estep` also derive
   `DecidableEq` (Lean-only; no statement depends on it).
5. Lean-only helper (no Rocq twin): `someOfIsSome` (the `is_Some` destructor).

**Not ported:** nothing — every Rocq definition and lemma has a Lean twin.
The two commented conjectures at the bottom of the Rocq file (slice-2
obligations) are prose, kept as the comment before `rdOkTsBounded`.

**Statements checked** (diffed against Rocq by hand): all of them; in
particular `promiseFreeSound`, `soundCoherence`, `soundOrd`, `execSnoc`,
`execNil`, `execWsBounded`, `evpreMono`.
-/
import Weak.WeakMem

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std

/-- Lean-only: destruct an `isSome`. -/
theorem someOfIsSome {α : Type _} {o : Option α} (h : o.isSome) : ∃ x, o = some x :=
  Option.isSome_iff_exists.1 h

/-! ## The label alphabet -/

/-- MODELLING CHOICE (events): ONE MACHINE STEP = ONE EVENT; byte structure is
carried inside the label.  MODELLING CHOICE (byte addressing): byte `j` of an
access based at `base` lives at `base + j`. -/
def accAddr (base : Int) (j : Nat) : Int := base + (j : Int)

theorem accAddrInj (base : Int) (j j' : Nat) : accAddr base j = accAddr base j' → j = j' := by
  unfold accAddr; omega

/-- MODELLING CHOICE (the alphabet).  Four labels: a load of `|ts|` bytes at
`base` (byte `j` reading timestamp `ts[j]` with value `vs[j]`), a store
appending ONE message of class `k`, a FENCE with its four kind bits, and an
AMO (read half + write half in ONE step, the read half constrained to the
globally latest message per byte).  The class field `k` is INERT. -/
inductive Lbl where
  | LLoad (aq : Bool) (base : Int) (ts : List Nat) (vs : List (BitVec 8))
  | LStore (rl : Bool) (base : Int) (vs : List (BitVec 8)) (k : WmClass)
  | LFence (pr pw sr sw : Bool)
  | LRmw (aq rl : Bool) (base : Int) (ts : List Nat) (rvs wvs : List (BitVec 8)) (k : WmClass)
  deriving DecidableEq, Inhabited

open Lbl

/-- MODELLING CHOICE (agents): a step names its agent; harts and the disk agent
are the same kind of thing (D-M6-4). -/
structure Estep where
  esAg : Nat
  esLb : Lbl
  deriving DecidableEq, Inhabited

structure Mstate where
  msImg : Image
  msLog : List Wmsg
  msWs : Nat → Wstate

def updWs (f : Nat → Wstate) (i : Nat) (w : Wstate) : Nat → Wstate :=
  fun j => if j = i then w else f j

theorem updWsEq (f : Nat → Wstate) (i : Nat) (w : Wstate) : updWs f i w i = w := by
  simp [updWs]

theorem updWsNe (f : Nat → Wstate) (i : Nat) (w : Wstate) (j : Nat) :
    j ≠ i → updWs f i w j = f j := by
  intro h; simp [updWs, h]

/-! ## The step relation -/

/-- One byte of a load: it returns `v` from timestamp `t`, admissible at the
load's pre-view. -/
def byteRd (img : Image) (log : List Wmsg) (ws : Wstate) (aq : Bool) (a : Int) (t : Nat)
    (v : BitVec 8) : Prop :=
  logByte img log t a = some v ∧ readable img log ws (loadVpre ws aq) a t

def rdOk (img : Image) (log : List Wmsg) (ws : Wstate) (aq : Bool) (base : Int) (ts : List Nat)
    (vs : List (BitVec 8)) : Prop :=
  vs.length = ts.length ∧
  ∀ (j : Nat) (t : Nat) (v : BitVec 8), ts[j]? = some t → vs[j]? = some v →
    byteRd img log ws aq (accAddr base j) t v

/-- The AMO's atomicity side condition: every byte of the read half takes the
globally-latest message. -/
def rmwLatest (img : Image) (log : List Wmsg) (base : Int) (ts : List Nat) : Prop :=
  ∀ (j : Nat) (t : Nat), ts[j]? = some t → latest img log (accAddr base j) t

inductive mstep (σ : Mstate) (i : Nat) : Lbl → Mstate → Prop where
  | MStepLoad (aq : Bool) (base : Int) (ts : List Nat) (vs : List (BitVec 8)) :
      rdOk σ.msImg σ.msLog (σ.msWs i) aq base ts vs →
      mstep σ i (LLoad aq base ts vs)
        ⟨σ.msImg, σ.msLog, updWs σ.msWs i (loadPostRun (σ.msWs i) aq base ts)⟩
  | MStepStore (rl : Bool) (base : Int) (vs : List (BitVec 8)) (k : WmClass) :
      vs ≠ [] →
      mstep σ i (LStore rl base vs k)
        ⟨σ.msImg, σ.msLog ++ [⟨base, vs, some i, k⟩],
         updWs σ.msWs i (storePostRun (σ.msWs i) rl base vs.length (σ.msLog.length + 1))⟩
  | MStepFence (pr pw sr sw : Bool) :
      mstep σ i (LFence pr pw sr sw)
        ⟨σ.msImg, σ.msLog, updWs σ.msWs i (fencePost (σ.msWs i) pr pw sr sw)⟩
  | MStepRmw (aq rl : Bool) (base : Int) (ts : List Nat) (rvs wvs : List (BitVec 8))
      (k : WmClass) :
      wvs ≠ [] → wvs.length = ts.length →
      rdOk σ.msImg σ.msLog (σ.msWs i) aq base ts rvs →
      rmwLatest σ.msImg σ.msLog base ts →
      mstep σ i (LRmw aq rl base ts rvs wvs k)
        ⟨σ.msImg, σ.msLog ++ [⟨base, wvs, some i, k⟩],
         updWs σ.msWs i
           (storePostRun (loadPostRun (σ.msWs i) aq base ts) rl base wvs.length
             (σ.msLog.length + 1))⟩

/-- Label classification. -/
def lbIsW (l : Lbl) : Bool :=
  match l with
  | LStore .. | LRmw .. => true
  | _ => false

def lbIsR (l : Lbl) : Bool :=
  match l with
  | LLoad .. | LRmw .. => true
  | _ => false

def lbAq (l : Lbl) : Bool :=
  match l with
  | LLoad aq _ _ _ => aq
  | LRmw aq _ _ _ _ _ _ => aq
  | _ => false

/-- The INERT class the label's write half publishes (`WCplain` elsewhere). -/
def lbCls (l : Lbl) : WmClass :=
  match l with
  | LStore _ _ _ k => k
  | LRmw _ _ _ _ _ _ k => k
  | _ => .WCplain

/-- The read footprint: base, per-byte timestamps, per-byte values. -/
def lbRd (l : Lbl) : Option (Int × List Nat × List (BitVec 8)) :=
  match l with
  | LLoad _ base ts vs => some (base, ts, vs)
  | LRmw _ _ base ts rvs _ _ => some (base, ts, rvs)
  | _ => none

/-- The write footprint: base and the bytes written. -/
def lbWr (l : Lbl) : Option (Int × List (BitVec 8)) :=
  match l with
  | LStore _ base vs _ => some (base, vs)
  | LRmw _ _ base _ _ wvs _ => some (base, wvs)
  | _ => none

theorem lbIsWWr (l : Lbl) : lbIsW l = true → ∃ base vs, lbWr l = some (base, vs) := by
  cases l with
  | LLoad => intro h; simp [lbIsW] at h
  | LStore rl base vs k => intro _; exact ⟨base, vs, rfl⟩
  | LFence => intro h; simp [lbIsW] at h
  | LRmw aq rl base ts rvs wvs k => intro _; exact ⟨base, wvs, rfl⟩

theorem lbIsRRd (l : Lbl) : lbIsR l = true → ∃ base ts vs, lbRd l = some (base, ts, vs) := by
  cases l with
  | LLoad aq base ts vs => intro _; exact ⟨base, ts, vs, rfl⟩
  | LStore => intro h; simp [lbIsR] at h
  | LFence => intro h; simp [lbIsR] at h
  | LRmw aq rl base ts rvs wvs k => intro _; exact ⟨base, ts, rvs, rfl⟩

/-! ## Per-step facts -/

theorem mstepImg (σ : Mstate) (i : Nat) (l : Lbl) (σ' : Mstate) :
    mstep σ i l σ' → σ'.msImg = σ.msImg := by
  intro h; cases h <;> rfl

theorem mstepLogNw (σ : Mstate) (i : Nat) (l : Lbl) (σ' : Mstate) :
    mstep σ i l σ' → lbIsW l = false → σ'.msLog = σ.msLog := by
  intro h hw; cases h <;> simp_all [lbIsW]

theorem mstepLogW (σ : Mstate) (i : Nat) (l : Lbl) (σ' : Mstate) :
    mstep σ i l σ' → lbIsW l = true →
    ∃ base vs, lbWr l = some (base, vs) ∧ vs ≠ [] ∧
      σ'.msLog = σ.msLog ++ [⟨base, vs, some i, lbCls l⟩] := by
  intro h hw
  cases h with
  | MStepLoad => simp [lbIsW] at hw
  | MStepStore rl base vs k hne => exact ⟨base, vs, rfl, hne, rfl⟩
  | MStepFence => simp [lbIsW] at hw
  | MStepRmw aq rl base ts rvs wvs k hne _ _ _ => exact ⟨base, wvs, rfl, hne, rfl⟩

theorem mstepLogPrefix (σ : Mstate) (i : Nat) (l : Lbl) (σ' : Mstate) :
    mstep σ i l σ' → σ.msLog <+: σ'.msLog := by
  intro hs
  cases hw : lbIsW l
  · rw [mstepLogNw _ _ _ _ hs hw]; exact ⟨[], List.append_nil _⟩
  · obtain ⟨base, vs, _, _, hlog⟩ := mstepLogW _ _ _ _ hs hw
    rw [hlog]; exact ⟨_, rfl⟩

theorem mstepWsNe (σ : Mstate) (i : Nat) (l : Lbl) (σ' : Mstate) (j : Nat) :
    mstep σ i l σ' → j ≠ i → σ'.msWs j = σ.msWs j := by
  intro hs hne
  cases hs <;> exact updWsNe _ _ _ _ hne

theorem mstepWsLe (σ : Mstate) (i : Nat) (l : Lbl) (σ' : Mstate) (j : Nat) :
    mstep σ i l σ' → wsLe (σ.msWs j) (σ'.msWs j) := by
  intro hs
  by_cases hj : j = i
  · subst hj
    cases hs with
    | MStepLoad => show wsLe _ (updWs _ _ _ _); rw [updWsEq]; exact loadPostRunLe _ _ _ _
    | MStepStore => show wsLe _ (updWs _ _ _ _); rw [updWsEq]; exact storePostRunLe _ _ _ _ _
    | MStepFence => show wsLe _ (updWs _ _ _ _); rw [updWsEq]; exact fencePostLe _ _ _ _ _
    | MStepRmw =>
      show wsLe _ (updWs _ _ _ _); rw [updWsEq]
      exact wsLeTrans (loadPostRunLe _ _ _ _) (storePostRunLe _ _ _ _ _)
  · rw [mstepWsNe _ _ _ _ _ hs hj]; exact wsLeRefl _

/-! ## Executions

MODELLING CHOICE (executions): a list of STATES with a list of STEPS, related
pointwise — event identity is "position in the run". -/

structure Exec where
  exSt : List Mstate
  exTr : List Estep

/-- MODELLING CHOICE (the era-initial image): timestamp 0 is the image, and the
initial LOG IS REQUIRED TO BE EMPTY; the initial per-agent states are
`wsInit`. -/
def execWf (E : Exec) : Prop :=
  E.exSt.length = E.exTr.length + 1 ∧
  (∀ σ0, E.exSt[0]? = some σ0 → σ0.msLog = [] ∧ ∀ i, σ0.msWs i = wsInit) ∧
  (∀ k s σ σ', E.exTr[k]? = some s → E.exSt[k]? = some σ →
    E.exSt[k + 1]? = some σ' → mstep σ s.esAg s.esLb σ')

/-- Total accessors (junk outside the run). -/
def msJunk : Mstate := ⟨fun _ => none, [], fun _ => wsInit⟩
def stt (E : Exec) (k : Nat) : Mstate := (E.exSt[k]?).getD msJunk
def elog (E : Exec) (k : Nat) : List Wmsg := (stt E k).msLog
def eimg (E : Exec) (k : Nat) : Image := (stt E k).msImg
def ews (E : Exec) (k : Nat) (i : Nat) : Wstate := (stt E k).msWs i

theorem sttLookup (E : Exec) (k : Nat) (σ : Mstate) : E.exSt[k]? = some σ → stt E k = σ := by
  intro h; simp [stt, h]

theorem execStLen (E : Exec) (k : Nat) :
    execWf E → k ≤ E.exTr.length → (E.exSt[k]?).isSome := by
  intro ⟨hlen, _, _⟩ hk
  exact lookup_lt_is_Some_2 (by omega)

/-- The one lemma that unpacks `execWf`'s step clause at the total accessors. -/
theorem execStepAt (E : Exec) (k : Nat) (s : Estep) :
    execWf E → E.exTr[k]? = some s → mstep (stt E k) s.esAg s.esLb (stt E (k + 1)) := by
  intro hwf hs
  have hlt := lookup_lt_Some hs
  obtain ⟨hlen, _, hstep⟩ := hwf
  have h1 : E.exSt[k]? = some E.exSt[k] := List.getElem?_eq_getElem (by omega)
  have h2 : E.exSt[k + 1]? = some E.exSt[k + 1] := List.getElem?_eq_getElem (by omega)
  rw [sttLookup _ _ _ h1, sttLookup _ _ _ h2]
  exact hstep k s _ _ hs h1 h2

theorem execTrLookup (E : Exec) (k : Nat) : k < E.exTr.length → (E.exTr[k]?).isSome :=
  lookup_lt_is_Some_2

/-- Structural monotonicity along a run. -/
theorem execLogPrefix (E : Exec) (k k' : Nat) :
    execWf E → k ≤ k' → k' ≤ E.exTr.length → elog E k <+: elog E k' := by
  intro hwf hle hk'
  induction k' with
  | zero =>
    have : k = 0 := by omega
    subst this; exact ⟨[], List.append_nil _⟩
  | succ k' ih =>
    by_cases hk : k = k' + 1
    · subst hk; exact ⟨[], List.append_nil _⟩
    · refine (ih (by omega) (by omega)).trans ?_
      obtain ⟨s, hs⟩ := someOfIsSome (execTrLookup E k' (by omega))
      exact mstepLogPrefix _ _ _ _ (execStepAt E k' s hwf hs)

theorem execLogLenLe (E : Exec) (k k' : Nat) :
    execWf E → k ≤ k' → k' ≤ E.exTr.length → (elog E k).length ≤ (elog E k').length := by
  intro hwf hle hk'
  exact prefix_length (execLogPrefix E k k' hwf hle hk')

theorem execWsLe (E : Exec) (k k' : Nat) (i : Nat) :
    execWf E → k ≤ k' → k' ≤ E.exTr.length → wsLe (ews E k i) (ews E k' i) := by
  intro hwf hle hk'
  induction k' with
  | zero =>
    have : k = 0 := by omega
    subst this; exact wsLeRefl _
  | succ k' ih =>
    by_cases hk : k = k' + 1
    · subst hk; exact wsLeRefl _
    · refine wsLeTrans (ih (by omega) (by omega)) ?_
      obtain ⟨s, hs⟩ := someOfIsSome (execTrLookup E k' (by omega))
      exact mstepWsLe _ _ _ _ i (execStepAt E k' s hwf hs)

theorem execImgConst (E : Exec) (k : Nat) :
    execWf E → k ≤ E.exTr.length → eimg E k = eimg E 0 := by
  intro hwf hk
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [← ih (by omega)]
    obtain ⟨s, hs⟩ := someOfIsSome (execTrLookup E k (by omega))
    exact mstepImg _ _ _ _ (execStepAt E k s hwf hs)

/-- The whole run's image and final log. -/
def exImg (E : Exec) : Image := eimg E 0
def exLog (E : Exec) : List Wmsg := elog E E.exTr.length

theorem exLogPrefix (E : Exec) (k : Nat) :
    execWf E → k ≤ E.exTr.length → elog E k <+: exLog E := by
  intro hwf hk; exact execLogPrefix E k _ hwf hk (Nat.le_refl _)

/-- A byte value read at step `k` is still there at the end of the run. -/
theorem logByteFinal (E : Exec) (k t : Nat) (a : Int) :
    execWf E → k ≤ E.exTr.length → t ≤ (elog E k).length →
    logByte (exImg E) (exLog E) t a = logByte (eimg E k) (elog E k) t a := by
  intro hwf hk ht
  rw [execImgConst E k hwf hk]
  obtain ⟨l, hl⟩ := exLogPrefix E k hwf hk
  rw [exImg, ← hl, logByteApp _ _ _ _ _ ht]

/-! ## Events

MODELLING CHOICE (event identity): the VIRTUAL INIT WRITE `ev_init`
(timestamp 0, the image) or the step at position `k`, `ev_at k`.  `evIx` is
the total order on events; `evTs` the event's global-memory-order position
(meaningful for writes). -/

inductive Ev where
  | ev_init
  | ev_at (k : Nat)
  deriving DecidableEq, Inhabited

open Ev

def evIx (e : Ev) : Nat :=
  match e with
  | ev_init => 0
  | ev_at k => k + 1

def evTs (E : Exec) (e : Ev) : Nat :=
  match e with
  | ev_init => 0
  | ev_at k => (elog E k).length + 1

theorem evTsAt (E : Exec) (k : Nat) : evTs E (ev_at k) = (elog E k).length + 1 := rfl

def isW (E : Exec) (e : Ev) : Prop :=
  match e with
  | ev_init => True
  | ev_at k => ∃ s, E.exTr[k]? = some s ∧ lbIsW s.esLb = true

def isR (E : Exec) (e : Ev) : Prop :=
  ∃ k s, e = ev_at k ∧ E.exTr[k]? = some s ∧ lbIsR s.esLb = true

theorem isWLt (E : Exec) (k : Nat) : isW E (ev_at k) → k < E.exTr.length := by
  rintro ⟨s, hs, _⟩; exact lookup_lt_Some hs

theorem lbWrIsW (l : Lbl) (x : Int × List (BitVec 8)) : lbWr l = some x → lbIsW l = true := by
  cases l <;> simp [lbWr, lbIsW]

theorem lbRdIsR (l : Lbl) (x : Int × List Nat × List (BitVec 8)) :
    lbRd l = some x → lbIsR l = true := by
  cases l <;> simp [lbRd, lbIsR]

/-- The bytes an event writes, read off the FINAL log at its timestamp. -/
def evWrites (E : Exec) (e : Ev) (a : Int) : Prop :=
  (logByte (exImg E) (exLog E) (evTs E e) a).isSome

theorem evWritesInit (E : Exec) (a : Int) : evWrites E ev_init a ↔ (exImg E a).isSome :=
  Iff.rfl

/-- Initial state facts. -/
theorem execSt0 (E : Exec) : execWf E → ∃ σ0, E.exSt[0]? = some σ0 := by
  intro hwf; exact someOfIsSome (execStLen E 0 hwf (Nat.zero_le _))

theorem execLogInit (E : Exec) : execWf E → elog E 0 = [] := by
  intro hwf
  obtain ⟨σ0, h0⟩ := execSt0 E hwf
  rw [elog, sttLookup _ _ _ h0]
  exact (hwf.2.1 σ0 h0).1

theorem execWsInit (E : Exec) (i : Nat) : execWf E → ews E 0 i = wsInit := by
  intro hwf
  obtain ⟨σ0, h0⟩ := execSt0 E hwf
  rw [ews, sttLookup _ _ _ h0]
  exact (hwf.2.1 σ0 h0).2 i

/-- The message a write step appends, located in the final log. -/
theorem execMsgAt (E : Exec) (k : Nat) (s : Estep) (base : Int) (vs : List (BitVec 8)) :
    execWf E → E.exTr[k]? = some s → lbWr s.esLb = some (base, vs) →
    (exLog E)[(elog E k).length]? = some ⟨base, vs, some s.esAg, lbCls s.esLb⟩ := by
  intro hwf hs hwr
  have hk := lookup_lt_Some hs
  have hstep := execStepAt E k s hwf hs
  obtain ⟨base', vs', hwr', _, hlog⟩ := mstepLogW _ _ _ _ hstep (lbWrIsW _ _ hwr)
  rw [hwr] at hwr'
  simp only [Option.some.injEq, Prod.mk.injEq] at hwr'
  obtain ⟨rfl, rfl⟩ := hwr'
  obtain ⟨l, hl⟩ := exLogPrefix E (k + 1) hwf (by omega)
  rw [← hl]
  change ((stt E (k + 1)).msLog ++ l)[(stt E k).msLog.length]? = _
  rw [hlog, List.append_assoc]
  simp

theorem evWritesAt (E : Exec) (k : Nat) (s : Estep) (base : Int) (vs : List (BitVec 8)) (a : Int) :
    execWf E → E.exTr[k]? = some s → lbWr s.esLb = some (base, vs) →
    (evWrites E (ev_at k) a ↔ (msgByte ⟨base, vs, some s.esAg, lbCls s.esLb⟩ a).isSome) := by
  intro hwf hs hwr
  unfold evWrites
  rw [evTsAt, logByteS, execMsgAt E k s base vs hwf hs hwr]
  rfl

/-- Write timestamps are strictly increasing in execution order. -/
theorem evTsNext (E : Exec) (k : Nat) (s : Estep) :
    execWf E → E.exTr[k]? = some s → lbIsW s.esLb = true →
    (elog E (k + 1)).length = evTs E (ev_at k) := by
  intro hwf hs hw
  have hstep := execStepAt E k s hwf hs
  obtain ⟨base, vs, _, _, hlog⟩ := mstepLogW _ _ _ _ hstep hw
  rw [evTsAt]
  change ((stt E (k + 1)).msLog).length = _
  rw [hlog, List.length_append]
  rfl

theorem evTsMono (E : Exec) (k k' : Nat) :
    execWf E → k < k' → isW E (ev_at k) → isW E (ev_at k') →
    evTs E (ev_at k) < evTs E (ev_at k') := by
  rintro hwf hlt ⟨s, hs, hw⟩ hW'
  have hk' := isWLt E k' hW'
  rw [← evTsNext E k s hwf hs hw]
  have := execLogLenLe E (k + 1) k' hwf (by omega) (by omega)
  rw [evTsAt]; omega

/-- Hence a write event is determined by its timestamp. -/
theorem evTsInj (E : Exec) (e1 e2 : Ev) :
    execWf E → isW E e1 → isW E e2 → evTs E e1 = evTs E e2 → e1 = e2 := by
  intro hwf h1 h2 hts
  cases e1 with
  | ev_init =>
    cases e2 with
    | ev_init => rfl
    | ev_at k2 => simp [evTs] at hts
  | ev_at k1 =>
    cases e2 with
    | ev_init => simp [evTs] at hts
    | ev_at k2 =>
      by_cases heq : k1 = k2
      · rw [heq]
      · exfalso
        by_cases hlt : k1 < k2
        · have := evTsMono E k1 k2 hwf hlt h1 h2; omega
        · have := evTsMono E k2 k1 hwf (by omega) h2 h1; omega

/-- Every non-zero timestamp present in the log is the timestamp of a unique
earlier WRITE STEP — what makes `rf` total. -/
theorem tsWriter (E : Exec) (k t : Nat) :
    execWf E → k ≤ E.exTr.length → 0 < t → t ≤ (elog E k).length →
    ∃ k' s, k' < k ∧ E.exTr[k']? = some s ∧ lbIsW s.esLb = true ∧ evTs E (ev_at k') = t := by
  intro hwf
  induction k with
  | zero => intro _ ht hlen; rw [execLogInit E hwf] at hlen; simp at hlen; omega
  | succ k ih =>
    intro hk ht hlen
    obtain ⟨s, hs⟩ := someOfIsSome (execTrLookup E k (by omega))
    cases hw : lbIsW s.esLb
    · have hstep := execStepAt E k s hwf hs
      have hl : elog E (k + 1) = elog E k := mstepLogNw _ _ _ _ hstep hw
      rw [hl] at hlen
      obtain ⟨k', s', h1, h2, h3, h4⟩ := ih (by omega) ht hlen
      exact ⟨k', s', by omega, h2, h3, h4⟩
    · rw [evTsNext E k s hwf hs hw, evTsAt] at hlen
      by_cases heq : t = (elog E k).length + 1
      · exact ⟨k, s, by omega, hs, hw, by rw [evTsAt, heq]⟩
      · obtain ⟨k', s', h1, h2, h3, h4⟩ := ih (by omega) ht (by omega)
        exact ⟨k', s', by omega, h2, h3, h4⟩

/-- Reading a step's side conditions back off the trace. -/
theorem lbRdCases (l : Lbl) (base : Int) (ts : List Nat) (vs : List (BitVec 8)) :
    lbRd l = some (base, ts, vs) →
    ∃ aq, lbAq l = aq ∧
      (l = LLoad aq base ts vs ∨ ∃ rl wvs k, l = LRmw aq rl base ts vs wvs k) := by
  cases l with
  | LLoad aq b t v =>
    intro h; simp only [lbRd, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨aq, rfl, .inl rfl⟩
  | LStore => intro h; simp [lbRd] at h
  | LFence => intro h; simp [lbRd] at h
  | LRmw aq rl b t rv wv k =>
    intro h; simp only [lbRd, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨aq, rfl, .inr ⟨rl, wv, k, rfl⟩⟩

theorem execRdOk (E : Exec) (k : Nat) (s : Estep) (base : Int) (ts : List Nat)
    (vs : List (BitVec 8)) :
    execWf E → E.exTr[k]? = some s → lbRd s.esLb = some (base, ts, vs) →
    rdOk (eimg E k) (elog E k) (ews E k s.esAg) (lbAq s.esLb) base ts vs := by
  intro hwf hs hrd
  have hstep := execStepAt E k s hwf hs
  obtain ⟨aq, haq, hl | ⟨rl, wvs, kc, hl⟩⟩ := lbRdCases _ _ _ _ hrd
  · rw [hl] at hstep; rw [hl]
    generalize stt E (k + 1) = σ' at hstep
    cases hstep with
    | MStepLoad _ _ _ _ h => exact h
  · rw [hl] at hstep; rw [hl]
    generalize stt E (k + 1) = σ' at hstep
    cases hstep with
    | MStepRmw _ _ _ _ _ _ _ _ _ h _ => exact h

theorem execRmwLatest (E : Exec) (k : Nat) (s : Estep) (aq rl : Bool) (base : Int)
    (ts : List Nat) (rvs wvs : List (BitVec 8)) (kc : WmClass) :
    execWf E → E.exTr[k]? = some s → s.esLb = LRmw aq rl base ts rvs wvs kc →
    rmwLatest (eimg E k) (elog E k) base ts := by
  intro hwf hs hl
  have hstep := execStepAt E k s hwf hs
  rw [hl] at hstep
  generalize stt E (k + 1) = σ' at hstep
  cases hstep with
  | MStepRmw _ _ _ _ _ _ _ _ _ _ h => exact h

/-! ## Reads, and the per-byte reads-from

MODELLING CHOICE (reads-from is PER BYTE): `readsAt E k a t v` says step `k`
read byte `a` at timestamp `t` obtaining `v`. -/

def readsAt (E : Exec) (k : Nat) (a : Int) (t : Nat) (v : BitVec 8) : Prop :=
  ∃ s base ts vs, ∃ j : Nat,
    E.exTr[k]? = some s ∧ lbRd s.esLb = some (base, ts, vs) ∧
    ts[j]? = some t ∧ vs[j]? = some v ∧ a = accAddr base j

theorem readsAtLt (E : Exec) (k : Nat) (a : Int) (t : Nat) (v : BitVec 8) :
    readsAt E k a t v → k < E.exTr.length := by
  rintro ⟨s, _, _, _, _, hs, _⟩; exact lookup_lt_Some hs

theorem readsAtByteRd (E : Exec) (k : Nat) (a : Int) (t : Nat) (v : BitVec 8) :
    execWf E → readsAt E k a t v →
    ∃ s, E.exTr[k]? = some s ∧
      byteRd (eimg E k) (elog E k) (ews E k s.esAg) (lbAq s.esLb) a t v := by
  rintro hwf ⟨s, base, ts, vs, j, hs, hrd, hj, hv, rfl⟩
  exact ⟨s, hs, (execRdOk E k s base ts vs hwf hs hrd).2 j t v hj hv⟩

theorem readsAtTsLe (E : Exec) (k : Nat) (a : Int) (t : Nat) (v : BitVec 8) :
    execWf E → readsAt E k a t v → t ≤ (elog E k).length := by
  intro hwf hr
  obtain ⟨s, _, hv, _⟩ := readsAtByteRd E k a t v hwf hr
  exact logByteBounded (eimg E k) (elog E k) t a (by rw [hv]; rfl)

/-! ## The relations of an axiomatic execution -/

/-- `e` writes / reads / accesses byte `a`. -/
def wrB (E : Exec) (a : Int) (e : Ev) : Prop := isW E e ∧ evWrites E e a
def rdB (E : Exec) (a : Int) (e : Ev) : Prop := ∃ k t v, e = ev_at k ∧ readsAt E k a t v
def accB (E : Exec) (a : Int) (e : Ev) : Prop := wrB E a e ∨ rdB E a e

/-- PROGRAM ORDER: the per-agent step order (`ev_init` is in no `po` edge). -/
def po (E : Exec) (e1 e2 : Ev) : Prop :=
  ∃ k1 k2 s1 s2, e1 = ev_at k1 ∧ e2 = ev_at k2 ∧ k1 < k2 ∧
    E.exTr[k1]? = some s1 ∧ E.exTr[k2]? = some s2 ∧ s1.esAg = s2.esAg

/-- READS-FROM, per byte and lifted to events. -/
def rfB (E : Exec) (a : Int) (w r : Ev) : Prop :=
  wrB E a w ∧ ∃ k t v, r = ev_at k ∧ readsAt E k a t v ∧ evTs E w = t
def rf (E : Exec) (w r : Ev) : Prop := ∃ a, rfB E a w r

/-- THE GLOBAL MEMORY ORDER ON WRITES: the log order. -/
def gmo (E : Exec) (w1 w2 : Ev) : Prop := isW E w1 ∧ isW E w2 ∧ evTs E w1 < evTs E w2

/-- COHERENCE ORDER: `gmo` restricted to the writes of one byte. -/
def coB (E : Exec) (a : Int) (w1 w2 : Ev) : Prop :=
  wrB E a w1 ∧ wrB E a w2 ∧ evTs E w1 < evTs E w2
def co (E : Exec) (w1 w2 : Ev) : Prop := ∃ a, coB E a w1 w2

/-- FROM-READ (the `r ≠ w` side condition is what fusing an RMW costs). -/
def frB (E : Exec) (a : Int) (r w : Ev) : Prop :=
  (∃ w0, rfB E a w0 r ∧ coB E a w0 w) ∧ r ≠ w
def fr (E : Exec) (r w : Ev) : Prop := ∃ a, frB E a r w

/-- Same-byte program order. -/
def poLocB (E : Exec) (a : Int) (e1 e2 : Ev) : Prop := po E e1 e2 ∧ accB E a e1 ∧ accB E a e2

/-- The event is a fused read-modify-write. -/
def isRmw (E : Exec) (e : Ev) : Prop :=
  ∃ k s, e = ev_at k ∧ E.exTr[k]? = some s ∧ lbIsR s.esLb = true ∧ lbIsW s.esLb = true

/-! ## Acyclicity by a lexicographic measure -/

def lexlt (p q : Nat × Nat) : Prop := p.1 < q.1 ∨ (p.1 = q.1 ∧ p.2 < q.2)

theorem lexltTrans (p q r : Nat × Nat) : lexlt p q → lexlt q r → lexlt p r := by
  unfold lexlt; omega

theorem lexltIrrefl (p : Nat × Nat) : ¬ lexlt p p := by
  unfold lexlt; omega

theorem tcLexlt {A : Type _} (R : A → A → Prop) (f : A → Nat × Nat) :
    (∀ x y, R x y → lexlt (f x) (f y)) → ∀ x, ¬ tc R x x := by
  intro hf x hc
  have hall : ∀ y z, tc R y z → lexlt (f y) (f z) := by
    intro y z hyz
    induction hyz with
    | single h => exact hf _ _ h
    | tail _ h ih => exact lexltTrans _ _ _ ih (hf _ _ h)
  exact lexltIrrefl (f x) (hall x x hc)

/-- The scalar special case. -/
theorem tcNatLt {A : Type _} (R : A → A → Prop) (f : A → Nat) :
    (∀ x y, R x y → f x < f y) → ∀ x, ¬ tc R x x := by
  intro hf
  apply tcLexlt R (fun x => (f x, 0))
  intro x y h; left; exact hf x y h

/-! ## Well-formedness of `rf`: total, functional, value-correct -/

theorem readsAtLogFinal (E : Exec) (k : Nat) (a : Int) (t : Nat) (v : BitVec 8) :
    execWf E → readsAt E k a t v → logByte (exImg E) (exLog E) t a = some v := by
  intro hwf hr
  have hk := readsAtLt E k a t v hr
  have ht := readsAtTsLe E k a t v hwf hr
  rw [logByteFinal E k t a hwf (by omega) ht]
  obtain ⟨s, _, hv, _⟩ := readsAtByteRd E k a t v hwf hr
  exact hv

/-- Two reads of the SAME byte by the SAME step agree. -/
theorem readsAtDet (E : Exec) (k : Nat) (a : Int) (t : Nat) (v : BitVec 8) (t' : Nat)
    (v' : BitVec 8) : readsAt E k a t v → readsAt E k a t' v' → t = t' ∧ v = v' := by
  rintro ⟨s, base, ts, vs, j, hs, hrd, hj, hv, ha⟩ ⟨s', base', ts', vs', j', hs', hrd', hj', hv', ha'⟩
  rw [hs] at hs'; cases hs'
  rw [hrd] at hrd'
  simp only [Option.some.injEq, Prod.mk.injEq] at hrd'
  obtain ⟨rfl, rfl, rfl⟩ := hrd'
  have : j = j' := accAddrInj base j j' (by rw [← ha, ← ha'])
  subst this
  rw [hj] at hj'; rw [hv] at hv'
  cases hj'; cases hv'
  exact ⟨rfl, rfl⟩

theorem rfBTotal (E : Exec) (k : Nat) (a : Int) (t : Nat) (v : BitVec 8) :
    execWf E → readsAt E k a t v → ∃ w, rfB E a w (ev_at k) := by
  intro hwf hr
  have hk := readsAtLt E k a t v hr
  have hlog := readsAtLogFinal E k a t v hwf hr
  cases t with
  | zero =>
    refine ⟨ev_init, ⟨trivial, ?_⟩, k, 0, v, rfl, hr, rfl⟩
    show (logByte (exImg E) (exLog E) 0 a).isSome
    rw [hlog]; rfl
  | succ t' =>
    obtain ⟨k', s', _, hs', hw', hts⟩ :=
      tsWriter E k (t' + 1) hwf (by omega) (by omega) (readsAtTsLe E k a _ v hwf hr)
    refine ⟨ev_at k', ⟨⟨s', hs', hw'⟩, ?_⟩, k, t' + 1, v, rfl, hr, hts⟩
    show (logByte (exImg E) (exLog E) (evTs E (ev_at k')) a).isSome
    rw [hts, hlog]; rfl

/-- `rf` is functional per byte. -/
theorem rfBFunctional (E : Exec) (a : Int) (w1 w2 r : Ev) :
    execWf E → rfB E a w1 r → rfB E a w2 r → w1 = w2 := by
  rintro hwf ⟨⟨hW1, _⟩, k, t, v, rfl, hr, hts1⟩ ⟨⟨hW2, _⟩, k', t', v', hk, hr', hts2⟩
  cases hk
  obtain ⟨rfl, _⟩ := readsAtDet E k a t v t' v' hr hr'
  exact evTsInj E w1 w2 hwf hW1 hW2 (by rw [hts1, hts2])

theorem rfBValue (E : Exec) (a : Int) (w : Ev) (k t : Nat) (v : BitVec 8) :
    execWf E → readsAt E k a t v → rfB E a w (ev_at k) →
    logByte (exImg E) (exLog E) (evTs E w) a = some v := by
  rintro hwf hr ⟨_, k', t', v', hk, hr', hts⟩
  cases hk
  obtain ⟨rfl, rfl⟩ := readsAtDet E k a t v t' v' hr hr'
  rw [hts]; exact readsAtLogFinal E k a t v hwf hr

/-! ## `rf` and `po` both point forward in execution order -/

theorem poIx (E : Exec) (e1 e2 : Ev) : po E e1 e2 → evIx e1 < evIx e2 := by
  rintro ⟨k1, k2, _, _, rfl, rfl, h, _⟩; simp [evIx]; omega

/-- THE key structural fact behind `acyclic(po ∪ rf)`: a load can only read a
message ALREADY IN THE LOG. -/
theorem rfIx (E : Exec) (w r : Ev) : execWf E → rf E w r → evIx w < evIx r := by
  rintro hwf ⟨a, ⟨hW, _⟩, k, t, v, rfl, hr, hts⟩
  cases w with
  | ev_init => simp [evIx]
  | ev_at k' =>
    have hk := readsAtLt E k a t v hr
    have ht := readsAtTsLe E k a t v hwf hr
    have hk' := isWLt E k' hW
    rw [evTsAt] at hts
    simp only [evIx]
    by_cases hlt : k' < k
    · omega
    · exfalso
      have := execLogLenLe E k k' hwf (by omega) (by omega)
      omega

/-! ## Per-agent state along a run: the shape of each step's update -/

theorem mstepWsLoad (σ : Mstate) (i : Nat) (aq : Bool) (base : Int) (ts : List Nat)
    (vs : List (BitVec 8)) (σ' : Mstate) :
    mstep σ i (LLoad aq base ts vs) σ' → σ'.msWs i = loadPostRun (σ.msWs i) aq base ts := by
  intro h; cases h; exact updWsEq _ _ _

theorem mstepWsStore (σ : Mstate) (i : Nat) (rl : Bool) (base : Int) (vs : List (BitVec 8))
    (k : WmClass) (σ' : Mstate) :
    mstep σ i (LStore rl base vs k) σ' →
    σ'.msWs i = storePostRun (σ.msWs i) rl base vs.length (σ.msLog.length + 1) := by
  intro h; cases h; exact updWsEq _ _ _

theorem mstepWsFence (σ : Mstate) (i : Nat) (pr pw sr sw : Bool) (σ' : Mstate) :
    mstep σ i (LFence pr pw sr sw) σ' → σ'.msWs i = fencePost (σ.msWs i) pr pw sr sw := by
  intro h; cases h; exact updWsEq _ _ _

theorem mstepWsRmw (σ : Mstate) (i : Nat) (aq rl : Bool) (base : Int) (ts : List Nat)
    (rvs wvs : List (BitVec 8)) (k : WmClass) (σ' : Mstate) :
    mstep σ i (LRmw aq rl base ts rvs wvs k) σ' →
    σ'.msWs i = storePostRun (loadPostRun (σ.msWs i) aq base ts) rl base wvs.length
      (σ.msLog.length + 1) := by
  intro h; cases h; exact updWsEq _ _ _

theorem execWsLoad (E : Exec) (k : Nat) (s : Estep) (aq : Bool) (base : Int) (ts : List Nat)
    (vs : List (BitVec 8)) :
    execWf E → E.exTr[k]? = some s → s.esLb = LLoad aq base ts vs →
    ews E (k + 1) s.esAg = loadPostRun (ews E k s.esAg) aq base ts := by
  intro hwf hs hl
  have hstep := execStepAt E k s hwf hs
  rw [hl] at hstep
  exact mstepWsLoad _ _ _ _ _ _ _ hstep

theorem execWsStore (E : Exec) (k : Nat) (s : Estep) (rl : Bool) (base : Int)
    (vs : List (BitVec 8)) (kc : WmClass) :
    execWf E → E.exTr[k]? = some s → s.esLb = LStore rl base vs kc →
    ews E (k + 1) s.esAg = storePostRun (ews E k s.esAg) rl base vs.length (evTs E (ev_at k)) := by
  intro hwf hs hl
  have hstep := execStepAt E k s hwf hs
  rw [hl] at hstep
  exact mstepWsStore _ _ _ _ _ _ _ hstep

theorem execWsFence (E : Exec) (k : Nat) (s : Estep) (pr pw sr sw : Bool) :
    execWf E → E.exTr[k]? = some s → s.esLb = LFence pr pw sr sw →
    ews E (k + 1) s.esAg = fencePost (ews E k s.esAg) pr pw sr sw := by
  intro hwf hs hl
  have hstep := execStepAt E k s hwf hs
  rw [hl] at hstep
  exact mstepWsFence _ _ _ _ _ _ _ hstep

theorem execWsRmw (E : Exec) (k : Nat) (s : Estep) (aq rl : Bool) (base : Int) (ts : List Nat)
    (rvs wvs : List (BitVec 8)) (kc : WmClass) :
    execWf E → E.exTr[k]? = some s → s.esLb = LRmw aq rl base ts rvs wvs kc →
    ews E (k + 1) s.esAg =
      storePostRun (loadPostRun (ews E k s.esAg) aq base ts) rl base wvs.length
        (evTs E (ev_at k)) := by
  intro hwf hs hl
  have hstep := execStepAt E k s hwf hs
  rw [hl] at hstep
  exact mstepWsRmw _ _ _ _ _ _ _ _ _ _ hstep

/-- A byte inside a message's range is byte `j` of it. -/
theorem msgByteIndex (base : Int) (vs : List (BitVec 8)) (tid : Option Nat) (k : WmClass)
    (a : Int) :
    (msgByte ⟨base, vs, tid, k⟩ a).isSome → ∃ j : Nat, j < vs.length ∧ a = accAddr base j := by
  intro h
  obtain ⟨j, hj, ha⟩ := msgByteRange _ a h
  exact ⟨j, hj, ha⟩

/-- Values are stable along the run. -/
theorem logByteAt (E : Exec) (k k' t : Nat) (a : Int) :
    execWf E → k ≤ k' → k' ≤ E.exTr.length → t ≤ (elog E k).length →
    logByte (eimg E k') (elog E k') t a = logByte (eimg E k) (elog E k) t a := by
  intro hwf hle hk' ht
  rw [execImgConst E k' hwf hk', execImgConst E k hwf (by omega)]
  obtain ⟨l, hl⟩ := execLogPrefix E k k' hwf hle hk'
  rw [← hl, logByteApp _ _ _ _ _ ht]

/-! ## `touches`: the timestamp a step uses at a byte -/

def touches (E : Exec) (k : Nat) (a : Int) (t : Nat) : Prop :=
  (∃ v, readsAt E k a t v) ∨
  (isW E (ev_at k) ∧ evWrites E (ev_at k) a ∧ t = evTs E (ev_at k))

/-- THE COHERENCE INVARIANT: a step's own timestamps are below its agent's
coherence floor for that byte immediately afterwards. -/
theorem touchesCoh (E : Exec) (k : Nat) (s : Estep) (a : Int) (t : Nat) :
    execWf E → E.exTr[k]? = some s → touches E k a t → t ≤ coh (ews E (k + 1) s.esAg) a := by
  intro hwf hs ht
  cases hl : s.esLb with
  | LLoad aq base ts vs =>
    rcases ht with ⟨v, hr⟩ | ⟨⟨s', hs', hw⟩, _, _⟩
    · obtain ⟨s', base', ts', vs', j, hs', hrd, hj, _, rfl⟩ := hr
      rw [hs] at hs'; cases hs'
      rw [hl] at hrd; simp only [lbRd, Option.some.injEq, Prod.mk.injEq] at hrd
      obtain ⟨rfl, rfl, rfl⟩ := hrd
      rw [execWsLoad E k s aq base ts vs hwf hs hl]
      exact loadPostRunCoh _ _ _ _ _ _ hj
    · rw [hs] at hs'; cases hs'; rw [hl] at hw; simp [lbIsW] at hw
  | LStore rl base vs kc =>
    rcases ht with ⟨v, hr⟩ | ⟨_, hwr, rfl⟩
    · obtain ⟨s', _, _, _, _, hs', hrd, _⟩ := hr
      rw [hs] at hs'; cases hs'; rw [hl] at hrd; simp [lbRd] at hrd
    · rw [evWritesAt E k s base vs a hwf hs (by rw [hl]; rfl)] at hwr
      obtain ⟨j, hj, rfl⟩ := msgByteIndex base vs _ _ a hwr
      rw [execWsStore E k s rl base vs kc hwf hs hl]
      exact storePostRunCoh _ _ _ _ _ _ hj
  | LFence pr pw sr sw =>
    rcases ht with ⟨v, hr⟩ | ⟨⟨s', hs', hw⟩, _, _⟩
    · obtain ⟨s', _, _, _, _, hs', hrd, _⟩ := hr
      rw [hs] at hs'; cases hs'; rw [hl] at hrd; simp [lbRd] at hrd
    · rw [hs] at hs'; cases hs'; rw [hl] at hw; simp [lbIsW] at hw
  | LRmw aq rl base ts rvs wvs kc =>
    rw [execWsRmw E k s aq rl base ts rvs wvs kc hwf hs hl]
    rcases ht with ⟨v, hr⟩ | ⟨_, hwr, rfl⟩
    · obtain ⟨s', base', ts', vs', j, hs', hrd, hj, _, rfl⟩ := hr
      rw [hs] at hs'; cases hs'
      rw [hl] at hrd; simp only [lbRd, Option.some.injEq, Prod.mk.injEq] at hrd
      obtain ⟨rfl, rfl, rfl⟩ := hrd
      exact Nat.le_trans (loadPostRunCoh _ _ _ _ _ _ hj)
        (wsLeCoh _ _ _ (storePostRunLe _ _ _ _ _))
    · rw [evWritesAt E k s base wvs a hwf hs (by rw [hl]; rfl)] at hwr
      obtain ⟨j, hj, rfl⟩ := msgByteIndex base wvs _ _ a hwr
      exact storePostRunCoh _ _ _ _ _ _ hj

theorem touchesCohLater (E : Exec) (k k' : Nat) (s : Estep) (a : Int) (t : Nat) :
    execWf E → E.exTr[k]? = some s → touches E k a t → k + 1 ≤ k' → k' ≤ E.exTr.length →
    t ≤ coh (ews E k' s.esAg) a := by
  intro hwf hs ht hle hk'
  exact Nat.le_trans (touchesCoh E k s a t hwf hs ht)
    (wsLeCoh _ _ _ (execWsLe E (k + 1) k' s.esAg hwf hle hk'))

/-- A touched timestamp is a real timestamp of the log at every LATER point,
and it does write the byte there. -/
theorem touchesLog (E : Exec) (k k' : Nat) (a : Int) (t : Nat) :
    execWf E → touches E k a t → k < k' → k' ≤ E.exTr.length →
    t ≤ (elog E k').length ∧ (logByte (eimg E k') (elog E k') t a).isSome := by
  intro hwf ht hlt hk'
  rcases ht with ⟨v, hr⟩ | ⟨hW, hwr, rfl⟩
  · have hle := readsAtTsLe E k a t v hwf hr
    have hlen := execLogLenLe E k k' hwf (by omega) hk'
    refine ⟨by omega, ?_⟩
    rw [logByteAt E k k' t a hwf (by omega) hk' hle]
    obtain ⟨s, _, hv, _⟩ := readsAtByteRd E k a t v hwf hr
    rw [hv]; rfl
  · obtain ⟨s, hs, hw⟩ := hW
    have hnext := evTsNext E k s hwf hs hw
    have hlen := execLogLenLe E (k + 1) k' hwf (by omega) hk'
    have ht : evTs E (ev_at k) ≤ (elog E k').length := by omega
    refine ⟨ht, ?_⟩
    rw [← logByteAt E k' E.exTr.length (evTs E (ev_at k)) a hwf hk' (Nat.le_refl _) ht]
    exact hwr

/-- THE PER-BYTE MONOTONICITY OF PROGRAM ORDER. -/
theorem touchesMono (E : Exec) (k1 k2 : Nat) (s1 s2 : Estep) (a : Int) (t1 t2 : Nat) :
    execWf E → k1 < k2 → E.exTr[k1]? = some s1 → E.exTr[k2]? = some s2 → s1.esAg = s2.esAg →
    touches E k1 a t1 → touches E k2 a t2 → t1 ≤ t2 := by
  intro hwf hlt hs1 hs2 hag ht1 ht2
  have hk2 := lookup_lt_Some hs2
  obtain ⟨ht1len, ht1some⟩ := touchesLog E k1 k2 a t1 hwf ht1 hlt (by omega)
  rcases ht2 with ⟨v2, hr2⟩ | ⟨_, _, rfl⟩
  · obtain ⟨s, hs, _, hread⟩ := readsAtByteRd E k2 a t2 v2 hwf hr2
    rw [hs] at hs2; cases hs2
    by_cases hle : t1 ≤ t2
    · exact hle
    · exfalso
      apply hread.2
      apply (writesInLogByte (eimg E k2) _ _ _ _).2
      have hcoh := touchesCohLater E k1 k2 s1 a t1 hwf hs1 ht1 (by omega) (by omega)
      rw [hag] at hcoh
      exact ⟨t1, by omega, by omega, ht1some⟩
  · rw [evTsAt]; omega

/-- An RMW's read half is the globally latest write to that byte at its step. -/
theorem lbRwRmw (l : Lbl) :
    lbIsW l = true → lbIsR l = true → ∃ aq rl base ts rvs wvs k, l = LRmw aq rl base ts rvs wvs k := by
  cases l with
  | LLoad => intro h; simp [lbIsW] at h
  | LStore => intro _ h; simp [lbIsR] at h
  | LFence => intro h; simp [lbIsW] at h
  | LRmw aq rl base ts rvs wvs k => intro _ _; exact ⟨aq, rl, base, ts, rvs, wvs, k, rfl⟩

theorem rmwReadLatest (E : Exec) (kr : Nat) (a : Int) (t : Nat) (v : BitVec 8) :
    execWf E → readsAt E kr a t v → isW E (ev_at kr) → latest (eimg E kr) (elog E kr) a t := by
  rintro hwf ⟨s, base, ts, vs, j, hs, hrd, hj, _, rfl⟩ ⟨s', hs', hw⟩
  rw [hs] at hs'; cases hs'
  obtain ⟨aq, rl, base', ts', rvs', wvs', kc, hl⟩ := lbRwRmw s.esLb hw (lbRdIsR _ _ hrd)
  have hlat := execRmwLatest E kr s aq rl base' ts' rvs' wvs' kc hwf hs hl
  rw [hl] at hrd; simp only [lbRd, Option.some.injEq, Prod.mk.injEq] at hrd
  obtain ⟨rfl, rfl, rfl⟩ := hrd
  exact hlat j t hj

/-! ## The per-byte timestamp of an event: the coherence measure -/

def isWb (E : Exec) (e : Ev) : Bool :=
  match e with
  | ev_init => true
  | ev_at k =>
    match E.exTr[k]? with
    | some s => lbIsW s.esLb
    | none => false

def writesb (E : Exec) (a : Int) (e : Ev) : Bool :=
  isWb E e &&
  match logByte (exImg E) (exLog E) (evTs E e) a with
  | some _ => true
  | none => false

def lbRdTs (l : Lbl) (a : Int) : Option Nat :=
  match lbRd l with
  | some (base, ts, _) => if base ≤ a then ts[(a - base).toNat]? else none
  | none => none

/-- `ets E a e` — the timestamp event `e` occupies at byte `a`. -/
def ets (E : Exec) (a : Int) (e : Ev) : Nat :=
  if writesb E a e then evTs E e
  else
    match e with
    | ev_init => 0
    | ev_at k =>
      match E.exTr[k]? with
      | some s => (lbRdTs s.esLb a).getD 0
      | none => 0

theorem writesbSpec (E : Exec) (a : Int) (e : Ev) : writesb E a e = true ↔ wrB E a e := by
  unfold writesb wrB evWrites
  rw [Bool.and_eq_true]
  constructor
  · rintro ⟨hW, hlog⟩
    refine ⟨?_, ?_⟩
    · cases e with
      | ev_init => trivial
      | ev_at k =>
        simp only [isWb] at hW
        cases hs : E.exTr[k]? with
        | none => rw [hs] at hW; simp at hW
        | some s => rw [hs] at hW; exact ⟨s, hs, hW⟩
    · revert hlog; cases logByte (exImg E) (exLog E) (evTs E e) a <;> simp
  · rintro ⟨hW, hv⟩
    refine ⟨?_, ?_⟩
    · cases e with
      | ev_init => rfl
      | ev_at k =>
        obtain ⟨s, hs, hw⟩ := hW
        simp only [isWb, hs]; exact hw
    · revert hv; cases logByte (exImg E) (exLog E) (evTs E e) a <;> simp

theorem writesbFalse (E : Exec) (a : Int) (e : Ev) : ¬ wrB E a e → writesb E a e = false := by
  intro hn
  cases hb : writesb E a e
  · rfl
  · exact absurd ((writesbSpec E a e).1 hb) hn

theorem etsWr (E : Exec) (a : Int) (e : Ev) : wrB E a e → ets E a e = evTs E e := by
  intro h; unfold ets; rw [(writesbSpec E a e).2 h]; rfl

theorem readsAtLbRdTs (E : Exec) (k : Nat) (s : Estep) (a : Int) (t : Nat) (v : BitVec 8) :
    E.exTr[k]? = some s → readsAt E k a t v → lbRdTs s.esLb a = some t := by
  rintro hs ⟨s', base, ts, vs, j, hs', hrd, hj, _, rfl⟩
  rw [hs] at hs'; cases hs'
  unfold lbRdTs
  rw [hrd]
  have h1 : base ≤ accAddr base j := by unfold accAddr; omega
  have h2 : (accAddr base j - base).toNat = j := by unfold accAddr; omega
  simp only [h1, ↓reduceIte, h2]
  exact hj

theorem etsRd (E : Exec) (a : Int) (k t : Nat) (v : BitVec 8) :
    ¬ wrB E a (ev_at k) → readsAt E k a t v → ets E a (ev_at k) = t := by
  intro hn hr
  unfold ets
  rw [writesbFalse E a _ hn]
  have hr' := hr
  obtain ⟨s, _, _, _, _, hs, _⟩ := hr'
  simp only [Bool.false_eq_true, ↓reduceIte, hs]
  rw [readsAtLbRdTs E k s a t v hs hr]; rfl

/-- Whatever `ets` picks, the step really does touch the byte at it. -/
theorem accTouches (E : Exec) (a : Int) (k : Nat) :
    accB E a (ev_at k) → touches E k a (ets E a (ev_at k)) := by
  intro hacc
  cases hb : writesb E a (ev_at k)
  · have hn : ¬ wrB E a (ev_at k) := fun hw => by rw [(writesbSpec E a _).2 hw] at hb; cases hb
    rcases hacc with hw | ⟨k', t, v, hk, hr⟩
    · exact absurd hw hn
    · cases hk
      left; exact ⟨v, by rw [etsRd E a k t v hn hr]; exact hr⟩
  · have hw := (writesbSpec E a _).1 hb
    right; rw [etsWr E a _ hw]; exact ⟨hw.1, hw.2, rfl⟩

/-! ## Per-byte coherence (SC-per-location) -/

def cohRel (E : Exec) (a : Int) : Ev → Ev → Prop := fun e1 e2 =>
  poLocB E a e1 e2 ∨ rfB E a e1 e2 ∨ coB E a e1 e2 ∨ frB E a e1 e2

theorem cohRelLexlt (E : Exec) (a : Int) (e1 e2 : Ev) :
    execWf E → cohRel E a e1 e2 → lexlt (ets E a e1, evIx e1) (ets E a e2, evIx e2) := by
  intro hwf h
  rcases h with hpl | hrf | hco | hfr
  · -- po-loc: non-decreasing timestamp, increasing position
    obtain ⟨⟨k1, k2, s1, s2, rfl, rfl, hlt, hs1, hs2, hag⟩, hacc1, hacc2⟩ := hpl
    have hle := touchesMono E k1 k2 s1 s2 a _ _ hwf hlt hs1 hs2 hag
      (accTouches E a k1 hacc1) (accTouches E a k2 hacc2)
    unfold lexlt; simp only [evIx]; omega
  · -- rf
    obtain ⟨hw, k, t, v, rfl, hr, hts⟩ := hrf
    rw [etsWr E a e1 hw, hts]
    cases hb : writesb E a (ev_at k)
    · have hn : ¬ wrB E a (ev_at k) := fun hx => by rw [(writesbSpec E a _).2 hx] at hb; cases hb
      rw [etsRd E a k t v hn hr]
      right; refine ⟨rfl, ?_⟩
      exact rfIx E e1 (ev_at k) hwf ⟨a, hw, k, t, v, rfl, hr, hts⟩
    · have hw2 := (writesbSpec E a _).1 hb
      rw [etsWr E a _ hw2, evTsAt]
      left
      have := readsAtTsLe E k a t v hwf hr
      show t < _; omega
  · -- co
    obtain ⟨hw1, hw2, hlt⟩ := hco
    rw [etsWr E a e1 hw1, etsWr E a e2 hw2]; left; exact hlt
  · -- fr
    obtain ⟨⟨w0, hrf, hco⟩, hne⟩ := hfr
    obtain ⟨hw0, hw2, hlt⟩ := hco
    rw [etsWr E a e2 hw2]
    obtain ⟨_, kr, t0, v0, rfl, hr, hts0⟩ := hrf
    cases hb : writesb E a (ev_at kr)
    · have hn : ¬ wrB E a (ev_at kr) := fun hx => by
        rw [(writesbSpec E a _).2 hx] at hb; cases hb
      rw [etsRd E a kr t0 v0 hn hr]; left; show t0 < _; omega
    · have hwr := (writesbSpec E a _).1 hb
      rw [etsWr E a _ hwr]; left
      show evTs E (ev_at kr) < evTs E e2
      by_cases hgt : evTs E e2 < evTs E (ev_at kr)
      · -- the RMW's read half was globally latest
        exfalso
        have hlat := (rmwReadLatest E kr a t0 v0 hwf hr hwr.1).2
        have hkr := readsAtLt E kr a t0 v0 hr
        apply hlat
        apply (writesInLogByte (eimg E kr) _ _ _ _).2
        refine ⟨evTs E e2, by omega, by rw [evTsAt] at hgt; omega, ?_⟩
        rw [← logByteFinal E kr (evTs E e2) a hwf (by omega) (by rw [evTsAt] at hgt; omega)]
        exact hw2.2
      · by_cases heq : evTs E e2 = evTs E (ev_at kr)
        · exact absurd (evTsInj E e2 (ev_at kr) hwf hw2.1 hwr.1 heq).symm hne
        · omega

/-! ## The preserved-program-order fragment the machine keeps

RVWMO's ppo rules, mapped onto this model: rules 1–3 → `poLocB` via
`axCoherence`; rule 4 → `fenceBetween`; rule 5 → `acqPo`; rule 6 NOT ENFORCED
(design Decision 2); rules 7, 8 vacuous here (rule 7 is slice 2's arm); rules
9–13 OUT OF SCOPE (Decision 3). -/

def fenceBetween (E : Exec) (k1 k2 : Nat) (pr pw sr sw : Bool) : Prop :=
  ∃ kf sf s1 s2, k1 < kf ∧ kf < k2 ∧
    E.exTr[k1]? = some s1 ∧ E.exTr[kf]? = some sf ∧ E.exTr[k2]? = some s2 ∧
    s1.esAg = sf.esAg ∧ sf.esAg = s2.esAg ∧ sf.esLb = LFence pr pw sr sw

def acqPo (E : Exec) (e1 e2 : Ev) : Prop :=
  ∃ k1 k2 s1 s2, e1 = ev_at k1 ∧ e2 = ev_at k2 ∧ k1 < k2 ∧
    E.exTr[k1]? = some s1 ∧ E.exTr[k2]? = some s2 ∧ s1.esAg = s2.esAg ∧
    lbIsR s1.esLb = true ∧ lbAq s1.esLb = true

/-- Ordering edges INTO A READ, by which predecessor bit justifies them. -/
def ordPw (E : Exec) (e1 e2 : Ev) : Prop :=
  ∃ k1 k2 pr sw, e1 = ev_at k1 ∧ e2 = ev_at k2 ∧ fenceBetween E k1 k2 pr true true sw

def ordPr (E : Exec) (e1 e2 : Ev) : Prop :=
  (∃ k1 k2 pw sw, e1 = ev_at k1 ∧ e2 = ev_at k2 ∧ fenceBetween E k1 k2 true pw true sw)
  ∨ acqPo E e1 e2

/-- PUBLICATIONS: a write publishes its own timestamp; an ACQUIRE read, or a
plain read whose rf edge is EXTERNAL, publishes the timestamp it read. -/
def pubW (E : Exec) (e : Ev) (t : Nat) : Prop :=
  isW E e ∧ (∃ k, e = ev_at k) ∧ t = evTs E e

def extW (E : Exec) (w : Ev) (i : Nat) : Prop :=
  match w with
  | ev_init => True
  | ev_at k => ∃ s, E.exTr[k]? = some s ∧ s.esAg ≠ i

def pubR (E : Exec) (e : Ev) (t : Nat) : Prop :=
  ∃ k s a v, e = ev_at k ∧ E.exTr[k]? = some s ∧ readsAt E k a t v ∧
    (lbAq s.esLb = true ∨ ∃ w, rfB E a w (ev_at k) ∧ extW E w s.esAg)

/-! ## The operational content: publications reach the reader's pre-view -/

theorem loadPostRunVrOldAq (ws : Wstate) (base : Int) (ts : List Nat) (j t : Nat) :
    ts[j]? = some t → t ≤ (loadPostRun ws true base ts).wVrOld := by
  intro ht
  exact loadPostRunVrOld' ws true base ts j t ht (fwdViewAq _ _ _)

/-- A write's own timestamp is under its agent's `wVwOld` straight after. -/
theorem pubWVwOld (E : Exec) (k : Nat) (s : Estep) :
    execWf E → E.exTr[k]? = some s → lbIsW s.esLb = true →
    evTs E (ev_at k) ≤ (ews E (k + 1) s.esAg).wVwOld := by
  intro hwf hs hw
  have hstep := execStepAt E k s hwf hs
  obtain ⟨base, vs, hwr, hne, _⟩ := mstepLogW _ _ _ _ hstep hw
  cases hl : s.esLb with
  | LLoad => rw [hl] at hw; simp [lbIsW] at hw
  | LStore rl b0 v0 kc =>
    rw [execWsStore E k s rl b0 v0 kc hwf hs hl]
    apply storePostRunVwOld
    rw [hl] at hwr; simp only [lbWr, Option.some.injEq, Prod.mk.injEq] at hwr
    obtain ⟨-, hv⟩ := hwr
    have hne0 : v0 ≠ [] := by rw [hv]; exact hne
    cases v0 with
    | nil => exact absurd rfl hne0
    | cons _ _ => simp
  | LFence => rw [hl] at hw; simp [lbIsW] at hw
  | LRmw aq0 rl b0 t0 rv0 wv0 kc =>
    rw [execWsRmw E k s aq0 rl b0 t0 rv0 wv0 kc hwf hs hl]
    apply storePostRunVwOld
    rw [hl] at hwr; simp only [lbWr, Option.some.injEq, Prod.mk.injEq] at hwr
    obtain ⟨-, hv⟩ := hwr
    have hne0 : wv0 ≠ [] := by rw [hv]; exact hne
    cases wv0 with
    | nil => exact absurd rfl hne0
    | cons _ _ => simp

/-! ### The forward-bank invariant: a bank entry is one of THIS agent's writes -/

def fwdOk (E : Exec) (k : Nat) (i : Nat) : Prop :=
  ∀ a tf vf, get? (ews E k i).wFwd a = some (tf, vf) →
    ∃ k' s', k' < k ∧ E.exTr[k']? = some s' ∧ s'.esAg = i ∧
      lbIsW s'.esLb = true ∧ evTs E (ev_at k') = tf

theorem execFwdOk (E : Exec) (k : Nat) (i : Nat) :
    execWf E → k ≤ E.exTr.length → fwdOk E k i := by
  intro hwf
  induction k with
  | zero =>
    intro _ a tf vf hlk
    rw [execWsInit E i hwf] at hlk
    simp [wsInit, lookupEmpty] at hlk
  | succ k ih =>
    intro hk a tf vf hlk
    obtain ⟨s, hs⟩ := someOfIsSome (execTrLookup E k (by omega))
    have lift : (∃ k' s', k' < k ∧ E.exTr[k']? = some s' ∧ s'.esAg = i ∧
        lbIsW s'.esLb = true ∧ evTs E (ev_at k') = tf) →
        ∃ k' s', k' < k + 1 ∧ E.exTr[k']? = some s' ∧ s'.esAg = i ∧
        lbIsW s'.esLb = true ∧ evTs E (ev_at k') = tf := by
      rintro ⟨k', s', h1, h2, h3, h4, h5⟩; exact ⟨k', s', by omega, h2, h3, h4, h5⟩
    by_cases hag : s.esAg = i
    · subst hag
      cases hl : s.esLb with
      | LLoad aq0 b0 t0 v0 =>
        rw [execWsLoad E k s aq0 b0 t0 v0 hwf hs hl, loadPostRunFwd] at hlk
        exact lift (ih (by omega) a tf vf hlk)
      | LStore rl b0 v0 kc =>
        rw [execWsStore E k s rl b0 v0 kc hwf hs hl] at hlk
        rcases storePostRunFwdInv _ _ _ _ _ a tf vf hlk with rfl | hlk
        · exact ⟨k, s, by omega, hs, rfl, by rw [hl]; rfl, rfl⟩
        · exact lift (ih (by omega) a tf vf hlk)
      | LFence p1 p2 p3 p4 =>
        rw [execWsFence E k s p1 p2 p3 p4 hwf hs hl, fencePostFwd] at hlk
        exact lift (ih (by omega) a tf vf hlk)
      | LRmw aq0 rl b0 t0 rv0 wv0 kc =>
        rw [execWsRmw E k s aq0 rl b0 t0 rv0 wv0 kc hwf hs hl] at hlk
        rcases storePostRunFwdInv _ _ _ _ _ a tf vf hlk with rfl | hlk
        · exact ⟨k, s, by omega, hs, rfl, by rw [hl]; rfl, rfl⟩
        · rw [loadPostRunFwd] at hlk
          exact lift (ih (by omega) a tf vf hlk)
    · have hstep := execStepAt E k s hwf hs
      have hws : ews E (k + 1) i = ews E k i := mstepWsNe _ _ _ _ i hstep (Ne.symm hag)
      rw [hws] at hlk
      exact lift (ih (by omega) a tf vf hlk)

/-- An acquire read, or a plain read whose rf edge is EXTERNAL, is not
forwarded. -/
theorem pubRFwdView (E : Exec) (k : Nat) (s : Estep) (a : Int) (t : Nat) (v : BitVec 8) :
    execWf E → E.exTr[k]? = some s → readsAt E k a t v →
    (lbAq s.esLb = true ∨ ∃ w, rfB E a w (ev_at k) ∧ extW E w s.esAg) →
    fwdView (ews E k s.esAg) (lbAq s.esLb) a t = t := by
  intro hwf hs hr hside
  cases haq : lbAq s.esLb
  · rcases hside with h | ⟨w, hrf, hext⟩
    · rw [haq] at h; cases h
    · cases hf : get? (ews E k s.esAg).wFwd a with
      | none => exact fwdViewMiss _ _ _ _ hf
      | some p =>
        obtain ⟨tf, vf⟩ := p
        simp only [fwdView, hf, Bool.false_eq_true, ↓reduceIte]
        by_cases ht : t = tf
        · exfalso
          subst ht
          have hk := readsAtLt E k a t v hr
          obtain ⟨k', s', hlt, hs', hag', hw', hts'⟩ :=
            execFwdOk E k s.esAg hwf (by omega) a t vf hf
          obtain ⟨hwb, k'', t'', v'', hk'', hr'', hts''⟩ := hrf
          cases hk''
          obtain ⟨rfl, _⟩ := readsAtDet E k a t v t'' v'' hr hr''
          have : w = ev_at k' :=
            evTsInj E w (ev_at k') hwf hwb.1 ⟨s', hs', hw'⟩ (by rw [hts'', hts'])
          subst this
          obtain ⟨s'', hs'', hne⟩ := hext
          rw [hs'] at hs''; cases hs''
          exact hne hag'
        · simp [ht]
  · exact fwdViewAq _ _ _

/-- ... hence its timestamp lands under `wVrOld`. -/
theorem pubRVrOld (E : Exec) (k : Nat) (s : Estep) (t : Nat) :
    execWf E → E.exTr[k]? = some s → pubR E (ev_at k) t →
    t ≤ (ews E (k + 1) s.esAg).wVrOld := by
  rintro hwf hs ⟨k0, s0, a, v, hk0, hs0, hr, hside⟩
  cases hk0
  rw [hs] at hs0; cases hs0
  have hfv := pubRFwdView E k s a t v hwf hs hr hside
  obtain ⟨s', base, ts, vs, j, hs', hrd, hj, _, ha⟩ := hr
  rw [hs] at hs'; cases hs'
  rw [ha] at hfv
  obtain ⟨aq, haq', hl | ⟨rl, wvs, kc, hl⟩⟩ := lbRdCases _ _ _ _ hrd
  · rw [haq'] at hfv
    rw [execWsLoad E k s aq base ts vs hwf hs hl]
    exact loadPostRunVrOld' _ _ _ _ j t hj hfv
  · rw [haq'] at hfv
    rw [execWsRmw E k s aq rl base ts vs wvs kc hwf hs hl]
    exact Nat.le_trans (loadPostRunVrOld' (ews E k s.esAg) aq base ts j t hj hfv)
      (wsLeVrOld _ _ (storePostRunLe _ _ _ _ _))

theorem pubRVrNewAq (E : Exec) (k : Nat) (s : Estep) (t : Nat) :
    execWf E → E.exTr[k]? = some s → pubR E (ev_at k) t → lbAq s.esLb = true →
    t ≤ (ews E (k + 1) s.esAg).wVrNew := by
  rintro hwf hs ⟨k0, s0, a, v, hk0, hs0, hr, _⟩ haq
  cases hk0
  rw [hs] at hs0; cases hs0
  obtain ⟨s', base, ts, vs, j, hs', hrd, hj, _, _⟩ := hr
  rw [hs] at hs'; cases hs'
  obtain ⟨aq, haq', hl | ⟨rl, wvs, kc, hl⟩⟩ := lbRdCases _ _ _ _ hrd
  · rw [haq] at haq'; subst haq'
    rw [execWsLoad E k s true base ts vs hwf hs hl]
    exact loadPostRunVrNewAq _ _ _ j t hj
  · rw [haq] at haq'; subst haq'
    rw [execWsRmw E k s true rl base ts vs wvs kc hwf hs hl]
    exact Nat.le_trans (loadPostRunVrNewAq (ews E k s.esAg) base ts j t hj)
      (wsLeVrNew _ _ (storePostRunLe _ _ _ _ _))

theorem ordLt (E : Exec) (e1 : Ev) (k2 : Nat) :
    ordPw E e1 (ev_at k2) ∨ ordPr E e1 (ev_at k2) → ∃ k1, e1 = ev_at k1 ∧ k1 < k2 := by
  rintro (⟨k1, k2', _, _, rfl, hk, kf, _, _, _, h1, h2, _⟩ |
          ⟨k1, k2', _, _, rfl, hk, kf, _, _, _, h1, h2, _⟩ |
          ⟨k1, k2', _, _, rfl, hk, hlt, _⟩) <;>
    (cases hk; exact ⟨k1, rfl, by omega⟩)

theorem pubWLeLog (E : Exec) (k1 k2 t : Nat) :
    execWf E → pubW E (ev_at k1) t → k1 < k2 → k2 ≤ E.exTr.length → t ≤ (elog E k2).length := by
  rintro hwf ⟨⟨s, hs, hw⟩, _, rfl⟩ hlt hk2
  rw [← evTsNext E k1 s hwf hs hw]
  exact execLogLenLe E (k1 + 1) k2 hwf (by omega) hk2

theorem pubRLeLog (E : Exec) (k1 k2 t : Nat) :
    execWf E → pubR E (ev_at k1) t → k1 < k2 → k2 ≤ E.exTr.length → t ≤ (elog E k2).length := by
  rintro hwf ⟨k, s, a, v, hk, _, hr, _⟩ hlt hk2
  cases hk
  exact Nat.le_trans (readsAtTsLe E k1 a t v hwf hr) (execLogLenLe E k1 k2 hwf (by omega) hk2)

/-- THE FENCE/ACQUIRE LEMMA: an ordering edge delivers the source's published
timestamp into the target read's PRE-VIEW. -/
theorem ordVrNew (E : Exec) (e1 : Ev) (t k2 : Nat) (s2 : Estep) :
    execWf E → E.exTr[k2]? = some s2 →
    ((ordPw E e1 (ev_at k2) ∧ pubW E e1 t) ∨ (ordPr E e1 (ev_at k2) ∧ pubR E e1 t)) →
    t ≤ (ews E k2 s2.esAg).wVrNew := by
  intro hwf hs2 hcase
  have hk2 := lookup_lt_Some hs2
  rcases hcase with ⟨hord, hpub⟩ | ⟨hord | hord, hpub⟩
  · -- pred-W fence, write publication
    obtain ⟨k1, k2', pr, sw, rfl, hk, kf, sf, s1, s2'', hlt1, hlt2, hs1, hsf, hs2'', hag1, hag2,
      hlf⟩ := hord
    cases hk
    rw [hs2] at hs2''; cases hs2''
    obtain ⟨⟨s1', hs1', hw1⟩, _, rfl⟩ := hpub
    rw [hs1] at hs1'; cases hs1'
    have hkf : evTs E (ev_at k1) ≤ (ews E kf sf.esAg).wVwOld := by
      rw [← hag1]
      exact Nat.le_trans (pubWVwOld E k1 s1 hwf hs1 hw1)
        (wsLeVwOld _ _ (execWsLe E (k1 + 1) kf s1.esAg hwf (by omega) (by omega)))
    rw [← hag2]
    refine Nat.le_trans ?_ (wsLeVrNew _ _ (execWsLe E (kf + 1) k2 sf.esAg hwf (by omega) (by omega)))
    rw [execWsFence E kf sf pr true true sw hwf hsf hlf]
    exact Nat.le_trans hkf (fencePostVrNewW _ _ _)
  · -- pred-R fence, acquire-read publication
    obtain ⟨k1, k2', pw, sw, rfl, hk, kf, sf, s1, s2'', hlt1, hlt2, hs1, hsf, hs2'', hag1, hag2,
      hlf⟩ := hord
    cases hk
    rw [hs2] at hs2''; cases hs2''
    have hkf : t ≤ (ews E kf sf.esAg).wVrOld := by
      rw [← hag1]
      exact Nat.le_trans (pubRVrOld E k1 s1 t hwf hs1 hpub)
        (wsLeVrOld _ _ (execWsLe E (k1 + 1) kf s1.esAg hwf (by omega) (by omega)))
    rw [← hag2]
    refine Nat.le_trans ?_ (wsLeVrNew _ _ (execWsLe E (kf + 1) k2 sf.esAg hwf (by omega) (by omega)))
    rw [execWsFence E kf sf true pw true sw hwf hsf hlf]
    exact Nat.le_trans hkf (fencePostVrNewR _ _ _)
  · -- acquire read, no fence needed
    obtain ⟨k1, k2', s1, s2'', rfl, hk, hlt, hs1, hs2'', hag, _, haq1⟩ := hord
    cases hk
    rw [hs2] at hs2''; cases hs2''
    rw [← hag]
    exact Nat.le_trans (pubRVrNewAq E k1 s1 t hwf hs1 hpub haq1)
      (wsLeVrNew _ _ (execWsLe E (k1 + 1) k2 s1.esAg hwf (by omega) (by omega)))

/-- ... and a timestamp in the reader's pre-view cannot be shadowed by a write
the reader then fails to see. -/
theorem noStale (E : Exec) (k2 : Nat) (s2 : Estep) (a : Int) (t t0 : Nat) (v0 : BitVec 8)
    (w : Ev) :
    execWf E → E.exTr[k2]? = some s2 → readsAt E k2 a t0 v0 →
    t ≤ (ews E k2 s2.esAg).wVrNew → t ≤ (elog E k2).length →
    wrB E a w → t0 < evTs E w → t < evTs E w := by
  intro hwf hs2 hr hv hlen hw hgt
  have hk2 := lookup_lt_Some hs2
  by_cases hlt : t < evTs E w
  · exact hlt
  · exfalso
    obtain ⟨s, hs, _, _, hnw⟩ := readsAtByteRd E k2 a t0 v0 hwf hr
    rw [hs] at hs2; cases hs2
    have hvp := loadVpreVrNew (ews E k2 s2.esAg) (lbAq s2.esLb)
    apply hnw
    apply (writesInLogByte (eimg E k2) _ _ _ _).2
    refine ⟨evTs E w, hgt, by omega, ?_⟩
    rw [← logByteFinal E k2 (evTs E w) a hwf (by omega) (by omega)]
    exact hw.2

/-! # THE AXIOMS -/

/-- rf is total, functional and value-correct, per byte. -/
def axRfTotal (E : Exec) : Prop :=
  ∀ k a t v, readsAt E k a t v → ∃ w, rfB E a w (ev_at k)

def axRfFunctional (E : Exec) : Prop :=
  ∀ a w1 w2 r, rfB E a w1 r → rfB E a w2 r → w1 = w2

def axRfValue (E : Exec) : Prop :=
  ∀ k a w t v, readsAt E k a t v → rfB E a w (ev_at k) →
    logByte (exImg E) (exLog E) (evTs E w) a = some v

/-- RVWMO coherence, per byte: SC-per-location. -/
def axCoherence (E : Exec) : Prop := ∀ a e, ¬ tc (cohRel E a) e e

/-- RVWMO's ATOMICITY axiom. -/
def axAtomicity (E : Exec) : Prop :=
  ∀ kr a w0 w, isW E (ev_at kr) → rfB E a w0 (ev_at kr) → wrB E a w →
    evTs E w0 < evTs E w → ¬ evTs E w < evTs E (ev_at kr)

/-- THE PPO FRAGMENT THE MACHINE KEEPS, in "no stale read across an ordering
edge" form. -/
def axOrd (E : Exec) : Prop :=
  ∀ e1 k2 s2 a w t,
    E.exTr[k2]? = some s2 →
    ((ordPw E e1 (ev_at k2) ∧ pubW E e1 t) ∨ (ordPr E e1 (ev_at k2) ∧ pubR E e1 t)) →
    frB E a (ev_at k2) w →
    t < evTs E w

/-- THE TWO PROMISE-FREE STRENGTHENINGS (design doc, Decision 1). -/
def axNoThinAir (E : Exec) : Prop := ∀ e, ¬ tc (fun x y => po E x y ∨ rf E x y) e e

def axPoWwGmo (E : Exec) : Prop := ∀ e1 e2, po E e1 e2 → isW E e1 → isW E e2 → gmo E e1 e2

/-! # SOUNDNESS: every promise-free execution satisfies the axioms -/

theorem soundRfTotal (E : Exec) : execWf E → axRfTotal E :=
  fun hwf k a t v hr => rfBTotal E k a t v hwf hr

theorem soundRfFunctional (E : Exec) : execWf E → axRfFunctional E :=
  fun hwf a w1 w2 r h1 h2 => rfBFunctional E a w1 w2 r hwf h1 h2

theorem soundRfValue (E : Exec) : execWf E → axRfValue E :=
  fun hwf k a w t v hr hrf => rfBValue E a w k t v hwf hr hrf

/-- ACYCLICITY OF `po ∪ rf` — the promise-free machine's defining property. -/
theorem soundNoThinAir (E : Exec) : execWf E → axNoThinAir E := by
  intro hwf
  apply tcNatLt _ evIx
  rintro x y (hpo | hrf)
  · exact poIx E x y hpo
  · exact rfIx E x y hwf hrf

/-- `(po ∩ W×W) ⊆ gmo`. -/
theorem soundPoWwGmo (E : Exec) : execWf E → axPoWwGmo E := by
  rintro hwf e1 e2 ⟨k1, k2, _, _, rfl, rfl, hlt, _⟩ hW1 hW2
  exact ⟨hW1, hW2, evTsMono E k1 k2 hwf hlt hW1 hW2⟩

theorem soundCoherence (E : Exec) : execWf E → axCoherence E := by
  intro hwf a
  apply tcLexlt _ (fun e => (ets E a e, evIx e))
  intro x y hxy
  exact cohRelLexlt E a x y hwf hxy

theorem soundAtomicity (E : Exec) : execWf E → axAtomicity E := by
  rintro hwf kr a w0 w hW ⟨_, k, t0, v0, hk, hr, hts0⟩ hw hgt hlt
  cases hk
  have hlat := (rmwReadLatest E kr a t0 v0 hwf hr hW).2
  have hkr := readsAtLt E kr a t0 v0 hr
  rw [evTsAt] at hlt
  apply hlat
  apply (writesInLogByte (eimg E kr) _ _ _ _).2
  refine ⟨evTs E w, by omega, by omega, ?_⟩
  rw [← logByteFinal E kr (evTs E w) a hwf (by omega) (by omega)]
  exact hw.2

theorem soundOrd (E : Exec) : execWf E → axOrd E := by
  intro hwf e1 k2 s2 a w t hs2 hcase hfr
  have hk2 := lookup_lt_Some hs2
  obtain ⟨⟨w0, ⟨_, k, t0, v0, hk0, hr, hts0⟩, ⟨_, hw, hgt⟩⟩, _⟩ := hfr
  cases hk0
  obtain ⟨k1, rfl, hlt⟩ := ordLt E e1 k2
    (by rcases hcase with ⟨h, _⟩ | ⟨h, _⟩; exact .inl h; exact .inr h)
  refine noStale E k2 s2 a t t0 v0 w hwf hs2 hr (ordVrNew E _ t k2 s2 hwf hs2 hcase) ?_ hw
    (by omega)
  rcases hcase with ⟨_, hp⟩ | ⟨_, hp⟩
  · exact pubWLeLog E k1 k2 t hwf hp hlt (by omega)
  · exact pubRLeLog E k1 k2 t hwf hp hlt (by omega)

/-- THE SLICE-1 SOUNDNESS THEOREM. -/
def axiomaticOk (E : Exec) : Prop :=
  axRfTotal E ∧ axRfFunctional E ∧ axRfValue E ∧
  axCoherence E ∧ axAtomicity E ∧ axOrd E ∧
  axNoThinAir E ∧ axPoWwGmo E

theorem promiseFreeSound (E : Exec) : execWf E → axiomaticOk E := by
  intro hwf
  exact ⟨soundRfTotal E hwf, soundRfFunctional E hwf, soundRfValue E hwf, soundCoherence E hwf,
    soundAtomicity E hwf, soundOrd E hwf, soundNoThinAir E hwf, soundPoWwGmo E hwf⟩

/-! # Execution constructors (and the non-vacuity guard) -/

theorem execNil (σ0 : Mstate) :
    σ0.msLog = [] → (∀ i, σ0.msWs i = wsInit) → execWf ⟨[σ0], []⟩ := by
  intro hlog hws
  refine ⟨rfl, ?_, ?_⟩
  · intro σ hσ; simp only [List.getElem?_cons_zero, Option.some.injEq] at hσ
    subst hσ; exact ⟨hlog, hws⟩
  · intro k s _ _ hs; simp at hs

theorem execSnoc (E : Exec) (s : Estep) (σ' : Mstate) :
    execWf E → mstep (stt E E.exTr.length) s.esAg s.esLb σ' →
    execWf ⟨E.exSt ++ [σ'], E.exTr ++ [s]⟩ := by
  rintro ⟨hlen, hinit, hstep⟩ hnew
  refine ⟨?_, ?_, ?_⟩
  · simp only [List.length_append, List.length_singleton]; omega
  · intro σ hσ
    rw [lookup_app_l (by omega)] at hσ
    exact hinit σ hσ
  · intro k s0 σ σ'' hs0 hσ hσ''
    by_cases hlt : k < E.exTr.length
    · rw [lookup_app_l hlt] at hs0
      rw [lookup_app_l (by omega)] at hσ
      rw [lookup_app_l (by omega)] at hσ''
      exact hstep k s0 σ σ'' hs0 hσ hσ''
    · have hk : k = E.exTr.length := by
        have := lookup_lt_Some hs0
        simp only [List.length_append, List.length_singleton] at this; omega
      subst hk
      rw [lookup_app_r (Nat.le_refl _), Nat.sub_self] at hs0
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hs0
      subst hs0
      rw [lookup_app_l (by omega)] at hσ
      rw [sttLookup E _ _ hσ] at hnew
      rw [lookup_app_r (by omega)] at hσ''
      have : E.exTr.length + 1 - E.exSt.length = 0 := by omega
      rw [this] at hσ''
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hσ''
      subst hσ''
      exact hnew

/-! ## The machine invariant along a run, and the event pre-view

(Lifted here from `WeakAxiomatic2` by the W4 batch.)

WHAT SLICE 1 DOES NOT DO (the Rocq file's closing comment, kept as prose):
(1) COMPLETENESS — an axiomatically-consistent candidate execution is
realized by the machine (proved in `WeakAxiomatic3`); (2) FULL
`ob`-ACYCLICITY — not provable by the measure arguments above, since `fr`
edges point BACKWARDS in execution order (proved over operations in
`WeakAxiomatic2`, and REFUTED over events there); (3) KNOWN GAPS IN `axOrd`:
an INTERNAL rf edge publishes only the weaker banked view (excluded from
`pubR`), and RVWMO ppo rule 6 is not modelled. -/

/-- The `Forall` shape `loadPostRunBounded` wants, from an `rdOk`. -/
theorem rdOkTsBounded (img : Image) (log : List Wmsg) (ws : Wstate) (aq : Bool) (base : Int)
    (ts : List Nat) (vs : List (BitVec 8)) :
    rdOk img log ws aq base ts vs → ∀ t ∈ ts, t ≤ log.length := by
  rintro ⟨hlen, hall⟩ t ht
  obtain ⟨j, hj⟩ := elem_of_list_lookup_1 ht
  have hjl : j < vs.length := by rw [hlen]; exact lookup_lt_Some hj
  obtain ⟨hb, _⟩ := hall j t vs[j] hj (List.getElem?_eq_getElem hjl)
  exact logByteBounded img log t _ (by rw [hb]; rfl)

/-! # 2. The machine invariant along a run: every view is a real timestamp -/

theorem execWsBounded (E : Exec) (k : Nat) (i : Nat) :
    execWf E → k ≤ E.exTr.length → wsBounded (ews E k i) (elog E k).length := by
  intro hwf
  induction k with
  | zero => intro _; rw [execWsInit E i hwf]; exact wsBoundedInit _
  | succ k ih =>
    intro hk
    obtain ⟨s, hs⟩ := someOfIsSome (execTrLookup E k (by omega))
    have hstep := execStepAt E k s hwf hs
    have hb := ih (by omega)
    have hlen := execLogLenLe E k (k + 1) hwf (by omega) hk
    by_cases hi : i = s.esAg
    · subst hi
      cases hl : s.esLb with
      | LLoad aq base ts vs =>
        rw [execWsLoad E k s aq base ts vs hwf hs hl]
        have hrd := execRdOk E k s base ts vs hwf hs (by rw [hl]; rfl)
        exact wsBoundedMono _ _ _ (loadPostRunBounded _ _ _ _ _ hb (rdOkTsBounded _ _ _ _ _ _ _ hrd))
          hlen
      | LStore rl base vs kc =>
        rw [execWsStore E k s rl base vs kc hwf hs hl]
        have hts : evTs E (ev_at k) = (elog E (k + 1)).length :=
          (evTsNext E k s hwf hs (by rw [hl]; rfl)).symm
        exact storePostRunBounded _ _ _ _ _ (elog E k).length _ hb (Nat.le_of_eq hts) hlen
      | LFence pr pw sr sw =>
        rw [execWsFence E k s pr pw sr sw hwf hs hl]
        exact wsBoundedMono _ _ _ (fencePostBounded _ _ _ _ _ _ hb) hlen
      | LRmw aq rl base ts rvs wvs kc =>
        rw [execWsRmw E k s aq rl base ts rvs wvs kc hwf hs hl]
        have hrd := execRdOk E k s base ts rvs hwf hs (by rw [hl]; rfl)
        have hts : evTs E (ev_at k) = (elog E (k + 1)).length :=
          (evTsNext E k s hwf hs (by rw [hl]; rfl)).symm
        exact storePostRunBounded _ _ _ _ _ (elog E k).length _
          (loadPostRunBounded _ _ _ _ _ hb (rdOkTsBounded _ _ _ _ _ _ _ hrd)) (Nat.le_of_eq hts) hlen
    · have hws : ews E (k + 1) i = ews E k i := mstepWsNe _ _ _ _ i hstep hi
      rw [hws]
      exact wsBoundedMono _ _ _ hb hlen

/-! # 3. `evpre`: the load pre-view an event ran at -/

def evpre (E : Exec) (e : Ev) : Nat :=
  match e with
  | ev_init => 0
  | ev_at k =>
    match E.exTr[k]? with
    | some s => loadVpre (ews E k s.esAg) (lbAq s.esLb)
    | none => 0

theorem evpreAt (E : Exec) (k : Nat) (s : Estep) :
    E.exTr[k]? = some s → evpre E (ev_at k) = loadVpre (ews E k s.esAg) (lbAq s.esLb) := by
  intro h; simp only [evpre, h]

/-- Bounded, like every other view. -/
theorem evpreLeLog (E : Exec) (k : Nat) :
    execWf E → k ≤ E.exTr.length → evpre E (ev_at k) ≤ (elog E k).length := by
  intro hwf hk
  simp only [evpre]
  split
  · exact loadVpreBounded _ _ _ (execWsBounded E k _ hwf hk)
  · exact Nat.zero_le _

/-- A READ's pre-view is under the agent's `wVrNew` IMMEDIATELY AFTER the step. -/
theorem evpreLeVrNewPost (E : Exec) (k : Nat) (s : Estep) (a : Int) (t : Nat) (v : BitVec 8) :
    execWf E → E.exTr[k]? = some s → readsAt E k a t v →
    evpre E (ev_at k) ≤ (ews E (k + 1) s.esAg).wVrNew := by
  intro hwf hs hr
  rw [evpreAt E k s hs]
  obtain ⟨s', base, ts, vs, j, hs', hrd, hj, _, _⟩ := hr
  rw [hs] at hs'; cases hs'
  cases haq : lbAq s.esLb
  · simp only [loadVpre, Bool.false_eq_true, ↓reduceIte, Nat.max_zero]
    exact wsLeVrNew _ _ (execWsLe E k (k + 1) s.esAg hwf (by omega)
      (by have := lookup_lt_Some hs; omega))
  · obtain ⟨aq, haq', hl | ⟨rl, wvs, kc, hl⟩⟩ := lbRdCases _ _ _ _ hrd
    · rw [haq] at haq'; subst haq'
      rw [execWsLoad E k s true base ts vs hwf hs hl]
      exact loadPostRunVrNewAqVpre _ _ _ j _ hj
    · rw [haq] at haq'; subst haq'
      rw [execWsRmw E k s true rl base ts vs wvs kc hwf hs hl]
      exact Nat.le_trans (loadPostRunVrNewAqVpre _ base ts j _ hj)
        (wsLeVrNew _ _ (storePostRunLe _ _ _ _ _))

/-- ... hence the pre-view is monotone along one agent's program order. -/
theorem evpreMono (E : Exec) (k1 k2 : Nat) (s1 s2 : Estep) (a : Int) (t : Nat) (v : BitVec 8) :
    execWf E → k1 < k2 → E.exTr[k1]? = some s1 → E.exTr[k2]? = some s2 → s1.esAg = s2.esAg →
    readsAt E k1 a t v → evpre E (ev_at k1) ≤ evpre E (ev_at k2) := by
  intro hwf hlt hs1 hs2 hag hr
  have hk2 := lookup_lt_Some hs2
  refine Nat.le_trans (evpreLeVrNewPost E k1 s1 a t v hwf hs1 hr) ?_
  rw [evpreAt E k2 s2 hs2, ← hag]
  refine Nat.le_trans (wsLeVrNew _ _ (execWsLe E (k1 + 1) k2 s1.esAg hwf (by omega) (by omega))) ?_
  rw [hag]
  exact loadVpreVrNew _ _

/-- The other half: a publication delivered into the target's `wVrNew` is under
the target's pre-view. -/
theorem vrNewLeEvpre (E : Exec) (k : Nat) (s : Estep) :
    E.exTr[k]? = some s → (ews E k s.esAg).wVrNew ≤ evpre E (ev_at k) := by
  intro hs; rw [evpreAt E k s hs]; exact loadVpreVrNew _ _

end Weak
