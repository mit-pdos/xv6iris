/-
Weak: **allocproc route P, increment P-W1 — `SbCand`, the BUFFERED twin candidate**
(`notes/weak-allocproc-routeP-design.md` §3.1; `notes/weak-allocproc-plan-review-R45.md` §2.3, §5 row
P-W1; rulings [OWN.110] [OWN.111]).  Lean-only, no Rocq twin.  A PRIMED TWIN: the registered machine
(`mstep`, `execWf`) is untouched; nothing registered imports this file.

`SbCand` is the promise-free machine of `Weak/WeakAxiomatic.lean` (`Mstate`: image, log, per-agent views)
plus a per-agent STORE BUFFER (`CandS.sb i`, pending stores oldest first).  A plain store ISSUES into the
buffer (no log append); an ADMIN step `land` (no label) appends a pending store to the log, at the then
top, and performs the store's view updates there.  WHICH pending store may land is the PARAMETER
`SbPol.landOk`; both instances are kept:

* **`SbPol.epoch` — the PRIMARY instance ([OWN.113]: the buffer is per-address + fence-epoch,
  RVWMO's store order; final after the MachCSL spike measures it)** — R45 §2.3 option (β): an entry
  may land when every OLDER entry of the hart is in the same fence epoch and writes no common byte
  (riscv.cat rules 1 and 4, nothing more);
* `SbPol.fifo` — first issued, first landed ([OWN.110]'s original text; the fallback).

Every policy must satisfy the four laws of `SbPol` (in range; the oldest entry may always land; rule 1;
rule 4); `SbPol.leEpoch`: `epoch` is the WEAKEST lawful policy, so it is exactly RVWMO's store side, and
`SbCand.execWfPMono` / `SbCand.execWfPEpoch` carry any run (in particular a FIFO run) to it.

## Spec first (riscv.cat / RVWMO; marks w.r.t. riscv.cat, Sail, Zifencei, PMAs)

| rule | `SbCand` | mark |
|---|---|---|
| load value (visible = gmo-before ∨ po-before, co-max) | a byte covered by an own pending entry FORWARDS from the youngest one (`fwdByte`, mandatory: a pending own store is po-before and lands after everything landed, so it is the co-max visible write); other bytes read the log at the views (`byteRd`, unchanged) | FAITHFUL |
| 1 `[M];po-loc;[W]` | own same-address stores land in order (`SbPol.sameAddr`); an AMO whose footprint hits an own pending entry waits (`amoOk`) | FAITHFUL |
| 2–3 R→R same address | the views, unchanged; a forwarded byte moves no view (`fwdMask` stamps it `0`) | FAITHFUL |
| 4 FENCE | `pw ∧ sr` drains the buffer (`drains`); `pw ∧ sw` opens a new EPOCH (`SbEnt.bump`): an older-epoch entry lands before every younger-epoch store (`SbPol.fenced`) and before every later AMO write (`amoOk`: all pending entries in the current epoch) | FAITHFUL |
| 5 `[AQ];po;[M]` | an `.aq` AMO does NOT drain: its write lands at its step, overtaking pending same-epoch entries to other bytes (the F44-1 freedom, [OWN.110]); later events follow it | FAITHFUL |
| 6–8 `.rl`, RCsc | an `.rl` store / AMO waits for an empty buffer; an `.aq` access waits while an own `.rl` entry is pending (`noRl`) | FAITHFUL (xv6 has no `.rl`: `SBAcq.l1NoRl`, `LockFacts.amoCensus`) |
| 9–13 dependencies | not tracked (as `mstep`, [OWN.109]) | more permissive, unchanged |
| I/O (PMAs) | `LIo` inert, neither buffered nor draining | WEAKER than RVWMO + PMAs on fences with i/o bits (Sail drops them at decode, `notes/sail-gaps.md` SAIL-GAP-1: `fence iorw,iorw` orders no MMIO access here); compensated by the trusted (R1), STRONGER than the spec (QEMU-TCG), kept until the capstone [OWN.142] (F-P1; `notes/rvwmo-spec-audit.md` §4 item 2) |
| `fence.i` / `sfence.vma` | the label `LFence false×4` is SHARED by both (`PfStepTsoView` rows); it does not drain here (riscv.cat has no `fence.i`; `sfence.vma` orders no data) | FAITHFUL w.r.t. riscv.cat; the MachCSL machine drains at `fence.i` today (STRONGER than Zifencei, EX-FENCEI-1; being made non-draining per [OWN.143]) — P-W6 must keep the candidate's fetch-free view or add a fetch marker (open item O-P-W1-a) |

Deviation from the design text (§1 rows 4–5): the design lets an `.aq` AMO overtake the WHOLE FIFO; that
would let it overtake a store issued BEFORE a `fence rw,w` (e.g. a critical-section store before
`release`, then the next `acquire`'s AMO), which rule 4 forbids.  `amoOk` keeps rule 4: the AMO
overtakes only current-epoch entries.  (Finding F-P-W1-1; it costs Litmus 1 nothing: `SbCandLit`.)

## What is defined / proved

* §1 `SbEnt`, `SbPol` (laws), `SbPol.fifo`, `SbPol.epoch`, **`SbPol.leEpoch`**.
* §2 `SbCand.CandS`; the event step **`SbCand.stepE`** (deterministic post-state `SbCand.nextE`); the
  landing **`SbCand.land`** (post-state `SbCand.nextL`); the run **`SbCand.execWfP`** (an `Exec`-shaped,
  event-indexed run whose step is an event followed by any number of landings, `SbCand.stepM`);
  monotonicity in the policy `SbCand.execWfPMono`, `SbCand.execWfPEpoch`.
* §3 **THE EMBEDDING `SbCand.execWfOfOld`**: every registered run (`execWf`) is an `SbCand` run under
  EVERY lawful policy, each store landing right after its issue (`SbCand.toExecLift`: forgetting the
  buffers gives the registered run back).
* §4 the view-boundedness invariant `SbCand.Inv` (every view ≤ the log length) along steps and landings.
* §5 a boolean checker `SbCand.runOkB` for runs whose reads are TOP reads (or forwarded) and whose
  landings take the oldest entry: **`SbCand.runOfB`** turns `runOkB … = true` (a `decide +kernel` goal)
  into an `execWfP` run under every lawful policy.  Used by `Weak/SbCandLit.lean`.
-/
import Weak.WeakAxiomatic2

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Lbl

/-! # 1. Pending entries and the landing policy -/

/-- A PENDING store: the message it appends when it lands, its `.rl` bit, the publication flag it
consumed at issue (`wRelp`, armed by a `pw ∧ sw` fence; the landing publishes with it), and `fs`, the
number of `pw ∧ sw` fences its hart executed since the issue — two entries of a hart are separated by
such a fence iff the older one's `fs` is larger. -/
structure SbEnt where
  msg : Wmsg
  rl : Bool
  relp : Bool
  fs : Nat
  deriving DecidableEq, Inhabited

/-- `e` writes a byte of the `n`-byte footprint at `base`. -/
def SbEnt.hits (e : SbEnt) (base : Int) (n : Nat) : Prop :=
  ∃ j, j < n ∧ (msgByte e.msg (accAddr base j)).isSome

/-- `e` and `e'` write a common byte. -/
def SbEnt.overlaps (e e' : SbEnt) : Prop := e.hits e'.msg.wmPa e'.msg.wmData.length

/-- A `pw ∧ sw` fence passes the entry. -/
def SbEnt.bump (e : SbEnt) : SbEnt := { e with fs := e.fs + 1 }

/-- **THE LANDING POLICY** (a parameter): which pending entry (by index, oldest = 0) of a hart's buffer
may land now.  The laws: only real entries; the oldest may always land (progress, and the embedding);
riscv.cat rule 1 (no overtaking of an own same-byte store) and rule 4 (no overtaking across a
`pw ∧ sw` fence). -/
structure SbPol where
  landOk : List SbEnt → Nat → Prop
  inRange : ∀ es k, landOk es k → k < es.length
  oldest : ∀ e es, landOk (e :: es) 0
  sameAddr : ∀ es k k' e e', landOk es k → k' < k → es[k']? = some e' → es[k]? = some e →
    ¬ SbEnt.overlaps e' e
  fenced : ∀ es k k' e e', landOk es k → k' < k → es[k']? = some e' → es[k]? = some e →
    e'.fs = e.fs

/-- **FIFO**: first issued, first landed. -/
def SbPol.fifo : SbPol where
  landOk es k := k = 0 ∧ k < es.length
  inRange _ _ h := h.2
  oldest _ _ := ⟨rfl, Nat.zero_lt_succ _⟩
  sameAddr _ _ _ _ _ h hk _ _ := absurd hk (by rw [h.1]; exact Nat.not_lt_zero _)
  fenced _ _ _ _ _ h hk _ _ := absurd hk (by rw [h.1]; exact Nat.not_lt_zero _)

/-- The per-address + fence-epoch condition. -/
def SbPol.epochOk (es : List SbEnt) (k : Nat) : Prop :=
  k < es.length ∧ ∀ k' e' e, k' < k → es[k']? = some e' → es[k]? = some e →
    e'.fs = e.fs ∧ ¬ SbEnt.overlaps e' e

/-- **PER-ADDRESS + FENCE EPOCH** (R45 §2.3 (β)): exactly riscv.cat rules 1 and 4. -/
def SbPol.epoch : SbPol where
  landOk := SbPol.epochOk
  inRange _ _ h := h.1
  oldest _ _ := And.intro (Nat.zero_lt_succ _) (fun _ _ _ hk => absurd hk (Nat.not_lt_zero _))
  sameAddr _ _ k' e e' h hk h1 h2 := (h.2 k' e' e hk h1 h2).2
  fenced _ _ k' e e' h hk h1 h2 := (h.2 k' e' e hk h1 h2).1

/-- **THE EPOCH POLICY IS THE WEAKEST LAWFUL ONE**: every lawful policy (FIFO in particular) lands
only what `epoch` lands. -/
theorem SbPol.leEpoch (pol : SbPol) (es : List SbEnt) (k : Nat) :
    pol.landOk es k → SbPol.epoch.landOk es k :=
  fun h => And.intro (pol.inRange es k h) (fun k' e' e hk h1 h2 =>
    ⟨pol.fenced es k k' e e' h hk h1 h2, pol.sameAddr es k k' e e' h hk h1 h2⟩)

theorem SbPol.fifoLeEpoch (es : List SbEnt) (k : Nat) :
    SbPol.fifo.landOk es k → SbPol.epoch.landOk es k :=
  SbPol.leEpoch SbPol.fifo es k

/-! # 2. The candidate: state, event step, landing, run -/

/-- The buffered candidate state: the registered `Mstate` and a buffer per agent (oldest first). -/
structure SbCand.CandS where
  ms : Mstate
  sb : Nat → List SbEnt

def SbCand.updSb (f : Nat → List SbEnt) (i : Nat) (l : List SbEnt) : Nat → List SbEnt :=
  fun j => if j = i then l else f j

theorem SbCand.updSbEq (f : Nat → List SbEnt) (i : Nat) (l : List SbEnt) :
    SbCand.updSb f i l i = l := by simp [SbCand.updSb]

theorem SbCand.updSbNe (f : Nat → List SbEnt) (i : Nat) (l : List SbEnt) (j : Nat) :
    j ≠ i → SbCand.updSb f i l j = f j := by intro h; simp [SbCand.updSb, h]

theorem SbCand.updSbConst (i : Nat) :
    SbCand.updSb (fun _ => ([] : List SbEnt)) i [] = fun _ => [] := by
  funext j; simp [SbCand.updSb]

theorem SbCand.updSbTwice (f : Nat → List SbEnt) (i : Nat) (l l' : List SbEnt) :
    SbCand.updSb (SbCand.updSb f i l) i l' = SbCand.updSb f i l' := by
  funext j; by_cases h : j = i <;> simp [SbCand.updSb, h]

theorem SbCand.updWsTwice (f : Nat → Wstate) (i : Nat) (a b : Wstate) :
    updWs (updWs f i a) i b = updWs f i b := by
  funext j; by_cases h : j = i <;> simp [updWs, h]

/-- The byte the hart's YOUNGEST pending entry covering `a` writes (forwarding). -/
def SbCand.fwdByte (sb : List SbEnt) (a : Int) : Option (BitVec 8) :=
  sb.foldl (fun o e => (msgByte e.msg a).or o) none

theorem SbCand.fwdByteNil (a : Int) : SbCand.fwdByte [] a = none := rfl

/-- The timestamps the load's view update uses: a FORWARDED byte counts as `0` (no view moves; the
label's own timestamp at a forwarded byte is not constrained — P-W2 chooses it). -/
def SbCand.fwdMaskFrom (sb : List SbEnt) (base : Int) : Nat → List Nat → List Nat
  | _, [] => []
  | j, t :: ts => (if (SbCand.fwdByte sb (accAddr base j)).isSome then 0 else t) ::
      SbCand.fwdMaskFrom sb base (j + 1) ts

def SbCand.fwdMask (sb : List SbEnt) (base : Int) (ts : List Nat) : List Nat :=
  SbCand.fwdMaskFrom sb base 0 ts

theorem SbCand.fwdMaskFromNil (base : Int) : ∀ (j : Nat) (ts : List Nat),
    SbCand.fwdMaskFrom [] base j ts = ts
  | _, [] => rfl
  | j, t :: ts => by
    simp only [SbCand.fwdMaskFrom, SbCand.fwdByteNil, Option.isSome_none, Bool.false_eq_true,
      if_false, SbCand.fwdMaskFromNil base (j + 1) ts]

theorem SbCand.fwdMaskNil (base : Int) (ts : List Nat) : SbCand.fwdMask [] base ts = ts :=
  SbCand.fwdMaskFromNil base 0 ts

/-- A load's bytes: forwarded from the own buffer, or read from the log at the views. -/
def SbCand.rdOkSb (img : Image) (log : List Wmsg) (ws : Wstate) (aq : Bool) (base : Int)
    (ts : List Nat) (vs : List (BitVec 8)) (sb : List SbEnt) : Prop :=
  vs.length = ts.length ∧
  ∀ (j t : Nat) (v : BitVec 8), ts[j]? = some t → vs[j]? = some v →
    SbCand.fwdByte sb (accAddr base j) = some v ∨
    (SbCand.fwdByte sb (accAddr base j) = none ∧ byteRd img log ws aq (accAddr base j) t v)

theorem SbCand.rdOkSbNil (img : Image) (log : List Wmsg) (ws : Wstate) (aq : Bool) (base : Int)
    (ts : List Nat) (vs : List (BitVec 8)) :
    SbCand.rdOkSb img log ws aq base ts vs [] ↔ rdOk img log ws aq base ts vs := by
  constructor
  · rintro ⟨hl, h⟩
    refine ⟨hl, fun j t v hj hv => ?_⟩
    rcases h j t v hj hv with h' | h'
    · rw [SbCand.fwdByteNil] at h'; cases h'
    · exact h'.2
  · rintro ⟨hl, h⟩
    exact ⟨hl, fun j t v hj hv => Or.inr ⟨rfl, h j t v hj hv⟩⟩

/-- No own `.rl` entry is pending (an `.aq` access may go: rule 8). -/
def SbCand.noRl (sb : List SbEnt) : Prop := ∀ e ∈ sb, e.rl = false

/-- An AMO may land its write now: every own pending entry is in the CURRENT fence epoch (rule 4) and
writes no byte of the AMO's footprint (rule 1). -/
def SbCand.amoOk (sb : List SbEnt) (base : Int) (n : Nat) : Prop :=
  ∀ e ∈ sb, e.fs = 0 ∧ ¬ e.hits base n

theorem SbCand.noRlNil : SbCand.noRl [] := fun _ h => absurd h (by simp)

theorem SbCand.amoOkNil (base : Int) (n : Nat) : SbCand.amoOk [] base n :=
  fun _ h => absurd h (by simp)

/-- A fence that drains the buffer: predecessor `w`, successor `r` (`rw,rw`, `rw,r`, `w,rw`, `w,r`,
`tso`). -/
def SbCand.drains (pw sr : Bool) : Bool := pw && sr

/-- The issue consumes the publication flag (the store after a `pw ∧ sw` fence is the release). -/
def SbCand.issuePost (ws : Wstate) : Wstate := { ws with wRelp := false }

/-- The landing: the store's view updates at its landing position `t`, with the publication flag it
consumed at issue; the hart's CURRENT flag is kept. -/
def SbCand.landPost (ws : Wstate) (e : SbEnt) (t : Nat) : Wstate :=
  { storePostRun { ws with wRelp := e.relp } e.rl e.msg.wmPa e.msg.wmData.length t with
    wRelp := ws.wRelp }

def SbCand.issueEnt (σ : SbCand.CandS) (i : Nat) (rl : Bool) (base : Int) (vs : List (BitVec 8))
    (k : WmClass) : SbEnt :=
  ⟨⟨base, vs, some i, k⟩, rl, (σ.ms.msWs i).wRelp, 0⟩

/-- The post-state of an event step. -/
def SbCand.nextE (σ : SbCand.CandS) (i : Nat) (l : Lbl) : SbCand.CandS :=
  match l with
  | LLoad aq base ts _ =>
    ⟨⟨σ.ms.msImg, σ.ms.msLog,
      updWs σ.ms.msWs i (loadPostRun (σ.ms.msWs i) aq base (SbCand.fwdMask (σ.sb i) base ts))⟩,
     σ.sb⟩
  | LStore rl base vs k =>
    ⟨⟨σ.ms.msImg, σ.ms.msLog, updWs σ.ms.msWs i (SbCand.issuePost (σ.ms.msWs i))⟩,
     SbCand.updSb σ.sb i (σ.sb i ++ [SbCand.issueEnt σ i rl base vs k])⟩
  | LFence pr pw sr sw =>
    ⟨⟨σ.ms.msImg, σ.ms.msLog, updWs σ.ms.msWs i (fencePost (σ.ms.msWs i) pr pw sr sw)⟩,
     if pw && sw then SbCand.updSb σ.sb i ((σ.sb i).map SbEnt.bump) else σ.sb⟩
  | LRmw aq rl base ts rvs wvs k => ⟨mnext σ.ms i (LRmw aq rl base ts rvs wvs k), σ.sb⟩
  | LIo .. => ⟨σ.ms, σ.sb⟩

/-- **THE EVENT STEP**: a forwarding load, a store ISSUE, a fence (draining when `pw ∧ sr`), an AMO
(read at the landed log, write landing at once; `amoOk`), an inert I/O step. -/
inductive SbCand.stepE (σ : SbCand.CandS) (i : Nat) : Lbl → SbCand.CandS → Prop where
  | load (aq : Bool) (base : Int) (ts : List Nat) (vs : List (BitVec 8)) :
      SbCand.rdOkSb σ.ms.msImg σ.ms.msLog (σ.ms.msWs i) aq base ts vs (σ.sb i) →
      (aq = true → SbCand.noRl (σ.sb i)) →
      SbCand.stepE σ i (LLoad aq base ts vs) (SbCand.nextE σ i (LLoad aq base ts vs))
  | issue (rl : Bool) (base : Int) (vs : List (BitVec 8)) (k : WmClass) :
      vs ≠ [] → (rl = true → σ.sb i = []) →
      SbCand.stepE σ i (LStore rl base vs k) (SbCand.nextE σ i (LStore rl base vs k))
  | fence (pr pw sr sw : Bool) :
      (SbCand.drains pw sr = true → σ.sb i = []) →
      SbCand.stepE σ i (LFence pr pw sr sw) (SbCand.nextE σ i (LFence pr pw sr sw))
  | rmw (aq rl : Bool) (base : Int) (ts : List Nat) (rvs wvs : List (BitVec 8)) (k : WmClass) :
      wvs ≠ [] → wvs.length = ts.length →
      rdOk σ.ms.msImg σ.ms.msLog (σ.ms.msWs i) aq base ts rvs →
      rmwLatest σ.ms.msImg σ.ms.msLog base ts →
      SbCand.amoOk (σ.sb i) base ts.length →
      (rl = true → σ.sb i = []) → (aq = true → SbCand.noRl (σ.sb i)) →
      SbCand.stepE σ i (LRmw aq rl base ts rvs wvs k)
        (SbCand.nextE σ i (LRmw aq rl base ts rvs wvs k))
  | io (kd : IoKind) (base : Int) (vs : List (BitVec 8)) :
      SbCand.stepE σ i (LIo kd base vs) (SbCand.nextE σ i (LIo kd base vs))

theorem SbCand.stepEDet (σ σ' : SbCand.CandS) (i : Nat) (l : Lbl) :
    SbCand.stepE σ i l σ' → σ' = SbCand.nextE σ i l := by
  intro h; cases h <;> rfl

/-- The post-state of agent `i`'s `k`-th pending entry landing (`σ` if there is none). -/
def SbCand.nextL (σ : SbCand.CandS) (i k : Nat) : SbCand.CandS :=
  match (σ.sb i)[k]? with
  | some e =>
    ⟨⟨σ.ms.msImg, σ.ms.msLog ++ [e.msg],
      updWs σ.ms.msWs i (SbCand.landPost (σ.ms.msWs i) e (σ.ms.msLog.length + 1))⟩,
     SbCand.updSb σ.sb i ((σ.sb i).eraseIdx k)⟩
  | none => σ

/-- **THE LANDING** (an admin step, no label), as the policy allows. -/
inductive SbCand.land (pol : SbPol) (σ : SbCand.CandS) (i k : Nat) : SbCand.CandS → Prop where
  | mk : pol.landOk (σ.sb i) k → SbCand.land pol σ i k (SbCand.nextL σ i k)

/-- Any number of landings. -/
inductive SbCand.Lands (pol : SbPol) : SbCand.CandS → SbCand.CandS → Prop where
  | refl (σ : SbCand.CandS) : SbCand.Lands pol σ σ
  | step (σ σ1 σ' : SbCand.CandS) (i k : Nat) :
      SbCand.land pol σ i k σ1 → SbCand.Lands pol σ1 σ' → SbCand.Lands pol σ σ'

/-- A RUN STEP: an event, then any number of landings (of any agents). -/
def SbCand.stepM (pol : SbPol) (σ : SbCand.CandS) (s : Estep) (σ' : SbCand.CandS) : Prop :=
  ∃ σ1, SbCand.stepE σ s.esAg s.esLb σ1 ∧ SbCand.Lands pol σ1 σ'

/-- A buffered run: states and events, as `Exec`. -/
structure SbCand.BExec where
  st : List SbCand.CandS
  tr : List Estep

def SbCand.Steps (pol : SbPol) (st : List SbCand.CandS) (tr : List Estep) : Prop :=
  st.length = tr.length + 1 ∧
  ∀ k s σ σ', tr[k]? = some s → st[k]? = some σ → st[k + 1]? = some σ' → SbCand.stepM pol σ s σ'

/-- The initial state: empty log, initial views, empty buffers. -/
def SbCand.initS (σ : SbCand.CandS) : Prop :=
  σ.ms.msLog = [] ∧ (∀ i, σ.ms.msWs i = wsInit) ∧ ∀ i, σ.sb i = []

/-- **THE BUFFERED RUN** under policy `pol`. -/
def SbCand.execWfP (pol : SbPol) (E : SbCand.BExec) : Prop :=
  (∀ σ0, E.st[0]? = some σ0 → SbCand.initS σ0) ∧ SbCand.Steps pol E.st E.tr

/-- Forgetting the buffers. -/
def SbCand.toExec (E : SbCand.BExec) : Weak.Exec := ⟨E.st.map (·.ms), E.tr⟩

/-! ## 2.1 Monotonicity in the policy -/

theorem SbCand.landMono (p1 p2 : SbPol) (hp : ∀ es k, p1.landOk es k → p2.landOk es k)
    (σ σ' : SbCand.CandS) (i k : Nat) : SbCand.land p1 σ i k σ' → SbCand.land p2 σ i k σ' := by
  intro h; cases h with | mk h => exact .mk (hp _ _ h)

theorem SbCand.landsMono (p1 p2 : SbPol) (hp : ∀ es k, p1.landOk es k → p2.landOk es k)
    (σ σ' : SbCand.CandS) : SbCand.Lands p1 σ σ' → SbCand.Lands p2 σ σ' := by
  intro h
  induction h with
  | refl σ => exact .refl σ
  | step σ σ1 σ' i k hl _ ih => exact .step σ σ1 σ' i k (SbCand.landMono p1 p2 hp σ σ1 i k hl) ih

theorem SbCand.execWfPMono (p1 p2 : SbPol) (hp : ∀ es k, p1.landOk es k → p2.landOk es k)
    (E : SbCand.BExec) : SbCand.execWfP p1 E → SbCand.execWfP p2 E := by
  rintro ⟨h0, hlen, hs⟩
  refine ⟨h0, hlen, fun k s σ σ' h1 h2 h3 => ?_⟩
  obtain ⟨σ1, he, hl⟩ := hs k s σ σ' h1 h2 h3
  exact ⟨σ1, he, SbCand.landsMono p1 p2 hp σ1 σ' hl⟩

/-- Every run under a lawful policy (FIFO in particular) is a run under `epoch`. -/
theorem SbCand.execWfPEpoch (pol : SbPol) (E : SbCand.BExec) :
    SbCand.execWfP pol E → SbCand.execWfP SbPol.epoch E :=
  SbCand.execWfPMono pol SbPol.epoch (SbPol.leEpoch pol) E

/-! # 3. The embedding: an unbuffered run is a buffered run with immediate landings -/

def SbCand.lift (σ : Mstate) : SbCand.CandS := ⟨σ, fun _ => []⟩

def SbCand.liftE (E : Weak.Exec) : SbCand.BExec := ⟨E.exSt.map SbCand.lift, E.exTr⟩

theorem SbCand.foldStoreRelp (rl : Bool) (t : Nat) :
    ∀ (as_ : List Int) (ws : Wstate), as_ ≠ [] →
      (as_.foldl (fun w a => storePost w rl a t) ws).wRelp = false
  | [], _, h => absurd rfl h
  | [_], _, _ => rfl
  | _ :: b :: as_, _, _ => SbCand.foldStoreRelp rl t (b :: as_) _ (List.cons_ne_nil _ _)

theorem SbCand.storePostRunRelp (ws : Wstate) (rl : Bool) (base : Int) (n t : Nat) :
    n ≠ 0 → (storePostRun ws rl base n t).wRelp = false := by
  intro hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hne : ((List.range' 0 (m + 1)).map (fun j : Nat => base + (j : Int))) ≠ [] := by simp
  exact SbCand.foldStoreRelp rl t _ ws hne

/-- Issue then immediate landing is the registered store's view update. -/
theorem SbCand.landIssue (ws : Wstate) (rl : Bool) (m : Wmsg) (t : Nat) (hn : m.wmData ≠ []) :
    SbCand.landPost (SbCand.issuePost ws) ⟨m, rl, ws.wRelp, 0⟩ t =
      storePostRun ws rl m.wmPa m.wmData.length t := by
  have h1 : ({ SbCand.issuePost ws with wRelp := ws.wRelp } : Wstate) = ws := by cases ws; rfl
  have h2 := SbCand.storePostRunRelp ws rl m.wmPa m.wmData.length t
    (fun h => hn (List.eq_nil_of_length_eq_zero h))
  show ({ storePostRun { SbCand.issuePost ws with wRelp := ws.wRelp } rl m.wmPa m.wmData.length t with
    wRelp := false } : Wstate) = _
  rw [h1]
  generalize storePostRun ws rl m.wmPa m.wmData.length t = X at h2 ⊢
  cases X
  simp only at h2
  subst h2
  rfl

/-- **ONE REGISTERED STEP IS ONE BUFFERED RUN STEP** (a store: issue + landing of the only entry). -/
theorem SbCand.stepMOfOld (pol : SbPol) (σ σ' : Mstate) (i : Nat) (l : Lbl) :
    mstep σ i l σ' → SbCand.stepM pol (SbCand.lift σ) ⟨i, l⟩ (SbCand.lift σ') := by
  intro h
  cases h with
  | MStepLoad aq base ts vs hrd =>
    refine ⟨_, SbCand.stepE.load aq base ts vs ((SbCand.rdOkSbNil _ _ _ _ _ _ _).2 hrd)
      (fun _ => SbCand.noRlNil), ?_⟩
    have e : SbCand.nextE (SbCand.lift σ) i (LLoad aq base ts vs) =
        SbCand.lift ⟨σ.msImg, σ.msLog, updWs σ.msWs i (loadPostRun (σ.msWs i) aq base ts)⟩ := by
      simp only [SbCand.nextE, SbCand.lift, SbCand.fwdMaskNil]
    rw [e]; exact .refl _
  | MStepStore rl base vs k hne =>
    have hs := SbCand.stepE.issue (σ := SbCand.lift σ) (i := i) rl base vs k hne (fun _ => rfl)
    have hsb : (SbCand.nextE (SbCand.lift σ) i (LStore rl base vs k)).sb i =
        [⟨⟨base, vs, some i, k⟩, rl, (σ.msWs i).wRelp, 0⟩] := by
      simp [SbCand.nextE, SbCand.lift, SbCand.updSb, SbCand.issueEnt]
    have hl : SbCand.land pol (SbCand.nextE (SbCand.lift σ) i (LStore rl base vs k)) i 0
        (SbCand.nextL (SbCand.nextE (SbCand.lift σ) i (LStore rl base vs k)) i 0) :=
      .mk (by rw [hsb]; exact pol.oldest _ [])
    refine ⟨_, hs, .step _ _ _ i 0 hl ?_⟩
    have hli := SbCand.landIssue (σ.msWs i) rl ⟨base, vs, some i, k⟩ (σ.msLog.length + 1) hne
    have e : SbCand.nextL (SbCand.nextE (SbCand.lift σ) i (LStore rl base vs k)) i 0 =
        SbCand.lift ⟨σ.msImg, σ.msLog ++ [⟨base, vs, some i, k⟩],
          updWs σ.msWs i (storePostRun (σ.msWs i) rl base vs.length (σ.msLog.length + 1))⟩ := by
      simp only [SbCand.nextL, hsb, List.getElem?_cons_zero]
      simp only [SbCand.nextE, SbCand.lift, SbCand.issueEnt, updWsEq, SbCand.updWsTwice,
        SbCand.updSbTwice, List.eraseIdx_cons_zero, SbCand.updSbConst, hli]
    rw [e]; exact .refl _
  | MStepFence pr pw sr sw =>
    refine ⟨_, SbCand.stepE.fence (σ := SbCand.lift σ) (i := i) pr pw sr sw (fun _ => rfl), ?_⟩
    have e : SbCand.nextE (SbCand.lift σ) i (LFence pr pw sr sw) =
        SbCand.lift ⟨σ.msImg, σ.msLog, updWs σ.msWs i (fencePost (σ.msWs i) pr pw sr sw)⟩ := by
      simp only [SbCand.nextE, SbCand.lift, List.map_nil, SbCand.updSbConst, ite_self]
    rw [e]; exact .refl _
  | MStepRmw aq rl base ts rvs wvs k hne hlen hrd hlat =>
    exact ⟨_, SbCand.stepE.rmw (σ := SbCand.lift σ) (i := i) aq rl base ts rvs wvs k hne hlen hrd hlat
      (SbCand.amoOkNil base ts.length) (fun _ => rfl) (fun _ => SbCand.noRlNil), .refl _⟩
  | MStepIo kd base vs =>
    exact ⟨_, SbCand.stepE.io (σ := SbCand.lift σ) (i := i) kd base vs, .refl _⟩

/-- **THE EMBEDDING**: every registered run is a buffered run, under every lawful policy. -/
theorem SbCand.execWfOfOld (pol : SbPol) (E : Weak.Exec) :
    execWf E → SbCand.execWfP pol (SbCand.liftE E) := by
  rintro ⟨hlen, h0, hstep⟩
  refine ⟨fun σ0 h => ?_, by simp [SbCand.liftE, hlen], fun k s σ σ' hs h1 h2 => ?_⟩
  · simp only [SbCand.liftE, List.getElem?_map] at h
    cases ho : E.exSt[0]? with
    | none => simp [ho] at h
    | some σo =>
      simp only [ho, Option.map_some, Option.some.injEq] at h
      subst h
      obtain ⟨hl, hw⟩ := h0 σo ho
      exact ⟨hl, hw, fun _ => rfl⟩
  · simp only [SbCand.liftE, List.getElem?_map] at h1 h2
    cases ho : E.exSt[k]? with
    | none => simp [ho] at h1
    | some σo =>
      cases ho' : E.exSt[k + 1]? with
      | none => simp [ho'] at h2
      | some σo' =>
        simp only [ho, ho', Option.map_some, Option.some.injEq] at h1 h2
        subst h1 h2
        exact SbCand.stepMOfOld pol σo σo' s.esAg s.esLb (hstep k s σo σo' hs ho ho')

/-- …and forgetting the buffers gives the registered run back. -/
theorem SbCand.toExecLift (E : Weak.Exec) : SbCand.toExec (SbCand.liftE E) = E := by
  have hc : ((fun x : SbCand.CandS => x.ms) ∘ SbCand.lift) = id := rfl
  cases E
  simp [SbCand.toExec, SbCand.liftE, hc]

/-! # 4. The view-boundedness invariant -/

/-- Every view an agent holds is at most the log length. -/
def SbCand.Inv (σ : SbCand.CandS) : Prop := ∀ j, wsBounded (σ.ms.msWs j) σ.ms.msLog.length

theorem SbCand.invInit (σ : SbCand.CandS) : SbCand.initS σ → SbCand.Inv σ := by
  rintro ⟨-, hw, -⟩ j
  rw [hw j]; exact wsBoundedInit _

theorem SbCand.wsBoundedRelp (ws : Wstate) (b : Bool) (n : Nat) :
    wsBounded ws n → wsBounded { ws with wRelp := b } n := fun h => h

theorem SbCand.invUpd (σ : SbCand.CandS) (i : Nat) (w : Wstate) (log : List Wmsg) :
    SbCand.Inv σ → σ.ms.msLog.length ≤ log.length → wsBounded w log.length →
    ∀ j, wsBounded (updWs σ.ms.msWs i w j) log.length := by
  intro h hle hw j
  by_cases hj : j = i
  · subst hj; rw [updWsEq]; exact hw
  · rw [updWsNe _ _ _ _ hj]; exact wsBoundedMono _ _ _ (h j) hle

theorem SbCand.fwdMaskFromMem (sb : List SbEnt) (base : Int) :
    ∀ (ts : List Nat) (j t : Nat), t ∈ SbCand.fwdMaskFrom sb base j ts →
      t = 0 ∨ ∃ j', ts[j']? = some t ∧ SbCand.fwdByte sb (accAddr base (j + j')) = none
  | [], _, _, h => by simp [SbCand.fwdMaskFrom] at h
  | t0 :: ts, j, t, h => by
    simp only [SbCand.fwdMaskFrom, List.mem_cons] at h
    rcases h with h | h
    · cases hf : SbCand.fwdByte sb (accAddr base j) with
      | some v => left; simpa [hf] using h
      | none =>
        right
        refine ⟨0, ?_, by simpa using hf⟩
        simp [hf] at h
        simp [h]
    · rcases SbCand.fwdMaskFromMem sb base ts (j + 1) t h with h0 | ⟨j', h1, h2⟩
      · exact Or.inl h0
      · refine Or.inr ⟨j' + 1, by simpa using h1, ?_⟩
        rw [show j + (j' + 1) = j + 1 + j' by omega]
        exact h2

theorem SbCand.fwdMaskBounded (img : Image) (log : List Wmsg) (ws : Wstate) (aq : Bool) (base : Int)
    (ts : List Nat) (vs : List (BitVec 8)) (sb : List SbEnt) :
    SbCand.rdOkSb img log ws aq base ts vs sb → ∀ t ∈ SbCand.fwdMask sb base ts, t ≤ log.length := by
  rintro ⟨hlen, hall⟩ t ht
  rcases SbCand.fwdMaskFromMem sb base ts 0 t ht with h0 | ⟨j, hj, hf⟩
  · omega
  · have hjl : j < vs.length := by rw [hlen]; exact lookup_lt_Some hj
    rw [Nat.zero_add] at hf
    rcases hall j t vs[j] hj (List.getElem?_eq_getElem hjl) with h | ⟨_, hb, _⟩
    · rw [hf] at h; cases h
    · exact logByteBounded img log t _ (by rw [hb]; rfl)

theorem SbCand.landPostBounded (ws : Wstate) (e : SbEnt) (t n n' : Nat) :
    wsBounded ws n → t ≤ n' → n ≤ n' → wsBounded (SbCand.landPost ws e t) n' := fun hb ht hle =>
  SbCand.wsBoundedRelp _ _ _ (storePostRunBounded _ _ _ _ _ n n'
    (SbCand.wsBoundedRelp _ _ _ hb) ht hle)

theorem SbCand.invStepE (σ σ' : SbCand.CandS) (i : Nat) (l : Lbl) :
    SbCand.Inv σ → SbCand.stepE σ i l σ' → SbCand.Inv σ' := by
  intro h hs
  cases hs with
  | load aq base ts vs hrd _ =>
    exact SbCand.invUpd σ i _ σ.ms.msLog h (Nat.le_refl _)
      (loadPostRunBounded _ _ _ _ _ (h i) (SbCand.fwdMaskBounded _ _ _ _ _ _ _ _ hrd))
  | issue => exact SbCand.invUpd σ i _ σ.ms.msLog h (Nat.le_refl _) (SbCand.wsBoundedRelp _ _ _ (h i))
  | fence pr pw sr sw _ =>
    exact SbCand.invUpd σ i _ σ.ms.msLog h (Nat.le_refl _) (fencePostBounded _ _ _ _ _ _ (h i))
  | rmw aq rl base ts rvs wvs k _ _ hrd _ _ _ _ =>
    exact SbCand.invUpd σ i _ (σ.ms.msLog ++ [⟨base, wvs, some i, k⟩]) h (by simp)
      (storePostRunBounded _ _ _ _ (σ.ms.msLog.length + 1) σ.ms.msLog.length _
        (loadPostRunBounded _ _ _ _ _ (h i) (rdOkTsBounded _ _ _ _ _ _ _ hrd)) (by simp) (by simp))
  | io => exact h

theorem SbCand.invNextL (σ : SbCand.CandS) (i k : Nat) : SbCand.Inv σ → SbCand.Inv (SbCand.nextL σ i k) := by
  intro h
  unfold SbCand.nextL
  cases he : (σ.sb i)[k]? with
  | none => exact h
  | some e =>
    exact SbCand.invUpd σ i _ (σ.ms.msLog ++ [e.msg]) h (by simp)
      (SbCand.landPostBounded _ e _ σ.ms.msLog.length _ (h i) (by simp) (by simp))

theorem SbCand.invLands (pol : SbPol) (σ σ' : SbCand.CandS) :
    SbCand.Inv σ → SbCand.Lands pol σ σ' → SbCand.Inv σ' := by
  intro h hl
  induction hl with
  | refl => exact h
  | step σ σ1 σ' i k hland _ ih =>
    cases hland with
    | mk _ => exact ih (SbCand.invNextL σ i k h)

/-! # 5. A boolean checker for TOP-read runs with oldest-first landings -/

/-- One byte of a top read: forwarded, or the LATEST log byte. -/
def SbCand.topByteB (img : Image) (log : List Wmsg) (sb : List SbEnt) (a : Int) (t : Nat)
    (v : BitVec 8) : Bool :=
  match SbCand.fwdByte sb a with
  | some v' => decide (v = v')
  | none => decide (logByte img log t a = some v) && !writesInb log a t log.length

def SbCand.topRdB (img : Image) (log : List Wmsg) (sb : List SbEnt) (base : Int) (ts : List Nat)
    (vs : List (BitVec 8)) : Bool :=
  decide (vs.length = ts.length) &&
  (List.range ts.length).all (fun j =>
    match ts[j]?, vs[j]? with
    | some t, some v => SbCand.topByteB img log sb (accAddr base j) t v
    | _, _ => true)

theorem SbCand.topRdBSound (img : Image) (log : List Wmsg) (ws : Wstate) (aq : Bool)
    (sb : List SbEnt) (base : Int) (ts : List Nat) (vs : List (BitVec 8)) :
    wsBounded ws log.length → SbCand.topRdB img log sb base ts vs = true →
    SbCand.rdOkSb img log ws aq base ts vs sb := by
  intro hb h
  unfold SbCand.topRdB at h
  rw [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨hlen, hall⟩ := h
  refine ⟨hlen, fun j t v hj hv => ?_⟩
  have hc := hall j (List.mem_range.2 (lookup_lt_Some hj))
  simp only [hj, hv] at hc
  unfold SbCand.topByteB at hc
  cases hf : SbCand.fwdByte sb (accAddr base j) with
  | some v' =>
    simp only [hf, decide_eq_true_eq] at hc
    left; rw [hc]
  | none =>
    simp only [hf, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hc
    obtain ⟨hl, hw⟩ := hc
    refine Or.inr ⟨rfl, hl, latestReadable img log ws _ _ t ?_ ⟨by rw [hl]; rfl, fun hw' => ?_⟩⟩
    · exact Nat.max_le.2 ⟨loadVpreBounded ws aq _ hb, hb.2.2.2.2.2.2.1 (accAddr base j)⟩
    · rw [writesInbSpec, hw] at hw'; cases hw'

def SbCand.latestAllB (img : Image) (log : List Wmsg) (base : Int) (ts : List Nat) : Bool :=
  (List.range ts.length).all (fun j =>
    match ts[j]? with
    | some t => (logByte img log t (accAddr base j)).isSome && !writesInb log (accAddr base j) t log.length
    | none => true)

theorem SbCand.latestAllBSound (img : Image) (log : List Wmsg) (base : Int) (ts : List Nat) :
    SbCand.latestAllB img log base ts = true → rmwLatest img log base ts := by
  intro h j t hj
  rw [SbCand.latestAllB, List.all_eq_true] at h
  have hc := h j (List.mem_range.2 (lookup_lt_Some hj))
  simp only [hj, Bool.and_eq_true, Bool.not_eq_true'] at hc
  exact ⟨hc.1, fun hw => by rw [writesInbSpec, hc.2] at hw; cases hw⟩

def SbEnt.hitsB (e : SbEnt) (base : Int) (n : Nat) : Bool :=
  (List.range n).any (fun j => msgWritesb e.msg (accAddr base j))

theorem SbEnt.hitsBOf (e : SbEnt) (base : Int) (n : Nat) : e.hits base n → e.hitsB base n = true := by
  rintro ⟨j, hj, hs⟩
  exact List.any_eq_true.2 ⟨j, List.mem_range.2 hj, (msgWritesbTrue _ _).2 hs⟩

def SbCand.amoOkB (sb : List SbEnt) (base : Int) (n : Nat) : Bool :=
  sb.all (fun e => decide (e.fs = 0) && !e.hitsB base n)

theorem SbCand.amoOkBSound (sb : List SbEnt) (base : Int) (n : Nat) :
    SbCand.amoOkB sb base n = true → SbCand.amoOk sb base n := by
  intro h e he
  rw [SbCand.amoOkB, List.all_eq_true] at h
  have hc := h e he
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hc
  exact ⟨hc.1, fun hh => by rw [SbEnt.hitsBOf e base n hh] at hc; cases hc.2⟩

def SbCand.noRlB (sb : List SbEnt) : Bool := sb.all (fun e => !e.rl)

theorem SbCand.noRlBSound (sb : List SbEnt) : SbCand.noRlB sb = true → SbCand.noRl sb := by
  intro h e he
  rw [SbCand.noRlB, List.all_eq_true] at h
  simpa using h e he

theorem SbCand.impB {b c : Bool} {P : Prop} (h : (!b || c) = true) (hc : c = true → P)
    (hb : b = true) : P := by
  subst hb; exact hc (by simpa using h)

theorem SbCand.neNilB {α : Type _} {l : List α} : (!l.isEmpty) = true → l ≠ [] := by
  cases l <;> simp

/-- The event-step checker: top reads (or forwarded bytes), the buffer side conditions. -/
def SbCand.okEB (σ : SbCand.CandS) (i : Nat) (l : Lbl) : Bool :=
  match l with
  | LLoad aq base ts vs =>
    SbCand.topRdB σ.ms.msImg σ.ms.msLog (σ.sb i) base ts vs && (!aq || SbCand.noRlB (σ.sb i))
  | LStore rl _ vs _ => !vs.isEmpty && (!rl || (σ.sb i).isEmpty)
  | LFence _ pw sr _ => !SbCand.drains pw sr || (σ.sb i).isEmpty
  | LRmw aq rl base ts rvs wvs _ =>
    !wvs.isEmpty && decide (wvs.length = ts.length) &&
    SbCand.topRdB σ.ms.msImg σ.ms.msLog [] base ts rvs &&
    SbCand.latestAllB σ.ms.msImg σ.ms.msLog base ts &&
    SbCand.amoOkB (σ.sb i) base ts.length &&
    (!rl || (σ.sb i).isEmpty) && (!aq || SbCand.noRlB (σ.sb i))
  | LIo .. => true

theorem SbCand.okEBSound (σ : SbCand.CandS) (i : Nat) (l : Lbl) :
    SbCand.Inv σ → SbCand.okEB σ i l = true → SbCand.stepE σ i l (SbCand.nextE σ i l) := by
  intro hI h
  cases l with
  | LLoad aq base ts vs =>
    simp only [SbCand.okEB, Bool.and_eq_true] at h
    exact SbCand.stepE.load aq base ts vs (SbCand.topRdBSound _ _ _ aq _ _ _ _ (hI i) h.1)
      (SbCand.impB h.2 (SbCand.noRlBSound _))
  | LStore rl base vs k =>
    simp only [SbCand.okEB, Bool.and_eq_true] at h
    exact SbCand.stepE.issue rl base vs k (SbCand.neNilB h.1) (SbCand.impB h.2 List.isEmpty_iff.1)
  | LFence pr pw sr sw =>
    simp only [SbCand.okEB] at h
    refine SbCand.stepE.fence pr pw sr sw (fun hd => ?_)
    rw [hd] at h
    exact List.isEmpty_iff.1 (by simpa using h)
  | LRmw aq rl base ts rvs wvs k =>
    simp only [SbCand.okEB, Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
    exact SbCand.stepE.rmw aq rl base ts rvs wvs k (SbCand.neNilB h1) (of_decide_eq_true h2)
      ((SbCand.rdOkSbNil _ _ _ _ _ _ _).1 (SbCand.topRdBSound _ _ _ aq _ _ _ _ (hI i) h3))
      (SbCand.latestAllBSound _ _ _ _ h4) (SbCand.amoOkBSound _ _ _ h5)
      (SbCand.impB h6 List.isEmpty_iff.1) (SbCand.impB h7 (SbCand.noRlBSound _))
  | LIo kd base vs => exact SbCand.stepE.io kd base vs

/-- Landings of the OLDEST entry of the listed agents, in order. -/
def SbCand.landAll (σ : SbCand.CandS) : List Nat → SbCand.CandS
  | [] => σ
  | i :: is => SbCand.landAll (SbCand.nextL σ i 0) is

def SbCand.landAllB (σ : SbCand.CandS) : List Nat → Bool
  | [] => true
  | i :: is => !(σ.sb i).isEmpty && SbCand.landAllB (SbCand.nextL σ i 0) is

theorem SbCand.landAllSound (pol : SbPol) : ∀ (is : List Nat) (σ : SbCand.CandS),
    SbCand.Inv σ → SbCand.landAllB σ is = true →
    SbCand.Lands pol σ (SbCand.landAll σ is) ∧ SbCand.Inv (SbCand.landAll σ is)
  | [], σ, hI, _ => ⟨.refl σ, hI⟩
  | i :: is, σ, hI, h => by
    simp only [SbCand.landAllB, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    obtain ⟨e, es, hes⟩ : ∃ e es, σ.sb i = e :: es := by
      cases hh : σ.sb i with
      | nil => exact absurd hh (SbCand.neNilB h1)
      | cons e es => exact ⟨e, es, rfl⟩
    have hl : SbCand.land pol σ i 0 (SbCand.nextL σ i 0) := .mk (by rw [hes]; exact pol.oldest e es)
    obtain ⟨h3, h4⟩ := SbCand.landAllSound pol is _ (SbCand.invNextL σ i 0 hI) h2
    exact ⟨.step _ _ _ i 0 hl h3, h4⟩

/-- A macro step: an event, then the oldest-entry landings of the listed agents. -/
def SbCand.nextM (σ : SbCand.CandS) (st : Estep × List Nat) : SbCand.CandS :=
  SbCand.landAll (SbCand.nextE σ st.1.esAg st.1.esLb) st.2

def SbCand.statesOf (σ : SbCand.CandS) : List (Estep × List Nat) → List SbCand.CandS
  | [] => [σ]
  | st :: rest => σ :: SbCand.statesOf (SbCand.nextM σ st) rest

def SbCand.runOkB (σ : SbCand.CandS) : List (Estep × List Nat) → Bool
  | [] => true
  | st :: rest => SbCand.okEB σ st.1.esAg st.1.esLb &&
      SbCand.landAllB (SbCand.nextE σ st.1.esAg st.1.esLb) st.2 &&
      SbCand.runOkB (SbCand.nextM σ st) rest

theorem SbCand.statesOfHead (σ : SbCand.CandS) (steps : List (Estep × List Nat)) :
    (SbCand.statesOf σ steps)[0]? = some σ := by
  cases steps <;> rfl

theorem SbCand.stepsCons (pol : SbPol) (σ σ' : SbCand.CandS) (s : Estep) (st : List SbCand.CandS)
    (tr : List Estep) : SbCand.Steps pol st tr → st[0]? = some σ' → SbCand.stepM pol σ s σ' →
    SbCand.Steps pol (σ :: st) (s :: tr) := by
  rintro ⟨hlen, hstep⟩ h0 hs
  refine ⟨by simp [hlen], fun k s0 σ0 σ0' hk h1 h2 => ?_⟩
  cases k with
  | zero =>
    simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at hk h1 h2
    rw [h0, Option.some.injEq] at h2
    subst hk h1 h2
    exact hs
  | succ k =>
    simp only [List.getElem?_cons_succ] at hk h1 h2
    exact hstep k s0 σ0 σ0' hk h1 h2

theorem SbCand.runSound (pol : SbPol) : ∀ (steps : List (Estep × List Nat)) (σ : SbCand.CandS),
    SbCand.Inv σ → SbCand.runOkB σ steps = true →
    SbCand.Steps pol (SbCand.statesOf σ steps) (steps.map Prod.fst)
  | [], _, _, _ => ⟨rfl, fun _ _ _ _ hs => by simp at hs⟩
  | st :: rest, σ, hI, h => by
    simp only [SbCand.runOkB, Bool.and_eq_true] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    have he := SbCand.okEBSound σ st.1.esAg st.1.esLb hI h1
    obtain ⟨hl, hI'⟩ := SbCand.landAllSound pol st.2 _ (SbCand.invStepE _ _ _ _ hI he) h2
    exact SbCand.stepsCons pol σ (SbCand.nextM σ st) st.1 _ _
      (SbCand.runSound pol rest _ hI' h3) (SbCand.statesOfHead _ _) ⟨_, he, hl⟩

/-- **THE CHECKER**: a passing step list from an initial state is a buffered run under EVERY lawful
policy (its landings take the oldest entry, which every policy allows). -/
theorem SbCand.runOfB (pol : SbPol) (σ0 : SbCand.CandS) (steps : List (Estep × List Nat)) :
    SbCand.initS σ0 → SbCand.runOkB σ0 steps = true →
    SbCand.execWfP pol ⟨SbCand.statesOf σ0 steps, steps.map Prod.fst⟩ := fun hi h =>
  ⟨fun σ h0 => by
      rw [SbCand.statesOfHead, Option.some.injEq] at h0
      subst h0; exact hi,
    SbCand.runSound pol steps σ0 (SbCand.invInit σ0 hi) h⟩

end Weak
