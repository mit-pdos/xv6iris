/-
Weak: **the standalone acyclicity MEASURE theorem** (M6 W2a, step 2: the
disciplined-cycle refutation).

Rocq: `iris/WeakRobustAcyc.v` @ xxvzwolszwmp.

The Rocq header, in substance: `Weak/WeakRobustGraph.lean` fixes the dependency
graph `gdep = gpo ∪ grf` over a traced behavior and proves the STRUCTURAL half
of acyclicity: every cycle contains a CROSS-AGENT rf edge (`tcGdepCross`),
because inside one agent both edge families increase the trace index
(`gdepSameAgentLt`, resting on `atraceOwnRead`).  This file supplies the
SEMANTIC half — the measure that refutes the remaining cross-agent cycles.

THE MEASURE IS THE MESSAGE TIMESTAMP, and the argument is one segment lemma
repeated around the cycle.  S1: if agent `i` READS timestamp `ts` at trace
position `k`, later FULFILS `ts'` at `k'`, and the read is OK relative to `k'`,
then `ts < ts'`.  Walking a cycle, each cross rf edge's reader is followed in
its own trace by the fulfil that sources the NEXT cross edge, so timestamps
strictly increase around the cycle — impossible.

WHAT "DISCIPLINED" MEANS (the worklist's correction of 2026-08-11): READER-side
acquire discipline — the cross read is `aq`-labelled, or it is followed,
strictly before the reader's next fulfil, by a `pr ∧ sw` fence
(`fence r, rw`).  The writer-side fence is refuted by LB with the fence before
the load.  THE SECOND ARM, `covered`: a critical-section read (`ld x; sd y`
inside a lock) is not disciplined, yet harmless — the lock acquire already
pushed the reader's `wVwNew` past the read message's timestamp, so EXT alone
pins every later fulfil.  The per-edge obligation is `edgeOk = disciplined ∨
covered`; A0 relativizes the coverage to the LATER FULFIL's own EXT view
(`fcov`, `edgeOkF`), a pure weakening (`edgeOkEdgeOkF`).

THE AUXILIARY INVARIANT `fwdOwn`: a forward-bank entry always names an
OWN-authored log position, so a FOREIGN read is never a bank hit and
`fwdView = ts`.  It is DERIVED for a `wpBehavior` bundle (`ptracesOfFwdOwn`):
the bank starts empty (`wsInit`), only the store post-run inserts (at the
timestamp `astepOk` pins to the acting agent), and the promise phase never
touches `paWs`.  NOT HERE: the SCowned arm (it needs φ, which speaks about
promise-free runs — W2b).  DEPENDENCY-FREE: no Iris, no Sail.

**Deviations from Rocq.**

1. NAMES: lowerCamelCase as `Weak/WeakMem.lean` deviation 1.  File-qualified
   (in `notes/weak-port-dupnames.json`): `ws_le_vwNew` ↦
   `WeakRobustAcyc.wsLeVwNew`, `load_post_fold_vwNew_aq` ↦
   `WeakRobustAcyc.loadPostFoldVwNewAq`, `load_post_run_vwNew_aq` ↦
   `WeakRobustAcyc.loadPostRunVwNewAq`, `lb_aq` ↦ `WeakRobustAcyc.lbAq`.  The
   first three already exist in `Weak/WeakMem.lean` (as `wsLeVwNew`,
   `loadPostFoldVwNewAq`, `loadPostRunVwNewAq`); the copies here are proved by
   them and kept for faithfulness.
2. VOCABULARY: as `WeakMem` deviation 2 and `WeakRobustGraph` deviation 2;
   `agent` ↦ `Nat`, `w_fwd ws !! a` ↦ `get? ws.wFwd a`, `tvs.*1` ↦
   `tvs.map Prod.fst`, `is_Some o` ↦ `o.isSome`, `S k` ↦ `k + 1`.  The Rocq
   option argument `D` of the `astepOk_*` lemmas is `Dl` (`D` is the device
   type).
3. SECTION VARIABLES: `pstep` (and `pdev` in `wpBehaviorGdepAcyclic`) are
   explicit arguments exactly where a statement mentions them, in Rocq's order
   (`WeakRobustTrace` deviation 3).
4. O2 / owner decision D4 (the Lean-only label `LIFetch`, `Weak/WeakPromise.lean`
   deviation 8): `lbAq (LIFetch ..) = false`, `lbFencePrsw (LIFetch ..) = False`,
   `fulfilVext _ (LIFetch ..) = none`; every `astepOk_*` case split gains the
   `LIFetch` arm (`f = id`, `Dl = none`).  For every Rocq label the definitions
   agree.
5. Not imported: `Weak.WeakAxiomatic` (Rocq imports it only for the parked
   `WeakMem` fold lemmas, whose Lean versions live in `Weak/WeakMem.lean`;
   `WeakRobustGraph` deviation 7).  `acc_addr base j` is `base + (j : Int)`
   (`WeakMem`'s statements of `loadPostRunVrOld'` / `loadPostRunVwNewAq`).
6. Proof shape only: `asteps_fwd_own`'s `is_Some` assertions become
   `lookup_lt_is_Some_2`; `rtc_gdep_first_cross`'s head induction is
   `MachCSL.rtc_ind_l`; `cfg_ws_init_promise_run` is the bare (tail)
   induction.  Statements unchanged.

**Name map** (Rocq → Lean): deviation 1's four; `lb_fence_prsw` ↦ `lbFencePrsw`;
`fwd_own` ↦ `fwdOwn`; `fwd_own_init` ↦ `fwdOwnInit`; `read_unforwarded` ↦
`readUnforwarded`; `fwd_own_read_unforwarded` ↦ `fwdOwnReadUnforwarded`;
`astep_ok_fwd_own` ↦ `astepOkFwdOwn`; `astep_ok_fulfil_ext` ↦
`astepOkFulfilExt`; `astep_ok_read_fulfil_lt` ↦ `astepOkReadFulfilLt`;
`astep_ok_read_vwNew_aq` ↦ `astepOkReadVwNewAq`; `astep_ok_read_vrOld` ↦
`astepOkReadVrOld`; `astep_ok_fence_vwNew` ↦ `astepOkFenceVwNew`;
`disciplined`; `covered`; `edge_ok` ↦ `edgeOk`; `edge_ok_disciplined` ↦
`edgeOkDisciplined`; `edge_ok_covered` ↦ `edgeOkCovered`; `fulfil_vext` ↦
`fulfilVext`; `fulfil_vext_vwNew` ↦ `fulfilVextVwNew`; `fcov`; `fcov_mono_ts` ↦
`fcovMonoTs`; `edge_ok_f` ↦ `edgeOkF`; `edge_ok_f_disciplined` ↦
`edgeOkFDisciplined`; `edge_ok_f_fcov` ↦ `edgeOkFFcov`; `astep_ok_fulfil_vext`
↦ `astepOkFulfilVext`; `asteps_fwd_own` ↦ `astepsFwdOwn`; `atrace_fwd_own` ↦
`atraceFwdOwn`; `atrace_S1_f` ↦ `atraceS1F`; `covered_fcov` ↦ `coveredFcov`;
`edge_ok_edge_ok_f` ↦ `edgeOkEdgeOkF`; `atrace_S1` ↦ `atraceS1`;
`atrace_S1_le_f` ↦ `atraceS1LeF`; `atrace_S1_le` ↦ `atraceS1Le`;
`ptraces_fwd_own` ↦ `ptracesFwdOwn`; `rf_edges_ok` ↦ `rfEdgesOk`;
`rf_disciplined` ↦ `rfDisciplined`; `rf_disciplined_edges_ok` ↦
`rfDisciplinedEdgesOk`; `cfg_ws_init` ↦ `cfgWsInit`; `gev_reads_ev` ↦
`gevReadsEv`; `gev_ts_ev` ↦ `gevTsEv`; `cfg_ws_init_init` ↦ `cfgWsInitInit`;
`cfg_ws_init_promise_step` ↦ `cfgWsInitPromiseStep`; `cfg_ws_init_promise_run`
↦ `cfgWsInitPromiseRun`; `ptraces_of_fwd_own` ↦ `ptracesOfFwdOwn`;
`on_cycle_rf` ↦ `onCycleRf`; `rtc_gdep_first_cross` ↦ `rtcGdepFirstCross`;
`on_cycle_rf_advance` ↦ `onCycleRfAdvance`; `on_cycle_rf_bounded` ↦
`onCycleRfBounded`; `on_cycle_rf_empty` ↦ `onCycleRfEmpty`;
`gdep_acyclic_edges_ok` ↦ `gdepAcyclicEdgesOk`; `gdep_acyclic_disciplined` ↦
`gdepAcyclicDisciplined`; `wp_behavior_gdep_acyclic` ↦ `wpBehaviorGdepAcyclic`.

**Not ported:** nothing.

**Statements checked** (by hand, against Rocq): all of them.
-/
import Weak.WeakRobustGraph

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std Wlabel

/-! ## `WeakMem`-level facts owed to the lift batch -/

theorem WeakRobustAcyc.wsLeVwNew (w1 w2 : Wstate) : wsLe w1 w2 → w1.wVwNew ≤ w2.wVwNew :=
  Weak.wsLeVwNew w1 w2

theorem WeakRobustAcyc.loadPostFoldVwNewAq (vpre : Nat) (ats : List (Int × Nat)) (ws : Wstate)
    (a : Int) (t : Nat) :
    (a, t) ∈ ats →
    t ≤ (ats.foldl (fun w at_ => loadPostAt w true vpre at_.1 at_.2) ws).wVwNew :=
  Weak.loadPostFoldVwNewAq vpre ats ws a t

/-- An ACQUIRE load pushes every byte's timestamp into `wVwNew` — the
reader-side ordering S1's aq arm rests on. -/
theorem WeakRobustAcyc.loadPostRunVwNewAq (ws : Wstate) (base : Int) (ts : List Nat) (j t : Nat) :
    ts[j]? = some t → t ≤ (loadPostRun ws true base ts).wVwNew :=
  Weak.loadPostRunVwNewAq ws base ts j t

/-! ## Label shapes the discipline speaks about -/

/-- Does the label's READ half carry `aq`? -/
def WeakRobustAcyc.lbAq (l : Wlabel) : Bool :=
  match l with
  | LLoad aq _ _ _ _ => aq
  | LRmw aq _ _ _ _ _ _ => aq
  | LExLoad aq _ _ _ => aq
  | LSilent | LStore .. | LFence .. | LDev | LRegW .. | LCtrl _ | LInstr | LExStore ..
  | LIFetch .. => false

/-- Is the label a `fence r, rw`-or-stronger — `pr` and `sw`?  Exactly the two
bits `fencePost` needs to route `wVrOld` into `wVwNew`. -/
def lbFencePrsw (l : Wlabel) : Prop :=
  match l with
  | LFence pr _ _ sw => pr = true ∧ sw = true
  | LSilent | LLoad .. | LStore .. | LRmw .. | LDev | LRegW .. | LCtrl _ | LInstr
  | LExLoad .. | LExStore .. | LIFetch .. => False

/-! ## DELIVERABLE 1: THE `fwdOwn` INVARIANT -/

/-- A forward-bank entry of agent `i`'s wstate names an OWN-authored log
position (timestamp `p + 1` is log position `p`; timestamp 0 is excluded). -/
def fwdOwn (log : List Wmsg) (i : Nat) (ws : Wstate) : Prop :=
  ∀ a tf vf, get? ws.wFwd a = some (tf, vf) →
    0 < tf ∧ ∃ m, log[tf - 1]? = some m ∧ m.wmTid = some i

theorem fwdOwnInit (log : List Wmsg) (i : Nat) : fwdOwn log i wsInit := by
  intro a tf vf h
  have he : get? wsInit.wFwd a = none := lookupEmpty
  rw [he] at h; cases h

/-- THE COROLLARY's premise: the read is `aq` (forwarding is disabled
outright) OR its source message is authored by somebody else. -/
def readUnforwarded (log : List Wmsg) (i : Nat) (l : Wlabel) (ts : Nat) : Prop :=
  WeakRobustAcyc.lbAq l = true ∨ ∃ m j, log[ts - 1]? = some m ∧ m.wmTid = some j ∧ j ≠ i

/-- A foreign read is never forwarded. -/
theorem fwdOwnReadUnforwarded (log : List Wmsg) (i : Nat) (ws : Wstate) (l : Wlabel) (a : Int)
    (ts : Nat) :
    fwdOwn log i ws → readUnforwarded log i l ts →
    fwdView ws (WeakRobustAcyc.lbAq l) a ts = ts := by
  rintro hfo (haq | ⟨m, j, hm, htid, hne⟩)
  · rw [haq]; rfl
  · unfold fwdView
    split
    · rfl
    · split
      · next tf vf hf =>
        split
        · next heq =>
          subst heq
          obtain ⟨_, m', hm', htid'⟩ := hfo a ts vf hf
          rw [hm] at hm'; cases hm'
          rw [htid] at htid'; cases htid'
          exact absurd rfl hne
        · rfl
      · rfl

/-! ## `astepOk`-level arithmetic (the four facts S1 consumes) -/

section astep

variable {P : Type}

/-- `fwdOwn` is a step invariant: only the store post-run inserts into the
bank, at the FULFILLED timestamp, whose message `astepOk` pins to agent `i`. -/
theorem astepOkFwdOwn (img : Image) (log : List Wmsg) (i : Nat) (ag : Wpagent P) (l : Wlabel)
    (f : Wstate → Wstate) (Dl : Option Nat) :
    astepOk img log i ag l f Dl → ∀ w, fwdOwn log i w → fwdOwn log i (f w) := by
  intro h w hw a tf vf hlk
  cases l with
  | LSilent => obtain ⟨rfl, _⟩ := h; exact hw a tf vf hlk
  | LLoad aq lat base tvs asrc =>
    obtain ⟨_, rfl, _⟩ := h
    dsimp only at hlk; rw [loadPostRunDFwd] at hlk; exact hw a tf vf hlk
  | LStore rl base data asrc vsrc =>
    obtain ⟨ts, k, _, hlog, ⟨_, hext⟩, rfl, _⟩ := h
    rcases storePostRunDFwdInv _ _ _ _ _ _ _ a tf vf hlk with ⟨rfl, _⟩ | hlk
    · exact ⟨by omega, _, hlog, rfl⟩
    · exact hw a tf vf hlk
  | LRmw aq rl base tvs data asrc vsrc =>
    obtain ⟨ts, k, _, _, hlog, _, _, ⟨_, hext⟩, rfl, _⟩ := h
    rcases storePostRunDFwdInv _ _ _ _ _ _ _ a tf vf hlk with ⟨rfl, _⟩ | hlk
    · exact ⟨by omega, _, hlog, rfl⟩
    · rw [loadPostRunDFwd] at hlk; exact hw a tf vf hlk
  | LFence pr pw sr sw =>
    obtain ⟨rfl, _⟩ := h
    dsimp only at hlk; rw [fencePostFwd] at hlk; exact hw a tf vf hlk
  | LDev => obtain ⟨rfl, _⟩ := h; exact hw a tf vf hlk
  | LRegW rd srcs => obtain ⟨rfl, _⟩ := h; exact hw a tf vf hlk
  | LCtrl srcs => obtain ⟨rfl, _⟩ := h; exact hw a tf vf hlk
  | LInstr => obtain ⟨rfl, _⟩ := h; exact hw a tf vf hlk
  -- THE RMW SPLIT (S2)
  | LExLoad aq base tvs asrc =>
    obtain ⟨_, rfl, _⟩ := h
    dsimp only at hlk; rw [exloadPostRunDFwd] at hlk; exact hw a tf vf hlk
  | LExStore rl base data asrc vsrc =>
    obtain ⟨ts, k, R, _, hlog, _, _, _, _, ⟨_, hext⟩, rfl, _⟩ := h
    rcases storePostRunDFwdInv _ _ _ _ _ _ _ a tf vf hlk with ⟨rfl, _⟩ | hlk
    · exact ⟨by omega, _, hlog, rfl⟩
    · exact hw a tf vf hlk
  | LIFetch base tvs => obtain ⟨_, rfl, _⟩ := h; exact hw a tf vf hlk

/-- EXT, in the form the measure wants: the fulfilling step's PRE-state write
floor is strictly below the timestamp it fulfils. -/
theorem astepOkFulfilExt (img : Image) (log : List Wmsg) (i : Nat) (ag : Wpagent P) (l : Wlabel)
    (f : Wstate → Wstate) (ts : Nat) :
    astepOk img log i ag l f (some ts) → ag.paWs.wVwNew < ts := by
  intro h
  cases l with
  | LSilent => obtain ⟨_, ⟨⟩⟩ := h
  | LLoad => obtain ⟨_, _, ⟨⟩⟩ := h
  | LStore =>
    obtain ⟨ts', k, _, _, ⟨_, hext⟩, _, hD⟩ := h
    cases hD; exact Nat.lt_of_le_of_lt (fulfilVpreDVwNew _ _ _) hext
  | LRmw =>
    obtain ⟨ts', k, _, _, _, _, _, ⟨_, hext⟩, _, hD⟩ := h
    cases hD
    exact Nat.lt_of_le_of_lt
      (Nat.le_trans (wsLeVwNew _ _ (loadPostRunDLe _ _ _ _ _)) (fulfilVpreDVwNew _ _ _)) hext
  | LFence => obtain ⟨_, ⟨⟩⟩ := h
  | LDev => obtain ⟨_, ⟨⟩⟩ := h
  | LRegW => obtain ⟨_, ⟨⟩⟩ := h
  | LCtrl => obtain ⟨_, ⟨⟩⟩ := h
  | LInstr => obtain ⟨_, ⟨⟩⟩ := h
  -- THE RMW SPLIT (S2): the conditional write is `LStore`'s arm
  | LExLoad => obtain ⟨_, _, ⟨⟩⟩ := h
  | LExStore =>
    obtain ⟨ts', k, R, _, _, _, _, _, _, ⟨_, hext⟩, _, hD⟩ := h
    cases hD; exact Nat.lt_of_le_of_lt (fulfilVpreDVwNew _ _ _) hext
  | LIFetch => obtain ⟨_, _, ⟨⟩⟩ := h

/-- THE SAME-STEP CASE, quantitatively: when the entry read and the exit
fulfil are the SAME `LRmw` event, the read half's `coh` gain is checked by the
write half's own `fulfilOkD`, giving the strict inequality. -/
theorem astepOkReadFulfilLt (img : Image) (log : List Wmsg) (i : Nat) (ag : Wpagent P)
    (l : Wlabel) (f : Wstate → Wstate) (ts ts' : Nat) (a : Int) :
    astepOk img log i ag l f (some ts') → (a, ts) ∈ lbReads l → ts < ts' := by
  intro h hin
  cases l with
  | LLoad => obtain ⟨_, _, ⟨⟩⟩ := h
  | LRmw aq rl base tvs data asrc vsrc =>
    obtain ⟨tsf, k, hlen, _, _, _, _, ⟨hcoh, _⟩, _, hD⟩ := h
    cases hD
    obtain ⟨j, v, hj, rfl⟩ := (memTvsReads _ _ _ _).1 hin
    have hts : (tvs.map Prod.fst)[j]? = some ts := by rw [List.getElem?_map, hj]; rfl
    have hjlt : j < data.length := by rw [← hlen]; exact lookup_lt_Some hj
    have hge := loadPostRunDCoh ag.paWs aq (srcsView ag.paWs asrc) base (tvs.map Prod.fst) j ts hts
    have hlt := hcoh j hjlt
    omega
  -- THE RMW SPLIT (S2): vacuous on both halves
  | LExLoad => obtain ⟨_, _, ⟨⟩⟩ := h
  | _ => simp [lbReads] at hin

/-- THE AQ ARM's gain: an acquire read joins its timestamp into `wVwNew`. -/
theorem astepOkReadVwNewAq (img : Image) (log : List Wmsg) (i : Nat) (ag : Wpagent P)
    (l : Wlabel) (f : Wstate → Wstate) (Dl : Option Nat) (a : Int) (ts : Nat) :
    astepOk img log i ag l f Dl → WeakRobustAcyc.lbAq l = true → (a, ts) ∈ lbReads l →
    ts ≤ (f ag.paWs).wVwNew := by
  intro h haq hin
  cases l with
  | LLoad aq lat base tvs asrc =>
    obtain ⟨_, rfl, _⟩ := h
    simp only [WeakRobustAcyc.lbAq] at haq; subst haq
    obtain ⟨j, v, hj, rfl⟩ := (memTvsReads _ _ _ _).1 hin
    have hts : (tvs.map Prod.fst)[j]? = some ts := by rw [List.getElem?_map, hj]; rfl
    exact Nat.le_trans (WeakRobustAcyc.loadPostRunVwNewAq ag.paWs base _ j ts hts)
      (wsLeVwNew _ _ (loadPostRunDMono _ _ _ _ _))
  | LRmw aq rl base tvs data asrc vsrc =>
    obtain ⟨_, _, _, _, _, _, _, _, rfl, _⟩ := h
    simp only [WeakRobustAcyc.lbAq] at haq; subst haq
    obtain ⟨j, v, hj, rfl⟩ := (memTvsReads _ _ _ _).1 hin
    have hts : (tvs.map Prod.fst)[j]? = some ts := by rw [List.getElem?_map, hj]; rfl
    exact Nat.le_trans (WeakRobustAcyc.loadPostRunVwNewAq ag.paWs base _ j ts hts)
      (Nat.le_trans (wsLeVwNew _ _ (loadPostRunDMono _ _ _ _ _))
        (wsLeVwNew _ _ (storePostRunDLe _ _ _ _ _ _ _)))
  -- THE RMW SPLIT (S2), D-2r: the exclusive read's byte fold IS the plain one
  | LExLoad aq base tvs asrc =>
    obtain ⟨_, rfl, _⟩ := h
    simp only [WeakRobustAcyc.lbAq] at haq; subst haq
    obtain ⟨j, v, hj, rfl⟩ := (memTvsReads _ _ _ _).1 hin
    have hts : (tvs.map Prod.fst)[j]? = some ts := by rw [List.getElem?_map, hj]; rfl
    exact WeakRobustAcyc.loadPostRunVwNewAq ag.paWs base _ j ts hts
  | _ => simp [lbReads] at hin

/-- THE FENCE ARM's gain, half 1: an UNFORWARDED read joins its timestamp into
`wVrOld` (this is where `fwdOwn` pays). -/
theorem astepOkReadVrOld (img : Image) (log : List Wmsg) (i : Nat) (ag : Wpagent P)
    (l : Wlabel) (f : Wstate → Wstate) (Dl : Option Nat) (a : Int) (ts : Nat) :
    astepOk img log i ag l f Dl →
    fwdView ag.paWs (WeakRobustAcyc.lbAq l) a ts = ts →
    (a, ts) ∈ lbReads l →
    ts ≤ (f ag.paWs).wVrOld := by
  intro h hfv hin
  cases l with
  | LLoad aq lat base tvs asrc =>
    obtain ⟨_, rfl, _⟩ := h
    obtain ⟨j, v, hj, rfl⟩ := (memTvsReads _ _ _ _).1 hin
    have hts : (tvs.map Prod.fst)[j]? = some ts := by rw [List.getElem?_map, hj]; rfl
    exact Nat.le_trans (loadPostRunVrOld' ag.paWs aq base _ j ts hts hfv)
      (wsLeVrOld _ _ (loadPostRunDMono _ _ _ _ _))
  | LRmw aq rl base tvs data asrc vsrc =>
    obtain ⟨_, _, _, _, _, _, _, _, rfl, _⟩ := h
    obtain ⟨j, v, hj, rfl⟩ := (memTvsReads _ _ _ _).1 hin
    have hts : (tvs.map Prod.fst)[j]? = some ts := by rw [List.getElem?_map, hj]; rfl
    exact Nat.le_trans (loadPostRunVrOld' ag.paWs aq base _ j ts hts hfv)
      (Nat.le_trans (wsLeVrOld _ _ (loadPostRunDMono _ _ _ _ _))
        (wsLeVrOld _ _ (storePostRunDLe _ _ _ _ _ _ _)))
  -- THE RMW SPLIT (S2), D-2r: no monotonicity bridge
  | LExLoad aq base tvs asrc =>
    obtain ⟨_, rfl, _⟩ := h
    obtain ⟨j, v, hj, rfl⟩ := (memTvsReads _ _ _ _).1 hin
    have hts : (tvs.map Prod.fst)[j]? = some ts := by rw [List.getElem?_map, hj]; rfl
    exact loadPostRunVrOld' ag.paWs aq base _ j ts hts hfv
  | _ => simp [lbReads] at hin

/-- THE FENCE ARM's gain, half 2: a `pr ∧ sw` fence ships `wVrOld` into
`wVwNew`. -/
theorem astepOkFenceVwNew (img : Image) (log : List Wmsg) (i : Nat) (ag : Wpagent P)
    (l : Wlabel) (f : Wstate → Wstate) (Dl : Option Nat) :
    astepOk img log i ag l f Dl → lbFencePrsw l → ag.paWs.wVrOld ≤ (f ag.paWs).wVwNew := by
  intro h hf
  cases l with
  | LFence pr pw sr sw =>
    obtain ⟨rfl, _⟩ := h
    obtain ⟨rfl, rfl⟩ := hf
    exact fencePostVwNewR _ _ _
  | _ => cases hf

end astep

/-! ## DELIVERABLE 2: READER DISCIPLINE -/

/-- Event `k` reads with `aq = true`, or a `pr ∧ sw` fence sits strictly
between `k` and `k'` (the reader's next fulfil on the cycle). -/
def disciplined {P D : Type} (T : Atrace P D) (k k' : Nat) : Prop :=
  (∃ ev, T.atEvs[k]? = some ev ∧ WeakRobustAcyc.lbAq ev.aeLb = true) ∨
  (∃ k0 ev0, k < k0 ∧ k0 < k' ∧ T.atEvs[k0]? = some ev0 ∧ lbFencePrsw ev0.aeLb)

/-- THE SECOND WAY an edge can be harmless (the critical-section shape): the
reader's write floor in the PRE-state of event `k` already covers `ts`. -/
def covered {P D : Type} (T : Atrace P D) (k : Nat) (ts : Nat) : Prop :=
  ∃ ag, T.atAgs[k]? = some ag ∧ ts ≤ ag.paWs.wVwNew

/-- THE PER-EDGE OBLIGATION: disciplined, or already covered at the read. -/
def edgeOk {P D : Type} (T : Atrace P D) (k k' : Nat) (ts : Nat) : Prop :=
  disciplined T k k' ∨ covered T k ts

theorem edgeOkDisciplined {P D : Type} (T : Atrace P D) (k k' ts : Nat) :
    disciplined T k k' → edgeOk T k k' ts := Or.inl

theorem edgeOkCovered {P D : Type} (T : Atrace P D) (k k' ts : Nat) :
    covered T k ts → edgeOk T k k' ts := Or.inr

/-! ## A0: COVERAGE AT THE *FULFIL*, NOT AT THE READ

`fulfilVext ws l` is exactly the EXT view `astepOk` passes to `fulfilOkD` in its
fulfilling arms (the dependency-carrying pre-view; for `LRmw`, at the POST-LOAD
state), and `none` on the non-fulfilling labels.  For `LExStore` it uses the
reservation's `resView` (state-only, so it cannot see the classifier; the
`astepOk` arm DOMINATES it, `astepOkFulfilVext`). -/

def fulfilVext (ws : Wstate) (l : Wlabel) : Option Nat :=
  match l with
  | LStore rl _ _ asrc vsrc =>
      some (fulfilVpreD ws rl (max (srcsView ws asrc) (srcsView ws vsrc)))
  | LRmw aq rl base tvs _ asrc vsrc =>
      some (fulfilVpreD (loadPostRunD ws aq (srcsView ws asrc) base (tvs.map Prod.fst)) rl
        (max (max (srcsView ws asrc) (srcsView ws vsrc))
          (ldvOf ws aq (srcsView ws asrc) base (tvs.map Prod.fst))))
  | LExStore rl _ _ asrc vsrc =>
      some (fulfilVpreD ws rl (max (max (srcsView ws asrc) (srcsView ws vsrc)) (resView ws)))
  | LSilent | LLoad .. | LFence .. | LDev | LRegW .. | LCtrl _ | LInstr | LExLoad ..
  | LIFetch .. => none

/-- `wVwNew` is a lower bound of the EXT view. -/
theorem fulfilVextVwNew (ws : Wstate) (l : Wlabel) (v : Nat) :
    fulfilVext ws l = some v → ws.wVwNew ≤ v := by
  intro h
  cases l with
  | LStore => simp only [fulfilVext, Option.some.injEq] at h; rw [← h]; exact fulfilVpreDVwNew _ _ _
  | LRmw =>
    simp only [fulfilVext, Option.some.injEq] at h; rw [← h]
    exact Nat.le_trans (wsLeVwNew _ _ (loadPostRunDLe _ _ _ _ _)) (fulfilVpreDVwNew _ _ _)
  | LExStore =>
    simp only [fulfilVext, Option.some.injEq] at h; rw [← h]; exact fulfilVpreDVwNew _ _ _
  | _ => simp [fulfilVext] at h

/-- THE RELATIVIZED COVERAGE: the fulfil at `k'` checks EXT at a view that
already includes `ts` (the PRE-state of step `k'`, run through an `LRmw`'s own
read half). -/
def fcov {P D : Type} (T : Atrace P D) (k' : Nat) (ts : Nat) : Prop :=
  ∃ ag ev v, T.atAgs[k']? = some ag ∧ T.atEvs[k']? = some ev ∧
    fulfilVext ag.paWs ev.aeLb = some v ∧ ts ≤ v

theorem fcovMonoTs {P D : Type} (T : Atrace P D) (k' ts ts' : Nat) :
    fcov T k' ts → ts' ≤ ts → fcov T k' ts' := by
  rintro ⟨ag, ev, v, h1, h2, h3, h4⟩ h
  exact ⟨ag, ev, v, h1, h2, h3, by omega⟩

/-- THE PER-EDGE OBLIGATION, RELATIVIZED (A0); weaker than `edgeOk`. -/
def edgeOkF {P D : Type} (T : Atrace P D) (k k' : Nat) (ts : Nat) : Prop :=
  disciplined T k k' ∨ fcov T k' ts

theorem edgeOkFDisciplined {P D : Type} (T : Atrace P D) (k k' ts : Nat) :
    disciplined T k k' → edgeOkF T k k' ts := Or.inl

theorem edgeOkFFcov {P D : Type} (T : Atrace P D) (k k' ts : Nat) :
    fcov T k' ts → edgeOkF T k k' ts := Or.inr

/-- EXT, RELATIVIZED: a fulfilling step's `fulfilVext` is strictly below the
fulfilled timestamp.  For `LExStore` (the walker gate, layer2 §13) the arm's
EXT argument dominates `fulfilVext`'s, and `fulfilOkDMono` transfers it down. -/
theorem astepOkFulfilVext {P : Type} (img : Image) (log : List Wmsg) (i : Nat) (ag : Wpagent P)
    (l : Wlabel) (f : Wstate → Wstate) (ts : Nat) :
    astepOk img log i ag l f (some ts) → ∃ v, fulfilVext ag.paWs l = some v ∧ v < ts := by
  intro h
  cases l with
  | LSilent => obtain ⟨_, ⟨⟩⟩ := h
  | LLoad => obtain ⟨_, _, ⟨⟩⟩ := h
  | LStore =>
    obtain ⟨ts', k, _, _, ⟨_, hext⟩, _, hD⟩ := h
    cases hD; exact ⟨_, rfl, hext⟩
  | LRmw =>
    obtain ⟨ts', k, _, _, _, _, _, ⟨_, hext⟩, _, hD⟩ := h
    cases hD; exact ⟨_, rfl, hext⟩
  | LFence => obtain ⟨_, ⟨⟩⟩ := h
  | LDev => obtain ⟨_, ⟨⟩⟩ := h
  | LRegW => obtain ⟨_, ⟨⟩⟩ := h
  | LCtrl => obtain ⟨_, ⟨⟩⟩ := h
  | LInstr => obtain ⟨_, ⟨⟩⟩ := h
  -- THE RMW SPLIT (S2)
  | LExLoad => obtain ⟨_, _, ⟨⟩⟩ := h
  | LExStore rl base data asrc vsrc =>
    obtain ⟨ts', k, R, _, _, hres, _, _, _, hful, _, hD⟩ := h
    cases hD
    refine ⟨_, rfl, ?_⟩
    rw [resViewSome _ _ hres]
    exact (fulfilOkDMono _ _ _ _ _ _ _ (exstoreVdGe img log ag.paWs base data asrc vsrc R) hful).2
  | LIFetch => obtain ⟨_, _, ⟨⟩⟩ := h

/-! ## Along a trace -/

section trace

variable {P D : Type}
variable (pstep : P → D → Wlabel → P → D → Prop)

theorem astepsFwdOwn (img : Image) (log : List Wmsg) (i : Nat) (ags : List (Wpagent P))
    (evs : List (Aev D)) (ag0 : Wpagent P) :
    astepsWf pstep img log i ags evs →
    ags[0]? = some ag0 → fwdOwn log i ag0.paWs →
    ∀ (k : Nat) (ag : Wpagent P), ags[k]? = some ag → fwdOwn log i ag.paWs := by
  intro hwf h0 hfo0 k
  induction k with
  | zero => intro ag hag; rw [h0] at hag; cases hag; exact hfo0
  | succ k ih =>
    intro ag hag
    have hlt : k < evs.length := by have := lookup_lt_Some hag; have := hwf.1; omega
    obtain ⟨ev, hev⟩ := Option.isSome_iff_exists.1 (lookup_lt_is_Some_2 hlt)
    obtain ⟨a1, a2, st', f, ha1, ha2, _, hok, heq⟩ :=
      astepsWfStep pstep img log i ags evs k ev hwf hev
    rw [hag] at ha2; cases ha2
    rw [heq]
    exact astepOkFwdOwn img log i a1 ev.aeLb f ev.aeTs hok a1.paWs (ih a1 ha1)

theorem atraceFwdOwn (img : Image) (log : List Wmsg) (i : Nat) (T : Atrace P D)
    (ag0 : Wpagent P) :
    atraceWf pstep img log i T →
    T.atAgs[0]? = some ag0 → fwdOwn log i ag0.paWs →
    ∀ (k : Nat) (ag : Wpagent P), T.atAgs[k]? = some ag → fwdOwn log i ag.paWs :=
  astepsFwdOwn pstep img log i T.atAgs T.atEvs ag0

/-! ### DELIVERABLE 3: THE SEGMENT LEMMA S1

An OK read of `ts` at `k` followed at `k' > k` by a fulfil of `ts'` forces
`ts < ts'`.  Every arm pushes `ts` into `wVwNew` at or before `k'` (the aq arm
at the read, the fence arm at the fence, the `fcov` arm in the fulfil's own EXT
view); `wVwNew` only grows along the trace and EXT closes at `k'`.  The
foreignness premise `readUnforwarded` is discharged at the call site: an own
read never sits on a cross-agent cycle (`atraceOwnRead`). -/

theorem atraceS1F (img : Image) (log : List Wmsg) (i : Nat) (T : Atrace P D) (k k' : Nat)
    (ev ev' : Aev D) (a : Int) (ts ts' : Nat) :
    atraceWf pstep img log i T →
    (∀ (n : Nat) (ag : Wpagent P), T.atAgs[n]? = some ag → fwdOwn log i ag.paWs) →
    T.atEvs[k]? = some ev →
    (a, ts) ∈ lbReads ev.aeLb →
    readUnforwarded log i ev.aeLb ts →
    T.atEvs[k']? = some ev' →
    ev'.aeTs = some ts' →
    k < k' →
    edgeOkF T k k' ts →
    ts < ts' := by
  intro hwf hfo hev hin hunf hev' hts' hlt hdisc
  -- the READ step
  obtain ⟨ag, agn, st1, f, hag, hagn, _, hok, hagne⟩ :=
    astepsWfStep pstep img log i T.atAgs T.atEvs k ev hwf hev
  -- the FULFIL step
  obtain ⟨ag', agn', st2, f', hag', _, _, hok', _⟩ :=
    astepsWfStep pstep img log i T.atAgs T.atEvs k' ev' hwf hev'
  rw [hts'] at hok'
  have hext := astepOkFulfilExt img log i ag' ev'.aeLb f' ts' hok'
  have hfv : fwdView ag.paWs (WeakRobustAcyc.lbAq ev.aeLb) a ts = ts :=
    fwdOwnReadUnforwarded log i ag.paWs ev.aeLb a ts (hfo k ag hag) hunf
  rcases hdisc with hdisc | ⟨agc, evc, vc, hagc, hevc, hvext, hlev⟩
  rotate_left
  · -- THE `fcov` ARM: the fulfil's own EXT view already covers `ts`
    rw [hag'] at hagc; cases hagc
    rw [hev'] at hevc; cases hevc
    obtain ⟨v', hv', hltv⟩ := astepOkFulfilVext img log i ag' ev'.aeLb f' ts' hok'
    rw [hvext] at hv'; cases hv'
    omega
  -- IT SUFFICES to push `ts` into `wVwNew` anywhere at or before `k'`
  suffices hsuff : ∃ n agm, n ≤ k' ∧ T.atAgs[n]? = some agm ∧ ts ≤ agm.paWs.wVwNew by
    obtain ⟨n, agm, hn, hagm, hge⟩ := hsuff
    have hle :=
      wsLeVwNew _ _ (astepsWsLe pstep img log i T.atAgs T.atEvs n k' agm ag' hwf hn hagm hag')
    omega
  rcases hdisc with ⟨ev0, hev0, haq⟩ | ⟨k0, ev0, hk0, hk0', hev0, hfen⟩
  · -- THE AQ ARM: the read itself lands in `wVwNew`
    rw [hev] at hev0; cases hev0
    refine ⟨k + 1, agn, by omega, hagn, ?_⟩
    rw [hagne]
    exact astepOkReadVwNewAq img log i ag ev.aeLb f ev.aeTs a ts hok haq hin
  · -- THE FENCE ARM: the read lands in `wVrOld`; the fence ships it
    have hro : ts ≤ agn.paWs.wVrOld := by
      rw [hagne]; exact astepOkReadVrOld img log i ag ev.aeLb f ev.aeTs a ts hok hfv hin
    have hlt0 : k0 < T.atAgs.length := by have := lookup_lt_Some hev0; have := hwf.1; omega
    obtain ⟨ag0, hag0⟩ := Option.isSome_iff_exists.1 (lookup_lt_is_Some_2 hlt0)
    have hro0 : ts ≤ ag0.paWs.wVrOld := Nat.le_trans hro
      (wsLeVrOld _ _
        (astepsWsLe pstep img log i T.atAgs T.atEvs (k + 1) k0 agn ag0 hwf (by omega) hagn hag0))
    obtain ⟨b0, b1, st3, f0, hb0, hb1, _, hok0, hb1e⟩ :=
      astepsWfStep pstep img log i T.atAgs T.atEvs k0 ev0 hwf hev0
    rw [hag0] at hb0; cases hb0
    refine ⟨k0 + 1, b1, by omega, hb1, ?_⟩
    rw [hb1e]
    exact Nat.le_trans hro0 (astepOkFenceVwNew img log i ag0 ev0.aeLb f0 ev0.aeTs hok0 hfen)

/-! ### A0: `covered` IS AN `fcov`, AND `edgeOk` AN `edgeOkF` -/

theorem coveredFcov (img : Image) (log : List Wmsg) (i : Nat) (T : Atrace P D) (k k' ts : Nat)
    (ev' : Aev D) :
    atraceWf pstep img log i T →
    covered T k ts → k ≤ k' →
    T.atEvs[k']? = some ev' → ev'.aeTs.isSome →
    fcov T k' ts := by
  rintro hwf ⟨ag, hag, hge⟩ hle hev' hsome
  obtain ⟨ts', hts'⟩ := Option.isSome_iff_exists.1 hsome
  obtain ⟨ag', agn', st2, f', hag', _, _, hok', _⟩ :=
    astepsWfStep pstep img log i T.atAgs T.atEvs k' ev' hwf hev'
  rw [hts'] at hok'
  obtain ⟨v, hv, _⟩ := astepOkFulfilVext img log i ag' ev'.aeLb f' ts' hok'
  refine ⟨ag', ev', v, hag', hev', hv, ?_⟩
  have hvw :=
    wsLeVwNew _ _ (astepsWsLe pstep img log i T.atAgs T.atEvs k k' ag ag' hwf hle hag hag')
  have hb := fulfilVextVwNew ag'.paWs ev'.aeLb v hv
  omega

theorem edgeOkEdgeOkF (img : Image) (log : List Wmsg) (i : Nat) (T : Atrace P D)
    (k k' ts : Nat) (ev' : Aev D) :
    atraceWf pstep img log i T → k ≤ k' →
    T.atEvs[k']? = some ev' → ev'.aeTs.isSome →
    edgeOk T k k' ts → edgeOkF T k k' ts := by
  rintro hwf hle hev' hsome (hd | hcov)
  · exact Or.inl hd
  · exact Or.inr (coveredFcov pstep img log i T k k' ts ev' hwf hcov hle hev' hsome)

/-- S1, in its ORIGINAL `edgeOk` form. -/
theorem atraceS1 (img : Image) (log : List Wmsg) (i : Nat) (T : Atrace P D) (k k' : Nat)
    (ev ev' : Aev D) (a : Int) (ts ts' : Nat) :
    atraceWf pstep img log i T →
    (∀ (n : Nat) (ag : Wpagent P), T.atAgs[n]? = some ag → fwdOwn log i ag.paWs) →
    T.atEvs[k]? = some ev →
    (a, ts) ∈ lbReads ev.aeLb →
    readUnforwarded log i ev.aeLb ts →
    T.atEvs[k']? = some ev' →
    ev'.aeTs = some ts' →
    k < k' →
    edgeOk T k k' ts →
    ts < ts' := by
  intro hwf hfo hev hin hunf hev' hts' hlt hok
  exact atraceS1F pstep img log i T k k' ev ev' a ts ts' hwf hfo hev hin hunf hev' hts' hlt
    (edgeOkEdgeOkF pstep img log i T k k' ts ev' hwf (by omega) hev' (by rw [hts']; rfl) hok)

/-- S1 with the SAME-STEP case folded in: `k ≤ k'`, and `edgeOkF` is demanded
only when the positions differ (an `LRmw` can be both the entry read and the
exit fulfil; then `astepOkReadFulfilLt` needs no premise). -/
theorem atraceS1LeF (img : Image) (log : List Wmsg) (i : Nat) (T : Atrace P D) (k k' : Nat)
    (ev ev' : Aev D) (a : Int) (ts ts' : Nat) :
    atraceWf pstep img log i T →
    (∀ (n : Nat) (ag : Wpagent P), T.atAgs[n]? = some ag → fwdOwn log i ag.paWs) →
    T.atEvs[k]? = some ev →
    (a, ts) ∈ lbReads ev.aeLb →
    readUnforwarded log i ev.aeLb ts →
    T.atEvs[k']? = some ev' →
    ev'.aeTs = some ts' →
    k ≤ k' →
    (k < k' → edgeOkF T k k' ts) →
    ts < ts' := by
  intro hwf hfo hev hin hunf hev' hts' hle hdisc
  by_cases hk : k = k'
  · subst hk
    rw [hev] at hev'; cases hev'
    obtain ⟨ag, agn, st1, f, _, _, _, hok, _⟩ :=
      astepsWfStep pstep img log i T.atAgs T.atEvs k ev hwf hev
    rw [hts'] at hok
    exact astepOkReadFulfilLt img log i ag ev.aeLb f ts ts' a hok hin
  · exact atraceS1F pstep img log i T k k' ev ev' a ts ts' hwf hfo hev hin hunf hev' hts'
      (by omega) (hdisc (by omega))

/-- …and its ORIGINAL `edgeOk` spelling. -/
theorem atraceS1Le (img : Image) (log : List Wmsg) (i : Nat) (T : Atrace P D) (k k' : Nat)
    (ev ev' : Aev D) (a : Int) (ts ts' : Nat) :
    atraceWf pstep img log i T →
    (∀ (n : Nat) (ag : Wpagent P), T.atAgs[n]? = some ag → fwdOwn log i ag.paWs) →
    T.atEvs[k]? = some ev →
    (a, ts) ∈ lbReads ev.aeLb →
    readUnforwarded log i ev.aeLb ts →
    T.atEvs[k']? = some ev' →
    ev'.aeTs = some ts' →
    k ≤ k' →
    (k < k' → edgeOk T k k' ts) →
    ts < ts' := by
  intro hwf hfo hev hin hunf hev' hts' hle hdisc
  exact atraceS1LeF pstep img log i T k k' ev ev' a ts ts' hwf hfo hev hin hunf hev' hts' hle
    (fun hlt => edgeOkEdgeOkF pstep img log i T k k' ts ev' hwf (by omega) hev'
      (by rw [hts']; rfl) (hdisc hlt))

end trace

/-! ## The bundle-level premises -/

/-- Every wstate reachable in every trace of the bundle satisfies `fwdOwn`. -/
def ptracesFwdOwn {P D : Type} (TS : Ptraces P D) : Prop :=
  ∀ (i : Nat) (T : Atrace P D) (k : Nat) (ag : Wpagent P), TS.ptTrs[i]? = some T → T.atAgs[k]? = some ag → fwdOwn TS.ptLog i ag.paWs

/-- THE PER-EDGE PREMISE: every cross-agent rf edge into `e2` is `edgeOk`
relative to EVERY later fulfil of the reader — a property of the bundle alone
(no cycle quantifier), dischargeable at the racy-read and lock rules. -/
def rfEdgesOk {P D : Type} (TS : Ptraces P D) : Prop :=
  ∀ (e1 e2 : Gev) (T : Atrace P D) (ts : Nat) (a : Int) (k' : Nat) (ev' : Aev D),
    gevTs TS e1 = some ts → gevReads TS e2 a ts → e1.1 ≠ e2.1 →
    TS.ptTrs[e2.1]? = some T →
    e2.2 < k' →
    T.atEvs[k']? = some ev' → ev'.aeTs.isSome →
    edgeOk T e2.2 k' ts

/-- The ORIGINAL, discipline-only premise (strictly stronger). -/
def rfDisciplined {P D : Type} (TS : Ptraces P D) : Prop :=
  ∀ (e1 e2 : Gev) (T : Atrace P D) (k' : Nat) (ev' : Aev D),
    WeakRobustGraph.grf TS e1 e2 → e1.1 ≠ e2.1 →
    TS.ptTrs[e2.1]? = some T →
    e2.2 < k' →
    T.atEvs[k']? = some ev' → ev'.aeTs.isSome →
    disciplined T e2.2 k'

theorem rfDisciplinedEdgesOk {P D : Type} (TS : Ptraces P D) :
    rfDisciplined TS → rfEdgesOk TS := by
  intro H e1 e2 T ts a k' ev' hts hrd hne hT hlt hev' hsome
  exact Or.inl (H e1 e2 T k' ev' ⟨ts, a, hts, hrd⟩ hne hT hlt hev' hsome)

/-- Every agent's wstate is `wsInit` — the promise phase's invariant. -/
def cfgWsInit {P D : Type} (c : Wpcfg P D) : Prop :=
  ∀ (i : Nat) (ag : Wpagent P), c.pcAgs[i]? = some ag → ag.paWs = wsInit

section acyc

variable {P D : Type}
variable (pstep : P → D → Wlabel → P → D → Prop)
variable (pdev : P → Wlabel → P → Bool)

/-! ### From the bundle to the traces -/

theorem gevReadsEv (TS : Ptraces P D) (e : Gev) (a : Int) (ts : Nat) (T : Atrace P D) :
    TS.ptTrs[e.1]? = some T → gevReads TS e a ts →
    ∃ ev, T.atEvs[e.2]? = some ev ∧ (a, ts) ∈ lbReads ev.aeLb := by
  rintro hT ⟨l, hl, hin⟩
  obtain ⟨T', ev, hT', hev, rfl⟩ := gevLbSome TS e l hl
  rw [hT] at hT'; cases hT'
  exact ⟨ev, hev, hin⟩

theorem gevTsEv (TS : Ptraces P D) (e : Gev) (ts : Nat) (T : Atrace P D) :
    TS.ptTrs[e.1]? = some T → gevTs TS e = some ts →
    ∃ ev, T.atEvs[e.2]? = some ev ∧ ev.aeTs = some ts := by
  intro hT hts
  obtain ⟨T', ev, hT', hev, hts'⟩ := gevTsSome TS e ts hts
  rw [hT] at hT'; cases hT'
  exact ⟨ev, hev, hts'⟩

/-! ### `fwdOwn` is DERIVED, not assumed -/

theorem cfgWsInitInit (img : Image) (d0 : D) (ps : List P) :
    cfgWsInit (wpInit (P := P) (D := D) img d0 ps) := by
  intro i ag hlk
  simp only [wpInit, List.getElem?_map] at hlk
  cases hp : ps[i]? with
  | none => rw [hp] at hlk; cases hlk
  | some p => rw [hp] at hlk; cases hlk; rfl

/-- `wpPromiseStep` does not touch `paWs` (`promAdd` keeps the wstate). -/
theorem cfgWsInitPromiseStep (c c' : Wpcfg P D) :
    cfgWsInit c → wpPromiseStep c c' → cfgWsInit c' := by
  intro h hs
  obtain ⟨j, agj, base, data, k, hlkj, _, rfl⟩ := wpPromiseStepInv c c' hs
  intro i ag hlk
  by_cases hij : i = j
  · subst hij
    rw [list_lookup_insert (lookup_lt_Some hlkj)] at hlk
    cases hlk
    exact h i agj hlkj
  · rw [list_lookup_insert_ne (Ne.symm hij)] at hlk
    exact h i ag hlk

theorem cfgWsInitPromiseRun (c c' : Wpcfg P D) :
    cfgWsInit c → rtc (wpPromiseStep (P := P) (D := D)) c c' → cfgWsInit c' := by
  intro h0 hr
  induction hr with
  | refl => exact h0
  | tail _ hs ih => exact cfgWsInitPromiseStep _ _ ih hs

theorem ptracesOfFwdOwn (TS : Ptraces P D) (mid c : Wpcfg P D) :
    cfgWsInit mid → ptracesOf pstep TS mid c → ptracesFwdOwn TS := by
  rintro hinit ⟨_, _, _, hwf, hfst, _⟩ i T k ag hT hag
  have hwfi := hwf i T hT
  obtain ⟨ag0, hag0⟩ :=
    Option.isSome_iff_exists.1 (atraceFirstIsSome pstep TS.ptImg TS.ptLog i T hwfi)
  have hmid : mid.pcAgs[i]? = some ag0 := by rw [← hfst i T hT]; exact hag0
  refine atraceFwdOwn pstep TS.ptImg TS.ptLog i T ag0 hwfi hag0 ?_ k ag hag
  rw [hinit i ag0 hmid]
  exact fwdOwnInit _ _

/-! ### DELIVERABLE 4: THE MEASURE -/

/-- A cross-agent rf edge SITS ON A CYCLE when its reader can reach its source
again (the shape `tcGdepCross` hands over). -/
def onCycleRf (TS : Ptraces P D) (ts : Nat) : Prop :=
  ∃ (e1 e2 : Gev) (a : Int), gevTs TS e1 = some ts ∧ gevReads TS e2 a ts ∧
    e1.1 ≠ e2.1 ∧ rtc (gdep TS) e2 e1

/-- THE CYCLE WALK, one step: follow the path from the reader until it leaves
the agent; the departing edge is cross-agent hence rf, sourced at a fulfil of
the same agent at a trace index `≥` the reader's. -/
theorem rtcGdepFirstCross (TS : Ptraces P D) (u v : Gev) :
    ptracesWf pstep TS → rtc (gdep TS) u v → u.1 ≠ v.1 →
    ∃ x y, u.1 = x.1 ∧ rtc (gdep TS) u x ∧ u.2 ≤ x.2 ∧
      WeakRobustGraph.grf TS x y ∧ x.1 ≠ y.1 ∧ rtc (gdep TS) y v := by
  intro hwf hr
  refine rtc_ind_l (R := gdep TS)
    (fun u => u.1 ≠ v.1 → ∃ x y, u.1 = x.1 ∧ rtc (gdep TS) u x ∧ u.2 ≤ x.2 ∧
      WeakRobustGraph.grf TS x y ∧ x.1 ≠ y.1 ∧ rtc (gdep TS) y v)
    v (fun h => absurd rfl h) ?_ u hr
  intro u w huw hwv ih hne
  by_cases hag : u.1 = w.1
  · have hlt := gdepSameAgentLt pstep TS u w hwf huw hag
    obtain ⟨x, y, hx1, hrx, hx2, hrf, hxy, hry⟩ := ih (by rw [← hag]; exact hne)
    exact ⟨x, y, hag.trans hx1, rtc_l huw hrx, by omega, hrf, hxy, hry⟩
  · refine ⟨u, w, rfl, rtc_refl u, Nat.le_refl _, ?_, hag, hwv⟩
    rcases huw with ⟨hag', _⟩ | hrf
    · exact absurd hag' hag
    · exact hrf

/-- THE ADVANCE STEP: a cross rf edge on a cycle is followed, around the cycle,
by a cross rf edge with a STRICTLY LARGER timestamp. -/
theorem onCycleRfAdvance (TS : Ptraces P D) (ts : Nat) :
    ptracesWf pstep TS → ptracesFwdOwn TS → rfEdgesOk TS →
    onCycleRf TS ts → ∃ ts', ts < ts' ∧ onCycleRf TS ts' := by
  rintro hwf hfo hdisc ⟨e1, e2, a, hts1, hrd, hne, hback⟩
  obtain ⟨x, y, hx1, hrx, hx2, ⟨ts2, a2, hts2, hrd2⟩, hxy, hry⟩ :=
    rtcGdepFirstCross pstep TS e2 e1 hwf hback (Ne.symm hne)
  -- the reader's trace, which is also `x`'s
  obtain ⟨T, hT, _⟩ := (gevWfBounds TS e2).1 (gevReadsWf TS e2 a ts hrd)
  have hTx : TS.ptTrs[x.1]? = some T := by rw [← hx1]; exact hT
  obtain ⟨ev, hev, hinr⟩ := gevReadsEv TS e2 a ts T hT hrd
  obtain ⟨ev2, hev2, hts2'⟩ := gevTsEv TS x ts2 T hTx hts2
  -- the source of the ENTRY edge is foreign, so the read is not forwarded
  obtain ⟨base, data, kc, hm⟩ := gevTsMsg pstep TS e1 ts hwf hts1
  have hunf : readUnforwarded TS.ptLog e2.1 ev.aeLb ts :=
    Or.inr ⟨⟨base, data, some e1.1, kc⟩, e1.1, hm, rfl, hne⟩
  -- S1
  have hlt : ts < ts2 :=
    atraceS1Le pstep TS.ptImg TS.ptLog e2.1 T e2.2 x.2 ev ev2 a ts ts2 (hwf e2.1 T hT)
      (fun n ag hag => hfo e2.1 T n ag hT hag) hev hinr hunf hev2 hts2' hx2
      (fun hklt => hdisc e1 e2 T ts a x.2 ev2 hts1 hrd hne hT hklt hev2 (by rw [hts2']; rfl))
  exact ⟨ts2, hlt, x, y, a2, hts2, hrd2, hxy,
    rtc_transitive hry (rtc_l (Or.inr ⟨ts, a, hts1, hrd⟩) hrx)⟩

/-- A timestamp on a cycle is a real log position, hence bounded. -/
theorem onCycleRfBounded (TS : Ptraces P D) (ts : Nat) :
    ptracesWf pstep TS → onCycleRf TS ts → ts ≤ TS.ptLog.length := by
  rintro hwf ⟨e1, e2, a, hts1, _⟩
  obtain ⟨base, data, kc, hm⟩ := gevTsMsg pstep TS e1 ts hwf hts1
  have := lookup_lt_Some hm
  have := gevTsPos pstep TS e1 ts hwf hts1
  omega

/-- THE REFUTATION: the advance step cannot be iterated inside a bounded set of
timestamps (the measure is `length log - ts`). -/
theorem onCycleRfEmpty (TS : Ptraces P D) :
    ptracesWf pstep TS → ptracesFwdOwn TS → rfEdgesOk TS →
    ∀ ts, ¬ onCycleRf TS ts := by
  intro hwf hfo hdisc
  have hgen : ∀ n ts, TS.ptLog.length - ts ≤ n → ¬ onCycleRf TS ts := by
    intro n
    induction n with
    | zero =>
      intro ts hn hoc
      obtain ⟨ts', hlt, hoc'⟩ := onCycleRfAdvance pstep TS ts hwf hfo hdisc hoc
      have := onCycleRfBounded pstep TS ts' hwf hoc'
      omega
    | succ n ih =>
      intro ts hn hoc
      obtain ⟨ts', hlt, hoc'⟩ := onCycleRfAdvance pstep TS ts hwf hfo hdisc hoc
      have := onCycleRfBounded pstep TS ts' hwf hoc'
      exact ih ts' (by omega) hoc'
  exact fun ts => hgen _ ts (Nat.le_refl _)

/-! ### THE THEOREM -/

theorem gdepAcyclicEdgesOk (TS : Ptraces P D) :
    ptracesWf pstep TS → ptracesFwdOwn TS → rfEdgesOk TS → gdepAcyclic TS := by
  intro hwf hfo hdisc e hc
  obtain ⟨x, y, hrx, ⟨ts, a, hts, hrd⟩, hcross, hry⟩ := tcGdepCross pstep TS e hwf hc
  exact onCycleRfEmpty pstep TS hwf hfo hdisc ts
    ⟨x, y, a, hts, hrd, hcross, rtc_transitive hry hrx⟩

/-- The ORIGINAL statement, now a corollary: discipline alone is a special case
of `edgeOk`. -/
theorem gdepAcyclicDisciplined (TS : Ptraces P D) :
    ptracesWf pstep TS → ptracesFwdOwn TS → rfDisciplined TS → gdepAcyclic TS :=
  fun hwf hfo hdisc => gdepAcyclicEdgesOk pstep TS hwf hfo (rfDisciplinedEdgesOk TS hdisc)

/-- … at the behavior level, with `fwdOwn` DISCHARGED.  Only the per-edge
obligation remains a premise (and the SCowned arm, which lives in W2b). -/
theorem wpBehaviorGdepAcyclic (img : Image) (d0 : D) (ps : List P) (c : Wpcfg P D) :
    pdevOk pstep pdev →
    latFreeProg pstep → wpBehavior pstep img d0 ps c →
    ∃ (mid : Wpcfg P D) (TS : Ptraces P D),
      rtc (wpPromiseStep (P := P) (D := D)) (wpInit img d0 ps) mid ∧
      ptracesOf pstep TS mid c ∧
      noPromises c ∧
      ptracesWf pstep TS ∧
      ptracesFwdOwn TS ∧
      (rfEdgesOk TS → gdepAcyclic TS) := by
  intro hpok hlfp hb
  obtain ⟨mid, TS, hprom, hTS, hnp⟩ := wpBehaviorTraced pstep pdev img d0 ps c hpok hlfp hb
  have hwf := ptracesOfWf pstep TS mid c hTS
  have hinit : cfgWsInit mid := cfgWsInitPromiseRun _ _ (cfgWsInitInit img d0 ps) hprom
  have hfo := ptracesOfFwdOwn pstep TS mid c hinit hTS
  exact ⟨mid, TS, hprom, hTS, hnp, hwf, hfo, gdepAcyclicEdgesOk pstep TS hwf hfo⟩

end acyc

/-! ## What W2b inherits from this file

`fwdOwn` / `ptracesFwdOwn` / `ptracesOfFwdOwn` (the forward bank never names a
foreign write, derived from `wpInit`); `fulfilVext` / `fcov` / `edgeOkF` and
`atraceS1F` / `atraceS1LeF` (A0: coverage at the later fulfil's own EXT view —
what makes xv6's "plain read; acquiring AMO" shape dischargeable), with
`coveredFcov` / `edgeOkEdgeOkF` keeping `atraceS1` / `atraceS1Le` as corollaries;
`disciplined` / `covered` / `edgeOk` / `rfEdgesOk` (the per-edge obligation the
Iris layer discharges, per (rf edge, later fulfil), no cycle quantifier); and
`gdepAcyclicEdgesOk` / `wpBehaviorGdepAcyclic`, the standalone acyclicity result
that W2b's topological sort consumes.  NOT here: the SCowned arm (it needs
φ) and any use of the classification `cls` or the publication `pub`. -/

end Weak
