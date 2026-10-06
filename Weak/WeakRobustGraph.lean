/-
Weak: **the dependency graph over a traced behavior** (M6 W2a, step 2: the
INFRASTRUCTURE slice).

Rocq: `iris/WeakRobustGraph.v` @ xxvzwolszwmp (1cc222280).

The Rocq header, in substance: `Weak/WeakRobustTrace.lean` delivers a lat-free
full-machine behavior as a promise phase into `mid` plus ONE TRACE PER AGENT
against `mid`'s frozen `(img, log)`, with the fulfilled timestamp recorded per
event (`aeTs`) and the fulfilment accounting proved (`wpBehaviorFulfilOnce`).
This file builds the VOCABULARY the per-class acyclicity theorem is stated in —
event identity, the reads-of relation, the dependency relation `gdep` — and the
STRUCTURAL lemmas that theorem will consume.  The per-class refutation itself
is NOT here; the goal it proves is stated at the bottom as
`gdepAcyclicityGoal`.

THE DELIVERABLES.  (1) EVENT IDENTITY: `Gev := (agent index, step index)`;
`gevEv` looks it up, `gevLb` is its label, `gevTs` the timestamp it fulfilled;
`gevWf` is `isSome ∘ gevEv` (`gevWfBounds`).  (2) READS-OF: `lbReads l` lists
the (byte address, timestamp) pairs a label reads: `LLoad`, `LRmw` and
`LExLoad` read `(base + j, tvs[j].1)`; every other label reads nothing.
(3) `gdep = gpo ∪ grf`, EVENT-LEVEL: a machine step is atomic in the
promise-free interleaving, so `gdep` carries no co/fr edges.  (4) THE
DEVICE-ORDER EDGES `gdev` (G3): the successor relation on the device-order
witness `pdOrd DS`; the witness is duplicate-free (`pdOrdIndexInj`) and a
SAME-AGENT `gdev` edge is already a `gpo` edge (`gdevGpo`); the transitive
facts are derived once (`gdevChain`).

THE OWN-READ FINDING, PROVED (`atraceOwnRead` / `grfOwnLt`): inside ONE
agent's trace, a read of `(a, ts)` can only sit trace AFTER the event
fulfilling `ts`.  `k = k'`: no step both reads and fulfils the same timestamp
(the fused `LRmw`'s read bytes ARE its written bytes, and `fulfilOkD`'s COH
conjunct is checked after `loadPostRunD` raised `coh`; the split rmw's two
halves each do only one); `k < k'`: the read raises `coh a` to `≥ ts`
(`astepOkReadCoh`), `coh` only grows along a trace (`astepsWsLe`), and the
fulfil needs `coh a < ts` on every byte of its message (`astepOkFulfilCoh`).
Consequently every `gdep` cycle is genuinely CROSS-agent (`tcGdepCross`).

DEPENDENCY-FREE like its parents: no Iris, no Sail.

**Deviations from Rocq.**

1. NAMES: as `Weak/WeakMem.lean` deviation 1 (lowerCamelCase lemmas, the type
   `gev` ↦ `Gev`, an `abbrev` for `Nat × Nat` so `evAt` and the witness
   positions share it).  Duplicated Rocq names (protocol rule) are
   FILE-QUALIFIED: `WeakRobustGraph.gpo`, `WeakRobustGraph.grf`.
2. VOCABULARY: as `WeakRobustTrace` deviation 2; `Z` ↦ `Int`, `bv 8` ↦
   `BitVec 8`, `imap` ↦ `List.mapIdx`, `is_Some o` ↦ `o.isSome`, `S p` ↦
   `p + 1`, `x ← o; e` ↦ `o.bind (fun x => e)`, `f <$> o` ↦ `o.map f`,
   `o ≫= f` ↦ `o.bind f`, `PDevs d []` ↦ `⟨d, []⟩`; the instances
   `gev_dev_dec`, `gdev_dec`, `gdev_rel_dec` are `Decidable`/`DecidableRel`
   instances (`gdevDec` decides the bounded existential through core's
   `Nat.decidableExistsLT` rather than stdpp `Exists` over `seq`).
3. SECTION VARIABLES: `pstep`, `pcls`, `pdev` are explicit arguments exactly
   where a statement mentions them, in Rocq's order (`WeakRobustTrace`
   deviation 3).  `grfSourceUnique` takes NO `pdev`: in Rocq it is abstracted
   over `pdev` only because its proof calls `asteps_fulfil_unique pstep pdev`,
   whose Lean twin `astepsFulfilUnique` takes only `pstep`.
4. O2 / owner decision D4 (Lean-only label `LIFetch base tvs`,
   `Weak/WeakPromise.lean` deviation 8): `lbReads (LIFetch ..) = []`,
   `lbAsrc (LIFetch ..) = []`, `lbRasrc (LIFetch ..) = []`.  REASON: an i-cache
   fetch moves no view (`astepOk`'s arm is `f = id`), so it raises no `coh`
   and `astepOkReadCoh` (hence the own-read lemma) would be FALSE for it if it
   counted as a reads-of source; it reads the frozen log through `ifetchOk`
   only, which is not a coherence read.  Every `astepOk_*` lemma gains the
   `LIFetch` case (the state-identity arm, as `LSilent`/`LDev`).  In Rocq the
   alphabet has no fetch (fetches are `LLoad`s there), so for every Rocq
   label the definitions agree.  The AxSL-tier graph's fetch read events
   (owner decision D1) are not this file's concern.
5. Induction over `tc`: the shim's `tc` is core `Relation.TransGen` (built
   from the LAST step).  `tcGpoLt`, `tcGdepSaLt` and `tcGdepSplit` go by tail
   induction instead of Rocq's head-style `induction 1`; statements unchanged.
   `logAuthoredPromiseRun` uses `MachCSL.rtc_ind_r`.
6. Lean-only helpers (no Rocq twin): `gevEvSome`, `gevTsSome`, `gevLbSome`
   (unfold `gevEv`/`gevTs`/`gevLb` into the trace and step lookups).
7. Not imported: `Weak.WeakAxiomatic` (Rocq imports it only for the parked
   fold lemmas `load_post_run_coh`/`store_post_run_coh`; their D-variants live
   in `Weak/WeakMem.lean`) and the `acc_addr` unfolding (Lean states
   `loadPostRunDCoh` at `base + j` directly).

**Rocq → Lean name map.**  `tvs_reads` ↦ `tvsReads`; `lb_reads` ↦ `lbReads`;
`lb_asrc` ↦ `lbAsrc`; `lb_rasrc` ↦ `lbRasrc`; `elem_of_tvs_reads` ↦
`memTvsReads`; `lb_reads_nil_silent`/`_store`/`_fence` ↦
`lbReadsNilSilent`/`lbReadsNilStore`/`lbReadsNilFence`; `astep_ok_f_le` ↦
`astepOkFLe`; `astep_ok_ts_pos` ↦ `astepOkTsPos`; `astep_ok_read_log_byte` ↦
`astepOkReadLogByte`; `astep_ok_read_coh` ↦ `astepOkReadCoh`;
`astep_ok_fulfil_msg` ↦ `astepOkFulfilMsg`; `astep_ok_fulfil_coh` ↦
`astepOkFulfilCoh`; `astep_ok_read_fulfil_same` ↦ `astepOkReadFulfilSame`;
`ptraces_wf` ↦ `ptracesWf`; `ptraces_of_wf` ↦ `ptracesOfWf`;
`asteps_ws_succ`/`_mono`/`_le` ↦ `astepsWsSucc`/`astepsWsMono`/`astepsWsLe`;
`atrace_own_read` ↦ `atraceOwnRead`; `gev` ↦ `Gev`; `gev_tr` ↦ `gevTr`;
`gev_ev` ↦ `gevEv`; `gev_lb` ↦ `gevLb`; `gev_ts` ↦ `gevTs`; `gev_wf` ↦
`gevWf`; `gev_wf_bounds` ↦ `gevWfBounds`; `gev_wf_index` ↦ `gevWfIndex`;
`gev_ts_wf` ↦ `gevTsWf`; `gev_lb_wf` ↦ `gevLbWf`; `gev_step` ↦ `gevStep`;
`gev_reads` ↦ `gevReads`; `gev_reads_wf` ↦ `gevReadsWf`;
`gev_reads_log_byte` ↦ `gevReadsLogByte`; `gev_reads_msg` ↦ `gevReadsMsg`;
`gpo` ↦ `WeakRobustGraph.gpo`; `grf` ↦ `WeakRobustGraph.grf`; `gdep` ↦
`gdep`; `grf_wf` ↦ `grfWf`; `gdep_wf` ↦ `gdepWf`; `gev_ts_pos` ↦ `gevTsPos`;
`grf_ts_pos` ↦ `grfTsPos`; `gev_ts_msg` ↦ `gevTsMsg`; `grf_source_unique` ↦
`grfSourceUnique`; `grf_own_lt` ↦ `grfOwnLt`; `gdep_same_agent_lt` ↦
`gdepSameAgentLt`; `gev_ev_ev_at` ↦ `gevEvEvAt`; `gev_dev` ↦ `gevDev`;
`gev_dev_dec` ↦ `gevDevDec`; `gev_dev_wf` ↦ `gevDevWf`; `gdev` ↦ `gdev`;
`gdev_dec` ↦ `gdevDec`; `gdev_rel_dec` ↦ `gdevRelDec`; `pd_ord_dev` ↦
`pdOrdDev`; `gdev_wf` ↦ `gdevWf`; `pd_ord_index_inj` ↦ `pdOrdIndexInj`;
`gdev_gpo` ↦ `gdevGpo`; `gdev_chain` ↦ `gdevChain`; `gdev_nil` ↦ `gdevNil`;
`gpo_lt` ↦ `gpoLt`; `tc_gpo_lt` ↦ `tcGpoLt`; `gpo_acyclic` ↦ `gpoAcyclic`;
`gdep_sa` ↦ `gdepSa`; `tc_gdep_sa_lt` ↦ `tcGdepSaLt`; `gdep_sa_acyclic` ↦
`gdepSaAcyclic`; `tc_gdep_split` ↦ `tcGdepSplit`; `tc_gdep_cross` ↦
`tcGdepCross`; `log_authored` ↦ `logAuthored`; `log_authored_promise_step` ↦
`logAuthoredPromiseStep`; `log_authored_promise_run` ↦
`logAuthoredPromiseRun`; `log_authored_init` ↦ `logAuthoredInit`;
`wp_behavior_graph` ↦ `wpBehaviorGraph`; `gdep_acyclic` ↦ `gdepAcyclic`;
`gdep_acyclicity_goal` ↦ `gdepAcyclicityGoal`; `gdep_acyclic_suffices` ↦
`gdepAcyclicSuffices`.

**Not ported:** the parsing-only `Notation msg_byte_in_range := msg_byte_range`
(an alias kept in Rocq so the proofs "read unchanged"; this file calls
`msgByteRange` directly).  Uses checked: `WeakRobustSer.v` uses the alias —
its port should call `msgByteRange` (NOT `WeakAxiomatic3.msgByteInRange`, a
different lemma of the same Lean name).

**Statements checked** (by hand, against Rocq): all of them.
-/
import Weak.WeakRobustTrace
import Weak.WeakRobust

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std Wlabel

/-! ## DELIVERABLE 2: what a label READS

Byte `j` of a load/rmw run reads address `base + j` at timestamp `tvs[j].1` —
`WeakMem`'s contiguous-run convention. -/

def tvsReads (base : Int) (tvs : List (Nat × BitVec 8)) : List (Int × Nat) :=
  tvs.mapIdx (fun j tv => (base + (j : Int), tv.1))

def lbReads (l : Wlabel) : List (Int × Nat) :=
  match l with
  | LLoad _ _ base tvs _ => tvsReads base tvs
  | LRmw _ _ base tvs _ _ _ => tvsReads base tvs
  | LExLoad _ base tvs _ => tvsReads base tvs
  | LSilent | LStore .. | LFence .. | LDev | LRegW .. | LCtrl _ | LInstr | LExStore ..
  | LIFetch .. => []

/-- THE ADDRESS-OPERAND LIST of a label (D2); `[]` on every label that has none. -/
def lbAsrc (l : Wlabel) : List Dsrc :=
  match l with
  | LLoad _ _ _ _ asrc => asrc
  | LStore _ _ _ asrc _ => asrc
  | LRmw _ _ _ _ _ asrc _ => asrc
  | LExLoad _ _ _ asrc => asrc
  | LExStore _ _ _ asrc _ => asrc
  | LSilent | LFence .. | LDev | LRegW .. | LCtrl _ | LInstr | LIFetch .. => []

/-- D-2r: THE READ-FLOOR OPERAND LIST — only a PLAIN load has one. -/
def lbRasrc (l : Wlabel) : List Dsrc :=
  match l with
  | LLoad _ _ _ _ asrc => asrc
  | LStore .. | LRmw .. | LExLoad .. | LExStore ..
  | LSilent | LFence .. | LDev | LRegW .. | LCtrl _ | LInstr | LIFetch .. => []

theorem memTvsReads (base : Int) (tvs : List (Nat × BitVec 8)) (a : Int) (ts : Nat) :
    (a, ts) ∈ tvsReads base tvs ↔
    ∃ (j : Nat) (v : BitVec 8), tvs[j]? = some (ts, v) ∧ a = base + (j : Int) := by
  rw [tvsReads, elem_of_lookup_imap]
  constructor
  · rintro ⟨j, ⟨t, v⟩, he, hj⟩
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨j, v, hj, rfl⟩
  · rintro ⟨j, v, hj, rfl⟩
    exact ⟨j, (ts, v), rfl, hj⟩

theorem lbReadsNilSilent : lbReads LSilent = [] := rfl
theorem lbReadsNilStore (rl : Bool) (base : Int) (data : List (BitVec 8)) (asrc vsrc : List Dsrc) :
    lbReads (LStore rl base data asrc vsrc) = [] := rfl
theorem lbReadsNilFence (pr pw sr sw : Bool) : lbReads (LFence pr pw sr sw) = [] := rfl

/-! ## `astepOk`-level facts: reads, fulfils and `coh` -/

section astep

variable {P : Type}

/-- Every step function only RAISES views. -/
theorem astepOkFLe (img : Image) (log : List Wmsg) (i : Nat) (ag : Wpagent P) (l : Wlabel)
    (f : Wstate → Wstate) (Dl : Option Nat) :
    astepOk img log i ag l f Dl → ∀ w, wsLe w (f w) := by
  intro h
  cases l with
  | LSilent => obtain ⟨rfl, _⟩ := h; exact wsLeRefl
  | LLoad aq lat base tvs asrc =>
    obtain ⟨_, rfl, _⟩ := h; exact fun w => loadPostRunDLe _ _ _ _ _
  | LStore rl base data asrc vsrc =>
    obtain ⟨ts, k, _, _, _, rfl, _⟩ := h; exact fun w => storePostRunDLe _ _ _ _ _ _ _
  | LRmw aq rl base tvs data asrc vsrc =>
    obtain ⟨ts, k, _, _, _, _, _, _, rfl, _⟩ := h
    exact fun w => wsLeTrans (loadPostRunDLe _ _ _ _ _) (storePostRunDLe _ _ _ _ _ _ _)
  | LFence pr pw sr sw => obtain ⟨rfl, _⟩ := h; exact fun w => fencePostLe _ _ _ _ _
  | LDev => obtain ⟨rfl, _⟩ := h; exact wsLeRefl
  | LRegW rd srcs => obtain ⟨rfl, _⟩ := h; exact fun w => regwPostLe _ _ _
  | LCtrl srcs => obtain ⟨rfl, _⟩ := h; exact fun w => ctrlPostLe _ _
  | LInstr => obtain ⟨rfl, _⟩ := h; exact instrPostLe
  | LExLoad aq base tvs asrc => obtain ⟨_, rfl, _⟩ := h; exact fun w => exloadPostRunDLe _ _ _ _ _
  | LExStore rl base data asrc vsrc =>
    obtain ⟨ts, k, R, _, _, _, _, _, _, _, rfl, _⟩ := h
    exact fun w => storePostRunDLe _ _ _ _ _ _ _
  | LIFetch base tvs => obtain ⟨_, rfl, _⟩ := h; exact wsLeRefl

/-- A fulfilled timestamp is nonzero: `fulfilOkD`'s EXT conjunct is unsatisfiable
at `ts = 0`. -/
theorem astepOkTsPos (img : Image) (log : List Wmsg) (i : Nat) (ag : Wpagent P) (l : Wlabel)
    (f : Wstate → Wstate) (ts : Nat) :
    astepOk img log i ag l f (some ts) → 0 < ts := by
  intro h
  cases l with
  | LSilent => obtain ⟨_, ⟨⟩⟩ := h
  | LLoad => obtain ⟨_, _, ⟨⟩⟩ := h
  | LStore =>
    obtain ⟨ts', k, _, _, ⟨_, hext⟩, _, hD⟩ := h
    cases hD; omega
  | LRmw =>
    obtain ⟨ts', k, _, _, _, _, _, ⟨_, hext⟩, _, hD⟩ := h
    cases hD; omega
  | LFence => obtain ⟨_, ⟨⟩⟩ := h
  | LDev => obtain ⟨_, ⟨⟩⟩ := h
  | LRegW => obtain ⟨_, ⟨⟩⟩ := h
  | LCtrl => obtain ⟨_, ⟨⟩⟩ := h
  | LInstr => obtain ⟨_, ⟨⟩⟩ := h
  | LExLoad => obtain ⟨_, _, ⟨⟩⟩ := h
  | LExStore =>
    obtain ⟨ts', k, R, _, _, _, _, _, _, ⟨_, hext⟩, _, hD⟩ := h
    cases hD; omega
  | LIFetch => obtain ⟨_, _, ⟨⟩⟩ := h

/-- A read's timestamp names a real write of the byte it reads. -/
theorem astepOkReadLogByte (img : Image) (log : List Wmsg) (i : Nat) (ag : Wpagent P)
    (l : Wlabel) (f : Wstate → Wstate) (Dl : Option Nat) (a : Int) (ts : Nat) :
    astepOk img log i ag l f Dl → (a, ts) ∈ lbReads l →
    (logByte img log ts a).isSome := by
  intro h hin
  cases l with
  | LLoad aq lat base tvs asrc =>
    obtain ⟨hro, _, _⟩ := h
    obtain ⟨j, v, hj, rfl⟩ := (memTvsReads _ _ _ _).1 hin
    rw [(hro j ts v hj).1]; rfl
  | LRmw aq rl base tvs data asrc vsrc =>
    obtain ⟨ts', k, _, _, _, hro, _⟩ := h
    obtain ⟨j, v, hj, rfl⟩ := (memTvsReads _ _ _ _).1 hin
    rw [(hro j ts v hj).1]; rfl
  | LExLoad aq base tvs asrc =>
    obtain ⟨hro, _, _⟩ := h
    obtain ⟨j, v, hj, rfl⟩ := (memTvsReads _ _ _ _).1 hin
    rw [(hro j ts v hj).1]; rfl
  | _ => simp [lbReads] at hin

/-- THE READ RAISES `coh`: after a step whose label reads `(a, ts)`, the agent's
coherence floor at `a` is at least `ts`. -/
theorem astepOkReadCoh (img : Image) (log : List Wmsg) (i : Nat) (ag : Wpagent P)
    (l : Wlabel) (f : Wstate → Wstate) (Dl : Option Nat) (a : Int) (ts : Nat) :
    astepOk img log i ag l f Dl → (a, ts) ∈ lbReads l →
    ts ≤ coh (f ag.paWs) a := by
  intro h hin
  cases l with
  | LLoad aq lat base tvs asrc =>
    obtain ⟨_, rfl, _⟩ := h
    obtain ⟨j, v, hj, rfl⟩ := (memTvsReads _ _ _ _).1 hin
    have hts : (tvs.map Prod.fst)[j]? = some ts := by rw [List.getElem?_map, hj]; rfl
    exact loadPostRunDCoh ag.paWs aq (srcsView ag.paWs asrc) base (tvs.map Prod.fst) j ts hts
  | LRmw aq rl base tvs data asrc vsrc =>
    obtain ⟨ts', k, _, _, _, _, _, _, rfl, _⟩ := h
    obtain ⟨j, v, hj, rfl⟩ := (memTvsReads _ _ _ _).1 hin
    have hts : (tvs.map Prod.fst)[j]? = some ts := by rw [List.getElem?_map, hj]; rfl
    exact Nat.le_trans
      (loadPostRunDCoh ag.paWs aq (srcsView ag.paWs asrc) base (tvs.map Prod.fst) j ts hts)
      (wsLeCoh _ _ _ (storePostRunDLe _ _ _ _ _ _ _))
  | LExLoad aq base tvs asrc =>
    obtain ⟨_, rfl, _⟩ := h
    obtain ⟨j, v, hj, rfl⟩ := (memTvsReads _ _ _ _).1 hin
    have hts : (tvs.map Prod.fst)[j]? = some ts := by rw [List.getElem?_map, hj]; rfl
    exact exloadPostRunDCoh ag.paWs aq (srcsView ag.paWs asrc) base (tvs.map Prod.fst) j ts hts
  | _ => simp [lbReads] at hin

/-- A fulfil names its own promised message, author included. -/
theorem astepOkFulfilMsg (img : Image) (log : List Wmsg) (i : Nat) (ag : Wpagent P)
    (l : Wlabel) (f : Wstate → Wstate) (ts : Nat) :
    astepOk img log i ag l f (some ts) →
    ∃ base data k, log[ts - 1]? = some ⟨base, data, some i, k⟩ := by
  intro h
  cases l with
  | LSilent => obtain ⟨_, ⟨⟩⟩ := h
  | LLoad => obtain ⟨_, _, ⟨⟩⟩ := h
  | LStore =>
    obtain ⟨ts', k, _, hlog, _, _, hD⟩ := h
    cases hD; exact ⟨_, _, _, hlog⟩
  | LRmw =>
    obtain ⟨ts', k, _, _, hlog, _, _, _, _, hD⟩ := h
    cases hD; exact ⟨_, _, _, hlog⟩
  | LFence => obtain ⟨_, ⟨⟩⟩ := h
  | LDev => obtain ⟨_, ⟨⟩⟩ := h
  | LRegW => obtain ⟨_, ⟨⟩⟩ := h
  | LCtrl => obtain ⟨_, ⟨⟩⟩ := h
  | LInstr => obtain ⟨_, ⟨⟩⟩ := h
  | LExLoad => obtain ⟨_, _, ⟨⟩⟩ := h
  | LExStore =>
    obtain ⟨ts', k, R, _, hlog, _, _, _, _, _, _, hD⟩ := h
    cases hD; exact ⟨_, _, _, hlog⟩
  | LIFetch => obtain ⟨_, _, ⟨⟩⟩ := h

/-- THE FULFIL DEMANDS `coh < ts` on every byte of the message it fulfils. -/
theorem astepOkFulfilCoh (img : Image) (log : List Wmsg) (i : Nat) (ag : Wpagent P)
    (l : Wlabel) (f : Wstate → Wstate) (ts : Nat) (m : Wmsg) (a : Int) :
    astepOk img log i ag l f (some ts) →
    log[ts - 1]? = some m → (msgByte m a).isSome →
    coh ag.paWs a < ts := by
  intro h hm hb
  cases l with
  | LSilent => obtain ⟨_, ⟨⟩⟩ := h
  | LLoad => obtain ⟨_, _, ⟨⟩⟩ := h
  | LStore rl base data asrc vsrc =>
    obtain ⟨ts', k, _, hlog, ⟨hcoh, _⟩, _, hD⟩ := h
    cases hD
    rw [hlog] at hm; cases hm
    obtain ⟨j, hj, rfl⟩ := msgByteRange _ _ hb
    exact hcoh j hj
  | LRmw aq rl base tvs data asrc vsrc =>
    obtain ⟨ts', k, _, _, hlog, _, _, ⟨hcoh, _⟩, _, hD⟩ := h
    cases hD
    rw [hlog] at hm; cases hm
    obtain ⟨j, hj, rfl⟩ := msgByteRange _ _ hb
    exact Nat.lt_of_le_of_lt (wsLeCoh _ _ _ (loadPostRunDLe _ _ _ _ _)) (hcoh j hj)
  | LFence => obtain ⟨_, ⟨⟩⟩ := h
  | LDev => obtain ⟨_, ⟨⟩⟩ := h
  | LRegW => obtain ⟨_, ⟨⟩⟩ := h
  | LCtrl => obtain ⟨_, ⟨⟩⟩ := h
  | LInstr => obtain ⟨_, ⟨⟩⟩ := h
  | LExLoad => obtain ⟨_, _, ⟨⟩⟩ := h
  | LExStore rl base data asrc vsrc =>
    obtain ⟨ts', k, R, _, hlog, _, _, _, _, ⟨hcoh, _⟩, _, hD⟩ := h
    cases hD
    rw [hlog] at hm; cases hm
    obtain ⟨j, hj, rfl⟩ := msgByteRange _ _ hb
    exact hcoh j hj
  | LIFetch => obtain ⟨_, _, ⟨⟩⟩ := h

/-- THE SAME-STEP CASE of the own-read lemma: a step can NEVER read the very
timestamp it fulfils. -/
theorem astepOkReadFulfilSame (img : Image) (log : List Wmsg) (i : Nat) (ag : Wpagent P)
    (l : Wlabel) (f : Wstate → Wstate) (ts : Nat) (a : Int) :
    astepOk img log i ag l f (some ts) → (a, ts) ∈ lbReads l → False := by
  intro h hin
  cases l with
  | LSilent => obtain ⟨_, ⟨⟩⟩ := h
  | LLoad => obtain ⟨_, _, ⟨⟩⟩ := h
  | LStore => simp [lbReads] at hin
  | LRmw aq rl base tvs data asrc vsrc =>
    obtain ⟨ts', k, hlen, _, _, _, _, ⟨hcoh, _⟩, _, hD⟩ := h
    cases hD
    obtain ⟨j, v, hj, rfl⟩ := (memTvsReads _ _ _ _).1 hin
    have hts : (tvs.map Prod.fst)[j]? = some ts := by rw [List.getElem?_map, hj]; rfl
    have hjlt : j < data.length := by rw [← hlen]; exact lookup_lt_Some hj
    have hge := loadPostRunDCoh ag.paWs aq (srcsView ag.paWs asrc) base (tvs.map Prod.fst) j ts hts
    have hlt := hcoh j hjlt
    omega
  | LFence => obtain ⟨_, ⟨⟩⟩ := h
  | LDev => obtain ⟨_, ⟨⟩⟩ := h
  | LRegW => obtain ⟨_, ⟨⟩⟩ := h
  | LCtrl => obtain ⟨_, ⟨⟩⟩ := h
  | LInstr => obtain ⟨_, ⟨⟩⟩ := h
  -- THE RMW SPLIT (S2): both arms are VACUOUS — the exclusive read fulfils
  -- nothing, the conditional write reads nothing.
  | LExLoad => obtain ⟨_, _, ⟨⟩⟩ := h
  | LExStore => simp [lbReads] at hin
  | LIFetch => obtain ⟨_, _, ⟨⟩⟩ := h

end astep

/-! ## The graph -/

section graph

variable {P D : Type}
variable (pstep : P → D → Wlabel → P → D → Prop)
variable (pcls : P → Wlabel → Wstate → WmClass)
variable (pdev : P → Wlabel → P → Bool)

/-! ### Trace-level plumbing -/

/-- The wf conjunct of `ptracesOf` on its own. -/
def ptracesWf (TS : Ptraces P D) : Prop :=
  ∀ (i : Nat) (T : Atrace P D), TS.ptTrs[i]? = some T → atraceWf pstep TS.ptImg TS.ptLog i T

theorem ptracesOfWf (TS : Ptraces P D) (mid c : Wpcfg P D) :
    ptracesOf pstep TS mid c → ptracesWf pstep TS := fun h => h.2.2.2.1

/-- Views only grow along one agent's trace. -/
theorem astepsWsSucc (img : Image) (log : List Wmsg) (i : Nat) (ags : List (Wpagent P))
    (evs : List (Aev D)) (k : Nat) (ag ag' : Wpagent P) :
    astepsWf pstep img log i ags evs →
    ags[k]? = some ag → ags[k + 1]? = some ag' →
    wsLe ag.paWs ag'.paWs := by
  intro hwf hk hk'
  have hlt : k < evs.length := by have := lookup_lt_Some hk'; have := hwf.1; omega
  obtain ⟨ev, hev⟩ := Option.isSome_iff_exists.1 (lookup_lt_is_Some_2 hlt)
  obtain ⟨a1, a2, st', f, ha1, ha2, _, hok, heq⟩ := astepsWfStep pstep img log i ags evs k ev hwf hev
  rw [hk] at ha1; cases ha1
  rw [hk'] at ha2; cases ha2
  rw [heq]
  exact astepOkFLe img log i ag ev.aeLb f ev.aeTs hok ag.paWs

theorem astepsWsMono (img : Image) (log : List Wmsg) (i : Nat) (ags : List (Wpagent P))
    (evs : List (Aev D)) (d : Nat) :
    ∀ (k : Nat) (ag ag' : Wpagent P),
      astepsWf pstep img log i ags evs →
      ags[k]? = some ag → ags[k + d]? = some ag' →
      wsLe ag.paWs ag'.paWs := by
  induction d with
  | zero =>
    intro k ag ag' _ hk hkd
    rw [Nat.add_zero, hk] at hkd; cases hkd; exact wsLeRefl _
  | succ d ih =>
    intro k ag ag' hwf hk hkd
    have hlt : k + 1 < ags.length := by have := lookup_lt_Some hkd; omega
    obtain ⟨agn, hagn⟩ := Option.isSome_iff_exists.1 (lookup_lt_is_Some_2 hlt)
    have hstep := astepsWsSucc pstep img log i ags evs k ag agn hwf hk hagn
    have heq : k + (d + 1) = (k + 1) + d := by omega
    rw [heq] at hkd
    exact wsLeTrans hstep (ih (k + 1) agn ag' hwf hagn hkd)

theorem astepsWsLe (img : Image) (log : List Wmsg) (i : Nat) (ags : List (Wpagent P))
    (evs : List (Aev D)) (k1 k2 : Nat) (ag1 ag2 : Wpagent P) :
    astepsWf pstep img log i ags evs →
    k1 ≤ k2 → ags[k1]? = some ag1 → ags[k2]? = some ag2 →
    wsLe ag1.paWs ag2.paWs := by
  intro hwf hle hk1 hk2
  have heq : k2 = k1 + (k2 - k1) := by omega
  rw [heq] at hk2
  exact astepsWsMono pstep img log i ags evs (k2 - k1) k1 ag1 ag2 hwf hk1 hk2

/-! ### DELIVERABLE 4: THE OWN-READ LEMMA -/

/-- In one agent's wf trace, the event fulfilling `ts` strictly PRECEDES every
event of that agent reading `ts`. -/
theorem atraceOwnRead (img : Image) (log : List Wmsg) (i : Nat) (T : Atrace P D)
    (k k' : Nat) (ev ev' : Aev D) (a : Int) (ts : Nat) :
    atraceWf pstep img log i T →
    T.atEvs[k]? = some ev → (a, ts) ∈ lbReads ev.aeLb →
    T.atEvs[k']? = some ev' → ev'.aeTs = some ts →
    k' < k := by
  intro hwf hev hin hev' hts
  obtain ⟨ag, agn, st', f, hag, hagn, _, hok, hagne⟩ :=
    astepsWfStep pstep img log i T.atAgs T.atEvs k ev hwf hev
  obtain ⟨ag', agn', st'', f', hag', _, _, hok', _⟩ :=
    astepsWfStep pstep img log i T.atAgs T.atEvs k' ev' hwf hev'
  rw [hts] at hok'
  rcases Nat.lt_trichotomy k' k with hlt | heq | hgt
  · exact hlt
  · -- k = k': a step reading its own fulfilment — refuted by geometry
    subst heq
    rw [hev] at hev'; cases hev'
    exact (astepOkReadFulfilSame img log i ag' ev.aeLb f' ts a hok' hin).elim
  · -- k < k': the read raised coh(a) past ts, the fulfil needs it below
    exfalso
    have hge : ts ≤ coh agn.paWs a := by
      rw [hagne]; exact astepOkReadCoh img log i ag ev.aeLb f ev.aeTs a ts hok hin
    have hmono : wsLe agn.paWs ag'.paWs :=
      astepsWsLe pstep img log i T.atAgs T.atEvs (k + 1) k' agn ag' hwf (by omega) hagn hag'
    have hle := wsLeCoh _ _ a hmono
    have hpos : 0 < ts := astepOkTsPos img log i ag' ev'.aeLb f' ts hok'
    have hlb : (logByte img log ts a).isSome :=
      astepOkReadLogByte img log i ag ev.aeLb f ev.aeTs a ts hok hin
    obtain ⟨p, rfl⟩ : ∃ p, ts = p + 1 := ⟨ts - 1, by omega⟩
    rw [logByteS] at hlb
    cases hm : log[p]? with
    | none => rw [hm] at hlb; simp at hlb
    | some m =>
      rw [hm] at hlb
      have hlt' : coh ag'.paWs a < p + 1 :=
        astepOkFulfilCoh img log i ag' ev'.aeLb f' (p + 1) m a hok' (by simpa using hm) hlb
      omega

/-! ### DELIVERABLE 1: EVENT IDENTITY over a bundle -/

/-- An event of a traced behavior: (agent index, step index). -/
abbrev Gev : Type := Nat × Nat

def gevTr (TS : Ptraces P D) (e : Gev) : Option (Atrace P D) := TS.ptTrs[e.1]?

def gevEv (TS : Ptraces P D) (e : Gev) : Option (Aev D) :=
  (TS.ptTrs[e.1]?).bind (fun T => T.atEvs[e.2]?)

def gevLb (TS : Ptraces P D) (e : Gev) : Option Wlabel := (gevEv TS e).map Aev.aeLb

/-- The timestamp the event FULFILLED (`none` for a non-store). -/
def gevTs (TS : Ptraces P D) (e : Gev) : Option Nat := (gevEv TS e).bind Aev.aeTs

def gevWf (TS : Ptraces P D) (e : Gev) : Prop := (gevEv TS e).isSome

/-- Lean-only helper: `gevEv` unfolded into the two lookups. -/
theorem gevEvSome (TS : Ptraces P D) (e : Gev) (ev : Aev D) :
    gevEv TS e = some ev → ∃ T, TS.ptTrs[e.1]? = some T ∧ T.atEvs[e.2]? = some ev := by
  unfold gevEv
  intro h
  cases hT : TS.ptTrs[e.1]? with
  | none => rw [hT] at h; cases h
  | some T => rw [hT] at h; exact ⟨T, rfl, h⟩

/-- Lean-only helper: `gevTs` unfolded. -/
theorem gevTsSome (TS : Ptraces P D) (e : Gev) (ts : Nat) :
    gevTs TS e = some ts →
    ∃ T ev, TS.ptTrs[e.1]? = some T ∧ T.atEvs[e.2]? = some ev ∧ ev.aeTs = some ts := by
  unfold gevTs
  intro h
  cases hev : gevEv TS e with
  | none => rw [hev] at h; cases h
  | some ev =>
    rw [hev] at h
    obtain ⟨T, hT, hev'⟩ := gevEvSome TS e ev hev
    exact ⟨T, ev, hT, hev', h⟩

/-- Lean-only helper: `gevLb` unfolded. -/
theorem gevLbSome (TS : Ptraces P D) (e : Gev) (l : Wlabel) :
    gevLb TS e = some l →
    ∃ T ev, TS.ptTrs[e.1]? = some T ∧ T.atEvs[e.2]? = some ev ∧ ev.aeLb = l := by
  unfold gevLb
  intro h
  cases hev : gevEv TS e with
  | none => rw [hev] at h; cases h
  | some ev =>
    rw [hev] at h
    obtain ⟨T, hT, hev'⟩ := gevEvSome TS e ev hev
    exact ⟨T, ev, hT, hev', Option.some.inj h⟩

theorem gevWfBounds (TS : Ptraces P D) (e : Gev) :
    gevWf TS e ↔ ∃ T, TS.ptTrs[e.1]? = some T ∧ e.2 < T.atEvs.length := by
  unfold gevWf
  constructor
  · intro h
    obtain ⟨ev, hev⟩ := Option.isSome_iff_exists.1 h
    obtain ⟨T, hT, hev'⟩ := gevEvSome TS e ev hev
    exact ⟨T, hT, lookup_lt_Some hev'⟩
  · rintro ⟨T, hT, hlt⟩
    unfold gevEv
    rw [hT]
    exact lookup_lt_is_Some_2 hlt

theorem gevWfIndex (TS : Ptraces P D) (e : Gev) : gevWf TS e → e.1 < TS.ptTrs.length := by
  intro h
  obtain ⟨T, hT, _⟩ := (gevWfBounds TS e).1 h
  exact lookup_lt_Some hT

theorem gevTsWf (TS : Ptraces P D) (e : Gev) (ts : Nat) : gevTs TS e = some ts → gevWf TS e := by
  unfold gevTs gevWf
  intro h
  cases hev : gevEv TS e with
  | none => rw [hev] at h; cases h
  | some ev => rfl

theorem gevLbWf (TS : Ptraces P D) (e : Gev) (l : Wlabel) : gevLb TS e = some l → gevWf TS e := by
  unfold gevLb gevWf
  intro h
  cases hev : gevEv TS e with
  | none => rw [hev] at h; cases h
  | some ev => rfl

/-- The step an event names, with its `astepOk` and the two agent records it runs
between. -/
theorem gevStep (TS : Ptraces P D) (e : Gev) (ev : Aev D) :
    ptracesWf pstep TS → gevEv TS e = some ev →
    ∃ (T : Atrace P D) (ag ag' : Wpagent P) (st' : P) (f : Wstate → Wstate),
      TS.ptTrs[e.1]? = some T ∧
      T.atAgs[e.2]? = some ag ∧ T.atAgs[e.2 + 1]? = some ag' ∧
      astepProg pstep ag ev st' ∧
      astepOk TS.ptImg TS.ptLog e.1 ag ev.aeLb f ev.aeTs ∧
      ag'.paWs = f ag.paWs := by
  intro hwf hev
  obtain ⟨T, hT, hev'⟩ := gevEvSome TS e ev hev
  obtain ⟨ag, ag', st', f, hag, hag', hps, hok, hagn⟩ :=
    astepsWfStep pstep TS.ptImg TS.ptLog e.1 T.atAgs T.atEvs e.2 ev (hwf _ _ hT) hev'
  exact ⟨T, ag, ag', st', f, hT, hag, hag', hps, hok, by rw [hagn]⟩

/-! ### DELIVERABLE 2 (continued): the reads-of PREDICATE -/

/-- `gevReads TS e a ts`: event `e` reads byte `a` at timestamp `ts`. -/
def gevReads (TS : Ptraces P D) (e : Gev) (a : Int) (ts : Nat) : Prop :=
  ∃ l, gevLb TS e = some l ∧ (a, ts) ∈ lbReads l

theorem gevReadsWf (TS : Ptraces P D) (e : Gev) (a : Int) (ts : Nat) :
    gevReads TS e a ts → gevWf TS e := fun ⟨l, hl, _⟩ => gevLbWf TS e l hl

/-- A read's timestamp names a real write of the byte read. -/
theorem gevReadsLogByte (TS : Ptraces P D) (e : Gev) (a : Int) (ts : Nat) :
    ptracesWf pstep TS → gevReads TS e a ts →
    (logByte TS.ptImg TS.ptLog ts a).isSome := by
  rintro hwf ⟨l, hl, hin⟩
  unfold gevLb at hl
  cases hev : gevEv TS e with
  | none => rw [hev] at hl; cases hl
  | some ev =>
    rw [hev] at hl
    cases hl
    obtain ⟨T, ag, ag', st', f, _, _, _, _, hok, _⟩ := gevStep pstep TS e ev hwf hev
    exact astepOkReadLogByte _ _ _ _ _ _ _ a ts hok hin

/-- A read of a NONZERO timestamp names a log message (timestamp `p + 1` is log
position `p`; timestamp 0 is the era-initial image and has no author). -/
theorem gevReadsMsg (TS : Ptraces P D) (e : Gev) (a : Int) (p : Nat) :
    ptracesWf pstep TS → gevReads TS e a (p + 1) →
    ∃ m, TS.ptLog[p]? = some m ∧ (msgByte m a).isSome := by
  intro hwf hr
  have hlb := gevReadsLogByte pstep TS e a (p + 1) hwf hr
  rw [logByteS] at hlb
  cases hm : TS.ptLog[p]? with
  | none => rw [hm] at hlb; simp at hlb
  | some m => rw [hm] at hlb; exact ⟨m, rfl, hlb⟩

/-! ### DELIVERABLE 3: THE DEPENDENCY RELATION `gdep` -/

/-- Per-agent program order: same trace, earlier step index, both events real. -/
def WeakRobustGraph.gpo (TS : Ptraces P D) (e1 e2 : Gev) : Prop :=
  e1.1 = e2.1 ∧ e1.2 < e2.2 ∧ gevWf TS e1 ∧ gevWf TS e2

/-- Reads-from: the event that FULFILLED a timestamp, to every event that reads it. -/
def WeakRobustGraph.grf (TS : Ptraces P D) (e1 e2 : Gev) : Prop :=
  ∃ (ts : Nat) (a : Int), gevTs TS e1 = some ts ∧ gevReads TS e2 a ts

def gdep (TS : Ptraces P D) (e1 e2 : Gev) : Prop :=
  WeakRobustGraph.gpo TS e1 e2 ∨ WeakRobustGraph.grf TS e1 e2

theorem grfWf (TS : Ptraces P D) (e1 e2 : Gev) :
    WeakRobustGraph.grf TS e1 e2 → gevWf TS e1 ∧ gevWf TS e2 :=
  fun ⟨ts, a, hts, hr⟩ => ⟨gevTsWf TS e1 ts hts, gevReadsWf TS e2 a ts hr⟩

theorem gdepWf (TS : Ptraces P D) (e1 e2 : Gev) : gdep TS e1 e2 → gevWf TS e1 ∧ gevWf TS e2 := by
  rintro (⟨_, _, h1, h2⟩ | hrf)
  · exact ⟨h1, h2⟩
  · exact grfWf TS e1 e2 hrf

/-- Fulfilled timestamps are nonzero. -/
theorem gevTsPos (TS : Ptraces P D) (e : Gev) (ts : Nat) :
    ptracesWf pstep TS → gevTs TS e = some ts → 0 < ts := by
  intro hwf hts
  obtain ⟨T, ev, hT, hev', hts'⟩ := gevTsSome TS e ts hts
  have hev : gevEv TS e = some ev := by unfold gevEv; rw [hT]; exact hev'
  obtain ⟨_, ag, ag', st', f, _, _, _, _, hok, _⟩ := gevStep pstep TS e ev hwf hev
  rw [hts'] at hok
  exact astepOkTsPos _ _ _ _ _ _ ts hok

theorem grfTsPos (TS : Ptraces P D) (e1 e2 : Gev) (ts : Nat) (a : Int) :
    ptracesWf pstep TS → gevTs TS e1 = some ts → gevReads TS e2 a ts → 0 < ts :=
  fun hwf hts _ => gevTsPos pstep TS e1 ts hwf hts

/-- The AUTHOR of a fulfilled message is the fulfilling agent. -/
theorem gevTsMsg (TS : Ptraces P D) (e : Gev) (ts : Nat) :
    ptracesWf pstep TS → gevTs TS e = some ts →
    ∃ base data k, TS.ptLog[ts - 1]? = some ⟨base, data, some e.1, k⟩ := by
  intro hwf hts
  obtain ⟨T, ev, hT, hev', hts'⟩ := gevTsSome TS e ts hts
  have hev : gevEv TS e = some ev := by unfold gevEv; rw [hT]; exact hev'
  obtain ⟨_, ag, ag', st', f, _, _, _, _, hok, _⟩ := gevStep pstep TS e ev hwf hev
  rw [hts'] at hok
  exact astepOkFulfilMsg _ _ _ _ _ _ ts hok

/-- UNIQUENESS of the rf source: two events fulfilling the same timestamp are the
same event. -/
theorem grfSourceUnique (TS : Ptraces P D) (e1 e2 : Gev) (ts : Nat) :
    ptracesWf pstep TS → gevTs TS e1 = some ts → gevTs TS e2 = some ts → e1 = e2 := by
  intro hwf h1 h2
  obtain ⟨b1, d1, kc1, hm1⟩ := gevTsMsg pstep TS e1 ts hwf h1
  obtain ⟨b2, d2, kc2, hm2⟩ := gevTsMsg pstep TS e2 ts hwf h2
  rw [hm1] at hm2
  simp only [Option.some.injEq, Wmsg.mk.injEq] at hm2
  obtain ⟨_, _, hag, _⟩ := hm2
  obtain ⟨T1, ev1, hT1, hev1, hts1⟩ := gevTsSome TS e1 ts h1
  obtain ⟨T2, ev2, hT2, hev2, hts2⟩ := gevTsSome TS e2 ts h2
  rw [← hag, hT1] at hT2
  cases hT2
  have hk : e1.2 = e2.2 :=
    astepsFulfilUnique pstep TS.ptImg TS.ptLog e1.1 T1.atAgs T1.atEvs ts e1.2 e2.2 ev1 ev2
      (hwf _ _ hT1) hev1 hts1 hev2 hts2
  obtain ⟨i1, k1⟩ := e1
  obtain ⟨i2, k2⟩ := e2
  simp only at hag hk
  rw [hag, hk]

/-! ### DELIVERABLE 4 (at the graph level): the own-read lemma -/

/-- Inside ONE agent, an rf edge points FORWARD in trace order. -/
theorem grfOwnLt (TS : Ptraces P D) (e1 e2 : Gev) :
    ptracesWf pstep TS → WeakRobustGraph.grf TS e1 e2 → e1.1 = e2.1 → e1.2 < e2.2 := by
  rintro hwf ⟨ts, a, hts, l, hl, hin⟩ hag
  obtain ⟨T1, ev1, hT1, hev1, hts1⟩ := gevTsSome TS e1 ts hts
  obtain ⟨T2, ev2, hT2, hev2, hl2⟩ := gevLbSome TS e2 l hl
  rw [hag, hT2] at hT1
  have hTT : T2 = T1 := Option.some.inj hT1
  subst hTT
  subst hl2
  exact atraceOwnRead pstep TS.ptImg TS.ptLog e2.1 T2 e2.2 e1.2 ev2 ev1 a ts
    (hwf _ _ hT2) hev2 hin hev1 hts1

/-- ALL `gdep` edges inside one agent strictly increase the step index. -/
theorem gdepSameAgentLt (TS : Ptraces P D) (e1 e2 : Gev) :
    ptracesWf pstep TS → gdep TS e1 e2 → e1.1 = e2.1 → e1.2 < e2.2 := by
  rintro hwf (⟨_, h, _⟩ | hrf) hag
  · exact h
  · exact grfOwnLt pstep TS e1 e2 hwf hrf hag

/-! ### DELIVERABLE 6 (G3): THE DEVICE-ORDER EDGES -/

/-- The graph's event lookup IS the witness's. -/
theorem gevEvEvAt (TS : Ptraces P D) (e : Gev) : gevEv TS e = evAt TS e := rfl

/-- A FABRIC-TOUCHING event: one that carries a recorded fabric pair. -/
def gevDev (TS : Ptraces P D) (e : Gev) : Prop :=
  ∃ ev, gevEv TS e = some ev ∧ ev.aeDev.isSome

instance gevDevDec (TS : Ptraces P D) (e : Gev) : Decidable (gevDev TS e) :=
  match h : gevEv TS e with
  | some ev =>
    if hd : ev.aeDev.isSome then isTrue ⟨ev, h, hd⟩
    else isFalse (fun ⟨ev', h', hd'⟩ => by rw [h] at h'; cases h'; exact hd hd')
  | none => isFalse (fun ⟨ev', h', _⟩ => by rw [h] at h'; cases h')

theorem gevDevWf (TS : Ptraces P D) (e : Gev) : gevDev TS e → gevWf TS e := by
  rintro ⟨ev, hev, _⟩
  unfold gevWf; rw [hev]; rfl

/-- THE GDEV CHAIN: consecutive entries of the device-order witness. -/
def gdev (_TS : Ptraces P D) (DS : Pdevs D) (e1 e2 : Gev) : Prop :=
  ∃ m, DS.pdOrd[m]? = some e1 ∧ DS.pdOrd[m + 1]? = some e2

instance gdevDec (TS : Ptraces P D) (DS : Pdevs D) (e1 e2 : Gev) : Decidable (gdev TS DS e1 e2) :=
  decidable_of_iff (∃ m, m < DS.pdOrd.length ∧ (DS.pdOrd[m]? = some e1 ∧ DS.pdOrd[m + 1]? = some e2))
    ⟨fun ⟨m, _, h⟩ => ⟨m, h⟩, fun ⟨m, h1, h2⟩ => ⟨m, lookup_lt_Some h1, h1, h2⟩⟩

instance gdevRelDec (TS : Ptraces P D) (DS : Pdevs D) : DecidableRel (gdev TS DS) :=
  fun e1 e2 => gdevDec TS DS e1 e2

/-- Every listed position is a real, fabric-touching event (W1). -/
theorem pdOrdDev (TS : Ptraces P D) (DS : Pdevs D) (m : Nat) (e : Gev) :
    ptracesWit TS DS → DS.pdOrd[m]? = some e → gevDev TS e := by
  rintro ⟨hW1, _⟩ hm
  obtain ⟨ev, hev, hdd⟩ := hW1 m e hm
  exact ⟨ev, hev, hdd⟩

theorem gdevWf (TS : Ptraces P D) (DS : Pdevs D) (e1 e2 : Gev) :
    ptracesWit TS DS → gdev TS DS e1 e2 → gevWf TS e1 ∧ gevWf TS e2 := by
  rintro hwit ⟨m, h1, h2⟩
  exact ⟨gevDevWf TS e1 (pdOrdDev TS DS m e1 hwit h1),
    gevDevWf TS e2 (pdOrdDev TS DS (m + 1) e2 hwit h2)⟩

/-- THE WITNESS IS DUPLICATE-FREE. -/
theorem pdOrdIndexInj (TS : Ptraces P D) (DS : Pdevs D) (m1 m2 : Nat) (e : Gev) :
    ptracesWit TS DS →
    DS.pdOrd[m1]? = some e → DS.pdOrd[m2]? = some e → m1 = m2 := by
  rintro ⟨_, _, hW3, _⟩ h1 h2
  obtain ⟨i, k⟩ := e
  rcases Nat.lt_trichotomy m1 m2 with hlt | heq | hgt
  · have := hW3 m1 m2 i k k hlt h1 h2; omega
  · exact heq
  · have := hW3 m2 m1 i k k hgt h2 h1; omega

/-- A SAME-AGENT gdev edge IS ALREADY A `gpo` EDGE. -/
theorem gdevGpo (TS : Ptraces P D) (DS : Pdevs D) (e1 e2 : Gev) :
    ptracesWit TS DS → gdev TS DS e1 e2 → e1.1 = e2.1 → WeakRobustGraph.gpo TS e1 e2 := by
  intro hwit hd hag
  obtain ⟨hw1, hw2⟩ := gdevWf TS DS e1 e2 hwit hd
  obtain ⟨_, _, hW3, _⟩ := hwit
  obtain ⟨m, h1, h2⟩ := hd
  obtain ⟨i1, k1⟩ := e1
  obtain ⟨i2, k2⟩ := e2
  simp only at hag
  subst hag
  exact ⟨rfl, hW3 m (m + 1) i1 k1 k2 (Nat.lt_succ_self m) h1 h2, hw1, hw2⟩

/-- THE TRANSITIVE FACT: earlier in the witness means `tc gdev`-earlier. -/
theorem gdevChain (TS : Ptraces P D) (DS : Pdevs D) (m1 m2 : Nat) (e1 e2 : Gev) :
    DS.pdOrd[m1]? = some e1 → DS.pdOrd[m2]? = some e2 → m1 < m2 →
    tc (gdev TS DS) e1 e2 := by
  intro h1 h2 hlt
  generalize hd : m2 - (m1 + 1) = d
  induction d generalizing m2 e2 with
  | zero =>
    have hm2 : m2 = m1 + 1 := by omega
    subst hm2
    exact tc_once ⟨m1, h1, h2⟩
  | succ d ih =>
    have hb : m2 < DS.pdOrd.length := lookup_lt_Some h2
    obtain ⟨e, he⟩ := Option.isSome_iff_exists.1
      (lookup_lt_is_Some_2 (l := DS.pdOrd) (i := m2 - 1) (by omega))
    have htc : tc (gdev TS DS) e1 e := ih (m2 - 1) e he (by omega) (by omega)
    refine tc_r htc ⟨m2 - 1, he, ?_⟩
    have hm : m2 - 1 + 1 = m2 := by omega
    rw [hm]; exact h2

theorem gdevNil (TS : Ptraces P D) (d : D) (e1 e2 : Gev) : ¬ gdev TS ⟨d, []⟩ e1 e2 := by
  rintro ⟨m, h1, _⟩
  simp at h1

/-! ### DELIVERABLE 5: STRUCTURAL ACYCLICITY PIECES -/

/-- (a) The po part embeds into the step index. -/
theorem gpoLt (TS : Ptraces P D) (e1 e2 : Gev) : WeakRobustGraph.gpo TS e1 e2 → e1.2 < e2.2 :=
  fun ⟨_, h, _⟩ => h

theorem tcGpoLt (TS : Ptraces P D) (e1 e2 : Gev) :
    tc (WeakRobustGraph.gpo TS) e1 e2 → e1.2 < e2.2 := by
  intro h
  induction h with
  | single hxy => exact gpoLt TS _ _ hxy
  | tail _ hyz ih => have := gpoLt TS _ _ hyz; omega

theorem gpoAcyclic (TS : Ptraces P D) (e : Gev) : ¬ tc (WeakRobustGraph.gpo TS) e e := by
  intro hc
  have := tcGpoLt TS e e hc
  omega

/-- (b) SINGLE-AGENT ACYCLICITY. -/
def gdepSa (TS : Ptraces P D) (e1 e2 : Gev) : Prop := gdep TS e1 e2 ∧ e1.1 = e2.1

theorem tcGdepSaLt (TS : Ptraces P D) (e1 e2 : Gev) :
    ptracesWf pstep TS → tc (gdepSa TS) e1 e2 → e1.1 = e2.1 ∧ e1.2 < e2.2 := by
  intro hwf h
  induction h with
  | single hxy =>
    obtain ⟨hd, hag⟩ := hxy
    exact ⟨hag, gdepSameAgentLt pstep TS _ _ hwf hd hag⟩
  | tail _ hyz ih =>
    obtain ⟨hd, hag⟩ := hyz
    have hlt := gdepSameAgentLt pstep TS _ _ hwf hd hag
    obtain ⟨hag', hlt'⟩ := ih
    exact ⟨hag'.trans hag, by omega⟩

theorem gdepSaAcyclic (TS : Ptraces P D) (e : Gev) :
    ptracesWf pstep TS → ¬ tc (gdepSa TS) e e := by
  intro hwf hc
  have := (tcGdepSaLt pstep TS e e hwf hc).2
  omega

/-- (c) THE NORMAL FORM: a `gdep` path either stayed inside ONE agent (and its step
index strictly grew) or it crosses agents somewhere. -/
theorem tcGdepSplit (TS : Ptraces P D) (e1 e2 : Gev) :
    ptracesWf pstep TS → tc (gdep TS) e1 e2 →
    (e1.1 = e2.1 ∧ e1.2 < e2.2) ∨
    (∃ x y, rtc (gdep TS) e1 x ∧ gdep TS x y ∧ x.1 ≠ y.1 ∧ rtc (gdep TS) y e2) := by
  intro hwf h
  induction h with
  | @single y hxy =>
    by_cases hag : e1.1 = y.1
    · exact .inl ⟨hag, gdepSameAgentLt pstep TS _ _ hwf hxy hag⟩
    · exact .inr ⟨e1, y, rtc_refl _, hxy, hag, rtc_refl _⟩
  | @tail y z hxy hyz ih =>
    by_cases hag : y.1 = z.1
    · have hlt := gdepSameAgentLt pstep TS _ _ hwf hyz hag
      rcases ih with ⟨hag', hlt'⟩ | ⟨u, v, hru, huv, hne, hrv⟩
      · exact .inl ⟨hag'.trans hag, by omega⟩
      · exact .inr ⟨u, v, hru, huv, hne, rtc_r hrv hyz⟩
    · exact .inr ⟨y, z, tc_rtc hxy, hyz, hag, rtc_refl _⟩

/-- Hence: ANY `gdep` cycle contains a CROSS-AGENT rf edge — the LB shape. -/
theorem tcGdepCross (TS : Ptraces P D) (e : Gev) :
    ptracesWf pstep TS → tc (gdep TS) e e →
    ∃ x y, rtc (gdep TS) e x ∧ WeakRobustGraph.grf TS x y ∧ x.1 ≠ y.1 ∧ rtc (gdep TS) y e := by
  intro hwf hc
  rcases tcGdepSplit pstep TS e e hwf hc with ⟨_, hlt⟩ | ⟨x, y, hrx, hxy, hne, hry⟩
  · exact absurd hlt (Nat.lt_irrefl _)
  · rcases hxy with ⟨hag, _⟩ | hrf
    · exact absurd hag hne
    · exact ⟨x, y, hrx, hrf, hne, hry⟩

/-! ### rf TOTALITY on a behavior: every read has a source -/

def logAuthored (log : List Wmsg) : Prop :=
  ∀ (p : Nat) (m : Wmsg), log[p]? = some m → m.wmTid.isSome

theorem logAuthoredPromiseStep (c c' : Wpcfg P D) :
    logAuthored c.pcLog → wpPromiseStep c c' → logAuthored c'.pcLog := by
  intro hla hs
  obtain ⟨j, agj, base, data, kc, _, _, rfl⟩ := wpPromiseStepInv c c' hs
  intro p m hp
  simp only at hp
  by_cases hlt : p < c.pcLog.length
  · rw [List.getElem?_append_left hlt] at hp
    exact hla p m hp
  · have hp' : p = c.pcLog.length := by
      have := lookup_lt_Some hp
      simp only [List.length_append, List.length_singleton] at this
      omega
    subst hp'
    rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self] at hp
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hp
    subst hp
    rfl

theorem logAuthoredPromiseRun (c c' : Wpcfg P D) :
    logAuthored c.pcLog → rtc (wpPromiseStep (P := P) (D := D)) c c' →
    logAuthored c'.pcLog := by
  intro h0 hr
  exact rtc_ind_r (fun c' => logAuthored c'.pcLog) c h0
    (fun y z _ hs ih => logAuthoredPromiseStep y z ih hs) c' hr

theorem logAuthoredInit (img : Image) (d0 : D) (ps : List P) :
    logAuthored (wpInit (P := P) (D := D) img d0 ps).pcLog := by
  intro p m hp
  simp [wpInit] at hp

/-- THE TRACED BEHAVIOR, GRAPH-READY: the traced form plus rf totality and rf
functionality. -/
theorem wpBehaviorGraph (img : Image) (d0 : D) (ps : List P) (c : Wpcfg P D) :
    pdevOk pstep pdev →
    latFreeProg pstep → wpBehavior pstep img d0 ps c →
    ∃ (mid : Wpcfg P D) (TS : Ptraces P D),
      rtc (wpPromiseStep (P := P) (D := D)) (wpInit img d0 ps) mid ∧
      ptracesOf pstep TS mid c ∧
      noPromises c ∧
      -- rf TOTALITY
      (∀ (e : Gev) (a : Int) (ts : Nat), gevReads TS e a ts → 0 < ts →
         ∃ e1, gevTs TS e1 = some ts ∧ WeakRobustGraph.grf TS e1 e) ∧
      -- rf FUNCTIONALITY
      (∀ (e1 e2 : Gev) (ts : Nat), gevTs TS e1 = some ts → gevTs TS e2 = some ts → e1 = e2) := by
  intro hpok hlfp hb
  obtain ⟨mid, TS, hprom, hTS, hnp, hacct⟩ :=
    wpBehaviorFulfilOnce pstep pdev img d0 ps c hpok hlfp hb
  have hwf : ptracesWf pstep TS := ptracesOfWf pstep TS mid c hTS
  refine ⟨mid, TS, hprom, hTS, hnp, ?_, fun e1 e2 ts h1 h2 => grfSourceUnique pstep TS e1 e2 ts hwf h1 h2⟩
  intro e a ts hr hpos
  obtain ⟨p, rfl⟩ : ∃ p, ts = p + 1 := ⟨ts - 1, by omega⟩
  obtain ⟨m, hm, _⟩ := gevReadsMsg pstep TS e a p hwf hr
  have hlog : TS.ptLog = mid.pcLog := hTS.2.1
  rw [hlog] at hm
  have hla : logAuthored mid.pcLog :=
    logAuthoredPromiseRun _ _ (logAuthoredInit img d0 ps) hprom
  obtain ⟨i, hi⟩ := Option.isSome_iff_exists.1 (hla p m hm)
  obtain ⟨T, hT, ⟨k, ev, hev, hts⟩, _⟩ := hacct p m i hm hi
  have hg : gevTs TS (i, k) = some (p + 1) := by
    unfold gevTs gevEv
    simp only [hT, Option.bind_some, hev]
    exact hts
  exact ⟨(i, k), hg, p + 1, a, hg, hr⟩

/-! ### THE ACYCLICITY GOAL (statement only — the coordinator's) -/

def gdepAcyclic (TS : Ptraces P D) : Prop := ∀ e, ¬ tc (gdep TS) e e

/-- The target theorem's SHAPE.  `pfViolationFree` is the SCowned arm's premise;
the SCfenced and SCexcl arms enter as the abstract premise `classPins`, so
nothing here claims violation-freedom ALONE suffices. -/
def gdepAcyclicityGoal (cls : Wmsg → StoreClass) (pub : Wpcfg P D → Nat → Prop)
    (classPins : Image → List P → Prop) : Prop :=
  ∀ (img : Image) (d0 : D) (ps : List P) (c mid : Wpcfg P D) (TS : Ptraces P D),
    latFreeProg pstep →
    pfViolationFree cls pub pstep pcls img d0 ps →
    classPins img ps →
    wpBehavior pstep img d0 ps c →
    rtc (wpPromiseStep (P := P) (D := D)) (wpInit img d0 ps) mid →
    ptracesOf pstep TS mid c →
    gdepAcyclic TS

/-- What the goal is WORTH, structurally: a counterexample cycle must contain a
cross-agent rf edge. -/
theorem gdepAcyclicSuffices (TS : Ptraces P D) :
    ptracesWf pstep TS →
    (∀ e x y, rtc (gdep TS) e x → WeakRobustGraph.grf TS x y → x.1 ≠ y.1 →
              rtc (gdep TS) y e → False) →
    gdepAcyclic TS := by
  intro hwf href e hc
  obtain ⟨x, y, hrx, hxy, hne, hry⟩ := tcGdepCross pstep TS e hwf hc
  exact href e x y hrx hxy hne hry

end graph

end Weak
