/-
Weak: **the write-serialization theorem** (M6 W2b, the second pillar: `co ⊆ tc gdep`
per byte).

Rocq: `iris/WeakRobustSer.v` @ xxvzwolszwmp.

The Rocq header, in substance: `WeakRobustAcyc.v` delivers the FIRST pillar of
W2b (the dependency graph `gdep = gpo ∪ grf` over a traced behavior is acyclic).
A topological sort of it is a promise-free run only if, for every byte `a`, the
writes of `a` appear in TIMESTAMP order along it — coherence order is contained
in `tc gdep`, per byte:

  `writesB TS a e1 t1 → writesB TS a e2 t2 → t1 < t2 → tc (gdep TS) e1 e2`.

This file proves it from LOCAL per-byte premises the Iris side of W2b discharges
at the kernel's data-structure rules.

THE VOCABULARY.  `writesB TS a e t`: `e` fulfilled `t` (`gevTs`) and the message
at log position `t - 1` covers byte `a`.  Its author is `e.1` (`gevTsMsg`), which
turns "same author" into "same trace" and "different author" into "the
message's `wmTid` disagrees".

THE FOUR DELIVERABLES.  (1) THE SAME-AUTHOR LEMMA `serSameAuthor`, premise-free:
a fulfil of `t` demands `coh a < t` in its pre-state (`astepOkFulfilCoh`) and
leaves `coh a ≥ t` in its post-state (`astepOkFulfilPostCoh`, new here), and
`coh` only grows along a trace (`astepsWsLe`); so the earlier timestamp is the
earlier trace position.  (2) THE PER-BYTE PREMISES: `swByte` (single writer),
`exclByte` (every write is behind an all-same-author prefix or is an rmw READING
the byte — the lock/AMO shape), `handoff` (a cross-author co-consecutive pair is
separated by a SYNC byte written po-after `e1` by `e1`'s agent and read back
po-before `e2` by `e2`'s agent — the release/acquire shape);
`WeakRobustSer.byteOk` is the disjunction.  (3) THE THEOREM `coSerialized`, by
STRATIFICATION: sync bytes are closed first (`syncConnect`, `sw`/`excl` arms
only, never recursing into `handoff`), then the general per-byte theorem uses it
non-recursively.  Each layer proves connectivity for co-consecutive pairs and
chains (`writesBChain`, fuel induction on `t2 - t1`); for a consecutive pair:
same author → (1); `excl` → the rmw's `exclOk` pins its read timestamp to
exactly `t1`, a single rf edge; `handoff` → the path
`e1 →po? er →tc(sync b) es →rf rr →po? e2`.  (4) THE BEHAVIOR-LEVEL WRAPPER
`wpBehaviorCoSerialized`, discharging `ptracesWf` and `writesFulfilled` from
`wpBehaviorFulfilOnce`.

DELTAS FROM THE W2b DESIGN NOTE (each weakens or removes a premise):
co-consecutiveness is spelled on the LOG (`coConsec`, decidable through
`writesInb`); the rf totality/functionality premises are replaced by
`writesFulfilled` (rf functionality is derived, `grfSourceUnique`); `handoff`
carries neither `t1 ≤ tr` nor a source event for `tStar`.  Deliberately
independent of `WeakRobustAcyc.v`.  DEPENDENCY-FREE: no Iris, no Sail.

**Deviations from Rocq.**

1. NAMES: lowerCamelCase as `Weak/WeakMem.lean` deviation 1.  File-qualified
   (in `notes/weak-port-dupnames.json`): `byte_ok` ↦ `WeakRobustSer.byteOk`.
2. VOCABULARY: as `Weak/WeakRobustGraph.lean` deviation 2 (`Z` ↦ `Int`,
   `is_Some o` ↦ `o.isSome`, `S p` ↦ `p + 1`, `tvs.*1` ↦ `tvs.map Prod.fst`).
3. SECTION VARIABLES: `pstep` (and `pdev`) are explicit arguments exactly where
   a statement mentions them (`WeakRobustGraph` deviation 3); `writesBWf`,
   `writesBChain`, `gpoLeRtc` and the definitions take neither.
4. O2 / owner decision D4: the three `astepOk_*` lemmas gain the Lean-only
   `LIFetch` arm (vacuous: it fulfils nothing and reads nothing,
   `WeakRobustGraph` deviation 4).
5. Not imported: `Weak.WeakAxiomatic` (Rocq imports it for the parked fold
   lemmas and `acc_addr`; Lean's `storePostRunDCoh` is stated at `base + j`, so
   the `acc_addr` rewrite step of `astep_ok_fulfil_post_coh` is gone).  Rocq's
   `msg_byte_in_range` notation is called as `msgByteRange`.

**Name map** (Rocq → Lean): `astep_ok_fulfil_post_coh` ↦ `astepOkFulfilPostCoh`;
`astep_ok_read_lt` ↦ `astepOkReadLt`; `astep_ok_read_excl` ↦ `astepOkReadExcl`;
`writes_b` ↦ `writesB`; `co_consec` ↦ `coConsec`; `sw_byte` ↦ `swByte`;
`excl_byte` ↦ `exclByte`; `handoff`; `byte_ok` ↦ `WeakRobustSer.byteOk`;
`ptraces_bytes_ok` ↦ `ptracesBytesOk`; `writes_fulfilled` ↦ `writesFulfilled`;
`co_tc` ↦ `coTc`; `writes_b_wf` ↦ `writesBWf`; `writes_b_pos` ↦ `writesBPos`;
`writes_b_author` ↦ `writesBAuthor`; `writes_b_unique` ↦ `writesBUnique`;
`writes_b_coh` ↦ `writesBCoh`; `ser_same_author` ↦ `serSameAuthor`;
`ser_same_author_tc` ↦ `serSameAuthorTc`; `gev_read_fulfil` ↦ `gevReadFulfil`;
`gev_reads_source` ↦ `gevReadsSource`; `writes_b_chain` ↦ `writesBChain`;
`ser_excl_consec` ↦ `serExclConsec`; `byte_connect_sw_excl` ↦
`byteConnectSwExcl`; `sync_connect` ↦ `syncConnect`; `gpo_le_rtc` ↦ `gpoLeRtc`;
`ser_handoff_consec` ↦ `serHandoffConsec`; `co_serialized` ↦ `coSerialized`;
`co_serialized_pkg` ↦ `coSerializedPkg`; `ptraces_of_writes_fulfilled` ↦
`ptracesOfWritesFulfilled`; `wp_behavior_co_serialized` ↦
`wpBehaviorCoSerialized`.

**Not ported:** nothing (every Rocq definition and lemma has a Lean twin).

**Statements checked** (by hand, against Rocq): all of them.
-/
import Weak.WeakRobustGraph

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std Wlabel

/-! ## `astepOk`-level facts

Three additions to `WeakRobustGraph`'s `astepOk*` block, in the same style: one
case per LABEL, not one per rule. -/

section astep

variable {P : Type}

/-- THE FULFIL RAISES `coh`: the POST-state half of `astepOkFulfilCoh`
(`coh a ≥ ts` on every byte of the fulfilled message).  The message's
`base`/`data` are read off the label, and `f` ends in a `storePostRunD` over
exactly those bytes. -/
theorem astepOkFulfilPostCoh (img : Image) (log : List Wmsg) (i : Nat) (ag : Wpagent P)
    (l : Wlabel) (f : Wstate → Wstate) (ts : Nat) (m : Wmsg) (a : Int) :
    astepOk img log i ag l f (some ts) →
    log[ts - 1]? = some m → (msgByte m a).isSome →
    ts ≤ coh (f ag.paWs) a := by
  intro h hm hb
  cases l with
  | LSilent => obtain ⟨_, ⟨⟩⟩ := h
  | LLoad => obtain ⟨_, _, ⟨⟩⟩ := h
  | LStore rl base data asrc vsrc =>
    obtain ⟨ts', k, _, hlog, _, rfl, hD⟩ := h
    cases hD
    rw [hlog] at hm; cases hm
    obtain ⟨j, hj, rfl⟩ := msgByteRange _ _ hb
    exact storePostRunDCoh _ _ _ _ _ _ _ _ hj
  | LRmw aq rl base tvs data asrc vsrc =>
    obtain ⟨ts', k, _, _, hlog, _, _, _, rfl, hD⟩ := h
    cases hD
    rw [hlog] at hm; cases hm
    obtain ⟨j, hj, rfl⟩ := msgByteRange _ _ hb
    exact storePostRunDCoh _ _ _ _ _ _ _ _ hj
  | LFence => obtain ⟨_, ⟨⟩⟩ := h
  | LDev => obtain ⟨_, ⟨⟩⟩ := h
  | LRegW => obtain ⟨_, ⟨⟩⟩ := h
  | LCtrl => obtain ⟨_, ⟨⟩⟩ := h
  | LInstr => obtain ⟨_, ⟨⟩⟩ := h
  -- THE RMW SPLIT (S2)
  | LExLoad => obtain ⟨_, _, ⟨⟩⟩ := h
  | LExStore rl base data asrc vsrc =>
    obtain ⟨ts', k, R, _, hlog, _, _, _, _, _, rfl, hD⟩ := h
    cases hD
    rw [hlog] at hm; cases hm
    obtain ⟨j, hj, rfl⟩ := msgByteRange _ _ hb
    exact storePostRunDCoh _ _ _ _ _ _ _ _ hj
  | LIFetch => obtain ⟨_, _, ⟨⟩⟩ := h

/-- A step that BOTH reads `(a, tr)` and fulfils `ts` is an `LRmw`, and its read
timestamp is strictly below the one it fulfils (`astepOkReadFulfilSame`,
quantified). -/
theorem astepOkReadLt (img : Image) (log : List Wmsg) (i : Nat) (ag : Wpagent P)
    (l : Wlabel) (f : Wstate → Wstate) (ts tr : Nat) (a : Int) :
    astepOk img log i ag l f (some ts) → (a, tr) ∈ lbReads l → tr < ts := by
  intro h hin
  cases l with
  | LLoad => obtain ⟨_, _, ⟨⟩⟩ := h
  | LRmw aq rl base tvs data asrc vsrc =>
    obtain ⟨ts', k, hlen, _, _, _, _, ⟨hcoh, _⟩, _, hD⟩ := h
    cases hD
    obtain ⟨j, v, hj, rfl⟩ := (memTvsReads _ _ _ _).1 hin
    have hts : (tvs.map Prod.fst)[j]? = some tr := by rw [List.getElem?_map, hj]; rfl
    have hjlt : j < data.length := by rw [← hlen]; exact lookup_lt_Some hj
    have hge := loadPostRunDCoh ag.paWs aq (srcsView ag.paWs asrc) base (tvs.map Prod.fst) j tr hts
    have hlt := hcoh j hjlt
    omega
  -- THE RMW SPLIT (S2): vacuous on both halves (design §7)
  | LExLoad => obtain ⟨_, _, ⟨⟩⟩ := h
  | _ => simp [lbReads] at hin

/-- ... and its EXCLUSIVITY WINDOW: no OTHER agent's write to the byte it read
lands in `(tr, ts - 1]` — the `LRmw` arm's `exclOk`, at byte `base + j`. -/
theorem astepOkReadExcl (img : Image) (log : List Wmsg) (i : Nat) (ag : Wpagent P)
    (l : Wlabel) (f : Wstate → Wstate) (ts tr : Nat) (a : Int) :
    astepOk img log i ag l f (some ts) → (a, tr) ∈ lbReads l →
    ¬ writesInBy log (fun tid => tid ≠ some i) a tr (ts - 1) := by
  intro h hin
  cases l with
  | LLoad => obtain ⟨_, _, ⟨⟩⟩ := h
  | LRmw aq rl base tvs data asrc vsrc =>
    obtain ⟨ts', k, _, _, _, _, hexcl, _, _, hD⟩ := h
    cases hD
    obtain ⟨j, v, hj, rfl⟩ := (memTvsReads _ _ _ _).1 hin
    exact hexcl j tr v hj
  -- THE RMW SPLIT (S2): vacuous on both halves (design §7)
  | LExLoad => obtain ⟨_, _, ⟨⟩⟩ := h
  | _ => simp [lbReads] at hin

end astep

/-! ## DELIVERABLE 2: the vocabulary and the per-byte premises

Functions of the trace bundle alone — no `pstep`, no Iris. -/

/-- `e` writes byte `a` at timestamp `t`. -/
def writesB {P D : Type} (TS : Ptraces P D) (a : Int) (e : Gev) (t : Nat) : Prop :=
  gevTs TS e = some t ∧ ∃ m, TS.ptLog[t - 1]? = some m ∧ (msgByte m a).isSome

/-- CO-CONSECUTIVE: no message strictly between `t1` and `t2` writes `a` (on the
LOG; decidable via `writesInb`). -/
def coConsec {P D : Type} (TS : Ptraces P D) (a : Int) (t1 t2 : Nat) : Prop :=
  ¬ writesIn TS.ptLog a t1 (t2 - 1)

/-- SINGLE WRITER: all writes of `a` come from one agent. -/
def swByte {P D : Type} (TS : Ptraces P D) (a : Int) : Prop :=
  ∀ e1 e2 t1 t2, writesB TS a e1 t1 → writesB TS a e2 t2 → e1.1 = e2.1

/-- EXCLUSIVITY-CHAINED: every write of `a` has only same-author writes below it,
or is an rmw whose read half reads byte `a`. -/
def exclByte {P D : Type} (TS : Ptraces P D) (a : Int) : Prop :=
  ∀ e t, writesB TS a e t →
    (∀ e' t', writesB TS a e' t' → t' < t → e'.1 = e.1) ∨ (∃ tr, gevReads TS e a tr)

/-- THE OWNED-BYTE HANDOFF: a cross-author co-consecutive pair is separated by a
sync byte `b`, written by `e1`'s agent at or after `e1` and read by `e2`'s agent
at or before `e2`, at a timestamp at least the write's. -/
def handoff {P D : Type} (TS : Ptraces P D) (sync : Int → Prop) (a : Int) : Prop :=
  ∀ e1 e2 t1 t2,
    writesB TS a e1 t1 → writesB TS a e2 t2 →
    e1.1 ≠ e2.1 → t1 < t2 → coConsec TS a t1 t2 →
    ∃ (b : Int) (er : Gev) (tr : Nat) (rr : Gev) (tStar : Nat),
      sync b ∧
      writesB TS b er tr ∧ er.1 = e1.1 ∧ e1.2 ≤ er.2 ∧
      gevReads TS rr b tStar ∧ rr.1 = e2.1 ∧ rr.2 ≤ e2.2 ∧
      tr ≤ tStar

/-- THE PER-BYTE OBLIGATION. -/
def WeakRobustSer.byteOk {P D : Type} (TS : Ptraces P D) (sync : Int → Prop) (a : Int) :
    Prop :=
  swByte TS a ∨ exclByte TS a ∨ handoff TS sync a

/-- THE BUNDLE-LEVEL PREMISE: sync bytes are `sw`-or-`excl` (stratification), and
every byte is `byteOk`. -/
def ptracesBytesOk {P D : Type} (TS : Ptraces P D) (sync : Int → Prop) : Prop :=
  (∀ b, sync b → swByte TS b ∨ exclByte TS b) ∧ (∀ a, WeakRobustSer.byteOk TS sync a)

/-- FULFILMENT TOTALITY: every log message is fulfilled by some event. -/
def writesFulfilled {P D : Type} (TS : Ptraces P D) : Prop :=
  ∀ (t : Nat) m, 0 < t → TS.ptLog[t - 1]? = some m → ∃ e, gevTs TS e = some t

/-- THE CONCLUSION, per byte: coherence order is contained in `tc gdep`. -/
def coTc {P D : Type} (TS : Ptraces P D) (a : Int) : Prop :=
  ∀ e1 e2 t1 t2, writesB TS a e1 t1 → writesB TS a e2 t2 → t1 < t2 → tc (gdep TS) e1 e2

section ser

variable {P D : Type}
variable (pstep : P → D → Wlabel → P → D → Prop)
variable (pdev : P → Wlabel → P → Bool)

/-! ## `writesB` basics -/

theorem writesBWf (TS : Ptraces P D) (a : Int) (e : Gev) (t : Nat) :
    writesB TS a e t → gevWf TS e :=
  fun h => gevTsWf TS e t h.1

theorem writesBPos (TS : Ptraces P D) (a : Int) (e : Gev) (t : Nat) :
    ptracesWf pstep TS → writesB TS a e t → 0 < t :=
  fun hwf h => gevTsPos pstep TS e t hwf h.1

/-- The message a write names is authored by the writing agent. -/
theorem writesBAuthor (TS : Ptraces P D) (a : Int) (e : Gev) (t : Nat) :
    ptracesWf pstep TS → writesB TS a e t →
    ∃ m, TS.ptLog[t - 1]? = some m ∧ (msgByte m a).isSome ∧ m.wmTid = some e.1 := by
  rintro hwf ⟨hts, m, hm, hb⟩
  obtain ⟨base, data, kc, hm'⟩ := gevTsMsg pstep TS e t hwf hts
  rw [hm'] at hm; cases hm
  exact ⟨_, hm', hb, rfl⟩

/-- rf FUNCTIONALITY, derived: two events fulfilling one timestamp are equal. -/
theorem writesBUnique (TS : Ptraces P D) (a1 a2 : Int) (e1 e2 : Gev) (t : Nat) :
    ptracesWf pstep TS → writesB TS a1 e1 t → writesB TS a2 e2 t → e1 = e2 :=
  fun hwf h1 h2 => grfSourceUnique pstep TS e1 e2 t hwf h1.1 h2.1

/-- The `coh` bracket around a write's step: `coh a < t` before, `t ≤ coh a`
after. -/
theorem writesBCoh (TS : Ptraces P D) (a : Int) (e : Gev) (t : Nat) (T : Atrace P D) :
    ptracesWf pstep TS → TS.ptTrs[e.1]? = some T → writesB TS a e t →
    ∃ ag agn, T.atAgs[e.2]? = some ag ∧ T.atAgs[e.2 + 1]? = some agn ∧
      coh ag.paWs a < t ∧ t ≤ coh agn.paWs a := by
  rintro hwf hT ⟨hts, m, hm, hb⟩
  obtain ⟨T', ev, hT', hev', hts'⟩ := gevTsSome TS e t hts
  rw [hT] at hT'; cases hT'
  have hev : gevEv TS e = some ev := by unfold gevEv; rw [hT]; exact hev'
  obtain ⟨T'', ag, agn, st', f, hT'', hag, hagn, _, hok, hagne⟩ := gevStep pstep TS e ev hwf hev
  rw [hT] at hT''; cases hT''
  rw [hts'] at hok
  refine ⟨ag, agn, hag, hagn, astepOkFulfilCoh _ _ _ _ _ _ t m a hok hm hb, ?_⟩
  rw [hagne]; exact astepOkFulfilPostCoh _ _ _ _ _ _ t m a hok hm hb

/-! ## DELIVERABLE 1: THE SAME-AUTHOR LEMMA (premise-free) -/

theorem serSameAuthor (TS : Ptraces P D) (a : Int) (e1 e2 : Gev) (t1 t2 : Nat) :
    ptracesWf pstep TS →
    writesB TS a e1 t1 → writesB TS a e2 t2 →
    e1.1 = e2.1 → t1 < t2 →
    WeakRobustGraph.gpo TS e1 e2 := by
  intro hwf h1 h2 hag hlt
  have hw1 := writesBWf TS a e1 t1 h1
  have hw2 := writesBWf TS a e2 t2 h2
  obtain ⟨T, hT, _⟩ := (gevWfBounds TS e1).1 hw1
  have hT2 : TS.ptTrs[e2.1]? = some T := by rw [← hag]; exact hT
  obtain ⟨ag1, agn1, hag1, _, hlo1, _⟩ := writesBCoh pstep TS a e1 t1 T hwf hT h1
  obtain ⟨ag2, agn2, _, hagn2, _, hhi2⟩ := writesBCoh pstep TS a e2 t2 T hwf hT2 h2
  rcases Nat.lt_trichotomy e1.2 e2.2 with hk | hk | hk
  · exact ⟨hag, hk, hw1, hw2⟩
  · -- same index and same agent: the same event, so `t1 = t2`
    exfalso
    have he : e1 = e2 := Prod.ext hag hk
    subst he
    have := Option.some.inj (h1.1.symm.trans h2.1)
    omega
  · -- `e2` came first: `coh a` was already `≥ t2` when `e1` ran
    exfalso
    have hmono := astepsWsLe pstep TS.ptImg TS.ptLog e1.1 T.atAgs T.atEvs (e2.2 + 1) e1.2
      agn2 ag1 (hwf _ _ hT) (by omega) hagn2 hag1
    have := wsLeCoh _ _ a hmono
    omega

theorem serSameAuthorTc (TS : Ptraces P D) (a : Int) (e1 e2 : Gev) (t1 t2 : Nat) :
    ptracesWf pstep TS →
    writesB TS a e1 t1 → writesB TS a e2 t2 →
    e1.1 = e2.1 → t1 < t2 →
    tc (gdep TS) e1 e2 :=
  fun hwf h1 h2 hag hlt => tc_once (Or.inl (serSameAuthor pstep TS a e1 e2 t1 t2 hwf h1 h2 hag hlt))

/-! ## Reads, and the events behind them -/

/-- A step that reads `(a, tr)` and fulfils `t` has `tr < t` and no FOREIGN write
to `a` in `(tr, t - 1]`. -/
theorem gevReadFulfil (TS : Ptraces P D) (e : Gev) (a : Int) (tr t : Nat) :
    ptracesWf pstep TS → gevReads TS e a tr → gevTs TS e = some t →
    tr < t ∧ ¬ writesInBy TS.ptLog (fun tid => tid ≠ some e.1) a tr (t - 1) := by
  rintro hwf ⟨l, hl, hin⟩ hts
  obtain ⟨T, ev, hT, hev', rfl⟩ := gevLbSome TS e l hl
  have hev : gevEv TS e = some ev := by unfold gevEv; rw [hT]; exact hev'
  have hts' : ev.aeTs = some t := by unfold gevTs at hts; rw [hev] at hts; exact hts
  obtain ⟨_, ag, agn, st', f, _, _, _, _, hok, _⟩ := gevStep pstep TS e ev hwf hev
  rw [hts'] at hok
  exact ⟨astepOkReadLt _ _ _ _ _ _ t tr a hok hin, astepOkReadExcl _ _ _ _ _ _ t tr a hok hin⟩

/-- The SOURCE of a read of a nonzero timestamp, via `writesFulfilled`: a write of
the byte read, with the rf edge. -/
theorem gevReadsSource (TS : Ptraces P D) (e : Gev) (a : Int) (tr : Nat) :
    ptracesWf pstep TS → writesFulfilled TS →
    gevReads TS e a tr → 0 < tr →
    ∃ er, writesB TS a er tr ∧ WeakRobustGraph.grf TS er e := by
  intro hwf hwfu hr hpos
  obtain ⟨p, rfl⟩ : ∃ p, tr = p + 1 := ⟨tr - 1, by omega⟩
  obtain ⟨m, hm, hb⟩ := gevReadsMsg pstep TS e a p hwf hr
  have hm' : TS.ptLog[p + 1 - 1]? = some m := by rw [Nat.add_sub_cancel]; exact hm
  obtain ⟨er, hts⟩ := hwfu (p + 1) m (by omega) hm'
  exact ⟨er, ⟨hts, m, hm', hb⟩, p + 1, a, hts, hr⟩

/-! ## CHAINING: from co-consecutive pairs to the whole order

A fuel induction on `t2 - t1`, case-splitting on the decidable `writesInb`. -/

theorem writesBChain (TS : Ptraces P D) (a : Int) :
    writesFulfilled TS →
    (∀ e1 e2 t1 t2, writesB TS a e1 t1 → writesB TS a e2 t2 →
       t1 < t2 → coConsec TS a t1 t2 → tc (gdep TS) e1 e2) →
    coTc TS a := by
  intro hwfu hcons
  have hgen : ∀ n e1 e2 t1 t2, t2 - t1 ≤ n →
      writesB TS a e1 t1 → writesB TS a e2 t2 → t1 < t2 → tc (gdep TS) e1 e2 := by
    intro n
    induction n with
    | zero => intro _ _ _ _ hn _ _ hlt; omega
    | succ n ih =>
      intro e1 e2 t1 t2 hn h1 h2 hlt
      cases hb : writesInb TS.ptLog a t1 (t2 - 1) with
      | true =>
        -- a message writes `a` strictly between: split the interval
        obtain ⟨t', hlo, hhi, m, hm, hbyte⟩ := writesInCompute _ _ _ _ hb
        obtain ⟨e', hts'⟩ := hwfu t' m (by omega) hm
        have h' : writesB TS a e' t' := ⟨hts', m, hm, hbyte⟩
        exact tc_transitive (ih e1 e' t1 t' (by omega) h1 h' (by omega))
          (ih e' e2 t' t2 (by omega) h' h2 (by omega))
      | false => exact hcons e1 e2 t1 t2 h1 h2 hlt (notWritesInCompute _ _ _ _ hb)
  intro e1 e2 t1 t2 h1 h2 hlt
  exact hgen (t2 - t1) e1 e2 t1 t2 (Nat.le_refl _) h1 h2 hlt

/-! ## THE `excl` ARM on a co-consecutive pair

The rmw's read timestamp is pinned to `t1` exactly: below is refuted by
`exclOk` (`t1` is a foreign write in the window), above by co-consecutiveness
(the read's own message would be a write of `a` strictly between). -/

theorem serExclConsec (TS : Ptraces P D) (a : Int) (e1 e2 : Gev) (t1 t2 : Nat) :
    ptracesWf pstep TS → exclByte TS a →
    writesB TS a e1 t1 → writesB TS a e2 t2 →
    e1.1 ≠ e2.1 → t1 < t2 → coConsec TS a t1 t2 →
    WeakRobustGraph.grf TS e1 e2 := by
  intro hwf hex h1 h2 hne hlt hcc
  rcases hex e2 t2 h2 with hall | ⟨tr, hr⟩
  · exact (hne (hall e1 t1 h1 hlt)).elim
  obtain ⟨hrlt, hnw⟩ := gevReadFulfil pstep TS e2 a tr t2 hwf hr h2.1
  rcases Nat.lt_trichotomy tr t1 with hc | hc | hc
  · -- `t1` itself sits in the exclusivity window, and it is FOREIGN
    exfalso
    obtain ⟨m, hm, hbyte, htid⟩ := writesBAuthor pstep TS a e1 t1 hwf h1
    exact hnw ⟨t1, hc, by omega, m, hm, hbyte,
      fun heq => hne (Option.some.inj (htid.symm.trans heq))⟩
  · -- the read is EXACTLY `e1`'s write: the rf edge
    subst hc
    exact ⟨tr, a, h1.1, hr⟩
  · -- the read's own message would be a write of `a` strictly between
    exfalso
    obtain ⟨p, rfl⟩ : ∃ p, tr = p + 1 := ⟨tr - 1, by omega⟩
    obtain ⟨m, hm, hbyte⟩ := gevReadsMsg pstep TS e2 a p hwf hr
    exact hcc ⟨p + 1, hc, by omega, m, by rw [Nat.add_sub_cancel]; exact hm, hbyte⟩

/-! ## LAYER 1: single-writer or exclusivity-chained bytes

Self-contained (no `handoff`); the layer the SYNC bytes must live in. -/

theorem byteConnectSwExcl (TS : Ptraces P D) (a : Int) :
    ptracesWf pstep TS → writesFulfilled TS →
    (swByte TS a ∨ exclByte TS a) →
    coTc TS a := by
  intro hwf hwfu harm
  refine writesBChain TS a hwfu ?_
  intro e1 e2 t1 t2 h1 h2 hlt hcc
  by_cases hag : e1.1 = e2.1
  · exact serSameAuthorTc pstep TS a e1 e2 t1 t2 hwf h1 h2 hag hlt
  · rcases harm with hsw | hex
    · exact (hag (hsw e1 e2 t1 t2 h1 h2)).elim
    · exact tc_once (Or.inr (serExclConsec pstep TS a e1 e2 t1 t2 hwf hex h1 h2 hag hlt hcc))

/-- The sync layer, closed. -/
theorem syncConnect (TS : Ptraces P D) (sync : Int → Prop) :
    ptracesWf pstep TS → writesFulfilled TS →
    (∀ b, sync b → swByte TS b ∨ exclByte TS b) →
    ∀ b, sync b → coTc TS b :=
  fun hwf hwfu hsync b hb => byteConnectSwExcl pstep TS b hwf hwfu (hsync b hb)

/-! ## LAYER 2: the `handoff` arm -/

/-- A po-or-equal hop, as an `rtc`. -/
theorem gpoLeRtc (TS : Ptraces P D) (e e' : Gev) :
    e.1 = e'.1 → e.2 ≤ e'.2 → gevWf TS e → gevWf TS e' →
    rtc (gdep TS) e e' := by
  intro hag hle hw hw'
  by_cases heq : e.2 = e'.2
  · have he : e = e' := Prod.ext hag heq
    subst he
    exact rtc_refl _
  · exact rtc_once (Or.inl ⟨hag, by omega, hw, hw'⟩)

/-- THE PATH `e1 →po? er →tc(sync b) es →rf rr →po? e2`; the middle hop is an
equality when `tr = tStar` (rf functionality), else layer 1 on `b`. -/
theorem serHandoffConsec (TS : Ptraces P D) (sync : Int → Prop) (a : Int) (e1 e2 : Gev)
    (t1 t2 : Nat) :
    ptracesWf pstep TS → writesFulfilled TS →
    (∀ b, sync b → swByte TS b ∨ exclByte TS b) →
    handoff TS sync a →
    writesB TS a e1 t1 → writesB TS a e2 t2 →
    e1.1 ≠ e2.1 → t1 < t2 → coConsec TS a t1 t2 →
    tc (gdep TS) e1 e2 := by
  intro hwf hwfu hsync hho h1 h2 hne hlt hcc
  obtain ⟨b, er, tr, rr, tStar, hb, her, her1, hpo1, hrr, hrr1, hpo2, hts⟩ :=
    hho e1 e2 t1 t2 h1 h2 hne hlt hcc
  -- the two po hops
  have hstep1 : rtc (gdep TS) e1 er :=
    gpoLeRtc TS e1 er her1.symm hpo1 (writesBWf TS a e1 t1 h1) (writesBWf TS b er tr her)
  have hstep4 : rtc (gdep TS) rr e2 :=
    gpoLeRtc TS rr e2 hrr1 hpo2 (gevReadsWf TS rr b tStar hrr) (writesBWf TS a e2 t2 h2)
  -- the source of `rr`'s read of the sync byte
  have hpos : 0 < tr := writesBPos pstep TS b er tr hwf her
  obtain ⟨es, hes, hrf⟩ := gevReadsSource pstep TS rr b tStar hwf hwfu hrr (by omega)
  -- the sync-byte hop
  have hstep2 : rtc (gdep TS) er es := by
    by_cases hee : tr = tStar
    · subst hee
      rw [writesBUnique pstep TS b b er es tr hwf her hes]
      exact rtc_refl _
    · exact tc_rtc (byteConnectSwExcl pstep TS b hwf hwfu (hsync b hb) er es tr tStar her hes
        (by omega))
  exact tc_rtc_l (rtc_transitive hstep1 hstep2) (tc_rtc_r (tc_once (Or.inr hrf)) hstep4)

/-! ## DELIVERABLE 3: THE CONNECTIVITY THEOREM -/

theorem coSerialized (TS : Ptraces P D) (sync : Int → Prop) :
    ptracesWf pstep TS → writesFulfilled TS →
    (∀ b, sync b → swByte TS b ∨ exclByte TS b) →
    (∀ a, WeakRobustSer.byteOk TS sync a) →
    ∀ a e1 e2 t1 t2,
      writesB TS a e1 t1 → writesB TS a e2 t2 → t1 < t2 →
      tc (gdep TS) e1 e2 := by
  intro hwf hwfu hsync hbytes a
  rcases hbytes a with hsw | hex | hho
  · exact byteConnectSwExcl pstep TS a hwf hwfu (Or.inl hsw)
  · exact byteConnectSwExcl pstep TS a hwf hwfu (Or.inr hex)
  · refine writesBChain TS a hwfu ?_
    intro e1 e2 t1 t2 h1 h2 hlt hcc
    by_cases hag : e1.1 = e2.1
    · exact serSameAuthorTc pstep TS a e1 e2 t1 t2 hwf h1 h2 hag hlt
    · exact serHandoffConsec pstep TS sync a e1 e2 t1 t2 hwf hwfu hsync hho h1 h2 hag hlt hcc

/-- The same, packaged against `ptracesBytesOk`. -/
theorem coSerializedPkg (TS : Ptraces P D) (sync : Int → Prop) :
    ptracesWf pstep TS → writesFulfilled TS → ptracesBytesOk TS sync →
    ∀ a, coTc TS a := by
  rintro hwf hwfu ⟨hsync, hbytes⟩ a
  exact coSerialized pstep TS sync hwf hwfu hsync hbytes a

/-! ## DELIVERABLE 4: THE BEHAVIOR-LEVEL WRAPPER

`writesFulfilled` is discharged: every logged message is authored
(`logAuthored`) and every authored message is fulfilled in its author's trace
(`wpBehaviorFulfilOnce`). -/

theorem ptracesOfWritesFulfilled (TS : Ptraces P D) (mid c : Wpcfg P D) :
    ptracesOf pstep TS mid c →
    logAuthored mid.pcLog →
    (∀ (p : Nat) (m : Wmsg) (i : Nat), mid.pcLog[p]? = some m → m.wmTid = some i →
       ∃ T, TS.ptTrs[i]? = some T ∧
         (∃ (k : Nat) (ev : Aev D), T.atEvs[k]? = some ev ∧ ev.aeTs = some (p + 1)) ∧
         (∀ (k1 k2 : Nat) (ev1 ev2 : Aev D),
            T.atEvs[k1]? = some ev1 → ev1.aeTs = some (p + 1) →
            T.atEvs[k2]? = some ev2 → ev2.aeTs = some (p + 1) →
            k1 = k2)) →
    writesFulfilled TS := by
  intro hTS hla hacct t m hpos hm
  obtain ⟨p, rfl⟩ : ∃ p, t = p + 1 := ⟨t - 1, by omega⟩
  rw [Nat.add_sub_cancel, hTS.2.1] at hm
  obtain ⟨i, hi⟩ := Option.isSome_iff_exists.1 (hla p m hm)
  obtain ⟨T, hT, ⟨k, ev, hev, hts⟩, _⟩ := hacct p m i hm hi
  exact ⟨(i, k), by simp [gevTs, gevEv, hT, hev, hts]⟩

theorem wpBehaviorCoSerialized (img : Image) (d0 : D) (ps : List P) (c : Wpcfg P D) :
    pdevOk pstep pdev →
    latFreeProg pstep → wpBehavior pstep img d0 ps c →
    ∃ (mid : Wpcfg P D) (TS : Ptraces P D),
      rtc (wpPromiseStep (P := P) (D := D)) (wpInit img d0 ps) mid ∧
      ptracesOf pstep TS mid c ∧
      noPromises c ∧
      ptracesWf pstep TS ∧
      writesFulfilled TS ∧
      (∀ sync, ptracesBytesOk TS sync → ∀ a, coTc TS a) := by
  intro hpok hlfp hb
  obtain ⟨mid, TS, hprom, hTS, hnp, hacct⟩ :=
    wpBehaviorFulfilOnce pstep pdev img d0 ps c hpok hlfp hb
  have hwf := ptracesOfWf pstep TS mid c hTS
  have hla : logAuthored mid.pcLog := logAuthoredPromiseRun _ _ (logAuthoredInit img d0 ps) hprom
  have hwfu := ptracesOfWritesFulfilled pstep TS mid c hTS hla hacct
  exact ⟨mid, TS, hprom, hTS, hnp, hwf, hwfu,
    fun sync hok => coSerializedPkg pstep TS sync hwf hwfu hok⟩

end ser

/-! ## What W2b's simulation inherits from this file

- `writesB` / `coConsec` / `coTc`: the per-byte coherence-order vocabulary, on
  the trace bundle alone.
- `serSameAuthor` (and `serSameAuthorTc`): PREMISE-FREE — two writes of a byte
  by one agent are in program order iff in timestamp order.
- `swByte` / `exclByte` / `handoff` / `WeakRobustSer.byteOk` / `ptracesBytesOk`:
  the exact per-byte obligations the Iris layer discharges (one per discipline:
  single-writer fields, lock words and AMO-guarded counters,
  release/acquire-published payloads); each is a property of the bundle alone,
  and `handoff`'s antecedent is the decidable log-level co-consecutiveness.
- The STRATIFICATION `syncConnect` / `byteConnectSwExcl` then `coSerialized`: a
  constraint on the caller's choice of `sync`, not on the proof.
- `coSerialized` / `wpBehaviorCoSerialized`: the theorem, and its behavior-level
  form with `ptracesWf` and `writesFulfilled` discharged.

NOT here: acyclicity (`WeakRobustAcyc.v`), the topological sort, and any use of
the classification `cls` or the publication `pub`. -/

end Weak
