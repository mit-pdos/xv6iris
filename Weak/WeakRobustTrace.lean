/-
Weak: **the TRACED form of a factorized behavior** (M6 W2a, step 1).

Rocq: `iris/WeakRobustTrace.v` @ xxvzwolszwmp (1cc222280).

The Rocq header, verbatim in substance: `WeakPromiseFact` delivers the state
phase of a lat-free behavior as `rtc`s (`wpPhases`: agent 0's whole run, then
agent 1's, …, each against the frozen log).  An `rtc` ERASES EVENT IDENTITY —
which agent did what, in what per-agent order, reading which timestamps,
fulfilling which promise — and event identity is exactly what the Layer-1
dependency graph (W2a step 2) is built out of.  This file re-presents the same
state phase as EXPLICIT PER-AGENT TRACES and proves the extraction (and the
converse replay, for rebuilding runs after graph surgery).

THE TRACE.  Agent `i`'s phase becomes a pair of lists: `atEvs`, one `Aev` per
step, and `atAgs`, the `atEvs.length + 1` agent records the steps pass through
(position `k`'s step goes from `atAgs[k]?` to `atAgs[k+1]?` emitting
`atEvs[k]?`).  An event is a LABEL plus the FULFILLED TIMESTAMP (`aeTs` is not
derivable from the label and MUST be recorded: two log positions can hold
identical messages, and the graph's fulfil→read edges are edges between LOG
POSITIONS) plus the DEVICE-FABRIC field `aeDev`.

WHY THE WF CONDITION IS ONE LINE PER STEP.  `WeakPromiseFact`'s `astepOk`
already collects the five state rules' side conditions by label, pinning BOTH
the `Wstate` update `f` and the deleted promise `Dl` as functions of the
label; `aeTs` is exactly that `Dl`.  In particular `aeTs` is FORCED to `none`
on non-store labels (`atraceTsNone`).

DELIVERABLE 4 (fulfilment accounting) IS PROVED: `wpBehaviorFulfilOnce` —
in a traced behavior, every log position authored by agent `i` is fulfilled
EXACTLY ONCE across agent `i`'s trace.  DEPENDENCY-FREE like its parents.

**Deviations from Rocq.**

1. NAMES: as `Weak/WeakMem.lean` deviation 1.  Rocq → Lean map: types
   `aev` ↦ `Aev` (`ae_lb`/`ae_ts`/`ae_dev` ↦ `aeLb`/`aeTs`/`aeDev`, `AEv l t d`
   ↦ `⟨l, t, d⟩`), `atrace` ↦ `Atrace` (`at_ags`/`at_evs` ↦ `atAgs`/`atEvs`,
   `ATr` ↦ `⟨ags, evs⟩`), `ptraces` ↦ `Ptraces` (`pt_img`/`pt_log`/`pt_trs` ↦
   `ptImg`/`ptLog`/`ptTrs`), `pdevs` ↦ `Pdevs` (`pd_init`/`pd_ord` ↦
   `pdInit`/`pdOrd`).  Lemmas lowerCamelCase (`cls_canonical` ↦
   `clsCanonical`, `pcls_obl` ↦ `pclsObl`, `list_ex_of_index` ↦
   `listExOfIndex`, `astep_prog` ↦ `astepProg`, `asteps_wf` ↦ `astepsWf`,
   `atrace_wf` ↦ `atraceWf`, `astep_of_atrace` ↦ `astepOfAtrace`,
   `wp_behavior_fulfil_once_dev` ↦ `wpBehaviorFulfilOnceDev`, ...).
2. VOCABULARY: as `WeakMem` deviation 2 and `WeakPromise` deviation 2;
   `agent` ↦ `Nat`; stdpp `last` ↦ `List.getLast?` (so the Rocq NOTE about
   `list_basics.last` shadowing has no Lean counterpart); `NoDup` ↦
   `List.Nodup`; `seq` ↦ `List.range'`; `tvs.*2` ↦ `tvs.map Prod.snd`;
   `o ≫= f` ↦ `o.bind f`; `f <$> o` ↦ `o.map f`; `default d o` ↦ `o.getD d`;
   `x ← o; e` ↦ `o.bind (fun x => e)`.
3. SECTION VARIABLES: `pstep` (and `pdev` where used) are explicit arguments,
   in Rocq's order, exactly where the Rocq `Global Arguments` / section
   closure puts them (`WeakPromiseFact` deviation 2).  `ev_at`, `ev_din`,
   `ev_dout`, `dev_at`, `evs_dev_free`, `ptraces_wit`, `prom_complete` and
   the lemmas about them alone take neither.
4. `astep_ok_ts_none` / `atrace_ts_none` are stated with a wildcard arm for
   the non-store constructors Rocq lists one by one (same truth value per
   constructor; `WeakPromise` deviation 7).
5. Inductions over `rtc` use `MachCSL.rtc_ind_l` / `rtc_ind_r` (Rocq's
   head-style `induction` / `rtc_ind_r`); `wp_lf_state_rtc` is `rtc_subrel`.
6. Lean-only helpers (no Rocq twin): `listSetId` (stdpp `list_insert_id`:
   `l[i]? = some x → l.set i x = l`), used by `astepsReplay`; and the private
   `memUnionR`, `memUnionSelf`, `subseteqTrans`, `memDelNe`, `notMemDelSelf`,
   `notMemEmpty` — the `set_solver` facts of the accounting proofs, stated in a
   small context (`WeakPromise` deviation 6's lesson: `set_solver`'s `grind`
   over a whole trace context is slow).

**Not ported:** nothing.

**Statements checked** (by hand, against Rocq): all of them.
-/
import Weak.WeakPromiseFact

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std Wlabel

/-! ## Events and traces -/

/-- One state step of one agent: the label it emitted, the timestamp it
fulfilled (for `LStore`/`LRmw`/`LExStore`; `none` otherwise), and the
DEVICE-FABRIC field, which is also the fabric-touching MARKER: `none` says the
step is dev-free (it runs at EVERY fabric and leaves it alone), `some (din,
dout)` says it read the fabric at `din` and left it at `dout`.  WHY THE FABRIC
LIVES HERE and not in the witness: `atraceWf` must stay a SELF-CONTAINED
statement about one agent's trace; the witness then carries only the ORDER. -/
structure Aev (D : Type) where
  aeLb : Wlabel
  aeTs : Option Nat
  aeDev : Option (D × D)

/-- One agent's whole state phase.  `atAgs` has one more entry than `atEvs`:
the records BEFORE each step, plus the final one. -/
structure Atrace (P D : Type) where
  atAgs : List (Wpagent P)
  atEvs : List (Aev D)

/-- The whole state phase: one trace per agent (index = agent), all against the
same frozen `(img, log)`. -/
structure Ptraces (P D : Type) where
  ptImg : Image
  ptLog : List Wmsg
  ptTrs : List (Atrace P D)

/-! ## THE MESSAGE CLASS OF A TRACED BUNDLE (G6a)

`WeakPromiseBridge.wp_pf_step` PINS the class of the message a store/rmw
appends.  The two halves of the obligation live here: `clsCanonical clsf TS`
— the RECORDED side: every logged message carries the class `clsf` computes at
its fulfil event's PRE-record agent state; `pclsObl clsf` — the REPLAYED side:
the class function must not look at any timestamp (it may look at the label's
non-timestamp data and at `wRelp`). -/

def clsCanonical {P D : Type} (clsf : P → Wlabel → Wstate → WmClass) (TS : Ptraces P D) : Prop :=
  ∀ (i : Nat) (T : Atrace P D) (k : Nat) (ev : Aev D) (ag : Wpagent P) (ts : Nat) (m : Wmsg),
    TS.ptTrs[i]? = some T →
    T.atEvs[k]? = some ev → T.atAgs[k]? = some ag →
    ev.aeTs = some ts → TS.ptLog[ts - 1]? = some m →
    m.wmAk = clsf ag.paSt ev.aeLb ag.paWs

/-- The obliviousness half, stated for EACH FIXED program state `p`. -/
def pclsObl {P : Type} (clsf : P → Wlabel → Wstate → WmClass) : Prop :=
  (∀ (p : P) (rl : Bool) (base : Int) (data : List (BitVec 8)) (asrc vsrc : List Dsrc)
     (ws ws' : Wstate), ws.wRelp = ws'.wRelp →
     clsf p (LStore rl base data asrc vsrc) ws = clsf p (LStore rl base data asrc vsrc) ws') ∧
  (∀ (p : P) (aq rl : Bool) (base : Int) (tvs tvs' : List (Nat × BitVec 8))
     (data : List (BitVec 8)) (asrc vsrc : List Dsrc) (ws ws' : Wstate),
     tvs.map Prod.snd = tvs'.map Prod.snd → ws.wRelp = ws'.wRelp →
     clsf p (LRmw aq rl base tvs data asrc vsrc) ws
     = clsf p (LRmw aq rl base tvs' data asrc vsrc) ws') ∧
  -- THE RMW SPLIT (S4): the conditional write appends a message too
  (∀ (p : P) (rl : Bool) (base : Int) (data : List (BitVec 8)) (asrc vsrc : List Dsrc)
     (ws ws' : Wstate), ws.wRelp = ws'.wRelp →
     clsf p (LExStore rl base data asrc vsrc) ws = clsf p (LExStore rl base data asrc vsrc) ws')

/-- THE GLOBAL DEVICE-ORDER WITNESS.  `pdInit` is the fabric the state phase
starts at; `pdOrd` lists, IN BEHAVIOR ORDER, every fabric-touching step as the
pair (acting agent, index of that step in that agent's trace). -/
structure Pdevs (D : Type) where
  pdInit : D
  pdOrd : List (Nat × Nat)

/-- A finite family of existentials collects into a list. -/
theorem listExOfIndex {A : Type _} (Φ : Nat → A → Prop) (n : Nat) :
    (∀ i, i < n → ∃ x, Φ i x) →
    ∃ xs : List A, xs.length = n ∧ ∀ i x, xs[i]? = some x → Φ i x := by
  induction n with
  | zero => intro _; exact ⟨[], rfl, fun i x hx => by simp at hx⟩
  | succ n ih =>
    intro hΦ
    obtain ⟨xs, hlen, hxs⟩ := ih (fun i hi => hΦ i (by omega))
    obtain ⟨x, hx⟩ := hΦ n (by omega)
    refine ⟨xs ++ [x], by simp [hlen], fun i y hy => ?_⟩
    by_cases hlt : i < n
    · rw [lookup_app_l (by omega)] at hy
      exact hxs i y hy
    · have hi : i = n := by
        have := lookup_lt_Some hy
        simp at this; omega
      subst hi
      rw [lookup_app_r (by omega), hlen, Nat.sub_self] at hy
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hy
      subst hy; exact hx

/-- `getLast?` from the index form, given the trace's length relation. -/
theorem lastOfLookup {A : Type _} (l : List A) (n : Nat) (x : A) :
    l.length = n + 1 → l[n]? = some x → l.getLast? = some x := by
  intro hlen hlk
  rw [List.getLast?_eq_getElem?, hlen, Nat.add_sub_cancel]
  exact hlk

/-- stdpp `list_insert_id`. -/
theorem listSetId {A : Type _} (l : List A) (i : Nat) (x : A) : l[i]? = some x → l.set i x = l := by
  intro h
  apply List.ext_getElem?
  intro j
  by_cases hij : i = j
  · subst hij; rw [list_lookup_insert (lookup_lt_Some h), h]
  · rw [list_lookup_insert_ne hij]

/-! ## The trace section -/

section trace

variable {P D : Type}
variable (pstep : P → D → Wlabel → P → D → Prop)
-- The fabric-touching marker, as in `WeakPromiseFact`.
variable (pdev : P → Wlabel → P → Bool)

/-! ### Well-formed traces -/

/-- The PROGRAM obligation of one traced step, split by the marker.  A dev-free
event demands the step at EVERY fabric; a fabric-touching event demands it at
the fabric pair the event itself records. -/
def astepProg (ag : Wpagent P) (ev : Aev D) (st' : P) : Prop :=
  match ev.aeDev with
  | none => ∀ d, pstep ag.paSt d ev.aeLb st' d
  | some dd => pstep ag.paSt dd.1 ev.aeLb st' dd.2

/-- A traced step IS a program step (the witness `d0` names a fabric for the
dev-free case; `D` is not assumed inhabited anywhere else). -/
theorem astepProgStep (d0 : D) (ag : Wpagent P) (ev : Aev D) (st' : P) :
    astepProg pstep ag ev st' → ∃ d d', pstep ag.paSt d ev.aeLb st' d' := by
  unfold astepProg
  cases ev.aeDev with
  | some dd => intro h; exact ⟨dd.1, dd.2, h⟩
  | none => intro h; exact ⟨d0, d0, h d0⟩

def astepsWf (img : Image) (log : List Wmsg) (i : Nat) (ags : List (Wpagent P))
    (evs : List (Aev D)) : Prop :=
  ags.length = evs.length + 1 ∧
  ∀ (k : Nat) (ev : Aev D) (ag ag' : Wpagent P),
    evs[k]? = some ev → ags[k]? = some ag → ags[k + 1]? = some ag' →
    ∃ (st' : P) (f : Wstate → Wstate),
      astepProg pstep ag ev st' ∧
      astepOk img log i ag ev.aeLb f ev.aeTs ∧
      ag' = ⟨st', f ag.paWs, promDel ev.aeTs ag.paProm⟩

def atraceWf (img : Image) (log : List Wmsg) (i : Nat) (T : Atrace P D) : Prop :=
  astepsWf pstep img log i T.atAgs T.atEvs

theorem astepsWfLen (img : Image) (log : List Wmsg) (i : Nat) (ags : List (Wpagent P))
    (evs : List (Aev D)) : astepsWf pstep img log i ags evs → ags.length = evs.length + 1 :=
  fun h => h.1

theorem atraceFirstIsSome (img : Image) (log : List Wmsg) (i : Nat) (T : Atrace P D) :
    atraceWf pstep img log i T → (T.atAgs[0]?).isSome := by
  intro h
  exact lookup_lt_is_Some_2 (by have := h.1; omega)

theorem atraceLastIsSome (img : Image) (log : List Wmsg) (i : Nat) (T : Atrace P D) :
    atraceWf pstep img log i T → (T.atAgs[T.atEvs.length]?).isSome := by
  intro h
  exact lookup_lt_is_Some_2 (by have := h.1; omega)

/-- The `getLast?` spelling of the trace's final agent record. -/
theorem atraceLast (img : Image) (log : List Wmsg) (i : Nat) (T : Atrace P D) (ag' : Wpagent P) :
    atraceWf pstep img log i T →
    T.atAgs[T.atEvs.length]? = some ag' →
    T.atAgs.getLast? = some ag' := fun h hl => lastOfLookup _ _ _ h.1 hl

/-- Position `k`'s step, with both endpoints. -/
theorem astepsWfStep (img : Image) (log : List Wmsg) (i : Nat) (ags : List (Wpagent P))
    (evs : List (Aev D)) (k : Nat) (ev : Aev D) :
    astepsWf pstep img log i ags evs → evs[k]? = some ev →
    ∃ (ag ag' : Wpagent P) (st' : P) (f : Wstate → Wstate),
      ags[k]? = some ag ∧ ags[k + 1]? = some ag' ∧
      astepProg pstep ag ev st' ∧
      astepOk img log i ag ev.aeLb f ev.aeTs ∧
      ag' = ⟨st', f ag.paWs, promDel ev.aeTs ag.paProm⟩ := by
  rintro ⟨hlen, hst⟩ hev
  have hlt := lookup_lt_Some hev
  obtain ⟨ag, hag⟩ := Option.isSome_iff_exists.1 (lookup_lt_is_Some_2 (l := ags) (i := k) (by omega))
  obtain ⟨ag', hag'⟩ :=
    Option.isSome_iff_exists.1 (lookup_lt_is_Some_2 (l := ags) (i := k + 1) (by omega))
  obtain ⟨st', f, h1, h2, h3⟩ := hst k ev ag ag' hev hag hag'
  exact ⟨ag, ag', st', f, hag, hag', h1, h2, h3⟩

/-- The one-element trace, and the cons laws. -/
theorem astepsWfSingle (img : Image) (log : List Wmsg) (i : Nat) (ag : Wpagent P) :
    astepsWf pstep img log i [ag] ([] : List (Aev D)) :=
  ⟨rfl, fun k ev _ _ hev _ _ => by simp at hev⟩

theorem astepsWfConsInv (img : Image) (log : List Wmsg) (i : Nat) (ag : Wpagent P)
    (ags : List (Wpagent P)) (ev : Aev D) (evs : List (Aev D)) :
    astepsWf pstep img log i (ag :: ags) (ev :: evs) →
    ∃ (agn : Wpagent P) (st' : P) (f : Wstate → Wstate),
      ags[0]? = some agn ∧
      astepProg pstep ag ev st' ∧
      astepOk img log i ag ev.aeLb f ev.aeTs ∧
      agn = ⟨st', f ag.paWs, promDel ev.aeTs ag.paProm⟩ ∧
      astepsWf pstep img log i ags evs := by
  rintro ⟨hlen, hst⟩
  simp only [List.length_cons] at hlen
  obtain ⟨agn, hagn⟩ :=
    Option.isSome_iff_exists.1 (lookup_lt_is_Some_2 (l := ags) (i := 0) (by omega))
  obtain ⟨st', f, hps, hok, hag⟩ := hst 0 ev ag agn rfl rfl hagn
  refine ⟨agn, st', f, hagn, hps, hok, hag, by omega, fun k ev' a b he ha hb => ?_⟩
  exact hst (k + 1) ev' a b he ha hb

theorem astepsWfCons (img : Image) (log : List Wmsg) (i : Nat) (ag : Wpagent P)
    (ags : List (Wpagent P)) (ev : Aev D) (evs : List (Aev D)) (st' : P) (f : Wstate → Wstate) :
    astepProg pstep ag ev st' →
    astepOk img log i ag ev.aeLb f ev.aeTs →
    ags[0]? = some ⟨st', f ag.paWs, promDel ev.aeTs ag.paProm⟩ →
    astepsWf pstep img log i ags evs →
    astepsWf pstep img log i (ag :: ags) (ev :: evs) := by
  rintro hps hok h0 ⟨hlen, hst⟩
  refine ⟨by simp [hlen], fun k ev' a b he ha hb => ?_⟩
  cases k with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at he ha
    subst he ha
    simp only [List.getElem?_cons_succ] at hb
    rw [h0] at hb
    exact ⟨st', f, hps, hok, (Option.some.inj hb).symm⟩
  | succ k =>
    simp only [List.getElem?_cons_succ] at he ha hb
    exact hst k ev' a b he ha hb

/-! ### `aeTs` is pinned by the label -/

theorem astepOkTsNone (img : Image) (log : List Wmsg) (i : Nat) (ag : Wpagent P) (l : Wlabel)
    (f : Wstate → Wstate) (Dl : Option Nat) :
    astepOk img log i ag l f Dl →
    match l with
    | LStore .. | LRmw .. | LExStore .. => True
    | _ => Dl = none := by
  intro h
  cases l with
  | LStore => trivial
  | LRmw => trivial
  | LExStore => trivial
  | LSilent => exact h.2
  | LLoad => exact h.2.2
  | LFence => exact h.2
  | LDev => exact h.2
  | LRegW => exact h.2
  | LCtrl => exact h.2
  | LInstr => exact h.2
  -- THE RMW SPLIT (S2): the exclusive read fulfils nothing, the conditional write does
  | LExLoad => exact h.2.2

theorem atraceTsNone (img : Image) (log : List Wmsg) (i : Nat) (T : Atrace P D) (k : Nat)
    (ev : Aev D) :
    atraceWf pstep img log i T → T.atEvs[k]? = some ev →
    match ev.aeLb with
    | LStore .. | LRmw .. | LExStore .. => True
    | _ => ev.aeTs = none := by
  intro hwf hev
  obtain ⟨_, _, _, _, _, _, _, hok, _⟩ := astepsWfStep pstep _ _ _ _ _ _ _ hwf hev
  exact astepOkTsNone _ _ _ _ _ _ _ hok

/-- A lat-free PROGRAM emits only lat-free labels, so every trace of a factorized
behavior is lat-free. -/
theorem atraceLatFree (d0 : D) (img : Image) (log : List Wmsg) (i : Nat) (T : Atrace P D)
    (k : Nat) (ev : Aev D) :
    latFreeProg pstep → atraceWf pstep img log i T →
    T.atEvs[k]? = some ev → latFree ev.aeLb := by
  intro hlfp hwf hev
  obtain ⟨ag, _, st', _, _, _, hps, _, _⟩ := astepsWfStep pstep _ _ _ _ _ _ _ hwf hev
  obtain ⟨d, d', hps⟩ := astepProgStep pstep d0 _ _ _ hps
  revert hps
  cases ev.aeLb with
  | LLoad aq lat base tvs asrc =>
    intro hps
    cases lat with
    | false => rfl
    | true => exact (latFreeProgLat pstep _ _ _ _ _ _ _ _ hlfp hps).elim
  | _ => intro _; trivial

/-! ### Building an event from a step: the MARKER decides `aeDev` -/

def mkAev (din : D) (ag : Wpagent P) (l : Wlabel) (st' : P) (d' : D) (Dl : Option Nat) : Aev D :=
  ⟨l, Dl, if pdev ag.paSt l st' then some (din, d') else none⟩

theorem mkAevLb (din : D) (ag : Wpagent P) (l : Wlabel) (st' : P) (d' : D) (Dl : Option Nat) :
    (mkAev pdev din ag l st' d' Dl).aeLb = l := rfl

theorem mkAevTs (din : D) (ag : Wpagent P) (l : Wlabel) (st' : P) (d' : D) (Dl : Option Nat) :
    (mkAev pdev din ag l st' d' Dl).aeTs = Dl := rfl

theorem astepProgMk (din : D) (ag : Wpagent P) (l : Wlabel) (st' : P) (d' : D) (Dl : Option Nat) :
    pdevOk pstep pdev →
    pstep ag.paSt din l st' d' →
    astepProg pstep ag (mkAev pdev din ag l st' d' Dl) st' := by
  intro hpok hs
  unfold astepProg mkAev
  cases hp : pdev ag.paSt l st' with
  | true => exact hs
  | false => exact (hpok _ _ _ _ _ hs hp).2

/-- The dev-free case of `mkAev` also pins the fabric. -/
theorem mkAevFree (din : D) (ag : Wpagent P) (l : Wlabel) (st' : P) (d' : D) (Dl : Option Nat) :
    pdevOk pstep pdev →
    pstep ag.paSt din l st' d' →
    (mkAev pdev din ag l st' d' Dl).aeDev = none → d' = din := by
  intro hpok hs
  unfold mkAev
  cases hp : pdev ag.paSt l st' with
  | true => intro h; simp at h
  | false => intro _; exact (hpok _ _ _ _ _ hs hp).1

/-! ### THE EXTRACTION: an `rtc` of one agent's steps IS a trace -/

/-- THE EXTRACTION.  Agent `i`'s phase, as a trace against the frozen
`(img, log)`, with its first record `i`'s entry in `c` and its last record
`i`'s entry in `c'` — plus the frame and the frozen-log facts. -/
theorem astepOfAtrace (i : Nat) (c c' : Wpcfg P D) (ag : Wpagent P) :
    pdevOk pstep pdev →
    rtc (wpAstepOf pstep i) c c' →
    c.pcAgs[i]? = some ag →
    ∃ (T : Atrace P D) (ag' : Wpagent P),
      atraceWf pstep c.pcImg c.pcLog i T ∧
      T.atAgs[0]? = some ag ∧
      T.atAgs[T.atEvs.length]? = some ag' ∧
      T.atAgs.getLast? = some ag' ∧
      c'.pcAgs[i]? = some ag' ∧
      (∀ j, j ≠ i → c'.pcAgs[j]? = c.pcAgs[j]?) ∧
      c'.pcLog = c.pcLog ∧ c'.pcImg = c.pcImg ∧
      c'.pcAgs.length = c.pcAgs.length := by
  intro hpok hrun
  revert ag
  refine rtc_ind_l (fun c => ∀ ag : Wpagent P, c.pcAgs[i]? = some ag →
    ∃ (T : Atrace P D) (ag' : Wpagent P),
      atraceWf pstep c.pcImg c.pcLog i T ∧
      T.atAgs[0]? = some ag ∧
      T.atAgs[T.atEvs.length]? = some ag' ∧
      T.atAgs.getLast? = some ag' ∧
      c'.pcAgs[i]? = some ag' ∧
      (∀ j, j ≠ i → c'.pcAgs[j]? = c.pcAgs[j]?) ∧
      c'.pcLog = c.pcLog ∧ c'.pcImg = c.pcImg ∧
      c'.pcAgs.length = c.pcAgs.length) c' ?_ ?_ c hrun
  · intro ag hlk
    exact ⟨⟨[ag], []⟩, ag, astepsWfSingle pstep _ _ _ _, rfl, rfl, rfl, hlk,
      fun _ _ => rfl, rfl, rfl, rfl⟩
  · intro c y hs _ ih ag hlk
    obtain ⟨l, hs⟩ := hs
    obtain ⟨ag0, st', d', f, Dl, hlk0, hps, hok, hy⟩ := wpAstepInv pstep i l c y hs
    rw [hlk] at hlk0
    cases hlk0
    have hlt := lookup_lt_Some hlk
    subst hy
    obtain ⟨T1, ag', hwf1, h01, hl1, _, hc', hfr, hlog, himg, hlen⟩ :=
      ih ⟨st', f ag.paWs, promDel Dl ag.paProm⟩ (list_lookup_insert hlt)
    dsimp only at hwf1 hfr hlog himg hlen
    have hwf : atraceWf pstep c.pcImg c.pcLog i
        ⟨ag :: T1.atAgs, mkAev pdev c.pcDev ag l st' d' Dl :: T1.atEvs⟩ :=
      astepsWfCons pstep _ _ _ _ _ _ _ st' f (astepProgMk pstep pdev _ _ _ _ _ _ hpok hps)
        hok h01 hwf1
    refine ⟨⟨ag :: T1.atAgs, mkAev pdev c.pcDev ag l st' d' Dl :: T1.atEvs⟩, ag', hwf, rfl, hl1,
      atraceLast pstep _ _ _ _ _ hwf hl1, hc', fun j hj => ?_, hlog, himg, ?_⟩
    · rw [hfr j hj, list_lookup_insert_ne (Ne.symm hj)]
    · rw [hlen, length_insert]

/-! ### THE CONVERSE: replaying a trace rebuilds the `rtc` -/

/-- A trace all of whose events are DEV-FREE.  Replay is stated for these. -/
def evsDevFree (evs : List (Aev D)) : Prop :=
  ∀ (k : Nat) (ev : Aev D), evs[k]? = some ev → ev.aeDev = none

theorem evsDevFreeCons (ev : Aev D) (evs : List (Aev D)) :
    evsDevFree (ev :: evs) → ev.aeDev = none ∧ evsDevFree evs := by
  intro h
  exact ⟨h 0 ev rfl, fun k ev' hk => h (k + 1) ev' hk⟩

theorem astepsReplay (i : Nat) (evs : List (Aev D)) :
    ∀ (c : Wpcfg P D) (ags : List (Wpagent P)) (ag ag' : Wpagent P),
      astepsWf pstep c.pcImg c.pcLog i ags evs →
      evsDevFree evs →
      c.pcAgs[i]? = some ag →
      ags[0]? = some ag →
      ags[evs.length]? = some ag' →
      rtc (wpAfreeOf pstep i) c ⟨c.pcImg, c.pcLog, c.pcDev, c.pcAgs.set i ag'⟩ := by
  induction evs with
  | nil =>
    intro c ags ag ag' _ _ hclk h0 hl
    simp only [List.length_nil] at hl
    rw [h0] at hl
    cases hl
    rw [listSetId _ _ _ hclk]
    exact rtc_refl _
  | cons ev evs ih =>
    intro c ags ag ag' hwf hdf hclk h0 hl
    cases ags with
    | nil => simp at h0
    | cons a ags =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h0
      subst h0
      obtain ⟨hdf0, hdf⟩ := evsDevFreeCons ev evs hdf
      obtain ⟨agn, st', f, hagn, hps, hok, hagne, hwf'⟩ :=
        astepsWfConsInv pstep _ _ _ _ _ _ _ hwf
      unfold astepProg at hps
      rw [hdf0] at hps
      have hstep : wpAfree pstep i ev.aeLb c
          ⟨c.pcImg, c.pcLog, c.pcDev, c.pcAgs.set i agn⟩ := by
        rw [hagne]
        exact wpAfree.WPAFree c a st' f ev.aeTs hclk hps hok
      refine rtc_l ⟨ev.aeLb, hstep⟩ ?_
      have hlk2 : (c.pcAgs.set i agn)[i]? = some agn := list_lookup_insert (lookup_lt_Some hclk)
      have hrun := ih ⟨c.pcImg, c.pcLog, c.pcDev, c.pcAgs.set i agn⟩ ags agn ag' hwf' hdf hlk2
        hagn hl
      dsimp only at hrun
      rw [list_insert_insert] at hrun
      exact hrun

theorem atraceReplay (i : Nat) (c : Wpcfg P D) (T : Atrace P D) (ag ag' : Wpagent P) :
    atraceWf pstep c.pcImg c.pcLog i T →
    evsDevFree T.atEvs →
    c.pcAgs[i]? = some ag →
    T.atAgs[0]? = some ag →
    T.atAgs[T.atEvs.length]? = some ag' →
    rtc (wpAfreeOf pstep i) c ⟨c.pcImg, c.pcLog, c.pcDev, c.pcAgs.set i ag'⟩ :=
  fun hwf hdf hclk h0 hl => astepsReplay pstep i T.atEvs c T.atAgs ag ag' hwf hdf hclk h0 hl

/-! ### THE WHOLE PHASE: `wpPhases` as one `Ptraces` -/

theorem wpPhasesFrozen (js : List Nat) (c c' : Wpcfg P D) :
    wpPhases pstep js c c' →
    c'.pcLog = c.pcLog ∧ c'.pcImg = c.pcImg ∧ c'.pcAgs.length = c.pcAgs.length := by
  induction js generalizing c c' with
  | nil => intro h; subst h; exact ⟨rfl, rfl, rfl⟩
  | cons j js ih =>
    rintro ⟨mid, hrun, hph⟩
    obtain ⟨h1, h2, h3, _⟩ := astepOfRtcFrozen pstep j c mid (wpAfreeOfAstepOf pstep j _ _ hrun)
    obtain ⟨h1', h2', h3'⟩ := ih mid c' hph
    exact ⟨h1'.trans h1, h2'.trans h2, h3'.trans h3⟩

theorem wpPhasesFrame (js : List Nat) (c c' : Wpcfg P D) (i : Nat) :
    wpPhases pstep js c c' → i ∉ js → c'.pcAgs[i]? = c.pcAgs[i]? := by
  induction js generalizing c c' with
  | nil => intro h _; subst h; rfl
  | cons j js ih =>
    rintro ⟨mid, hrun, hph⟩ hni
    rw [List.mem_cons, not_or] at hni
    obtain ⟨_, _, _, hfr⟩ := astepOfRtcFrozen pstep j c mid (wpAfreeOfAstepOf pstep j _ _ hrun)
    rw [ih mid c' hph hni.2]
    exact hfr i (fun h => hni.1 h)

/-- Agent `i`'s trace out of a whole `wpPhases` run.  `Nodup js` is what makes
`i`'s steps contiguous; `i` need not occur in `js`. -/
theorem wpPhasesAgent (js : List Nat) (c c' : Wpcfg P D) (i : Nat) (ag : Wpagent P) :
    pdevOk pstep pdev →
    js.Nodup → wpPhases pstep js c c' → c.pcAgs[i]? = some ag →
    ∃ (T : Atrace P D) (ag' : Wpagent P),
      atraceWf pstep c.pcImg c.pcLog i T ∧
      T.atAgs[0]? = some ag ∧
      T.atAgs[T.atEvs.length]? = some ag' ∧
      c'.pcAgs[i]? = some ag' := by
  intro hpok
  induction js generalizing c c' ag with
  | nil =>
    intro _ hph hlk
    subst hph
    exact ⟨⟨[ag], []⟩, ag, astepsWfSingle pstep _ _ _ _, rfl, rfl, hlk⟩
  | cons j js ih =>
    intro hnd hph hlk
    rw [List.nodup_cons] at hnd
    obtain ⟨hnj, hnd⟩ := hnd
    obtain ⟨mid, hrun, hph⟩ := hph
    by_cases hji : j = i
    · subst hji
      obtain ⟨T, ag', hwf, h0, hl, _, hmid, _⟩ :=
        astepOfAtrace pstep pdev j c mid ag hpok (wpAfreeOfAstepOf pstep j _ _ hrun) hlk
      exact ⟨T, ag', hwf, h0, hl, by rw [wpPhasesFrame pstep js mid c' j hph hnj]; exact hmid⟩
    · obtain ⟨hlog, himg, _, hfr⟩ :=
        astepOfRtcFrozen pstep j c mid (wpAfreeOfAstepOf pstep j _ _ hrun)
      have hmid : mid.pcAgs[i]? = some ag := by rw [hfr i (Ne.symm hji)]; exact hlk
      obtain ⟨T, ag', hwf, h0, hl, hc'⟩ := ih mid c' ag hnd hph hmid
      rw [hlog, himg] at hwf
      exact ⟨T, ag', hwf, h0, hl, hc'⟩

/-- The traced form of a whole state phase: one trace per agent, all against
the frozen `(img, log)`, first records = `mid`'s agents, last records = `c`'s
agents. -/
def ptracesOf (TS : Ptraces P D) (mid c : Wpcfg P D) : Prop :=
  TS.ptImg = mid.pcImg ∧
  TS.ptLog = mid.pcLog ∧
  TS.ptTrs.length = mid.pcAgs.length ∧
  (∀ (i : Nat) (T : Atrace P D), TS.ptTrs[i]? = some T → atraceWf pstep TS.ptImg TS.ptLog i T) ∧
  (∀ (i : Nat) (T : Atrace P D), TS.ptTrs[i]? = some T → T.atAgs[0]? = mid.pcAgs[i]?) ∧
  (∀ (i : Nat) (T : Atrace P D), TS.ptTrs[i]? = some T →
     T.atAgs[T.atEvs.length]? = c.pcAgs[i]?) ∧
  c.pcLog = mid.pcLog ∧ c.pcImg = mid.pcImg ∧
  c.pcAgs.length = mid.pcAgs.length

theorem phasesPtraces (mid c : Wpcfg P D) :
    pdevOk pstep pdev →
    wpPhases pstep (List.range' 0 mid.pcAgs.length) mid c →
    ∃ TS, ptracesOf pstep TS mid c := by
  intro hpok hph
  obtain ⟨hlog, himg, hlen⟩ := wpPhasesFrozen pstep _ _ _ hph
  obtain ⟨Ts, hlenTs, hTs⟩ := listExOfIndex
    (fun i (T : Atrace P D) => atraceWf pstep mid.pcImg mid.pcLog i T ∧
      T.atAgs[0]? = mid.pcAgs[i]? ∧
      T.atAgs[T.atEvs.length]? = c.pcAgs[i]?)
    mid.pcAgs.length (by
      intro i hi
      obtain ⟨ag, hag⟩ := Option.isSome_iff_exists.1 (lookup_lt_is_Some_2 hi)
      obtain ⟨T, ag', hwf, h0, hl, hc⟩ :=
        wpPhasesAgent pstep pdev _ _ _ i ag hpok List.nodup_range' hph hag
      exact ⟨T, hwf, by rw [h0, hag], by rw [hl, hc]⟩)
  exact ⟨⟨mid.pcImg, mid.pcLog, Ts⟩, rfl, rfl, hlenTs, fun i T hi => (hTs i T hi).1,
    fun i T hi => (hTs i T hi).2.1, fun i T hi => (hTs i T hi).2.2, hlog, himg, hlen⟩

/-- `wpLfStep` ⊆ `wpStateStep`. -/
theorem wpLfStateRtc (c c' : Wpcfg P D) :
    rtc (wpLfStep pstep) c c' → rtc (wpStateStep pstep) c c' :=
  rtc_subrel (fun _ _ ⟨i, l, _, hs⟩ => ⟨i, l, hs⟩)

/-! ### THE DEVICE-ORDER WITNESS, AND THE EXTRACTION THAT PRODUCES IT

With a shared fabric the state phase can no longer be reordered
agent-contiguous, so the general state phase is handled NOT by reordering it
but by reading the traces off the INTERLEAVING directly, one appended event per
step, and recording the fabric-touching steps in a global order as we go. -/

/-- The event at a witness position, and its recorded fabric pair. -/
def evAt (TS : Ptraces P D) (e : Nat × Nat) : Option (Aev D) :=
  (TS.ptTrs[e.1]?).bind (fun T => T.atEvs[e.2]?)

def evDin (TS : Ptraces P D) (e : Nat × Nat) : Option D :=
  ((evAt TS e).bind Aev.aeDev).map Prod.fst

def evDout (TS : Ptraces P D) (e : Nat × Nat) : Option D :=
  ((evAt TS e).bind Aev.aeDev).map Prod.snd

/-- THE FOLD: the fabric BEFORE witness position `m` is `pdInit` at the head and
the previous entry's `dout` thereafter. -/
def devAt (TS : Ptraces P D) (DS : Pdevs D) (m : Nat) : D :=
  match m with
  | 0 => DS.pdInit
  | m' + 1 => ((DS.pdOrd[m']?).bind (evDout TS)).getD DS.pdInit

def ptracesDevOf (TS : Ptraces P D) (DS : Pdevs D) (mid c : Wpcfg P D) : Prop :=
  -- the per-agent traces, EXACTLY as before the fabric
  ptracesOf pstep TS mid c ∧
  DS.pdInit = mid.pcDev ∧
  -- (W1) every listed position IS a fabric-touching event
  (∀ (m : Nat) (e : Nat × Nat), DS.pdOrd[m]? = some e →
     ∃ ev : Aev D, evAt TS e = some ev ∧ ev.aeDev.isSome) ∧
  -- (W2) and every fabric-touching event IS listed
  (∀ (i k : Nat) (ev : Aev D), evAt TS (i, k) = some ev → ev.aeDev.isSome →
     ∃ m : Nat, DS.pdOrd[m]? = some (i, k)) ∧
  -- (W3) the witness order REFINES each agent's trace order
  (∀ (m1 m2 i k1 k2 : Nat), m1 < m2 →
     DS.pdOrd[m1]? = some (i, k1) → DS.pdOrd[m2]? = some (i, k2) → k1 < k2) ∧
  -- (W4) THE FOLD: a listed step reads the fabric its predecessor left
  (∀ (m : Nat) (e : Nat × Nat), DS.pdOrd[m]? = some e → evDin TS e = some (devAt TS DS m)) ∧
  -- (W5) the phase ends at the fabric the last listed step left
  c.pcDev = devAt TS DS DS.pdOrd.length ∧
  -- (W6) THE MARKER IS THE AUTHORITY on the flag
  (∀ (i : Nat) (T : Atrace P D) (k : Nat) (ev : Aev D) (ag ag' : Wpagent P),
     TS.ptTrs[i]? = some T → T.atEvs[k]? = some ev →
     T.atAgs[k]? = some ag → T.atAgs[k + 1]? = some ag' →
     ev.aeDev = none ∨ pdev ag.paSt ev.aeLb ag'.paSt = true)

/-- THE WITNESS ALONE — clauses (W1)–(W4). -/
def ptracesWit (TS : Ptraces P D) (DS : Pdevs D) : Prop :=
  (∀ (m : Nat) (e : Nat × Nat), DS.pdOrd[m]? = some e →
     ∃ ev : Aev D, evAt TS e = some ev ∧ ev.aeDev.isSome) ∧
  (∀ (i k : Nat) (ev : Aev D), evAt TS (i, k) = some ev → ev.aeDev.isSome →
     ∃ m : Nat, DS.pdOrd[m]? = some (i, k)) ∧
  (∀ (m1 m2 i k1 k2 : Nat), m1 < m2 →
     DS.pdOrd[m1]? = some (i, k1) → DS.pdOrd[m2]? = some (i, k2) → k1 < k2) ∧
  (∀ (m : Nat) (e : Nat × Nat), DS.pdOrd[m]? = some e → evDin TS e = some (devAt TS DS m))

theorem ptracesDevOfWit (TS : Ptraces P D) (DS : Pdevs D) (mid c : Wpcfg P D) :
    ptracesDevOf pstep pdev TS DS mid c → ptracesWit TS DS :=
  fun ⟨_, _, h1, h2, h3, h4, _, _⟩ => ⟨h1, h2, h3, h4⟩

/-- `devAt` at the EMPTY witness is the initial fabric, always. -/
theorem devAtNil (TS : Ptraces P D) (d : D) (m : Nat) : devAt TS ⟨d, []⟩ m = d := by
  cases m with
  | zero => rfl
  | succ m' => simp [devAt]

/-- …and the empty witness IS a witness of a DEV-FREE bundle. -/
theorem ptracesWitNil (TS : Ptraces P D) (d : D) :
    (∀ (i : Nat) (T : Atrace P D) (k : Nat) (ev : Aev D), TS.ptTrs[i]? = some T →
       T.atEvs[k]? = some ev → ev.aeDev = none) →
    ptracesWit TS ⟨d, []⟩ := by
  intro hdf
  refine ⟨fun m e hm => by simp at hm, fun i k ev hev hdd => ?_,
    fun _ _ _ _ _ _ hm => by simp at hm, fun m e hm => by simp at hm⟩
  unfold evAt at hev
  cases hT : TS.ptTrs[i]? with
  | none => rw [hT] at hev; cases hev
  | some T =>
    rw [hT] at hev
    rw [hdf i T k ev hT hev] at hdd
    cases hdd

/-- Appending one step to a well-formed trace. -/
theorem astepsWfSnoc (img : Image) (log : List Wmsg) (i : Nat) (ags : List (Wpagent P))
    (evs : List (Aev D)) (ag : Wpagent P) (ev : Aev D) (st' : P) (f : Wstate → Wstate) :
    astepsWf pstep img log i ags evs →
    ags[evs.length]? = some ag →
    astepProg pstep ag ev st' →
    astepOk img log i ag ev.aeLb f ev.aeTs →
    astepsWf pstep img log i (ags ++ [⟨st', f ag.paWs, promDel ev.aeTs ag.paProm⟩]) (evs ++ [ev]) := by
  rintro ⟨hlen, hst⟩ hag hps hok
  refine ⟨by simp [hlen], fun k ev0 a b hev ha hb => ?_⟩
  by_cases hlt : k < evs.length
  · rw [lookup_app_l hlt] at hev
    rw [lookup_app_l (by omega)] at ha
    rw [lookup_app_l (by omega)] at hb
    exact hst k ev0 a b hev ha hb
  · have hk : k = evs.length := by
      have := lookup_lt_Some hev
      simp at this; omega
    subst hk
    rw [lookup_app_r (Nat.le_refl _), Nat.sub_self] at hev
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hev
    subst hev
    rw [lookup_app_l (by omega), hag] at ha
    cases ha
    rw [lookup_app_r (by omega), hlen, Nat.sub_self] at hb
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hb
    exact ⟨st', f, hps, hok, hb.symm⟩

/-- The trace at `i` only GROWS, so every position that already resolved
resolves the same way. -/
theorem evAtGrow (TS : Ptraces P D) (i : Nat) (T T' : Atrace P D) (e : Nat × Nat) :
    TS.ptTrs[i]? = some T →
    (∀ (k : Nat) (ev : Aev D), T.atEvs[k]? = some ev → T'.atEvs[k]? = some ev) →
    (evAt TS e).isSome →
    evAt ⟨TS.ptImg, TS.ptLog, TS.ptTrs.set i T'⟩ e = evAt TS e := by
  intro hi hgrow hs
  obtain ⟨ev, hev⟩ := Option.isSome_iff_exists.1 hs
  obtain ⟨j, k⟩ := e
  unfold evAt at hev ⊢
  dsimp only at hev ⊢
  have hlt := lookup_lt_Some hi
  by_cases hji : j = i
  · subst hji
    rw [hi] at hev
    rw [list_lookup_insert hlt, hi]
    simp only [Option.bind_some] at hev ⊢
    rw [hgrow k ev hev, hev]
  · rw [list_lookup_insert_ne (Ne.symm hji)]

theorem evDinGrow (TS : Ptraces P D) (i : Nat) (T T' : Atrace P D) (e : Nat × Nat) :
    TS.ptTrs[i]? = some T →
    (∀ (k : Nat) (ev : Aev D), T.atEvs[k]? = some ev → T'.atEvs[k]? = some ev) →
    (evAt TS e).isSome →
    evDin ⟨TS.ptImg, TS.ptLog, TS.ptTrs.set i T'⟩ e = evDin TS e := by
  intro h1 h2 h3
  unfold evDin
  rw [evAtGrow TS i T T' e h1 h2 h3]

theorem evDoutGrow (TS : Ptraces P D) (i : Nat) (T T' : Atrace P D) (e : Nat × Nat) :
    TS.ptTrs[i]? = some T →
    (∀ (k : Nat) (ev : Aev D), T.atEvs[k]? = some ev → T'.atEvs[k]? = some ev) →
    (evAt TS e).isSome →
    evDout ⟨TS.ptImg, TS.ptLog, TS.ptTrs.set i T'⟩ e = evDout TS e := by
  intro h1 h2 h3
  unfold evDout
  rw [evAtGrow TS i T T' e h1 h2 h3]

/-- THE EXTRACTION.  Every state phase yields per-agent traces PLUS the global
device-order witness.  Induction is on the SNOC form of the run: one step
appends one event to its own agent's trace, and — if the marker calls it
fabric-touching — one entry to the witness. -/
theorem statePtraces (mid cfin : Wpcfg P D) :
    pdevOk pstep pdev →
    rtc (wpStateStep pstep) mid cfin →
    ∃ TS DS, ptracesDevOf pstep pdev TS DS mid cfin := by
  intro hpok hrun
  refine rtc_ind_r (R := wpStateStep pstep)
    (fun z => ∃ TS DS, ptracesDevOf pstep pdev TS DS mid z) mid ?_ ?_ cfin hrun
  · -- the empty phase: one one-record trace per agent, empty witness
    have htr : ∀ (i : Nat) (T : Atrace P D),
        (mid.pcAgs.map (fun ag => (⟨[ag], []⟩ : Atrace P D)))[i]? = some T →
        ∃ ag, mid.pcAgs[i]? = some ag ∧ T = ⟨[ag], []⟩ := by
      intro i T hT
      rw [list_lookup_fmap] at hT
      cases hag : mid.pcAgs[i]? with
      | none => rw [hag] at hT; cases hT
      | some ag => rw [hag] at hT; exact ⟨ag, rfl, (Option.some.inj hT).symm⟩
    refine ⟨⟨mid.pcImg, mid.pcLog, mid.pcAgs.map (fun ag => ⟨[ag], []⟩)⟩, ⟨mid.pcDev, []⟩,
      ⟨rfl, rfl, by simp, ?_, ?_, ?_, rfl, rfl, rfl⟩, rfl, fun m e hm => by simp at hm,
      ?_, fun _ _ _ _ _ _ hm => by simp at hm, fun m e hm => by simp at hm, rfl, ?_⟩
    · intro i T hT
      obtain ⟨ag, _, rfl⟩ := htr i T hT
      exact astepsWfSingle pstep _ _ _ _
    · intro i T hT
      obtain ⟨ag, hag, rfl⟩ := htr i T hT
      rw [hag]; rfl
    · intro i T hT
      obtain ⟨ag, hag, rfl⟩ := htr i T hT
      rw [hag]; rfl
    · intro i k ev hev _
      unfold evAt at hev
      dsimp only at hev
      rw [list_lookup_fmap] at hev
      cases hag : mid.pcAgs[i]? with
      | none => rw [hag] at hev; cases hev
      | some ag => rw [hag] at hev; simp at hev
    · intro i T k ev ag ag' hT hev _ _
      obtain ⟨ag0, _, rfl⟩ := htr i T hT
      simp at hev
  -- one more step
  intro y c _ hstep ih
  obtain ⟨TS, DS, hpt, hinit, HW1, HW2, HW3, HW4, HW5, HW6⟩ := ih
  obtain ⟨himg, hlog, hlenTS, hwf, hfst, hlst, hclog, hcimg, hclen⟩ := hpt
  obtain ⟨i, l, hs⟩ := hstep
  obtain ⟨ag, st', d', f, Dl, hlk, hps, hok, hc⟩ := wpAstepInv pstep i l y c hs
  -- the new event, kept OPAQUE (a bare variable with three field equations)
  obtain ⟨ev, hevlb, hevts, hevdd⟩ : ∃ ev : Aev D, ev.aeLb = l ∧ ev.aeTs = Dl ∧
      ((pdev ag.paSt l st' = true ∧ ev.aeDev = some (y.pcDev, d')) ∨
       (pdev ag.paSt l st' = false ∧ ev.aeDev = none)) := by
    cases hm0 : pdev ag.paSt l st' with
    | true => exact ⟨⟨l, Dl, some (y.pcDev, d')⟩, rfl, rfl, .inl ⟨rfl, rfl⟩⟩
    | false => exact ⟨⟨l, Dl, none⟩, rfl, rfl, .inr ⟨rfl, rfl⟩⟩
  have hilt : i < TS.ptTrs.length := by rw [hlenTS, ← hclen]; exact lookup_lt_Some hlk
  obtain ⟨T, hT⟩ := Option.isSome_iff_exists.1 (lookup_lt_is_Some_2 hilt)
  have hwfT : atraceWf pstep TS.ptImg TS.ptLog i T := hwf i T hT
  have hlastT : T.atAgs[T.atEvs.length]? = some ag := by rw [hlst i T hT, hlk]
  let agn : Wpagent P := ⟨st', f ag.paWs, promDel Dl ag.paProm⟩
  let T' : Atrace P D := ⟨T.atAgs ++ [agn], T.atEvs ++ [ev]⟩
  let TS' : Ptraces P D := ⟨TS.ptImg, TS.ptLog, TS.ptTrs.set i T'⟩
  have hT'ags : T'.atAgs = T.atAgs ++ [agn] := rfl
  have hT'evs : T'.atEvs = T.atEvs ++ [ev] := rfl
  have hlenT : T.atAgs.length = T.atEvs.length + 1 := hwfT.1
  -- the trace at `i` only grows
  have hgrow : ∀ (k : Nat) (e0 : Aev D), T.atEvs[k]? = some e0 → T'.atEvs[k]? = some e0 := by
    intro k e0 hk
    rw [hT'evs, lookup_app_l (lookup_lt_Some hk)]; exact hk
  have hgrowAt : ∀ e0, (evAt TS e0).isSome → evAt TS' e0 = evAt TS e0 :=
    fun e0 he0 => evAtGrow TS i T T' e0 hT hgrow he0
  have hgrowDin : ∀ e0, (evAt TS e0).isSome → evDin TS' e0 = evDin TS e0 :=
    fun e0 he0 => evDinGrow TS i T T' e0 hT hgrow he0
  have hgrowDout : ∀ e0, (evAt TS e0).isSome → evDout TS' e0 = evDout TS e0 :=
    fun e0 he0 => evDoutGrow TS i T T' e0 hT hgrow he0
  -- the OLD witness entries resolve identically in `TS'`
  have hold : ∀ (m : Nat) (e0 : Nat × Nat), DS.pdOrd[m]? = some e0 → (evAt TS e0).isSome := by
    intro m e0 hm
    obtain ⟨ev0, hev0, _⟩ := HW1 m e0 hm
    rw [hev0]; rfl
  have hdevAt : ∀ m, m ≤ DS.pdOrd.length → devAt TS' DS m = devAt TS DS m := by
    intro m _
    cases m with
    | zero => rfl
    | succ m' =>
      show ((DS.pdOrd[m']?).bind (evDout TS')).getD DS.pdInit
        = ((DS.pdOrd[m']?).bind (evDout TS)).getD DS.pdInit
      cases he0 : DS.pdOrd[m']? with
      | none => rfl
      | some e0 =>
        show (evDout TS' e0).getD _ = (evDout TS e0).getD _
        rw [hgrowDout e0 (hold _ _ he0)]
  -- the new event's lookups
  have hevT' : T'.atEvs[T.atEvs.length]? = some ev := by
    rw [hT'evs, lookup_app_r (Nat.le_refl _), Nat.sub_self]; rfl
  have hTS'i : TS'.ptTrs[i]? = some T' := list_lookup_insert hilt
  have hevAtNew : evAt TS' (i, T.atEvs.length) = some ev := by
    unfold evAt; dsimp only; rw [hTS'i]; exact hevT'
  -- every event of `TS'` is either an old one or the new one
  have hcases : ∀ (j k : Nat) (ev0 : Aev D), evAt TS' (j, k) = some ev0 →
      (j = i ∧ k = T.atEvs.length ∧ ev0 = ev) ∨ evAt TS (j, k) = some ev0 := by
    intro j k ev0
    unfold evAt
    dsimp only
    by_cases hji : j = i
    · subst hji
      rw [hTS'i, hT]
      simp only [Option.bind_some]
      by_cases hlt : k < T.atEvs.length
      · rw [hT'evs, lookup_app_l hlt]; exact fun h => .inr h
      · intro hk
        left
        have hk' : k = T.atEvs.length := by
          have := lookup_lt_Some hk
          rw [hT'evs] at this; simp at this; omega
        subst hk'
        rw [hevT'] at hk
        exact ⟨by trivial, by trivial, (Option.some.inj hk).symm⟩
    · show (TS.ptTrs.set i T')[j]?.bind _ = _ → _
      rw [list_lookup_insert_ne (Ne.symm hji)]
      exact fun h => .inr h
  have hwfT' : atraceWf pstep TS.ptImg TS.ptLog i T' := by
    have hprog : astepProg pstep ag ev st' := by
      unfold astepProg
      rcases hevdd with ⟨_, hd⟩ | ⟨hm0, hd⟩
      · rw [hd, hevlb]; exact hps
      · rw [hd, hevlb]; exact (hpok _ _ _ _ _ hps hm0).2
    have hok' : astepOk TS.ptImg TS.ptLog i ag ev.aeLb f ev.aeTs := by
      rw [hevlb, hevts, himg, hlog, ← hcimg, ← hclog]; exact hok
    have h := astepsWfSnoc pstep _ _ _ _ _ ag ev st' f hwfT hlastT hprog hok'
    rw [hevts] at h
    exact h
  -- THE TRACE SIDE, common to both cases
  have hpt' : ptracesOf pstep TS' mid c := by
    subst hc
    refine ⟨himg, hlog, by simp [TS', hlenTS], fun j Tj hTj => ?_, fun j Tj hTj => ?_,
      fun j Tj hTj => ?_, hclog, hcimg, by simp [hclen]⟩
    · by_cases hji : j = i
      · subst hji
        rw [hTS'i] at hTj; cases hTj; exact hwfT'
      · have hTj' : TS.ptTrs[j]? = some Tj := by
          rw [← list_lookup_insert_ne (Ne.symm hji) (x := T')]; exact hTj
        exact hwf j Tj hTj'
    · by_cases hji : j = i
      · subst hji
        rw [hTS'i] at hTj; cases hTj
        rw [hT'ags, lookup_app_l (by omega)]
        exact hfst j T hT
      · have hTj' : TS.ptTrs[j]? = some Tj := by
          rw [← list_lookup_insert_ne (Ne.symm hji) (x := T')]; exact hTj
        exact hfst j Tj hTj'
    · by_cases hji : j = i
      · subst hji
        rw [hTS'i] at hTj; cases hTj
        dsimp only
        rw [hT'ags, hT'evs, List.length_append, List.length_singleton,
          lookup_app_r (by omega), hlenT, Nat.sub_self, list_lookup_insert (lookup_lt_Some hlk)]
        rfl
      · have hTj' : TS.ptTrs[j]? = some Tj := by
          rw [← list_lookup_insert_ne (Ne.symm hji) (x := T')]; exact hTj
        dsimp only
        rw [list_lookup_insert_ne (Ne.symm hji)]
        exact hlst j Tj hTj'
  have HW6' : ∀ (j : Nat) (T0 : Atrace P D) (k : Nat) (ev0 : Aev D) (ag0 ag0' : Wpagent P),
      TS'.ptTrs[j]? = some T0 → T0.atEvs[k]? = some ev0 →
      T0.atAgs[k]? = some ag0 → T0.atAgs[k + 1]? = some ag0' →
      ev0.aeDev = none ∨ pdev ag0.paSt ev0.aeLb ag0'.paSt = true := by
    intro j T0 k ev0 ag0 ag0' hT0 hev0 hag0 hag0'
    by_cases hji : j = i
    · subst hji
      rw [hTS'i] at hT0; cases hT0
      rw [hT'evs] at hev0
      rw [hT'ags] at hag0 hag0'
      by_cases hlt : k < T.atEvs.length
      · rw [lookup_app_l hlt] at hev0
        rw [lookup_app_l (by omega)] at hag0
        rw [lookup_app_l (by omega)] at hag0'
        exact HW6 j T k ev0 ag0 ag0' hT hev0 hag0 hag0'
      · have hk : k = T.atEvs.length := by
          have := lookup_lt_Some hev0
          simp at this; omega
        subst hk
        rw [lookup_app_r (Nat.le_refl _), Nat.sub_self] at hev0
        rw [lookup_app_l (by omega), hlastT] at hag0
        rw [lookup_app_r (by omega), hlenT, Nat.sub_self] at hag0'
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hev0 hag0 hag0'
        subst hev0 hag0 hag0'
        rcases hevdd with ⟨hm0, _⟩ | ⟨_, hd0⟩
        · right; rw [hevlb]; exact hm0
        · left; exact hd0
    · have hT0' : TS.ptTrs[j]? = some T0 := by
        rw [← list_lookup_insert_ne (Ne.symm hji) (x := T')]; exact hT0
      exact HW6 j T0 k ev0 ag0 ag0' hT0' hev0 hag0 hag0'
  have hcdev : c.pcDev = d' := by rw [hc]
  rcases hevdd with ⟨hmark, hevdev⟩ | ⟨hmark, hevdev⟩
  · -- FABRIC-TOUCHING: extend the witness
    let DS' : Pdevs D := ⟨DS.pdInit, DS.pdOrd ++ [(i, T.atEvs.length)]⟩
    have hdinNew : evDin TS' (i, T.atEvs.length) = some y.pcDev := by
      unfold evDin; rw [hevAtNew]; simp [hevdev]
    have hdoutNew : evDout TS' (i, T.atEvs.length) = some d' := by
      unfold evDout; rw [hevAtNew]; simp [hevdev]
    have hordl : DS'.pdOrd.length = DS.pdOrd.length + 1 := by simp [DS']
    have hordold : ∀ m, m < DS.pdOrd.length → DS'.pdOrd[m]? = DS.pdOrd[m]? :=
      fun m hm => lookup_app_l hm
    have hordnew : DS'.pdOrd[DS.pdOrd.length]? = some (i, T.atEvs.length) := by
      show (DS.pdOrd ++ [(i, T.atEvs.length)])[DS.pdOrd.length]? = _
      rw [lookup_app_r (Nat.le_refl _), Nat.sub_self]; rfl
    have hdevAt' : ∀ m, m ≤ DS.pdOrd.length → devAt TS' DS' m = devAt TS DS m := by
      intro m hm
      cases m with
      | zero => rfl
      | succ m' =>
        rw [← hdevAt (m' + 1) hm]
        show ((DS'.pdOrd[m']?).bind (evDout TS')).getD DS.pdInit
          = ((DS.pdOrd[m']?).bind (evDout TS')).getD DS.pdInit
        rw [hordold m' (by omega)]
    refine ⟨TS', DS', hpt', hinit, ?_, ?_, ?_, ?_, ?_, HW6'⟩
    · intro m e0 hm
      by_cases hlt : m < DS.pdOrd.length
      · rw [hordold m hlt] at hm
        obtain ⟨ev0, hev0, hdd⟩ := HW1 m e0 hm
        exact ⟨ev0, by rw [hgrowAt e0 (hold _ _ hm)]; exact hev0, hdd⟩
      · have hm' : m = DS.pdOrd.length := by
          have := lookup_lt_Some hm
          rw [hordl] at this; omega
        subst hm'
        rw [hordnew] at hm; cases hm
        exact ⟨ev, hevAtNew, by rw [hevdev]; rfl⟩
    · intro j k ev0 hev0 hdd
      rcases hcases j k ev0 hev0 with ⟨rfl, rfl, rfl⟩ | hold0
      · exact ⟨DS.pdOrd.length, hordnew⟩
      · obtain ⟨m, hm⟩ := HW2 j k ev0 hold0 hdd
        exact ⟨m, by rw [hordold m (lookup_lt_Some hm)]; exact hm⟩
    · intro m1 m2 j k1 k2 hlt hm1 hm2
      by_cases h2 : m2 < DS.pdOrd.length
      · rw [hordold m1 (by omega)] at hm1
        rw [hordold m2 h2] at hm2
        exact HW3 m1 m2 j k1 k2 hlt hm1 hm2
      · have hm2' : m2 = DS.pdOrd.length := by
          have := lookup_lt_Some hm2
          rw [hordl] at this; omega
        subst hm2'
        rw [hordnew] at hm2
        simp only [Option.some.injEq, Prod.mk.injEq] at hm2
        obtain ⟨rfl, rfl⟩ := hm2
        rw [hordold m1 (by omega)] at hm1
        obtain ⟨ev0, hev0, _⟩ := HW1 m1 _ hm1
        unfold evAt at hev0
        dsimp only at hev0
        rw [hT] at hev0
        exact lookup_lt_Some hev0
    · intro m e0 hm
      by_cases hlt : m < DS.pdOrd.length
      · rw [hordold m hlt] at hm
        rw [hgrowDin e0 (hold _ _ hm), HW4 m e0 hm, hdevAt' m (by omega)]
      · have hm' : m = DS.pdOrd.length := by
          have := lookup_lt_Some hm
          rw [hordl] at this; omega
        subst hm'
        rw [hordnew] at hm; cases hm
        rw [hdinNew, hdevAt' _ (Nat.le_refl _), ← HW5]
    · rw [hcdev, hordl]
      show d' = ((DS'.pdOrd[DS.pdOrd.length]?).bind (evDout TS')).getD DS.pdInit
      rw [hordnew]
      simp only [Option.bind_some]
      rw [hdoutNew]; rfl
  · -- DEV-FREE: the witness is unchanged, and so is the fabric
    have hd'y : d' = y.pcDev := (hpok _ _ _ _ _ hps hmark).1
    refine ⟨TS', DS, hpt', hinit, ?_, ?_, HW3, ?_, ?_, HW6'⟩
    · intro m e0 hm
      obtain ⟨ev0, hev0, hdd⟩ := HW1 m e0 hm
      exact ⟨ev0, by rw [hgrowAt e0 (hold _ _ hm)]; exact hev0, hdd⟩
    · intro j k ev0 hev0 hdd
      rcases hcases j k ev0 hev0 with ⟨rfl, rfl, rfl⟩ | hold0
      · rw [hevdev] at hdd; cases hdd
      · exact HW2 j k ev0 hold0 hdd
    · intro m e0 hm
      have hmle : m ≤ DS.pdOrd.length := Nat.le_of_lt (lookup_lt_Some hm)
      rw [hgrowDin e0 (hold _ _ hm), HW4 m e0 hm, hdevAt m hmle]
    · rw [hcdev, hd'y, HW5, hdevAt _ (Nat.le_refl _)]

/-- THE CONSTANT-FABRIC COLLAPSE: under a marker that never fires, every event
of an extracted bundle is dev-free. -/
theorem ptracesDevOfFree (TS : Ptraces P D) (DS : Pdevs D) (mid c : Wpcfg P D) :
    (∀ p l p', pdev p l p' = false) →
    ptracesDevOf pstep pdev TS DS mid c →
    ∀ (i : Nat) (T : Atrace P D) (k : Nat) (ev : Aev D), TS.ptTrs[i]? = some T →
      T.atEvs[k]? = some ev → ev.aeDev = none := by
  intro hno ⟨hpt, _, _, _, _, _, _, HW6⟩ i T k ev hT hev
  obtain ⟨_, _, _, hwf, _⟩ := hpt
  obtain ⟨ag, ag', _, _, hag, hag', _⟩ := astepsWfStep pstep _ _ _ _ _ _ _ (hwf i T hT) hev
  rcases HW6 i T k ev ag ag' hT hev hag hag' with h | hm
  · exact h
  · rw [hno] at hm; cases hm

/-- THE TOP-LEVEL COMPOSITION with the witness: `wpBehaviorFactor`'s conclusion
in traced form. -/
theorem wpBehaviorTracedDev (img : Image) (d0 : D) (ps : List P) (c : Wpcfg P D) :
    pdevOk pstep pdev →
    latFreeProg pstep → wpBehavior pstep img d0 ps c →
    ∃ (mid : Wpcfg P D) (TS : Ptraces P D) (DS : Pdevs D),
      rtc (wpPromiseStep (P := P) (D := D)) (wpInit img d0 ps) mid ∧
      ptracesDevOf pstep pdev TS DS mid c ∧
      noPromises c := by
  intro hpok hlfp hb
  obtain ⟨mid, hprom, hstate, hnp⟩ := wpBehaviorFactor pstep img d0 ps c hlfp hb
  obtain ⟨TS, DS, hTS⟩ := statePtraces pstep pdev mid c hpok (wpLfStateRtc pstep _ _ hstate)
  exact ⟨mid, TS, DS, hprom, hTS, hnp⟩

/-- The witness-free reading (the OLD `wp_behavior_traced`). -/
theorem wpBehaviorTraced (img : Image) (d0 : D) (ps : List P) (c : Wpcfg P D) :
    pdevOk pstep pdev →
    latFreeProg pstep → wpBehavior pstep img d0 ps c →
    ∃ (mid : Wpcfg P D) (TS : Ptraces P D),
      rtc (wpPromiseStep (P := P) (D := D)) (wpInit img d0 ps) mid ∧
      ptracesOf pstep TS mid c ∧
      noPromises c := by
  intro hpok hlfp hb
  obtain ⟨mid, TS, DS, h1, ⟨h2, _⟩, h3⟩ := wpBehaviorTracedDev pstep pdev img d0 ps c hpok hlfp hb
  exact ⟨mid, TS, h1, h2, h3⟩

/-! ### FULFILMENT ACCOUNTING

Every log position authored by agent `i` is fulfilled exactly once across agent
`i`'s trace: (1) the PROMISE PHASE puts an authored message's timestamp into its
author's promise set; (2) a trace step only DELETES from the promise set, and
the deleted timestamp is one the agent held; (3) `noPromises` at the end forces
every member deleted. -/

theorem promDelSubseteq (Dl : Option Nat) (pr : GSet Nat) : promDel Dl pr ⊆ pr := by
  cases Dl with
  | none => exact fun _ h => h
  | some ts => show pr \ {ts} ⊆ pr; set_solver

/-- (1) The promise-phase invariant. -/
def promComplete (c : Wpcfg P D) : Prop :=
  ∀ (p : Nat) (m : Wmsg) (i : Nat), c.pcLog[p]? = some m → m.wmTid = some i →
    ∃ ag, c.pcAgs[i]? = some ag ∧ p + 1 ∈ ag.paProm

theorem promCompleteInit (img : Image) (d0 : D) (ps : List P) :
    promComplete (wpInit img d0 ps) := by
  intro p m i hp
  simp [wpInit] at hp

private theorem memUnionR (x T : Nat) (pr : GSet Nat) : x ∈ pr → x ∈ ({T} ∪ pr : GSet Nat) := by
  intro h; set_solver

private theorem memUnionSelf (T : Nat) (pr : GSet Nat) : T ∈ ({T} ∪ pr : GSet Nat) := by
  set_solver

theorem promCompleteStep (c c' : Wpcfg P D) :
    promComplete c → wpPromiseStep c c' → promComplete c' := by
  intro hpc hstep
  obtain ⟨j, agj, base, data, kc, hlkj, _, rfl⟩ := wpPromiseStepInv c c' hstep
  have hjlt := lookup_lt_Some hlkj
  intro p m i hp hm
  dsimp only at hp ⊢
  by_cases hlt : p < c.pcLog.length
  · rw [lookup_app_l hlt] at hp
    obtain ⟨ag, hag, hin⟩ := hpc p m i hp hm
    by_cases hij : i = j
    · subst hij
      rw [hlkj] at hag; cases hag
      exact ⟨promAdd (c.pcLog.length + 1) agj, list_lookup_insert hjlt,
        memUnionR _ _ _ hin⟩
    · exact ⟨ag, by rw [list_lookup_insert_ne (Ne.symm hij)]; exact hag, hin⟩
  · have hp' : p = c.pcLog.length := by
      have := lookup_lt_Some hp
      simp at this; omega
    subst hp'
    rw [lookup_app_r (Nat.le_refl _), Nat.sub_self] at hp
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hp
    subst hp
    simp only [Option.some.injEq] at hm
    subst hm
    exact ⟨promAdd (c.pcLog.length + 1) agj, list_lookup_insert hjlt, memUnionSelf _ _⟩

theorem promCompleteRun (c c' : Wpcfg P D) :
    promComplete c → rtc (wpPromiseStep (P := P) (D := D)) c c' → promComplete c' := by
  intro h0 hr
  induction hr with
  | refl => exact h0
  | tail _ hs ih => exact promCompleteStep _ _ ih hs

/-- (2) Promise sets only shrink along a trace. -/
theorem astepsPromDel (img : Image) (log : List Wmsg) (i : Nat) (ags : List (Wpagent P))
    (evs : List (Aev D)) (k : Nat) (ev : Aev D) (ag ag' : Wpagent P) :
    astepsWf pstep img log i ags evs →
    evs[k]? = some ev → ags[k]? = some ag → ags[k + 1]? = some ag' →
    ag'.paProm = promDel ev.aeTs ag.paProm ∧
    (∀ ts, ev.aeTs = some ts → ts ∈ ag.paProm) := by
  rintro ⟨_, hst⟩ hev hk hk'
  obtain ⟨st', f, _, hok, rfl⟩ := hst k ev ag ag' hev hk hk'
  exact ⟨rfl, fun ts hts => astepOkDel _ _ _ _ _ _ _ ts hok hts⟩

theorem astepsPromSucc (img : Image) (log : List Wmsg) (i : Nat) (ags : List (Wpagent P))
    (evs : List (Aev D)) (k : Nat) (ag ag' : Wpagent P) :
    astepsWf pstep img log i ags evs →
    ags[k]? = some ag → ags[k + 1]? = some ag' →
    ag'.paProm ⊆ ag.paProm := by
  intro hwf hk hk'
  have hlt := lookup_lt_Some hk'
  have hlen := hwf.1
  obtain ⟨ev, hev⟩ := Option.isSome_iff_exists.1 (lookup_lt_is_Some_2 (l := evs) (i := k) (by omega))
  rw [(astepsPromDel pstep _ _ _ _ _ _ _ _ _ hwf hev hk hk').1]
  exact promDelSubseteq _ _

private theorem subseteqTrans (A B C : GSet Nat) : A ⊆ B → B ⊆ C → A ⊆ C := by
  intro h1 h2; set_solver

theorem astepsPromMono (img : Image) (log : List Wmsg) (i : Nat) (ags : List (Wpagent P))
    (evs : List (Aev D)) (d : Nat) :
    ∀ (k : Nat) (ag ag' : Wpagent P),
      astepsWf pstep img log i ags evs →
      ags[k]? = some ag → ags[k + d]? = some ag' →
      ag'.paProm ⊆ ag.paProm := by
  induction d with
  | zero =>
    intro k ag ag' _ hk hkd
    rw [Nat.add_zero, hk] at hkd
    cases hkd
    exact fun _ h => h
  | succ d ih =>
    intro k ag ag' hwf hk hkd
    obtain ⟨agn, hagn⟩ :=
      Option.isSome_iff_exists.1 (lookup_lt_is_Some_2 (l := ags) (i := k + 1)
        (by have := lookup_lt_Some hkd; omega))
    have hstep : agn.paProm ⊆ ag.paProm := astepsPromSucc pstep _ _ _ _ _ _ _ _ hwf hk hagn
    have heq : k + (d + 1) = (k + 1) + d := by omega
    rw [heq] at hkd
    have hrest : ag'.paProm ⊆ agn.paProm := ih (k + 1) agn ag' hwf hagn hkd
    exact subseteqTrans _ _ _ hrest hstep

theorem astepsPromLe (img : Image) (log : List Wmsg) (i : Nat) (ags : List (Wpagent P))
    (evs : List (Aev D)) (k1 k2 : Nat) (ag1 ag2 : Wpagent P) :
    astepsWf pstep img log i ags evs →
    k1 ≤ k2 → ags[k1]? = some ag1 → ags[k2]? = some ag2 →
    ag2.paProm ⊆ ag1.paProm := by
  intro hwf hle hk1 hk2
  refine astepsPromMono pstep _ _ _ _ _ (k2 - k1) k1 ag1 ag2 hwf hk1 ?_
  rw [Nat.add_sub_cancel' hle]; exact hk2

private theorem memDelNe (ts t : Nat) (pr : GSet Nat) : ts ∈ pr → t ≠ ts → ts ∈ pr \ {t} := by
  intro h hne; set_solver

/-- (3) EXISTENCE: a promise held at the start and gone at the end was deleted by
some event. -/
theorem astepsPromDeleted (img : Image) (log : List Wmsg) (i : Nat) (evs : List (Aev D)) :
    ∀ (ags : List (Wpagent P)) (ag ag' : Wpagent P) (ts : Nat),
      astepsWf pstep img log i ags evs →
      ags[0]? = some ag → ags[evs.length]? = some ag' →
      ts ∈ ag.paProm → ts ∉ ag'.paProm →
      ∃ (k : Nat) (ev : Aev D), evs[k]? = some ev ∧ ev.aeTs = some ts := by
  induction evs with
  | nil =>
    intro ags ag ag' ts _ h0 hl hin hnin
    simp only [List.length_nil] at hl
    rw [h0] at hl; cases hl
    exact (hnin hin).elim
  | cons ev evs ih =>
    intro ags ag ag' ts hwf h0 hl hin hnin
    cases ags with
    | nil => simp at h0
    | cons a ags =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h0
      subst h0
      obtain ⟨agn, st', f, hagn, _, _, hagne, hwf'⟩ := astepsWfConsInv pstep _ _ _ _ _ _ _ hwf
      subst hagne
      simp only [List.length_cons, List.getElem?_cons_succ] at hl
      by_cases heq : ev.aeTs = some ts
      · exact ⟨0, ev, rfl, heq⟩
      · have hin' : ts ∈ promDel ev.aeTs a.paProm := by
          cases hts : ev.aeTs with
          | none => exact hin
          | some t =>
            have hne : t ≠ ts := fun h => heq (by rw [hts, h])
            exact memDelNe ts t _ hin hne
        obtain ⟨k, ev', hev', hts'⟩ := ih ags _ ag' ts hwf' hagn hl hin' hnin
        exact ⟨k + 1, ev', hev', hts'⟩

private theorem notMemDelSelf (ts : Nat) (pr : GSet Nat) : ts ∉ pr \ {ts} := by
  set_solver

/-- UNIQUENESS: a second fulfilment of `ts` would need `ts` in the promise set
after its first deletion. -/
theorem astepsFulfilLt (img : Image) (log : List Wmsg) (i : Nat) (ags : List (Wpagent P))
    (evs : List (Aev D)) (ts k1 k2 : Nat) (ev1 ev2 : Aev D) :
    astepsWf pstep img log i ags evs →
    k1 < k2 →
    evs[k1]? = some ev1 → ev1.aeTs = some ts →
    evs[k2]? = some ev2 → ev2.aeTs = some ts →
    False := by
  intro hwf hlt he1 hts1 he2 hts2
  obtain ⟨a1, a1', _, _, ha1, ha1', _⟩ := astepsWfStep pstep _ _ _ _ _ _ _ hwf he1
  obtain ⟨a2, _, _, _, ha2, _, _, hok2, _⟩ := astepsWfStep pstep _ _ _ _ _ _ _ hwf he2
  have heq := (astepsPromDel pstep _ _ _ _ _ _ _ _ _ hwf he1 ha1 ha1').1
  have hin2 : ts ∈ a2.paProm := astepOkDel _ _ _ _ _ _ _ ts hok2 hts2
  have hsub : a2.paProm ⊆ a1'.paProm :=
    astepsPromLe pstep _ _ _ _ _ (k1 + 1) k2 _ _ hwf (by omega) ha1' ha2
  have hin : ts ∈ a1'.paProm := hsub ts hin2
  rw [heq, hts1] at hin
  exact notMemDelSelf ts _ hin

theorem astepsFulfilUnique (img : Image) (log : List Wmsg) (i : Nat) (ags : List (Wpagent P))
    (evs : List (Aev D)) (ts k1 k2 : Nat) (ev1 ev2 : Aev D) :
    astepsWf pstep img log i ags evs →
    evs[k1]? = some ev1 → ev1.aeTs = some ts →
    evs[k2]? = some ev2 → ev2.aeTs = some ts →
    k1 = k2 := by
  intro hwf he1 hts1 he2 hts2
  rcases Nat.lt_trichotomy k1 k2 with hlt | heq | hgt
  · exact (astepsFulfilLt pstep img log i ags evs ts k1 k2 ev1 ev2 hwf hlt he1 hts1 he2 hts2).elim
  · exact heq
  · exact (astepsFulfilLt pstep img log i ags evs ts k2 k1 ev2 ev1 hwf hgt he2 hts2 he1 hts1).elim

private theorem notMemEmpty (x : Nat) : x ∉ (∅ : GSet Nat) := by set_solver

/-- THE ACCOUNTING THEOREM, on a traced behavior. -/
theorem wpBehaviorFulfilOnceDev (img : Image) (d0 : D) (ps : List P) (c : Wpcfg P D) :
    pdevOk pstep pdev →
    latFreeProg pstep → wpBehavior pstep img d0 ps c →
    ∃ (mid : Wpcfg P D) (TS : Ptraces P D) (DS : Pdevs D),
      rtc (wpPromiseStep (P := P) (D := D)) (wpInit img d0 ps) mid ∧
      ptracesDevOf pstep pdev TS DS mid c ∧
      noPromises c ∧
      -- every log position `p` authored by agent `i` is fulfilled EXACTLY ONCE
      -- across agent `i`'s trace
      (∀ (p : Nat) (m : Wmsg) (i : Nat), mid.pcLog[p]? = some m → m.wmTid = some i →
         ∃ T, TS.ptTrs[i]? = some T ∧
           (∃ (k : Nat) (ev : Aev D), T.atEvs[k]? = some ev ∧ ev.aeTs = some (p + 1)) ∧
           (∀ (k1 k2 : Nat) (ev1 ev2 : Aev D),
              T.atEvs[k1]? = some ev1 → ev1.aeTs = some (p + 1) →
              T.atEvs[k2]? = some ev2 → ev2.aeTs = some (p + 1) →
              k1 = k2)) := by
  intro hpok hlfp hb
  obtain ⟨mid, TS, DS, hprom, hTS, hnp⟩ := wpBehaviorTracedDev pstep pdev img d0 ps c hpok hlfp hb
  refine ⟨mid, TS, DS, hprom, hTS, hnp, ?_⟩
  obtain ⟨⟨himg, hlog, hlenTS, hwf, hfst, hlst, _, _, _⟩, _⟩ := hTS
  have hpc : promComplete mid := promCompleteRun _ _ (promCompleteInit img d0 ps) hprom
  intro p m i hp hm
  obtain ⟨ag, hag, hin⟩ := hpc p m i hp hm
  have hilt : i < TS.ptTrs.length := by rw [hlenTS]; exact lookup_lt_Some hag
  obtain ⟨T, hT⟩ := Option.isSome_iff_exists.1 (lookup_lt_is_Some_2 hilt)
  refine ⟨T, hT, ?_⟩
  have hwfT := hwf i T hT
  rw [himg, hlog] at hwfT
  have h0 : T.atAgs[0]? = some ag := by rw [hfst i T hT, hag]
  obtain ⟨agl, hagl⟩ := Option.isSome_iff_exists.1 (atraceLastIsSome pstep _ _ _ _ hwfT)
  have hcl : c.pcAgs[i]? = some agl := by rw [← hlst i T hT]; exact hagl
  have hempty : agl.paProm = ∅ := hnp i agl hcl
  have hnin : p + 1 ∉ agl.paProm := by rw [hempty]; exact notMemEmpty _
  refine ⟨astepsPromDeleted pstep mid.pcImg mid.pcLog i T.atEvs T.atAgs ag agl (p + 1) hwfT h0
    hagl hin hnin, fun k1 k2 ev1 ev2 h1 h2 h3 h4 => ?_⟩
  exact astepsFulfilUnique pstep mid.pcImg mid.pcLog i T.atAgs T.atEvs (p + 1) k1 k2 ev1 ev2
    hwfT h1 h2 h3 h4

/-- The witness-free reading (the OLD `wp_behavior_fulfil_once`). -/
theorem wpBehaviorFulfilOnce (img : Image) (d0 : D) (ps : List P) (c : Wpcfg P D) :
    pdevOk pstep pdev →
    latFreeProg pstep → wpBehavior pstep img d0 ps c →
    ∃ (mid : Wpcfg P D) (TS : Ptraces P D),
      rtc (wpPromiseStep (P := P) (D := D)) (wpInit img d0 ps) mid ∧
      ptracesOf pstep TS mid c ∧
      noPromises c ∧
      (∀ (p : Nat) (m : Wmsg) (i : Nat), mid.pcLog[p]? = some m → m.wmTid = some i →
         ∃ T, TS.ptTrs[i]? = some T ∧
           (∃ (k : Nat) (ev : Aev D), T.atEvs[k]? = some ev ∧ ev.aeTs = some (p + 1)) ∧
           (∀ (k1 k2 : Nat) (ev1 ev2 : Aev D),
              T.atEvs[k1]? = some ev1 → ev1.aeTs = some (p + 1) →
              T.atEvs[k2]? = some ev2 → ev2.aeTs = some (p + 1) →
              k1 = k2)) := by
  intro hpok hlfp hb
  obtain ⟨mid, TS, DS, h1, ⟨h2, _⟩, h3, h4⟩ :=
    wpBehaviorFulfilOnceDev pstep pdev img d0 ps c hpok hlfp hb
  exact ⟨mid, TS, h1, h2, h3, h4⟩

end trace

/-! ## What W2a step 2 (the dependency graph) inherits

- `wpBehaviorTracedDev`: a lat-free behavior is a promise phase into `mid`,
  plus one trace per agent against `mid`'s frozen `(img, log)` whose first
  records are `mid`'s agents and last records are the final configuration's,
  PLUS the GLOBAL DEVICE-ORDER WITNESS `DS`.  Per-agent program order is LIST
  ORDER in `atEvs`; `pdOrd DS` is the third edge family (G3's gdev chain).
- `wpBehaviorFulfilOnce` (+ `Dev`): the rf edge family's well-definedness.
- THE WITNESS, for G3: (W1) every listed position really is a dev-flagged
  event, (W2) every dev-flagged event is listed, and (W3) the witness order
  REFINES per-agent trace order.
- `ptracesWit` (+ `ptracesDevOfWit`, `ptracesWitNil`): the WITNESS-ONLY part
  of the bundle (W1–W4); the EMPTY witness satisfies it for a dev-free bundle.
- THE FOLD, for G4: `devAt TS DS m` is the fabric BEFORE witness position
  `m`; (W4) says a listed step reads exactly that, and (W5) that the phase ends
  at the last listed step's `dout`.
- THE CONSTANT-FABRIC COLLAPSE: `ptracesDevOfFree`.
- `atraceReplay` is the inverse of `astepOfAtrace` for a SINGLE agent, stated
  for DEV-FREE traces.
- G5 SANITY (recorded, not yet mechanized): `WeakEvPf.epf_step` is the event
  language's promise-free machine; its marker is `pdev p l p' := true` exactly
  on the device-access steps, so `pdevOk` holds and G5's obligation is to read
  the decomposition off `statePtraces`. -/

end Weak
