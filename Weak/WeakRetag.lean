/-
Weak: **the CLASS-RETAG simulation** (premise-ledger stage A1).

Rocq: `iris/WeakRetag.v` @ xxvzwolszwmp (1cc222280).

The Rocq header, in substance: `WeakMem`'s `wmAk` (the message class, D-M6-6) is an INERT
syntactic tag.  This file PROVES that inertness and turns it into the elimination the capstone's
premise ledger wants (`claude-notes/projects/weak-memory-premises.md`, stage A1): the `Hcls`
premise (`clsCanonical`) is not an assumption about the machine, it is a property every behavior
can be BROUGHT INTO by relabelling its log.

THE KEY FACT, verified rule by rule below: no rule of `wpstep` ever READS a message's `wmAk`.
`WPPromise` APPENDS a class (its own free binder `k`); `WPFulfil`/`WPRmw`/`WPExStore` require the
fulfilled entry to BE `⟨base, data, some i, k⟩` for SOME `k` (a rule binder too); `readOkD`,
`exclOk`, `exclOkTs`, `adShapedb`, `fulfilOkD`, `ifetchOk` see the log only through
`msgByte`/`logByte`/`writesIn`/`writesInBy`, which project `wmPa`/`wmData`/`wmTid` only; labels,
trace events (`Aev`) and agent records (`Wpagent`) carry no class.  Hence changing EVERY message's
class, uniformly and pointwise by POSITION (`retagLog f = mapIdx (retagMsg f)`), commutes with
every step (`wpstepRetag`), with whole behaviors, traces and the observables `progOf`/`memOf`.
Position (not message identity) is the right index: two log entries can be identical messages,
and the canonical class of each is computed at ITS OWN fulfil event.

FINDING (recorded rather than proved, as in Rocq): the CONVERSE simulation is FALSE — `retagCfg
f` is not injective, and a silent step mapping an agent to itself relates two retag-equal
configurations that differ in one class, which no `wpstep` relates.  Nothing downstream needs it.

DEPENDENCY-LIGHT: `WeakMem`, `WeakPromise`, `WeakPromiseFact`, `WeakRobust` (for
`progOf`/`memOf`), `WeakRobustTrace`.  Canonicity is stated against a PARAMETER
`clsf : P → Wlabel → Wstate → WmClass`.

WHAT STAGE B INHERITS: `behaviorCanonical` (a lat-free behavior is matched by a behavior of the
same program with the same `progOf`/`memOf` whose traced factorization satisfies `clsCanonical
clsf`); the reusable half `wpstepRetag` / `wpPromiseStepRetag` / `atraceWfRetag` /
`ptracesOfRetag` / `ptracesDevOfRetag`; `retagConclusion` to transport a conclusion back.

**Deviations from Rocq.**

1. NAMES: as `Weak/WeakMem.lean` deviation 1 (lowerCamelCase).  None of this file's names is in
   the duplicated-name table, so none is file-qualified.
2. VOCABULARY: `imap` ↦ `List.mapIdx`; `list_find` ↦ `MachCSL.Stdpp.listFind` with the Boolean
   predicate `fun ev => decide (ev.aeTs = some (p + 1))`; `S p` ↦ `p + 1`; otherwise as
   `WeakPromise` deviation 2.  Record literals are anonymous constructors.
3. SECTION VARIABLES: `pstep` / `pdev` are explicit arguments exactly where the statement (or,
   for `cfgWfPromiseRun`, the proof: `include pstep in`, as Rocq's section closure gives it)
   uses them.  `clsCanonicalCanon` takes NO `pdev`: in Rocq it carries `pdev` only because its
   proof calls `asteps_fulfil_unique pstep pdev`, whose Lean twin `astepsFulfilUnique` has no
   `pdev` (its statement does not mention it).  Statement otherwise unchanged.
4. O2 — THE INSTRUCTION FETCH (Lean-only label `LIFetch`, `Weak/WeakPromise.lean` deviation 8):
   `wpstepRetag` gains the `WPIFetch` arm and `astepOkRetag` the `LIFetch` arm; both go through
   the Lean-only `retagIfetchByteOk` / `retagIfetchOk` (`ifetchOk` reads the log only through
   `logByte` and `writesIn`, so it is retag-invariant like every other side condition).  The
   `clsCanonicalCanon` author argument's `LIFetch` arm is the non-store case (`Dl = none`).
   No statement changes.
5. PROOFS: `retagAdShaped` / `retagAdShapedb` are proved by rewriting with `retagResReadByte`
   directly (Rocq goes through `ad_shapedb_spec` for the Boolean); `retag_log_app` is
   `List.mapIdx_append`; `canonFSpec` cases on the scan with `cases E :` instead of
   `destruct … eqn:`.  Statements unchanged.
6. Lean-only helpers (no Rocq twin): `retagLogLookupLit` (a positional literal is found retagged
   at `f p`) and `retagLogLookupLitInv` (its converse up to the class), used where Rocq writes
   `rewrite retag_log_lookup Hm` / `simplify_eq`; `retagIfetchByteOk`, `retagIfetchOk`
   (deviation 4).

**Rocq → Lean name map.**  `retag_msg` ↦ `retagMsg`; `retag_log` ↦ `retagLog`;
`retag_msg_{pa,data,tid,ak,lit,byte,writesb}` ↦ `retagMsg{Pa,Data,Tid,Ak,Lit,Byte,Writesb}`;
`retag_log_{nil,length,lookup,lookup_Some,lookup_inv,app,retag,untag,byte}` ↦
`retagLog{Nil,Length,Lookup,LookupSome,LookupInv,App,Retag,Untag,Byte}`; `untag_f` ↦ `untagF`;
`retag_writes_in{,_1,_2}` ↦ `retagWritesIn{,1,2}`; `retag_writes_in_by{,_1,_2}` ↦
`retagWritesInBy{,1,2}`; `retag_latest_ts` ↦ `retagLatestTs`; `retag_latest` ↦ `retagLatest`;
`retag_readable{,_1,_2}` ↦ `retagReadable{,1,2}`; `retag_read_ok_d` ↦ `retagReadOkD`;
`retag_read_ok{,_1,_2}` ↦ `retagReadOk{,1,2}`; `retag_excl_ok{,_1,_2}` ↦ `retagExclOk{,1,2}`;
`retag_excl_ok_ts{,_1,_2}` ↦ `retagExclOkTs{,1,2}`; `retag_res_read_byte` ↦ `retagResReadByte`;
`retag_ad_shaped{,b}` ↦ `retagAdShaped{,b}`; `retag_fulfil_ok` ↦ `retagFulfilOk`; `retag_cfg` ↦
`retagCfg`; `retag_cfg_{img,log,ags,log_length,retag,untag}` ↦
`retagCfg{Img,Log,Ags,LogLength,Retag,Untag}`; `wpstep_retag` ↦ `wpstepRetag`;
`wpsteps_retag` ↦ `wpstepsRetag`; `wp_promise_step_retag` ↦ `wpPromiseStepRetag`;
`wp_promise_steps_retag` ↦ `wpPromiseStepsRetag`; `retag_wp_init` ↦ `retagWpInit`;
`no_promises_retag` ↦ `noPromisesRetag`; `wp_behavior_retag` ↦ `wpBehaviorRetag`;
`prom_wf_retag` ↦ `promWfRetag`; `cfg_wf_retag` ↦ `cfgWfRetag`; `prog_of_retag` ↦
`progOfRetag`; `mem_of_retag` ↦ `memOfRetag`; `retag_conclusion` ↦ `retagConclusion`;
`retag_traces` ↦ `retagTraces`; `retag_traces_{img,log,trs}` ↦ `retagTraces{Img,Log,Trs}`;
`astep_ok_retag` ↦ `astepOkRetag`; `asteps_wf_retag` ↦ `astepsWfRetag`; `atrace_wf_retag` ↦
`atraceWfRetag`; `ptraces_of_retag` ↦ `ptracesOfRetag`; `ptraces_dev_of_retag` ↦
`ptracesDevOfRetag`; `fulfil_at` ↦ `fulfilAt`; `canon_f` ↦ `canonF`; `canon_f_spec` ↦
`canonFSpec`; `ts_pos` ↦ `tsPos`; `cls_canonical_canon` ↦ `clsCanonicalCanon`;
`cfg_wf_promise_run` ↦ `cfgWfPromiseRun`; `ts_pos_of_ptraces` ↦ `tsPosOfPtraces`;
`behavior_canonical` ↦ `behaviorCanonical`.

**Not ported:** nothing — every Rocq definition and lemma has a Lean twin.

**Statements checked** (by hand, against Rocq): all of them.
-/
import Weak.WeakRobust
import Weak.WeakRobustTrace

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std Wlabel

/-! ## 1. The pointwise retag, and the log predicates it fixes -/

/-- Re-tag ONE message, at its log position `p`. -/
def retagMsg (f : Nat → WmClass) (p : Nat) (m : Wmsg) : Wmsg :=
  ⟨m.wmPa, m.wmData, m.wmTid, f p⟩

/-- Re-tag a whole log, pointwise by position. -/
def retagLog (f : Nat → WmClass) (log : List Wmsg) : List Wmsg :=
  log.mapIdx (retagMsg f)

/-! ### The three surviving projections, and the one that changes -/

theorem retagMsgPa (f : Nat → WmClass) (p : Nat) (m : Wmsg) : (retagMsg f p m).wmPa = m.wmPa := rfl

theorem retagMsgData (f : Nat → WmClass) (p : Nat) (m : Wmsg) :
    (retagMsg f p m).wmData = m.wmData := rfl

theorem retagMsgTid (f : Nat → WmClass) (p : Nat) (m : Wmsg) :
    (retagMsg f p m).wmTid = m.wmTid := rfl

theorem retagMsgAk (f : Nat → WmClass) (p : Nat) (m : Wmsg) : (retagMsg f p m).wmAk = f p := rfl

/-- The one shape that matters to `WPFulfil`/`WPRmw`/`astepOk`: a positional literal keeps its
base/data/tid and takes the new class. -/
theorem retagMsgLit (f : Nat → WmClass) (p : Nat) (base : Int) (data : List (BitVec 8))
    (tid : Option Nat) (k : WmClass) :
    retagMsg f p ⟨base, data, tid, k⟩ = ⟨base, data, tid, f p⟩ := rfl

theorem retagMsgByte (f : Nat → WmClass) (p : Nat) (m : Wmsg) (a : Int) :
    msgByte (retagMsg f p m) a = msgByte m a := rfl

theorem retagMsgWritesb (f : Nat → WmClass) (p : Nat) (m : Wmsg) (a : Int) :
    msgWritesb (retagMsg f p m) a = msgWritesb m a := rfl

/-! ### The list-level laws -/

theorem retagLogNil (f : Nat → WmClass) : retagLog f [] = [] := by
  simp [retagLog]

theorem retagLogLength (f : Nat → WmClass) (log : List Wmsg) :
    (retagLog f log).length = log.length := List.length_mapIdx

theorem retagLogLookup (f : Nat → WmClass) (log : List Wmsg) (p : Nat) :
    (retagLog f log)[p]? = log[p]?.map (retagMsg f p) := List.getElem?_mapIdx

theorem retagLogLookupSome (f : Nat → WmClass) (log : List Wmsg) (p : Nat) (m : Wmsg) :
    log[p]? = some m → (retagLog f log)[p]? = some (retagMsg f p m) := by
  intro h; rw [retagLogLookup, h]; rfl

theorem retagLogLookupInv (f : Nat → WmClass) (log : List Wmsg) (p : Nat) (m' : Wmsg) :
    (retagLog f log)[p]? = some m' → ∃ m, log[p]? = some m ∧ m' = retagMsg f p m := by
  rw [retagLogLookup]
  cases h : log[p]? with
  | none => intro h'; cases h'
  | some m =>
    intro h'
    simp only [Option.map_some, Option.some.injEq] at h'
    exact ⟨m, rfl, h'.symm⟩

/-- (Lean-only helper) A positional literal is found retagged at `f p`. -/
theorem retagLogLookupLit (f : Nat → WmClass) (log : List Wmsg) (p : Nat) (base : Int)
    (data : List (BitVec 8)) (tid : Option Nat) (k : WmClass) :
    log[p]? = some ⟨base, data, tid, k⟩ → (retagLog f log)[p]? = some ⟨base, data, tid, f p⟩ :=
  retagLogLookupSome f log p _

/-- (Lean-only helper) ... and conversely, up to the class. -/
theorem retagLogLookupLitInv (f : Nat → WmClass) (log : List Wmsg) (p : Nat) (base : Int)
    (data : List (BitVec 8)) (tid : Option Nat) (k : WmClass) :
    (retagLog f log)[p]? = some ⟨base, data, tid, k⟩ → ∃ k', log[p]? = some ⟨base, data, tid, k'⟩ := by
  intro h
  obtain ⟨m, hm, he⟩ := retagLogLookupInv f log p _ h
  obtain ⟨pa, dat, tid', ak⟩ := m
  simp only [retagMsg, Wmsg.mk.injEq] at he
  obtain ⟨rfl, rfl, rfl, -⟩ := he
  exact ⟨ak, hm⟩

/-- THE APPEND LAW — what `WPPromise`'s case needs: the new top's class is `f` at the OLD
length. -/
theorem retagLogApp (f : Nat → WmClass) (log : List Wmsg) (m : Wmsg) :
    retagLog f (log ++ [m]) = retagLog f log ++ [retagMsg f log.length m] := by
  simp [retagLog, List.mapIdx_append]

/-- Retagging is ABSORBING: the last retag wins. -/
theorem retagLogRetag (f g : Nat → WmClass) (log : List Wmsg) :
    retagLog f (retagLog g log) = retagLog f log := by
  apply List.ext_getElem?
  intro p
  rw [retagLogLookup, retagLogLookup, retagLogLookup]
  cases log[p]? <;> rfl

/-- ... and the identity retag exists (positionally computed), so a log is always in the image
of a retag. -/
def untagF (log : List Wmsg) (p : Nat) : WmClass :=
  match log[p]? with
  | some m => m.wmAk
  | none => .WCplain

theorem retagLogUntag (log : List Wmsg) : retagLog (untagF log) log = log := by
  apply List.ext_getElem?
  intro p
  rw [retagLogLookup]
  cases hm : log[p]? with
  | none => rfl
  | some m =>
    simp only [Option.map_some, retagMsg, untagF, hm]

/-! ### Every log predicate of the machine is retag-invariant -/

theorem retagLogByte (f : Nat → WmClass) (img : Image) (log : List Wmsg) (t : Nat) (a : Int) :
    logByte img (retagLog f log) t a = logByte img log t a := by
  cases t with
  | zero => rfl
  | succ i =>
    rw [logByteS, logByteS, retagLogLookup]
    cases log[i]? <;> rfl

theorem retagWritesIn (f : Nat → WmClass) (log : List Wmsg) (a : Int) (lo hi : Nat) :
    writesIn (retagLog f log) a lo hi ↔ writesIn log a lo hi := by
  constructor
  · rintro ⟨t, hlo, hhi, m', hm', hs⟩
    obtain ⟨m, hm, rfl⟩ := retagLogLookupInv f log _ _ hm'
    exact ⟨t, hlo, hhi, m, hm, hs⟩
  · rintro ⟨t, hlo, hhi, m, hm, hs⟩
    exact ⟨t, hlo, hhi, retagMsg f (t - 1) m, retagLogLookupSome f log _ _ hm, hs⟩

theorem retagWritesIn1 (f : Nat → WmClass) (log : List Wmsg) (a : Int) (lo hi : Nat) :
    writesIn (retagLog f log) a lo hi → writesIn log a lo hi := (retagWritesIn f log a lo hi).1

theorem retagWritesIn2 (f : Nat → WmClass) (log : List Wmsg) (a : Int) (lo hi : Nat) :
    writesIn log a lo hi → writesIn (retagLog f log) a lo hi := (retagWritesIn f log a lo hi).2

theorem retagWritesInBy (f : Nat → WmClass) (log : List Wmsg) (Q : Option Nat → Prop) (a : Int)
    (lo hi : Nat) : writesInBy (retagLog f log) Q a lo hi ↔ writesInBy log Q a lo hi := by
  constructor
  · rintro ⟨t, hlo, hhi, m', hm', hs, hQ⟩
    obtain ⟨m, hm, rfl⟩ := retagLogLookupInv f log _ _ hm'
    exact ⟨t, hlo, hhi, m, hm, hs, hQ⟩
  · rintro ⟨t, hlo, hhi, m, hm, hs, hQ⟩
    exact ⟨t, hlo, hhi, retagMsg f (t - 1) m, retagLogLookupSome f log _ _ hm, hs, hQ⟩

theorem retagWritesInBy1 (f : Nat → WmClass) (log : List Wmsg) (Q : Option Nat → Prop) (a : Int)
    (lo hi : Nat) : writesInBy (retagLog f log) Q a lo hi → writesInBy log Q a lo hi :=
  (retagWritesInBy f log Q a lo hi).1

theorem retagWritesInBy2 (f : Nat → WmClass) (log : List Wmsg) (Q : Option Nat → Prop) (a : Int)
    (lo hi : Nat) : writesInBy log Q a lo hi → writesInBy (retagLog f log) Q a lo hi :=
  (retagWritesInBy f log Q a lo hi).2

theorem retagLatestTs (f : Nat → WmClass) (log : List Wmsg) (a : Int) :
    latestTs (retagLog f log) a = latestTs log a := by
  induction log using snocInd with
  | h0 => rw [retagLogNil]
  | hs l m ih =>
    rw [retagLogApp, latestTsApp, latestTsApp, retagLogLength, ih, retagMsgWritesb]

theorem retagLatest (f : Nat → WmClass) (img : Image) (log : List Wmsg) (a : Int) (t : Nat) :
    latest img (retagLog f log) a t ↔ latest img log a t := by
  unfold latest
  rw [retagLogByte, retagLogLength, retagWritesIn]

theorem retagReadable (f : Nat → WmClass) (img : Image) (log : List Wmsg) (ws : Wstate)
    (vpre : Nat) (a : Int) (t : Nat) :
    readable img (retagLog f log) ws vpre a t ↔ readable img log ws vpre a t := by
  unfold readable
  rw [retagLogByte, retagWritesIn]

theorem retagReadable1 (f : Nat → WmClass) (img : Image) (log : List Wmsg) (ws : Wstate)
    (vpre : Nat) (a : Int) (t : Nat) :
    readable img (retagLog f log) ws vpre a t → readable img log ws vpre a t :=
  (retagReadable f img log ws vpre a t).1

theorem retagReadable2 (f : Nat → WmClass) (img : Image) (log : List Wmsg) (ws : Wstate)
    (vpre : Nat) (a : Int) (t : Nat) :
    readable img log ws vpre a t → readable img (retagLog f log) ws vpre a t :=
  (retagReadable f img log ws vpre a t).2

theorem retagReadOkD (f : Nat → WmClass) (img : Image) (log : List Wmsg) (ws : Wstate)
    (aq lat : Bool) (base : Int) (tvs : List (Nat × BitVec 8)) (va : Nat) :
    readOkD img (retagLog f log) ws aq lat base tvs va ↔ readOkD img log ws aq lat base tvs va := by
  unfold readOkD
  simp only [retagLogByte, retagReadable, retagWritesIn, retagLogLength]

theorem retagReadOk (f : Nat → WmClass) (img : Image) (log : List Wmsg) (ws : Wstate)
    (aq lat : Bool) (base : Int) (tvs : List (Nat × BitVec 8)) :
    readOk img (retagLog f log) ws aq lat base tvs ↔ readOk img log ws aq lat base tvs :=
  retagReadOkD f img log ws aq lat base tvs 0

theorem retagReadOk1 (f : Nat → WmClass) (img : Image) (log : List Wmsg) (ws : Wstate)
    (aq lat : Bool) (base : Int) (tvs : List (Nat × BitVec 8)) (va : Nat) :
    readOkD img (retagLog f log) ws aq lat base tvs va → readOkD img log ws aq lat base tvs va :=
  (retagReadOkD f img log ws aq lat base tvs va).1

theorem retagReadOk2 (f : Nat → WmClass) (img : Image) (log : List Wmsg) (ws : Wstate)
    (aq lat : Bool) (base : Int) (tvs : List (Nat × BitVec 8)) (va : Nat) :
    readOkD img log ws aq lat base tvs va → readOkD img (retagLog f log) ws aq lat base tvs va :=
  (retagReadOkD f img log ws aq lat base tvs va).2

theorem retagExclOk (f : Nat → WmClass) (log : List Wmsg) (i : Nat) (base : Int)
    (tvs : List (Nat × BitVec 8)) (ts : Nat) :
    exclOk (retagLog f log) i base tvs ts ↔ exclOk log i base tvs ts := by
  unfold exclOk
  simp only [retagWritesInBy]

theorem retagExclOk1 (f : Nat → WmClass) (log : List Wmsg) (i : Nat) (base : Int)
    (tvs : List (Nat × BitVec 8)) (ts : Nat) :
    exclOk (retagLog f log) i base tvs ts → exclOk log i base tvs ts :=
  (retagExclOk f log i base tvs ts).1

theorem retagExclOk2 (f : Nat → WmClass) (log : List Wmsg) (i : Nat) (base : Int)
    (tvs : List (Nat × BitVec 8)) (ts : Nat) :
    exclOk log i base tvs ts → exclOk (retagLog f log) i base tvs ts :=
  (retagExclOk f log i base tvs ts).2

/-- THE RMW SPLIT (S2): the same, for the reservation-shaped window. -/
theorem retagExclOkTs (f : Nat → WmClass) (log : List Wmsg) (i : Nat) (base : Int)
    (rts : List Nat) (ts : Nat) :
    exclOkTs (retagLog f log) i base rts ts ↔ exclOkTs log i base rts ts := by
  unfold exclOkTs
  simp only [retagWritesInBy]

theorem retagExclOkTs1 (f : Nat → WmClass) (log : List Wmsg) (i : Nat) (base : Int)
    (rts : List Nat) (ts : Nat) :
    exclOkTs (retagLog f log) i base rts ts → exclOkTs log i base rts ts :=
  (retagExclOkTs f log i base rts ts).1

theorem retagExclOkTs2 (f : Nat → WmClass) (log : List Wmsg) (i : Nat) (base : Int)
    (rts : List Nat) (ts : Nat) :
    exclOkTs log i base rts ts → exclOkTs (retagLog f log) i base rts ts :=
  (retagExclOkTs f log i base rts ts).2

/-- THE WALKER DISCRIMINATOR (layer2 §13, W2a) is retag-invariant: it reads the log only through
`logByte`, and a retag moves no byte. -/
theorem retagResReadByte (f : Nat → WmClass) (img : Image) (log : List Wmsg) (base : Int)
    (rts : List Nat) (j : Nat) :
    resReadByte img (retagLog f log) base rts j = resReadByte img log base rts j := by
  unfold resReadByte
  simp only [retagLogByte]

theorem retagAdShaped (f : Nat → WmClass) (img : Image) (log : List Wmsg) (base : Int)
    (rts : List Nat) (data : List (BitVec 8)) :
    adShaped img (retagLog f log) base rts data ↔ adShaped img log base rts data := by
  unfold adShaped
  simp only [retagResReadByte]

theorem retagAdShapedb (f : Nat → WmClass) (img : Image) (log : List Wmsg) (base : Int)
    (rts : List Nat) (data : List (BitVec 8)) :
    adShapedb img (retagLog f log) base rts data = adShapedb img log base rts data := by
  unfold adShapedb
  simp only [retagResReadByte]

/-- `fulfilOk` mentions no log at all — recorded so the audit above is complete on the page. -/
theorem retagFulfilOk (ws : Wstate) (rl : Bool) (base : Int) (n ts : Nat) :
    fulfilOk ws rl base n ts → fulfilOk ws rl base n ts := id

/-- (Lean-only, O2) the i-cache read is retag-invariant too. -/
theorem retagIfetchByteOk (f : Nat → WmClass) (img : Image) (log : List Wmsg) (itv : Nat)
    (a : Int) (t : Nat) (v : BitVec 8) :
    ifetchByteOk img (retagLog f log) itv a t v ↔ ifetchByteOk img log itv a t v := by
  unfold ifetchByteOk
  rw [retagLogByte, retagWritesIn]

theorem retagIfetchOk (f : Nat → WmClass) (img : Image) (log : List Wmsg) (itv : Nat)
    (base : Int) (tvs : List (Nat × BitVec 8)) :
    ifetchOk img (retagLog f log) itv base tvs ↔ ifetchOk img log itv base tvs := by
  unfold ifetchOk
  simp only [retagIfetchByteOk]

/-! ## 2. Configurations and the step simulation -/

/-- Agent records carry NO class, so a retag touches the log and nothing else. -/
def retagCfg {P D : Type} (f : Nat → WmClass) (c : Wpcfg P D) : Wpcfg P D :=
  ⟨c.pcImg, retagLog f c.pcLog, c.pcDev, c.pcAgs⟩

theorem retagCfgImg {P D : Type} (f : Nat → WmClass) (c : Wpcfg P D) :
    (retagCfg f c).pcImg = c.pcImg := rfl

theorem retagCfgLog {P D : Type} (f : Nat → WmClass) (c : Wpcfg P D) :
    (retagCfg f c).pcLog = retagLog f c.pcLog := rfl

theorem retagCfgAgs {P D : Type} (f : Nat → WmClass) (c : Wpcfg P D) :
    (retagCfg f c).pcAgs = c.pcAgs := rfl

theorem retagCfgLogLength {P D : Type} (f : Nat → WmClass) (c : Wpcfg P D) :
    (retagCfg f c).pcLog.length = c.pcLog.length := retagLogLength f c.pcLog

theorem retagCfgRetag {P D : Type} (f g : Nat → WmClass) (c : Wpcfg P D) :
    retagCfg f (retagCfg g c) = retagCfg f c := by
  simp only [retagCfg, retagLogRetag]

theorem retagCfgUntag {P D : Type} (c : Wpcfg P D) : retagCfg (untagF c.pcLog) c = c := by
  simp only [retagCfg, retagLogUntag]

section machine

variable {P D : Type}
variable (pstep : P → D → Wlabel → P → D → Prop)
variable (pdev : P → Wlabel → P → Bool)

/-! ### THE STEP SIMULATION — all rules (`WPDev`, the three dependency-only arms, the RMW split,
and the Lean-only fetch) -/

theorem wpstepRetag (f : Nat → WmClass) (c c' : Wpcfg P D) :
    wpstep pstep c c' → wpstep pstep (retagCfg f c) (retagCfg f c') := by
  intro hstep
  cases hstep with
  | WPPromise i ag base data k hlk hnn =>
    -- the appended class is the rule's free binder: take `f` at the OLD log length
    have hs := wpstep.WPPromise (pstep := pstep) (retagCfg f c) i ag base data
      (f c.pcLog.length) hlk hnn
    rw [retagCfgLogLength] at hs
    simp only [retagCfg, retagLogApp]
    exact hs
  | WPSilent i ag st' d' hlk hps =>
    exact wpstep.WPSilent (retagCfg f c) i ag st' d' hlk hps
  | WPLoad i ag aq lat base tvs asrc st' d' hlk hps hr =>
    exact wpstep.WPLoad (retagCfg f c) i ag aq lat base tvs asrc st' d' hlk hps
      ((retagReadOkD f c.pcImg c.pcLog _ _ _ _ _ _).2 hr)
  | WPFulfil i ag rl base data asrc vsrc k ts st' d' hlk hps h1 h2 h3 =>
    -- the matched entry's class is the rule's free binder
    exact wpstep.WPFulfil (retagCfg f c) i ag rl base data asrc vsrc (f (ts - 1)) ts st' d'
      hlk hps h1 (retagLogLookupLit f c.pcLog _ _ _ _ _ h2) h3
  | WPRmw i ag aq rl base tvs data asrc vsrc k ts st' d' hlk hps h1 h2 h3 h4 h5 h6 =>
    exact wpstep.WPRmw (retagCfg f c) i ag aq rl base tvs data asrc vsrc (f (ts - 1)) ts st' d'
      hlk hps h1 h2 (retagLogLookupLit f c.pcLog _ _ _ _ _ h3)
      ((retagReadOk f c.pcImg c.pcLog _ _ _ _ _).2 h4)
      ((retagExclOk f c.pcLog _ _ _ _).2 h5) h6
  | WPFence i ag pr pw sr sw st' d' hlk hps =>
    exact wpstep.WPFence (retagCfg f c) i ag pr pw sr sw st' d' hlk hps
  | WPDev i ag st' d' hlk hps =>
    exact wpstep.WPDev (retagCfg f c) i ag st' d' hlk hps
  | WPRegW i ag rd srcs st' d' hlk hps =>
    exact wpstep.WPRegW (retagCfg f c) i ag rd srcs st' d' hlk hps
  | WPCtrl i ag srcs st' d' hlk hps =>
    exact wpstep.WPCtrl (retagCfg f c) i ag srcs st' d' hlk hps
  | WPInstr i ag st' d' hlk hps =>
    exact wpstep.WPInstr (retagCfg f c) i ag st' d' hlk hps
  | WPExLoad i ag aq base tvs asrc st' d' hlk hps hr =>
    exact wpstep.WPExLoad (retagCfg f c) i ag aq base tvs asrc st' d' hlk hps
      ((retagReadOk f c.pcImg c.pcLog _ _ _ _ _).2 hr)
  | WPExStore i ag rl base data asrc vsrc k ts R st' d' hlk hps h1 h2 h3 h4 h5 h6 h7 =>
    have h7' : fulfilOkD ag.paWs rl base data.length ts
        (max (max (srcsView ag.paWs asrc) (srcsView ag.paWs vsrc))
          (max R.rvView
            (if adShapedb (retagCfg f c).pcImg (retagCfg f c).pcLog base R.rvTs data
             then max ag.paWs.wVrOld ag.paWs.wVwOld else 0))) := by
      rw [retagCfgImg, retagCfgLog, retagAdShapedb]; exact h7
    exact wpstep.WPExStore (retagCfg f c) i ag rl base data asrc vsrc (f (ts - 1)) ts R st' d'
      hlk hps h1 (retagLogLookupLit f c.pcLog _ _ _ _ _ h2) h3 h4 h5
      ((retagExclOkTs f c.pcLog _ _ _ _).2 h6) h7'
  | WPIFetch i ag base tvs st' d' hlk hps hr =>
    exact wpstep.WPIFetch (retagCfg f c) i ag base tvs st' d' hlk hps
      ((retagIfetchOk f c.pcImg c.pcLog _ _ _).2 hr)

theorem wpstepsRetag (f : Nat → WmClass) (c c' : Wpcfg P D) :
    rtc (wpstep pstep) c c' → rtc (wpstep pstep) (retagCfg f c) (retagCfg f c') := by
  intro h
  induction h with
  | refl => exact rtc_refl _
  | tail _ hs ih => exact rtc_r ih (wpstepRetag pstep f _ _ hs)

/-- The promise phase alone — the shape the traced factorization exports. -/
theorem wpPromiseStepRetag (f : Nat → WmClass) (c c' : Wpcfg P D) :
    wpPromiseStep c c' → wpPromiseStep (retagCfg f c) (retagCfg f c') := by
  intro hstep
  cases hstep with
  | WPPromStep i ag base data k hlk hnn =>
    have hs := wpPromiseStep.WPPromStep (retagCfg f c) i ag base data (f c.pcLog.length) hlk hnn
    rw [retagCfgLogLength] at hs
    simp only [retagCfg, retagLogApp]
    exact hs

theorem wpPromiseStepsRetag (f : Nat → WmClass) (c c' : Wpcfg P D) :
    rtc (wpPromiseStep (P := P) (D := D)) c c' →
    rtc (wpPromiseStep (P := P) (D := D)) (retagCfg f c) (retagCfg f c') := by
  intro h
  induction h with
  | refl => exact rtc_refl _
  | tail _ hs ih => exact rtc_r ih (wpPromiseStepRetag f _ _ hs)

/-! ### Initial configurations, promise-freedom, behaviors -/

theorem retagWpInit (f : Nat → WmClass) (img : Image) (d0 : D) (ps : List P) :
    retagCfg f (wpInit img d0 ps) = wpInit img d0 ps := by
  simp only [retagCfg, wpInit, retagLogNil]

theorem noPromisesRetag (f : Nat → WmClass) (c : Wpcfg P D) :
    noPromises c ↔ noPromises (retagCfg f c) := Iff.rfl

theorem wpBehaviorRetag (f : Nat → WmClass) (img : Image) (d0 : D) (ps : List P) (c : Wpcfg P D) :
    wpBehavior pstep img d0 ps c → wpBehavior pstep img d0 ps (retagCfg f c) := by
  rintro ⟨hrun, hnp⟩
  refine ⟨?_, (noPromisesRetag f c).1 hnp⟩
  have h := wpstepsRetag pstep f _ _ hrun
  rw [retagWpInit] at h
  exact h

/-- Well-formedness survives too (nothing in `cfgWf` reads a class). -/
theorem promWfRetag (f : Nat → WmClass) (log : List Wmsg) (i : Nat) (ag : Wpagent P) :
    promWf log i ag ↔ promWf (retagLog f log) i ag := by
  constructor
  · intro hp ts hts
    obtain ⟨h1, h2, m, hm, ht⟩ := hp ts hts
    exact ⟨h1, by rw [retagLogLength]; exact h2, retagMsg f (ts - 1) m,
      retagLogLookupSome f log _ _ hm, ht⟩
  · intro hp ts hts
    obtain ⟨h1, h2, m', hm', ht⟩ := hp ts hts
    obtain ⟨m, hm, rfl⟩ := retagLogLookupInv f log _ _ hm'
    rw [retagLogLength] at h2
    exact ⟨h1, h2, m, hm, ht⟩

theorem cfgWfRetag (f : Nat → WmClass) (c : Wpcfg P D) : cfgWf c ↔ cfgWf (retagCfg f c) := by
  constructor
  · intro hwf i ag hlk
    obtain ⟨hb, hp⟩ := hwf i ag hlk
    refine ⟨?_, (promWfRetag f _ _ _).1 hp⟩
    rw [retagCfgLogLength]; exact hb
  · intro hwf i ag hlk
    obtain ⟨hb, hp⟩ := hwf i ag hlk
    rw [retagCfgLogLength] at hb
    exact ⟨hb, (promWfRetag f _ _ _).2 hp⟩

/-! ## 3. Conclusion transport: the observables are class-independent -/

theorem progOfRetag (f : Nat → WmClass) (c : Wpcfg P D) : progOf (retagCfg f c) = progOf c := rfl

theorem memOfRetag (f : Nat → WmClass) (c : Wpcfg P D) (a : Int) :
    memOf (retagCfg f c) a = memOf c a := by
  show logByte c.pcImg (retagLog f c.pcLog) (latestTs (retagLog f c.pcLog) a) a
    = logByte c.pcImg c.pcLog (latestTs c.pcLog a) a
  rw [retagLatestTs, retagLogByte]

/-- The capstone's plumbing: a promise-free witness run matched against the RETAGGED behavior
matches the original behavior too. -/
theorem retagConclusion (f : Nat → WmClass) (c cf : Wpcfg P D) :
    progOf cf = progOf (retagCfg f c) →
    (∀ a, memOf cf a = memOf (retagCfg f c) a) →
    progOf cf = progOf c ∧ (∀ a, memOf cf a = memOf c a) := by
  intro hp hm
  refine ⟨by rw [hp, progOfRetag], fun a => by rw [hm, memOfRetag]⟩

/-! ## 4. Trace transport

Traces carry no classes: `Aev` is a label plus a fulfilled timestamp (and the fabric field), and
`Wpagent` has no class field.  So a retag moves only the `ptLog` component of a bundle. -/

def retagTraces (f : Nat → WmClass) (TS : Ptraces P D) : Ptraces P D :=
  ⟨TS.ptImg, retagLog f TS.ptLog, TS.ptTrs⟩

theorem retagTracesImg (f : Nat → WmClass) (TS : Ptraces P D) :
    (retagTraces f TS).ptImg = TS.ptImg := rfl

theorem retagTracesLog (f : Nat → WmClass) (TS : Ptraces P D) :
    (retagTraces f TS).ptLog = retagLog f TS.ptLog := rfl

theorem retagTracesTrs (f : Nat → WmClass) (TS : Ptraces P D) :
    (retagTraces f TS).ptTrs = TS.ptTrs := rfl

/-- `astepOk`'s ONLY log-reading conjuncts are `readOk`, `exclOk`, `exclOkTs`, `adShapedb`,
`ifetchOk` and the fulfilled-entry match — whose class is an existential binder. -/
theorem astepOkRetag (f : Nat → WmClass) (img : Image) (log : List Wmsg) (i : Nat)
    (ag : Wpagent P) (l : Wlabel) (g : Wstate → Wstate) (Dl : Option Nat) :
    astepOk img log i ag l g Dl ↔ astepOk img (retagLog f log) i ag l g Dl := by
  cases l with
  | LStore rl base data asrc vsrc =>
    simp only [astepOk]
    constructor
    · rintro ⟨ts, k, h1, h2, h3, h4, h5⟩
      exact ⟨ts, f (ts - 1), h1, retagLogLookupLit f log _ _ _ _ _ h2, h3, h4, h5⟩
    · rintro ⟨ts, k, h1, h2, h3, h4, h5⟩
      obtain ⟨k', h2'⟩ := retagLogLookupLitInv f log _ _ _ _ _ h2
      exact ⟨ts, k', h1, h2', h3, h4, h5⟩
  | LRmw aq rl base tvs data asrc vsrc =>
    simp only [astepOk]
    constructor
    · rintro ⟨ts, k, h0, h1, h2, hr, he, h3, h4, h5⟩
      exact ⟨ts, f (ts - 1), h0, h1, retagLogLookupLit f log _ _ _ _ _ h2,
        (retagReadOk f img log _ _ _ _ _).2 hr, (retagExclOk f log _ _ _ _).2 he, h3, h4, h5⟩
    · rintro ⟨ts, k, h0, h1, h2, hr, he, h3, h4, h5⟩
      obtain ⟨k', h2'⟩ := retagLogLookupLitInv f log _ _ _ _ _ h2
      exact ⟨ts, k', h0, h1, h2', (retagReadOk f img log _ _ _ _ _).1 hr,
        (retagExclOk f log _ _ _ _).1 he, h3, h4, h5⟩
  | LExStore rl base data asrc vsrc =>
    simp only [astepOk]
    constructor
    · rintro ⟨ts, k, R, h1, h2, hres, hb, hl, he, hok, h4, h5⟩
      refine ⟨ts, f (ts - 1), R, h1, retagLogLookupLit f log _ _ _ _ _ h2, hres, hb, hl,
        (retagExclOkTs f log _ _ _ _).2 he, ?_, h4, h5⟩
      rw [retagAdShapedb]; exact hok
    · rintro ⟨ts, k, R, h1, h2, hres, hb, hl, he, hok, h4, h5⟩
      obtain ⟨k', h2'⟩ := retagLogLookupLitInv f log _ _ _ _ _ h2
      rw [retagAdShapedb] at hok
      exact ⟨ts, k', R, h1, h2', hres, hb, hl, (retagExclOkTs f log _ _ _ _).1 he, hok, h4, h5⟩
  | _ => simp only [astepOk, retagReadOkD, retagReadOk, retagIfetchOk]

theorem astepsWfRetag (f : Nat → WmClass) (img : Image) (log : List Wmsg) (i : Nat)
    (ags : List (Wpagent P)) (evs : List (Aev D)) :
    astepsWf pstep img log i ags evs ↔ astepsWf pstep img (retagLog f log) i ags evs := by
  constructor
  · rintro ⟨hlen, hst⟩
    refine ⟨hlen, fun k ev ag ag' hev hk hk' => ?_⟩
    obtain ⟨st', g, hps, hok, heq⟩ := hst k ev ag ag' hev hk hk'
    exact ⟨st', g, hps, (astepOkRetag f img log i ag _ g _).1 hok, heq⟩
  · rintro ⟨hlen, hst⟩
    refine ⟨hlen, fun k ev ag ag' hev hk hk' => ?_⟩
    obtain ⟨st', g, hps, hok, heq⟩ := hst k ev ag ag' hev hk hk'
    exact ⟨st', g, hps, (astepOkRetag f img log i ag _ g _).2 hok, heq⟩

theorem atraceWfRetag (f : Nat → WmClass) (img : Image) (log : List Wmsg) (i : Nat)
    (T : Atrace P D) :
    atraceWf pstep img log i T ↔ atraceWf pstep img (retagLog f log) i T :=
  astepsWfRetag pstep f img log i T.atAgs T.atEvs

theorem ptracesOfRetag (f : Nat → WmClass) (TS : Ptraces P D) (mid c : Wpcfg P D) :
    ptracesOf pstep TS mid c →
    ptracesOf pstep (retagTraces f TS) (retagCfg f mid) (retagCfg f c) := by
  rintro ⟨himg, hlog, hlen, hwf, hfst, hlst, hlc, hic, hlenc⟩
  refine ⟨himg, ?_, hlen, ?_, hfst, hlst, ?_, hic, hlenc⟩
  · show retagLog f TS.ptLog = retagLog f mid.pcLog
    rw [hlog]
  · intro i T hT
    exact (atraceWfRetag pstep f _ _ i T).1 (hwf i T hT)
  · show retagLog f c.pcLog = retagLog f mid.pcLog
    rw [hlc]

/-- ... AND THE SAME WITH THE DEVICE WITNESS (M5/B4).  `DS` is untouched: every clause of
`ptracesDevOf` beyond `ptracesOf` reads only `ptTrs` and `pcDev`, which the retag does not move. -/
theorem ptracesDevOfRetag (f : Nat → WmClass) (TS : Ptraces P D) (DS : Pdevs D)
    (mid c : Wpcfg P D) :
    ptracesDevOf pstep pdev TS DS mid c →
    ptracesDevOf pstep pdev (retagTraces f TS) DS (retagCfg f mid) (retagCfg f c) := by
  rintro ⟨hof, hd, hw1, hw2, hw3, hw4, hw5, hw6⟩
  exact ⟨ptracesOfRetag pstep f TS mid c hof, hd, hw1, hw2, hw3, hw4, hw5, hw6⟩

/-! ## 5. THE CANONICAL RETAG

`clsCanonical` lives in `WeakRobustTrace` (G6a).  What stays here is what this file PROVES —
that every bundle can be brought into that form. -/

/-- THE SCAN.  The fulfil event of a log position is found by `listFind` over the finite trace,
not by choice: no axiom enters. -/
def fulfilAt (T : Atrace P D) (p : Nat) : Option (Nat × Aev D) :=
  listFind (fun ev => decide (ev.aeTs = some (p + 1))) T.atEvs

def canonF (clsf : P → Wlabel → Wstate → WmClass) (TS : Ptraces P D) (p : Nat) : WmClass :=
  match TS.ptLog[p]? with
  | none => .WCplain
  | some m =>
    match m.wmTid with
    | none => .WCplain
    | some i =>
      match TS.ptTrs[i]? with
      | none => .WCplain
      | some T =>
        match fulfilAt T p with
        | none => .WCplain
        | some (k, ev) =>
          match T.atAgs[k]? with
          | none => .WCplain
          | some ag => clsf ag.paSt ev.aeLb ag.paWs

/-- The scan's correctness: given the fulfil event and its uniqueness, `canonF` computes exactly
that event's class. -/
theorem canonFSpec (clsf : P → Wlabel → Wstate → WmClass) (TS : Ptraces P D) (p : Nat) (m : Wmsg)
    (i : Nat) (T : Atrace P D) (k : Nat) (ev : Aev D) (ag : Wpagent P) :
    TS.ptLog[p]? = some m → m.wmTid = some i →
    TS.ptTrs[i]? = some T →
    T.atEvs[k]? = some ev → ev.aeTs = some (p + 1) →
    T.atAgs[k]? = some ag →
    (∀ (k1 k2 : Nat) (ev1 ev2 : Aev D),
       T.atEvs[k1]? = some ev1 → ev1.aeTs = some (p + 1) →
       T.atEvs[k2]? = some ev2 → ev2.aeTs = some (p + 1) → k1 = k2) →
    canonF clsf TS p = clsf ag.paSt ev.aeLb ag.paWs := by
  intro hm hi hT hev hts hag huniq
  unfold canonF
  simp only [hm, hi, hT]
  cases E : fulfilAt T p with
  | none =>
    exfalso
    have hall := list_find_None.1 E ev (elem_of_list_lookup_2 hev)
    simp [hts] at hall
  | some q =>
    obtain ⟨k', ev'⟩ := q
    obtain ⟨hev', hts', _⟩ := list_find_Some.1 E
    have hts'' : ev'.aeTs = some (p + 1) := of_decide_eq_true hts'
    have hkk : k' = k := huniq k' k ev' ev hev' hts'' hev hts
    subst hkk
    rw [hev] at hev'
    cases hev'
    simp only [hag]

/-- The one degenerate corner the scan cannot see: a fulfil of timestamp `0` would key on log
position `0 - 1 = 0`.  Promised timestamps are positive (`promWf`), so this never happens; it is
a hypothesis of the canonicity lemma, discharged in `behaviorCanonical`. -/
def tsPos (TS : Ptraces P D) : Prop :=
  ∀ (i : Nat) (T : Atrace P D) (k : Nat) (ev : Aev D) (ts : Nat),
    TS.ptTrs[i]? = some T → T.atEvs[k]? = some ev →
    ev.aeTs = some ts → 0 < ts

theorem clsCanonicalCanon (clsf : P → Wlabel → Wstate → WmClass) (TS : Ptraces P D) :
    (∀ (i : Nat) (T : Atrace P D), TS.ptTrs[i]? = some T →
       atraceWf pstep TS.ptImg TS.ptLog i T) →
    tsPos TS →
    clsCanonical clsf (retagTraces (canonF clsf TS) TS) := by
  intro hwf hpos i T k ev ag ts m hT hev hag hts hm
  obtain ⟨m0, hm0, rfl⟩ := retagLogLookupInv (canonF clsf TS) TS.ptLog _ _ hm
  have hts0 : 0 < ts := hpos i T k ev ts hT hev hts
  have hsp : ts - 1 + 1 = ts := Nat.sub_add_cancel hts0
  have hwfi := hwf i T hT
  -- the trace's own step at `k` names `i` as the message's author
  obtain ⟨ag1, ag1', st1, g1, _, _, _, hok, _⟩ := astepsWfStep pstep _ _ _ _ _ k ev hwfi hev
  have htid : m0.wmTid = some i := by
    rw [hts] at hok
    generalize ev.aeLb = l at hok
    cases l with
    | LStore rl base data asrc vsrc =>
      obtain ⟨ts', k', _, hlk, _, _, hD⟩ := hok
      cases hD
      rw [hm0] at hlk
      cases hlk
      rfl
    | LRmw aq rl base tvs data asrc vsrc =>
      obtain ⟨ts', k', _, _, hlk, _, _, _, _, hD⟩ := hok
      cases hD
      rw [hm0] at hlk
      cases hlk
      rfl
    | LExStore rl base data asrc vsrc =>
      obtain ⟨ts', k', R, _, hlk, _, _, _, _, _, _, hD⟩ := hok
      cases hD
      rw [hm0] at hlk
      cases hlk
      rfl
    | _ => simp [astepOk] at hok
  show canonF clsf TS (ts - 1) = clsf ag.paSt ev.aeLb ag.paWs
  refine canonFSpec clsf TS (ts - 1) m0 i T k ev ag hm0 htid hT hev (by rw [hsp]; exact hts)
    hag ?_
  intro k1 k2 ev1 ev2 he1 ht1 he2 ht2
  rw [hsp] at ht1 ht2
  exact astepsFulfilUnique pstep TS.ptImg TS.ptLog i T.atAgs T.atEvs ts k1 k2 ev1 ev2 hwfi
    he1 ht1 he2 ht2

/-! ### `tsPos` out of the promise phase

A trace event's fulfilled timestamp is in the fulfilling agent's promise set at that point
(`astepOkDel`); promise sets only shrink along a trace (`astepsPromLe`), so it is in the trace's
FIRST record's set, which is `mid`'s — and `cfgWf mid`'s `promWf` says every promised timestamp
is positive. -/

include pstep in
theorem cfgWfPromiseRun (c c' : Wpcfg P D) :
    cfgWf c → rtc (wpPromiseStep (P := P) (D := D)) c c' → cfgWf c' := by
  intro h0 hr
  induction hr with
  | refl => exact h0
  | tail _ hs ih => exact cfgWfPromiseStep pstep _ _ ih hs

theorem tsPosOfPtraces (TS : Ptraces P D) (mid c : Wpcfg P D) :
    cfgWf mid → ptracesOf pstep TS mid c → tsPos TS := by
  rintro hcfg ⟨himg, hlog, hlen, hwf, hfst, -⟩
  intro i T k ev ts hT hev hts
  have hw := hwf i T hT
  rw [himg, hlog] at hw
  -- the record at `k` holds `ts`
  obtain ⟨ag, ag', st', g, hag, _, _, hok, _⟩ := astepsWfStep pstep _ _ _ _ _ k ev hw hev
  have hin : ts ∈ ag.paProm := astepOkDel _ _ _ _ _ _ _ ts hok hts
  -- ... hence so does the FIRST record, which is `mid`'s agent `i`
  have hilt : i < mid.pcAgs.length := by
    rw [← hlen]; exact lookup_lt_Some hT
  obtain ⟨ag0, hag0⟩ := Option.isSome_iff_exists.1 (lookup_lt_is_Some_2 (l := mid.pcAgs) hilt)
  have hfst0 : T.atAgs[0]? = some ag0 := by rw [hfst i T hT]; exact hag0
  have hsub : ag.paProm ⊆ ag0.paProm :=
    astepsPromLe pstep _ _ _ _ _ 0 k ag0 ag hw (Nat.zero_le _) hfst0 hag
  have hin0 : ts ∈ ag0.paProm := hsub ts hin
  exact ((hcfg i ag0 hag0).2 ts hin0).1

/-! ### THE DELIVERABLE: every behavior retags to a CANONICAL one -/

theorem behaviorCanonical (clsf : P → Wlabel → Wstate → WmClass) (img : Image) (d0 : D)
    (ps : List P) (c : Wpcfg P D) :
    pdevOk pstep pdev →
    latFreeProg pstep →
    wpBehavior pstep img d0 ps c →
    ∃ (f : Nat → WmClass) (mid : Wpcfg P D) (TS : Ptraces P D),
      wpBehavior pstep img d0 ps (retagCfg f c) ∧
      rtc (wpPromiseStep (P := P) (D := D)) (wpInit img d0 ps) (retagCfg f mid) ∧
      ptracesOf pstep (retagTraces f TS) (retagCfg f mid) (retagCfg f c) ∧
      clsCanonical clsf (retagTraces f TS) ∧
      progOf (retagCfg f c) = progOf c ∧
      (∀ a, memOf (retagCfg f c) a = memOf c a) := by
  intro hpok hlfp hb
  obtain ⟨mid, TS, hprom, hTS, _⟩ := wpBehaviorTraced pstep pdev img d0 ps c hpok hlfp hb
  have hcfg : cfgWf mid := cfgWfPromiseRun pstep _ _ (cfgWfInit img d0 ps) hprom
  have hpos : tsPos TS := tsPosOfPtraces pstep TS mid c hcfg hTS
  have hpr := wpPromiseStepsRetag (canonF clsf TS) _ _ hprom
  rw [retagWpInit] at hpr
  exact ⟨canonF clsf TS, mid, TS, wpBehaviorRetag pstep _ _ _ _ _ hb, hpr,
    ptracesOfRetag pstep _ _ _ _ hTS, clsCanonicalCanon pstep clsf TS hTS.2.2.2.1 hpos,
    progOfRetag _ _, memOfRetag _ _⟩

end machine

end Weak
