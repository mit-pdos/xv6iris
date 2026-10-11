/-
Weak: **COVERAGE FROM RELEASE/ACQUIRE SITE FACTS** (premise discharge, Track A,
items A1–A6).

Rocq: `iris/WeakRobustDisc.v` @ xxvzwolszwmp.

The Rocq header, in substance.  `claude-notes/design/weak-memory-premise-discharge.md`
splits the discharge of `WeakRobustMain.mainPremises` into three tracks; this
file is TRACK A: the machine-side view arithmetic, over an arbitrary traced
bundle (no xv6, no Iris, no Sail), that turns SITE FACTS about a
release/acquire pair into the per-edge obligations `WeakRobustAcyc.edgeOk` and
`WeakRobustAcyc2.eeOk`.  A site fact is a projection of the RECORDED TRACE (one
event's label, `gevTs`, `gevReads`, or a pre-state `covered`).

- A1 `coveredOfReleaseAcquire`: writer `i` fulfils `ts` at `k1`, a `fence rw,w`
  (`lbFencePwsw`) at `kf > k1`, the RELEASE store `ts_s` at `ks > kf`; reader
  `j ≠ i` reads `ts_s` at `kr` DISCIPLINED (the ACQUIRE) ⟹ `covered Tj k2 ts`.
  Consequences `edgeOkOfReleaseAcquire` / `edgeOkFOfReleaseAcquire`.  A0 shapes:
  `fcovOfAqRmw` (the acquiring RMW covers what its read half acquired) and
  `fcovOfAcquireBefore` (an acquire po-before the fulfil covers it).
- A2 `coveredOfReleaseChain`: the same through any number of hops; the hop
  lemma `acquireReleaseLt` needs NO fence (an acquire lands in `wVwNew`, EXT
  reads `wVwNew`); `chainOk` / `chainEnd` fold the hops, `chainLt` iterates;
  `coveredOfReleaseTwoHops` is the hop-record-free two-hop spelling.
- A3 `eeOkFenceCover` / `eeOkWawCover` / `eeOkZeroFloor`, assembled by
  `eeOkOfArms` into `eeOk TS`.
- A4 `exclByteOfRmw` / `swByteOfLogSingleWriter` / `handoffOfSyncChains` /
  `handoffOfDirectSync` / `ptracesBytesOkOfArms`: `WeakRobustSer`'s per-byte
  premises.  The chain's contribution to `handoff` is EXACTLY its order
  conjunct `tr ≤ tStar`; the structural conjuncts are site facts.
- A5 `devDom` / `devEpochOkOfDom` / `devDomOfDevEpochOk` /
  `devEpochOkDevfreeReader` / `devEpochOkOfDevfreeSources` (+ the A0′ transports
  `devWitOkOfDom` / `devWitOkOfDevfreeSources`): the EXACT characterization of
  the SUPERSEDED premise `WeakRobustOrd.devEpochOk` as a DOMINATION condition,
  and the machine-checked reason it is not dischargeable (a reader with no
  fabric history forces the writer to have none: the ordinary promise-free
  bundle `A: <fabric>; st x=1 / B: ld x (reads 1)` refutes it).
- A6 `tcMin` (constructive finite-ancestry minimality for a DECIDABLE predicate,
  measured by `WeakRobustMain.anc`'s computed ancestor list) / `badWfOfAcyclic`
  / `badWfOfNoBad`.  CIRCULARITY: `badWfOfAcyclic` consumes `gdep3Acyclic`, the
  conclusion `badWf` is a premise of; it is useful only for a bundle known
  acyclic on independent grounds, or one with no bad edges.

HYPOTHESES BEYOND THE BUNDLE: exactly S1's, `ptracesWf` and `ptracesFwdOwn`
(`fwdOwn` is needed only by the FENCE flavour of an acquire).  The one
non-site-fact hypothesis, `(msgByte m a).isSome` in `releaseLt`, is read off
the frozen log (a zero-width store would raise nothing).  DEPENDENCY-FREE.

**Deviations from Rocq.**

1. NAMES: lowerCamelCase as `Weak/WeakMem.lean` deviation 1; no name of this
   file is in `notes/weak-port-dupnames.json`.  The record `hop` is the
   structure `Hop` (constructor `Hop.mk`, fields `hpAg … hpA`); `ts_s` /
   `t_star` binders are `tsS` / `tStar`.  Used duplicated names:
   `WeakRobustGraph.grf`, `WeakRobustAcyc.lbAq`,
   `WeakRobustAcyc.loadPostRunVwNewAq`.
2. VOCABULARY: as `Weak/WeakRobustAcyc.lean` deviation 2 (`l !! i` ↦ `l[i]?`,
   `is_Some o` ↦ `o.isSome`, `S k` ↦ `k + 1`, `agent` ↦ `Nat`, `NoDup` ↦
   `List.Nodup`, `tvs.*1` ↦ `tvs.map Prod.fst`); `Exists P l` ↦ `∃ z ∈ l, P z`;
   `Decision`/`RelDecision` ↦ `DecidablePred`/`DecidableRel`; Rocq's
   `elem_of_tvs_reads` is `memTvsReads`, `NoDup_gev_enum` is `nodupGevEnum`.
   The Rocq option argument `D` of the two `astepOk` lemmas is `Dl`.
3. SECTION VARIABLES: the `disc` section's `pstep TS` are `variable`s (included
   where mentioned); its HYPOTHESES `Hwf Hfo` are explicit arguments (`hwf`,
   `hfo`, in that order, before the lemma's own) of exactly the declarations
   whose Rocq proof uses them.  Likewise `wfmin`'s `Hcar Hnd Hacyc` (`ancSub`
   takes `hcar hnd`; `ancMuLt` and `tcMin` all three) and `badwf`'s `TS DS`.
   `bad_wf_of_acyclic`'s `∀ e, Decision (bad_target nh e)` is an explicit
   `∀ e, Decidable (badTarget TS DS nh e)` argument, installed as an instance.
4. O2 / owner decision D4 (the Lean-only label `LIFetch`): `lbFencePwsw
   (LIFetch ..) = False`; `astepOkFulfilVwOld` / `astepOkFenceVwNewW` gain the
   (vacuous) `LIFetch` arm.  For every Rocq label the definitions agree.
   THE FETCH-SOURCE PREMISE `fetchSrcOk` (`WeakRobustSim` deviation 4,
   `WeakRobustMain` deviation 5): NO declaration here goes through the replay
   (`QinvStep` / `simFull`) — A6 uses only `gdep3Wf` / `gevEnum` / `tcMin` — so
   none gains it, and no `NoFetch` variant is needed.
5. `devDom` / `depGoWitness` / `depochWitness` / `depochLeOfDom` /
   `domOfDepochLe` do not take `TS` (Rocq's section variable is unused there,
   so Rocq does not abstract it either).  `depGo` in Lean is the `max`-form
   (`WeakRobustOrd`); `depGoWitness`'s statement is Rocq's.
6. Not imported: `Weak.WeakAxiomatic` (Rocq imports it first only for label
   constructor shadowing).

**Rocq → Lean name map.**  `lb_fence_pwsw` ↦ `lbFencePwsw`; `msg_byte_len` ↦
`msgByteLen`; `astep_ok_fulfil_vwOld` ↦ `astepOkFulfilVwOld`;
`astep_ok_fence_vwNew_w` ↦ `astepOkFenceVwNewW`; `covered_mono_ts` ↦
`coveredMonoTs`; `hop` ↦ `Hop`; `Hop` ↦ `Hop.mk`; `hp_ag`/`hp_kr`/`hp_kd`/
`hp_ks`/`hp_ts`/`hp_a` ↦ `Hop.hpAg`/`hpKr`/`hpKd`/`hpKs`/`hpTs`/`hpA`;
`trace_wf` ↦ `traceWf`; `ag_at` ↦ `agAt`; `ws_mono` ↦ `wsMono`;
`covered_pos_mono` ↦ `coveredPosMono`; `gev_ts_at` ↦ `gevTsAt`;
`gev_reads_at` ↦ `gevReadsAt`; `step_at` ↦ `stepAt`; `foreign_ts` ↦
`foreignTs`; `foreign_ts_unforwarded` ↦ `foreignTsUnforwarded`;
`foreign_ts_of_fulfil` ↦ `foreignTsOfFulfil`; `disciplined_covered` ↦
`disciplinedCovered`; `acquire_covered` ↦ `acquireCovered`; `fcov_of_aq_rmw` ↦
`fcovOfAqRmw`; `fcov_of_acquire_before` ↦ `fcovOfAcquireBefore`; `release_lt`
↦ `releaseLt`; `covered_fulfil_lt` ↦ `coveredFulfilLt`; `acquire_release_lt` ↦
`acquireReleaseLt`; `hop_ok` ↦ `hopOk`; `chain_ok` ↦ `chainOk`; `chain_end` ↦
`chainEnd`; `hop_lt` ↦ `hopLt`; `chain_lt` ↦ `chainLt`;
`covered_of_release_acquire` ↦ `coveredOfReleaseAcquire`;
`edge_ok_of_release_acquire` ↦ `edgeOkOfReleaseAcquire`;
`edge_ok_f_of_release_acquire` ↦ `edgeOkFOfReleaseAcquire`;
`covered_of_release_two_hops` ↦ `coveredOfReleaseTwoHops`;
`covered_of_release_chain` ↦ `coveredOfReleaseChain`; `ee_ok_fence_cover` ↦
`eeOkFenceCover`; `ee_ok_waw_cover` ↦ `eeOkWawCover`; `ee_ok_zero_floor` ↦
`eeOkZeroFloor`; `ee_arm` ↦ `eeArm`; `ee_ok_of_arms` ↦ `eeOkOfArms`;
`rmw_written` ↦ `rmwWritten`; `excl_byte_of_rmw` ↦ `exclByteOfRmw`;
`log_single_writer` ↦ `logSingleWriter`; `sw_byte_of_log_single_writer` ↦
`swByteOfLogSingleWriter`; `handoff_of_sync_chains` ↦ `handoffOfSyncChains`;
`handoff_of_direct_sync` ↦ `handoffOfDirectSync`; `ptraces_bytes_ok_of_arms` ↦
`ptracesBytesOkOfArms`; `dep_go_witness` ↦ `depGoWitness`; `depoch_witness` ↦
`depochWitness`; `dev_dom` ↦ `devDom`; `depoch_le_of_dom` ↦ `depochLeOfDom`;
`dom_of_depoch_le` ↦ `domOfDepochLe`; `dev_epoch_ok_of_dom` ↦
`devEpochOkOfDom`; `dev_dom_of_dev_epoch_ok` ↦ `devDomOfDevEpochOk`;
`dev_epoch_ok_devfree_reader` ↦ `devEpochOkDevfreeReader`;
`dev_epoch_ok_of_devfree_sources` ↦ `devEpochOkOfDevfreeSources`;
`dev_wit_ok_of_dom` ↦ `devWitOkOfDom`; `dev_wit_ok_of_devfree_sources` ↦
`devWitOkOfDevfreeSources`; `anc_sub` ↦ `ancSub`; `anc_mu_lt` ↦ `ancMuLt`;
`tc_min` ↦ `tcMin`; `bad_target` ↦ `badTarget`; `bad_wf_of_no_bad` ↦
`badWfOfNoBad`; `bad_wf_of_acyclic` ↦ `badWfOfAcyclic`.

**Dropped:** nothing.

**Statements checked** (by hand, against Rocq): all of them.
-/
import Weak.WeakRobustMain

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std Wlabel

/-! ## THE RELEASE FENCE

The mirror of `lbFencePrsw`: `fence rw,w` — past WRITES pred (`pw`), future
writes succ (`sw`), exactly the pair `fencePostVwNewW` routes `wVwOld` into
`wVwNew` on. -/

def lbFencePwsw (l : Wlabel) : Prop :=
  match l with
  | LFence _ pw _ sw => pw = true ∧ sw = true
  | LSilent | LLoad .. | LStore .. | LRmw .. | LDev .. | LRegW .. | LCtrl _ | LInstr
  | LExLoad .. | LExStore .. | LIFetch .. => False

/-! ## THE TWO NEW `astepOk` FACTS -/

/-- A message that writes byte `a` has nonempty data. -/
theorem msgByteLen (m : Wmsg) (a : Int) : (msgByte m a).isSome → 0 < m.wmData.length := by
  unfold msgByte
  split
  · intro h
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 h
    have := lookup_lt_Some hb
    omega
  · intro h; simp at h

section astep

variable {P : Type}

/-- A FULFIL raises `wVwOld` to the timestamp it fulfils. -/
theorem astepOkFulfilVwOld (img : Image) (log : List Wmsg) (i : Nat) (ag : Wpagent P)
    (l : Wlabel) (f : Wstate → Wstate) (ts : Nat) (a : Int) (m : Wmsg) :
    astepOk img log i ag l f (some ts) →
    log[ts - 1]? = some m → (msgByte m a).isSome →
    ts ≤ (f ag.paWs).wVwOld := by
  intro h hm hb
  cases l with
  | LSilent => obtain ⟨_, ⟨⟩⟩ := h
  | LLoad => obtain ⟨_, _, ⟨⟩⟩ := h
  | LStore rl base data asrc vsrc =>
    obtain ⟨ts', k, _, hlog, _, rfl, hD⟩ := h
    cases hD
    rw [hlog] at hm; cases hm
    exact storePostRunDVwOld _ _ _ _ _ _ _ (msgByteLen _ a hb)
  | LRmw aq rl base tvs data asrc vsrc =>
    obtain ⟨ts', k, _, _, hlog, _, _, _, rfl, hD⟩ := h
    cases hD
    rw [hlog] at hm; cases hm
    exact storePostRunDVwOld _ _ _ _ _ _ _ (msgByteLen _ a hb)
  | LFence => obtain ⟨_, ⟨⟩⟩ := h
  | LDev => obtain ⟨_, ⟨⟩⟩ := h
  | LRegW => obtain ⟨_, ⟨⟩⟩ := h
  | LCtrl => obtain ⟨_, ⟨⟩⟩ := h
  | LInstr => obtain ⟨_, ⟨⟩⟩ := h
  -- THE RMW SPLIT (S2): the conditional write is `LStore`'s arm
  | LExLoad => obtain ⟨_, _, ⟨⟩⟩ := h
  | LExStore rl base data asrc vsrc =>
    obtain ⟨ts', k, R, _, hlog, _, _, _, _, _, rfl, hD⟩ := h
    cases hD
    rw [hlog] at hm; cases hm
    exact storePostRunDVwOld _ _ _ _ _ _ _ (msgByteLen _ a hb)
  | LIFetch => obtain ⟨_, _, ⟨⟩⟩ := h

/-- The `pw ∧ sw` mirror of `astepOkFenceVwNew`: a `fence rw,w` ships `wVwOld`
into `wVwNew`. -/
theorem astepOkFenceVwNewW (img : Image) (log : List Wmsg) (i : Nat) (ag : Wpagent P)
    (l : Wlabel) (f : Wstate → Wstate) (Dl : Option Nat) :
    astepOk img log i ag l f Dl → lbFencePwsw l → ag.paWs.wVwOld ≤ (f ag.paWs).wVwNew := by
  intro h hf
  cases l with
  | LFence pr pw sr sw =>
    obtain ⟨rfl, _⟩ := h
    obtain ⟨rfl, rfl⟩ := hf
    exact fencePostVwNewW _ _ _
  | _ => cases hf

end astep

/-! ## `covered` weakens in the timestamp -/

theorem coveredMonoTs {P D : Type} (T : Atrace P D) (k ts ts' : Nat) :
    covered T k ts → ts' ≤ ts → covered T k ts' := by
  rintro ⟨ag, hag, hge⟩ hle
  exact ⟨ag, hag, by omega⟩

/-! ## A HOP of a synchronization chain (A2) -/

/-- One intermediate agent of the chain: it ACQUIRES at `hpKr` (discipline
window closing at `hpKd`) and RELEASES at `hpKs`, fulfilling `hpTs`. -/
structure Hop where
  /-- the agent performing this hop -/
  hpAg : Nat
  /-- its acquiring read's trace position -/
  hpKr : Nat
  /-- the position by which the acquire is complete -/
  hpKd : Nat
  /-- its releasing fulfil's trace position -/
  hpKs : Nat
  /-- the timestamp that fulfil consumes -/
  hpTs : Nat
  /-- the byte its acquiring read reads -/
  hpA : Int

/-! ## The `disc` section -/

section disc

variable {P D : Type}
variable (pstep : P → D → Wlabel → P → D → Prop)
variable (TS : Ptraces P D)

/-! ### Bookkeeping -/

theorem traceWf (hwf : ptracesWf pstep TS) (i : Nat) (T : Atrace P D) :
    TS.ptTrs[i]? = some T → atraceWf pstep TS.ptImg TS.ptLog i T :=
  fun hT => hwf i T hT

theorem agAt (hwf : ptracesWf pstep TS) (i : Nat) (T : Atrace P D) (k : Nat) (ev : Aev D) :
    TS.ptTrs[i]? = some T → T.atEvs[k]? = some ev →
    ∃ ag, T.atAgs[k]? = some ag := by
  intro hT hev
  have hlen := (traceWf pstep TS hwf i T hT).1
  have hlt := lookup_lt_Some hev
  exact Option.isSome_iff_exists.1 (lookup_lt_is_Some_2 (by omega))

theorem wsMono (hwf : ptracesWf pstep TS) (i : Nat) (T : Atrace P D) (k k' : Nat)
    (ag ag' : Wpagent P) :
    TS.ptTrs[i]? = some T → k ≤ k' →
    T.atAgs[k]? = some ag → T.atAgs[k']? = some ag' →
    wsLe ag.paWs ag'.paWs := by
  intro hT hle hk hk'
  exact astepsWsLe pstep TS.ptImg TS.ptLog i T.atAgs T.atEvs k k' ag ag'
    (traceWf pstep TS hwf i T hT) hle hk hk'

/-- `covered` propagates FORWARD along the trace (views only grow). -/
theorem coveredPosMono (hwf : ptracesWf pstep TS) (i : Nat) (T : Atrace P D) (k k' ts : Nat)
    (ag' : Wpagent P) :
    TS.ptTrs[i]? = some T → covered T k ts → k ≤ k' →
    T.atAgs[k']? = some ag' → covered T k' ts := by
  rintro hT ⟨ag, hag, hge⟩ hle hag'
  refine ⟨ag', hag', ?_⟩
  have := wsLeVwNew _ _ (wsMono pstep TS hwf i T k k' ag ag' hT hle hag hag')
  omega

/-- The two bundle-level trace facts, unpacked at a NAMED trace. -/
theorem gevTsAt (i : Nat) (T : Atrace P D) (k ts : Nat) :
    TS.ptTrs[i]? = some T → gevTs TS (i, k) = some ts →
    ∃ ev, T.atEvs[k]? = some ev ∧ ev.aeTs = some ts := by
  intro hT hts
  obtain ⟨T', ev, hT', hev, hts'⟩ := gevTsSome TS (i, k) ts hts
  have hTT : T' = T := by
    have h : TS.ptTrs[i]? = some T' := hT'
    rw [hT] at h; exact (Option.some.inj h).symm
  subst hTT
  exact ⟨ev, hev, hts'⟩

theorem gevReadsAt (i : Nat) (T : Atrace P D) (k : Nat) (a : Int) (ts : Nat) :
    TS.ptTrs[i]? = some T → gevReads TS (i, k) a ts →
    ∃ ev, T.atEvs[k]? = some ev ∧ (a, ts) ∈ lbReads ev.aeLb := by
  rintro hT ⟨l, hl, hin⟩
  obtain ⟨T', ev, hT', hev, hlb⟩ := gevLbSome TS (i, k) l hl
  have hTT : T' = T := by
    have h : TS.ptTrs[i]? = some T' := hT'
    rw [hT] at h; exact (Option.some.inj h).symm
  subst hTT
  subst hlb
  exact ⟨ev, hev, hin⟩

/-- The step at a position, with both agent records. -/
theorem stepAt (hwf : ptracesWf pstep TS) (i : Nat) (T : Atrace P D) (k : Nat) (ev : Aev D) :
    TS.ptTrs[i]? = some T → T.atEvs[k]? = some ev →
    ∃ (ag ag' : Wpagent P) (f : Wstate → Wstate),
      T.atAgs[k]? = some ag ∧ T.atAgs[k + 1]? = some ag' ∧
      astepOk TS.ptImg TS.ptLog i ag ev.aeLb f ev.aeTs ∧
      ag'.paWs = f ag.paWs := by
  intro hT hev
  obtain ⟨ag, ag', st', f, hag, hag', _, hok, heq⟩ :=
    astepsWfStep pstep TS.ptImg TS.ptLog i T.atAgs T.atEvs k ev (traceWf pstep TS hwf i T hT) hev
  exact ⟨ag, ag', f, hag, hag', hok, by rw [heq]⟩

/-! ### THE NON-FORWARDING SIDE CONDITION, as a site fact -/

def foreignTs (i : Nat) (ts : Nat) : Prop :=
  ∃ m j, TS.ptLog[ts - 1]? = some m ∧ m.wmTid = some j ∧ j ≠ i

theorem foreignTsUnforwarded (i : Nat) (l : Wlabel) (ts : Nat) :
    foreignTs TS i ts → readUnforwarded TS.ptLog i l ts :=
  fun h => Or.inr h

theorem foreignTsOfFulfil (hwf : ptracesWf pstep TS) (i : Nat) (e : Gev) (ts : Nat) :
    gevTs TS e = some ts → e.1 ≠ i → foreignTs TS i ts := by
  intro hts hne
  obtain ⟨base, data, kc, hm⟩ := gevTsMsg pstep TS e ts hwf hts
  exact ⟨⟨base, data, some e.1, kc⟩, e.1, hm, rfl, hne⟩

/-! ### DELIVERABLE A1a: THE ACQUIRE SITE

A DISCIPLINED read of `ts` is COVERED at every position from the discipline
point on (`atraceS1`'s first two arms, stated as a `covered` fact). -/

theorem disciplinedCovered (hwf : ptracesWf pstep TS) (hfo : ptracesFwdOwn TS)
    (i : Nat) (T : Atrace P D) (kr k2 : Nat) (evr : Aev D) (a : Int) (ts : Nat)
    (ag2 : Wpagent P) :
    TS.ptTrs[i]? = some T →
    T.atEvs[kr]? = some evr →
    (a, ts) ∈ lbReads evr.aeLb →
    readUnforwarded TS.ptLog i evr.aeLb ts →
    disciplined T kr k2 →
    kr < k2 →
    T.atAgs[k2]? = some ag2 →
    covered T k2 ts := by
  intro hT hev hin hunf hdisc hlt hag2
  obtain ⟨ag, agn, f, hag, hagn, hok, hws⟩ := stepAt pstep TS hwf i T kr evr hT hev
  have hfv : fwdView ag.paWs (WeakRobustAcyc.lbAq evr.aeLb) a ts = ts :=
    fwdOwnReadUnforwarded TS.ptLog i ag.paWs evr.aeLb a ts (hfo i T kr ag hT hag) hunf
  -- IT SUFFICES to push `ts` into `wVwNew` at some position ≤ `k2`
  suffices hs : ∃ n agm, n ≤ k2 ∧ T.atAgs[n]? = some agm ∧ ts ≤ agm.paWs.wVwNew by
    obtain ⟨n, agm, hn, hagm, hge⟩ := hs
    exact coveredPosMono pstep TS hwf i T n k2 ts ag2 hT ⟨agm, hagm, hge⟩ hn hag2
  rcases hdisc with ⟨ev0, hev0, haq⟩ | ⟨k0, ev0, hk0, hk0', hev0, hfen⟩
  · -- THE AQ ARM: the read itself lands in `wVwNew`
    rw [hev] at hev0; cases hev0
    refine ⟨kr + 1, agn, by omega, hagn, ?_⟩
    rw [hws]
    exact astepOkReadVwNewAq TS.ptImg TS.ptLog i ag _ f _ a ts hok haq hin
  · -- THE FENCE ARM: the read lands in `wVrOld`; the fence ships it
    have hro : ts ≤ agn.paWs.wVrOld := by
      rw [hws]; exact astepOkReadVrOld TS.ptImg TS.ptLog i ag _ f _ a ts hok hfv hin
    obtain ⟨ag0, hag0⟩ := agAt pstep TS hwf i T k0 ev0 hT hev0
    have hro0 : ts ≤ ag0.paWs.wVrOld := Nat.le_trans hro
      (wsLeVrOld _ _ (wsMono pstep TS hwf i T (kr + 1) k0 agn ag0 hT (by omega) hagn hag0))
    obtain ⟨b0, b1, f0, hb0, hb1, hok0, hws0⟩ := stepAt pstep TS hwf i T k0 ev0 hT hev0
    rw [hag0] at hb0; cases hb0
    refine ⟨k0 + 1, b1, by omega, hb1, ?_⟩
    rw [hws0]
    exact Nat.le_trans hro0 (astepOkFenceVwNew TS.ptImg TS.ptLog i ag0 _ f0 _ hok0 hfen)

/-- The bundle-level spelling, with the non-forwarding side condition discharged
from "the timestamp was fulfilled by somebody else". -/
theorem acquireCovered (hwf : ptracesWf pstep TS) (hfo : ptracesFwdOwn TS)
    (i : Nat) (esrc : Gev) (T : Atrace P D) (kr k2 : Nat) (a : Int) (ts : Nat)
    (ag2 : Wpagent P) :
    esrc.1 ≠ i →
    TS.ptTrs[i]? = some T →
    gevReads TS (i, kr) a ts →
    gevTs TS esrc = some ts →
    disciplined T kr k2 →
    kr < k2 →
    T.atAgs[k2]? = some ag2 →
    covered T k2 ts := by
  intro hne hT hrd hts hdisc hlt hag2
  obtain ⟨evr, hev, hin⟩ := gevReadsAt TS i T kr a ts hT hrd
  exact disciplinedCovered pstep TS hwf hfo i T kr k2 evr a ts ag2 hT hev hin
    (foreignTsUnforwarded TS i _ ts (foreignTsOfFulfil pstep TS hwf i esrc ts hts hne))
    hdisc hlt hag2

/-! ### A0: THE TWO xv6 SHAPES THE RELATIVIZED PREMISE ASKS FOR -/

/-- (a) THE ACQUIRING RMW COVERS WHAT ITS OWN READ HALF ACQUIRED. -/
theorem fcovOfAqRmw (hwf : ptracesWf pstep TS) (i : Nat) (T : Atrace P D) (k' : Nat)
    (ev : Aev D) (rl : Bool) (base : Int) (tvs : List (Nat × BitVec 8))
    (data : List (BitVec 8)) (asrc vsrc : List Dsrc) (a : Int) (tsS ts : Nat) :
    TS.ptTrs[i]? = some T →
    T.atEvs[k']? = some ev →
    ev.aeLb = LRmw true rl base tvs data asrc vsrc →
    (a, tsS) ∈ lbReads ev.aeLb →
    ts ≤ tsS →
    fcov T k' ts := by
  intro hT hev hlb hin hle
  obtain ⟨ag, hag⟩ := agAt pstep TS hwf i T k' ev hT hev
  refine ⟨ag, ev,
    fulfilVpreD (loadPostRunD ag.paWs true (srcsView ag.paWs asrc) base (tvs.map Prod.fst)) rl
      (max (max (srcsView ag.paWs asrc) (srcsView ag.paWs vsrc))
        (ldvOf ag.paWs true (srcsView ag.paWs asrc) base (tvs.map Prod.fst))),
    hag, hev, by rw [hlb]; rfl, ?_⟩
  rw [hlb] at hin
  obtain ⟨j, v, hj, _⟩ := (memTvsReads _ _ _ _).1 hin
  have hts : (tvs.map Prod.fst)[j]? = some tsS := by rw [List.getElem?_map, hj]; rfl
  have hge := WeakRobustAcyc.loadPostRunVwNewAq ag.paWs base _ j tsS hts
  have hmn := wsLeVwNew _ _
    (loadPostRunDMono ag.paWs true (srcsView ag.paWs asrc) base (tvs.map Prod.fst))
  have hfv := fulfilVpreDVwNew
    (loadPostRunD ag.paWs true (srcsView ag.paWs asrc) base (tvs.map Prod.fst)) rl
    (max (max (srcsView ag.paWs asrc) (srcsView ag.paWs vsrc))
      (ldvOf ag.paWs true (srcsView ag.paWs asrc) base (tvs.map Prod.fst)))
  omega

/-- (b) AN ACQUIRE po-BEFORE THE FULFIL COVERS IT. -/
theorem fcovOfAcquireBefore (hwf : ptracesWf pstep TS) (hfo : ptracesFwdOwn TS)
    (i : Nat) (esrc : Gev) (T : Atrace P D) (ka kd k' : Nat) (ev' : Aev D) (a : Int)
    (tsS ts : Nat) :
    esrc.1 ≠ i →
    TS.ptTrs[i]? = some T →
    gevReads TS (i, ka) a tsS →
    gevTs TS esrc = some tsS →
    disciplined T ka kd →
    ka < kd → kd ≤ k' →
    T.atEvs[k']? = some ev' → ev'.aeTs.isSome →
    ts ≤ tsS →
    fcov T k' ts := by
  intro hne hT hrd hsrc hdisc h1 h2 hev' hsome hle
  have hwfT := traceWf pstep TS hwf i T hT
  obtain ⟨ag2, hag2⟩ : ∃ ag2, T.atAgs[kd]? = some ag2 := by
    have hlen := hwfT.1
    have hlt := lookup_lt_Some hev'
    exact Option.isSome_iff_exists.1 (lookup_lt_is_Some_2 (by omega))
  have hcov : covered T kd ts :=
    coveredMonoTs T kd tsS ts
      (acquireCovered pstep TS hwf hfo i esrc T ka kd a tsS ag2 hne hT hrd hsrc hdisc h1 hag2)
      hle
  exact coveredFcov pstep TS.ptImg TS.ptLog i T kd k' ts ev' hwfT hcov h2 hev' hsome

/-! ### DELIVERABLE A1b: THE RELEASE SITE

`ts` fulfilled at `k1`, a `pw ∧ sw` fence at `kf > k1`, `tsS` fulfilled at
`ks > kf` ⟹ `ts < tsS`.  The fence is LOAD-BEARING here and only here. -/

theorem releaseLt (hwf : ptracesWf pstep TS) (i : Nat) (T : Atrace P D) (k1 kf ks ts tsS : Nat)
    (a : Int) (m : Wmsg) :
    TS.ptTrs[i]? = some T →
    gevTs TS (i, k1) = some ts →
    TS.ptLog[ts - 1]? = some m → (msgByte m a).isSome →
    k1 < kf →
    (∃ ev, T.atEvs[kf]? = some ev ∧ lbFencePwsw ev.aeLb) →
    kf < ks →
    gevTs TS (i, ks) = some tsS →
    ts < tsS := by
  rintro hT hts1 hm hb hlt1 ⟨evf, hevf, hfen⟩ hlt2 htss
  obtain ⟨ev1, hev1, hts1'⟩ := gevTsAt TS i T k1 ts hT hts1
  obtain ⟨evs, hevs, htss'⟩ := gevTsAt TS i T ks tsS hT htss
  -- the fulfil at `k1` raises `wVwOld` to `ts`
  obtain ⟨ag1, agn1, f1, hag1, hagn1, hok1, hws1⟩ := stepAt pstep TS hwf i T k1 ev1 hT hev1
  rw [hts1'] at hok1
  have hwo : ts ≤ agn1.paWs.wVwOld := by
    rw [hws1]; exact astepOkFulfilVwOld TS.ptImg TS.ptLog i ag1 _ f1 ts a m hok1 hm hb
  -- … carried to the fence's pre-state …
  obtain ⟨agf, agnf, ff, hagf, hagnf, hokf, hwsf⟩ := stepAt pstep TS hwf i T kf evf hT hevf
  have hwof : ts ≤ agf.paWs.wVwOld := Nat.le_trans hwo
    (wsLeVwOld _ _ (wsMono pstep TS hwf i T (k1 + 1) kf agn1 agf hT (by omega) hagn1 hagf))
  -- … and shipped into `wVwNew` by the `pw ∧ sw` fence
  have hwn : ts ≤ agnf.paWs.wVwNew := by
    rw [hwsf]
    exact Nat.le_trans hwof (astepOkFenceVwNewW TS.ptImg TS.ptLog i agf _ ff _ hokf hfen)
  -- EXT at the release store
  obtain ⟨ags, agns, fs, hags, _, hoks, _⟩ := stepAt pstep TS hwf i T ks evs hT hevs
  rw [htss'] at hoks
  have hext := astepOkFulfilExt TS.ptImg TS.ptLog i ags _ fs tsS hoks
  have := wsLeVwNew _ _ (wsMono pstep TS hwf i T (kf + 1) ks agnf ags hT (by omega) hagnf hags)
  omega

/-! ### DELIVERABLE A2a: THE HOP LEMMA -/

/-- Whatever an agent has already got into `wVwNew` is strictly below every
timestamp it fulfils afterwards. -/
theorem coveredFulfilLt (hwf : ptracesWf pstep TS) (i : Nat) (T : Atrace P D) (k ks ts ts' : Nat) :
    TS.ptTrs[i]? = some T →
    covered T k ts →
    k ≤ ks →
    gevTs TS (i, ks) = some ts' →
    ts < ts' := by
  rintro hT ⟨ag, hag, hge⟩ hle hts'
  obtain ⟨evs, hevs, hts''⟩ := gevTsAt TS i T ks ts' hT hts'
  obtain ⟨ags, _, fs, hags, _, hoks, _⟩ := stepAt pstep TS hwf i T ks evs hT hevs
  rw [hts''] at hoks
  have hext := astepOkFulfilExt TS.ptImg TS.ptLog i ags _ fs ts' hoks
  have := wsLeVwNew _ _ (wsMono pstep TS hwf i T k ks ag ags hT hle hag hags)
  omega

/-- ONE HOP: an intermediate agent ACQUIRES `tin` and later fulfils `tout`.  NO
release fence is needed. -/
theorem acquireReleaseLt (hwf : ptracesWf pstep TS) (hfo : ptracesFwdOwn TS)
    (i : Nat) (esrc : Gev) (T : Atrace P D) (kr kd ks tin tout : Nat) (a : Int)
    (ag2 : Wpagent P) :
    esrc.1 ≠ i →
    TS.ptTrs[i]? = some T →
    gevReads TS (i, kr) a tin →
    gevTs TS esrc = some tin →
    disciplined T kr kd →
    kr < kd → kd ≤ ks →
    T.atAgs[kd]? = some ag2 →
    gevTs TS (i, ks) = some tout →
    tin < tout := by
  intro hne hT hrd hsrc hdisc h1 h2 hag2 hout
  exact coveredFulfilLt pstep TS hwf i T kd ks tin tout hT
    (acquireCovered pstep TS hwf hfo i esrc T kr kd a tin ag2 hne hT hrd hsrc hdisc h1 hag2)
    h2 hout

/-! ### DELIVERABLE A2b: CHAINS OF HOPS -/

def hopOk (esrc : Gev) (tin : Nat) (h : Hop) : Prop :=
  ∃ (T : Atrace P D) (ag : Wpagent P),
    TS.ptTrs[h.hpAg]? = some T ∧
    esrc.1 ≠ h.hpAg ∧
    gevTs TS esrc = some tin ∧
    gevReads TS (h.hpAg, h.hpKr) h.hpA tin ∧
    disciplined T h.hpKr h.hpKd ∧
    h.hpKr < h.hpKd ∧ h.hpKd ≤ h.hpKs ∧
    T.atAgs[h.hpKd]? = some ag ∧
    gevTs TS (h.hpAg, h.hpKs) = some h.hpTs

def chainOk : Gev → Nat → List Hop → Prop
  | esrc, tin, [] => gevTs TS esrc = some tin
  | esrc, tin, h :: hs' => hopOk TS esrc tin h ∧ chainOk (h.hpAg, h.hpKs) h.hpTs hs'

def chainEnd : Gev → Nat → List Hop → Gev × Nat
  | esrc, tin, [] => (esrc, tin)
  | _, _, h :: hs' => chainEnd (h.hpAg, h.hpKs) h.hpTs hs'

theorem hopLt (hwf : ptracesWf pstep TS) (hfo : ptracesFwdOwn TS)
    (esrc : Gev) (tin : Nat) (h : Hop) :
    hopOk TS esrc tin h → tin < h.hpTs := by
  rintro ⟨T, ag, hT, hne, hsrc, hrd, hd, h1, h2, hag, hout⟩
  exact acquireReleaseLt pstep TS hwf hfo h.hpAg esrc T h.hpKr h.hpKd h.hpKs tin h.hpTs h.hpA ag
    hne hT hrd hsrc hd h1 h2 hag hout

/-- THE ITERATION. -/
theorem chainLt (hwf : ptracesWf pstep TS) (hfo : ptracesFwdOwn TS)
    (esrc : Gev) (tin : Nat) (hs : List Hop) :
    chainOk TS esrc tin hs →
    tin ≤ (chainEnd esrc tin hs).2 ∧
    gevTs TS (chainEnd esrc tin hs).1 = some (chainEnd esrc tin hs).2 := by
  induction hs generalizing esrc tin with
  | nil => intro hc; exact ⟨Nat.le_refl _, hc⟩
  | cons h hs ih =>
    rintro ⟨hh, hrest⟩
    obtain ⟨hle, hts⟩ := ih (h.hpAg, h.hpKs) h.hpTs hrest
    refine ⟨?_, hts⟩
    have := hopLt pstep TS hwf hfo esrc tin h hh
    simp only [chainEnd]
    omega

/-! ### DELIVERABLE A1: COVERAGE FROM ONE RELEASE/ACQUIRE PAIR -/

theorem coveredOfReleaseAcquire (hwf : ptracesWf pstep TS) (hfo : ptracesFwdOwn TS)
    (i j : Nat) (Ti Tj : Atrace P D) (k1 kf ks kr k2 ts tsS : Nat) (a1 : Int) (m : Wmsg)
    (a : Int) (ag2 : Wpagent P) :
    i ≠ j →
    TS.ptTrs[i]? = some Ti →
    TS.ptTrs[j]? = some Tj →
    -- the RELEASE site of `i`
    gevTs TS (i, k1) = some ts →
    TS.ptLog[ts - 1]? = some m → (msgByte m a1).isSome →
    k1 < kf →
    (∃ ev, Ti.atEvs[kf]? = some ev ∧ lbFencePwsw ev.aeLb) →
    kf < ks →
    gevTs TS (i, ks) = some tsS →
    -- the ACQUIRE site of `j`
    gevReads TS (j, kr) a tsS →
    disciplined Tj kr k2 →
    kr < k2 →
    Tj.atAgs[k2]? = some ag2 →
    covered Tj k2 ts := by
  intro hne hTi hTj hts1 hm hb hlt1 hfen hlt2 htss hrd hdisc hlt hag2
  have hlts : ts < tsS :=
    releaseLt pstep TS hwf i Ti k1 kf ks ts tsS a1 m hTi hts1 hm hb hlt1 hfen hlt2 htss
  exact coveredMonoTs Tj k2 tsS ts
    (acquireCovered pstep TS hwf hfo j (i, ks) Tj kr k2 a tsS ag2 hne hTj hrd htss hdisc hlt hag2)
    (Nat.le_of_lt hlts)

/-- THE CONSEQUENCE IN `edgeOk` FORM: the acquire sits BEFORE the reading event
`kr`. -/
theorem edgeOkOfReleaseAcquire (hwf : ptracesWf pstep TS) (hfo : ptracesFwdOwn TS)
    (i j : Nat) (Ti Tj : Atrace P D) (k1 kf ks ka kr ts tsS : Nat) (a1 : Int) (m : Wmsg)
    (a : Int) (agr : Wpagent P) :
    i ≠ j →
    TS.ptTrs[i]? = some Ti →
    TS.ptTrs[j]? = some Tj →
    gevTs TS (i, k1) = some ts →
    TS.ptLog[ts - 1]? = some m → (msgByte m a1).isSome →
    k1 < kf →
    (∃ ev, Ti.atEvs[kf]? = some ev ∧ lbFencePwsw ev.aeLb) →
    kf < ks →
    gevTs TS (i, ks) = some tsS →
    -- `j`'s ACQUIRE of the release message, po-BEFORE `kr`
    gevReads TS (j, ka) a tsS →
    disciplined Tj ka kr →
    ka < kr →
    Tj.atAgs[kr]? = some agr →
    ∀ k', edgeOk Tj kr k' ts := by
  intro hne hTi hTj hts1 hm hb hlt1 hfen hlt2 htss hrd hdisc hlt hagr k'
  exact edgeOkCovered Tj kr k' ts
    (coveredOfReleaseAcquire pstep TS hwf hfo i j Ti Tj k1 kf ks ka kr ts tsS a1 m a agr
      hne hTi hTj hts1 hm hb hlt1 hfen hlt2 htss hrd hdisc hlt hagr)

/-- …and the `edgeOkF` restatement (A0). -/
theorem edgeOkFOfReleaseAcquire (hwf : ptracesWf pstep TS) (hfo : ptracesFwdOwn TS)
    (i j : Nat) (Ti Tj : Atrace P D) (k1 kf ks ka kr ts tsS : Nat) (a1 : Int) (m : Wmsg)
    (a : Int) (agr : Wpagent P) :
    i ≠ j →
    TS.ptTrs[i]? = some Ti →
    TS.ptTrs[j]? = some Tj →
    gevTs TS (i, k1) = some ts →
    TS.ptLog[ts - 1]? = some m → (msgByte m a1).isSome →
    k1 < kf →
    (∃ ev, Ti.atEvs[kf]? = some ev ∧ lbFencePwsw ev.aeLb) →
    kf < ks →
    gevTs TS (i, ks) = some tsS →
    -- `j`'s ACQUIRE of the release message, po-BEFORE `kr`
    gevReads TS (j, ka) a tsS →
    disciplined Tj ka kr →
    ka < kr →
    Tj.atAgs[kr]? = some agr →
    ∀ (k' : Nat) (ev' : Aev D), kr ≤ k' → Tj.atEvs[k']? = some ev' →
      ev'.aeTs.isSome → edgeOkF Tj kr k' ts := by
  intro hne hTi hTj hts1 hm hb hlt1 hfen hlt2 htss hrd hdisc hlt hagr k' ev' hle hev' hsome
  exact edgeOkFFcov Tj kr k' ts
    (coveredFcov pstep TS.ptImg TS.ptLog j Tj kr k' ts ev' (traceWf pstep TS hwf j Tj hTj)
      (coveredOfReleaseAcquire pstep TS hwf hfo i j Ti Tj k1 kf ks ka kr ts tsS a1 m a agr
        hne hTi hTj hts1 hm hb hlt1 hfen hlt2 htss hrd hdisc hlt hagr)
      hle hev' hsome)

/-! ### DELIVERABLE A2: COVERAGE THROUGH A CHAIN -/

/-- THE TWO-HOP SPELLING: `i` releases, `j` acquires and re-releases, `l`
acquires. -/
theorem coveredOfReleaseTwoHops (hwf : ptracesWf pstep TS) (hfo : ptracesFwdOwn TS)
    (i j l : Nat) (Ti Tj Tl : Atrace P D) (k1 kf ks kr kd kjs kr2 k2 ts tsS tsJ : Nat)
    (a1 : Int) (m : Wmsg) (a aj : Int) (agd ag2 : Wpagent P) :
    i ≠ j → j ≠ l →
    TS.ptTrs[i]? = some Ti →
    TS.ptTrs[j]? = some Tj →
    TS.ptTrs[l]? = some Tl →
    -- `i`'s release site
    gevTs TS (i, k1) = some ts →
    TS.ptLog[ts - 1]? = some m → (msgByte m a1).isSome →
    k1 < kf →
    (∃ ev, Ti.atEvs[kf]? = some ev ∧ lbFencePwsw ev.aeLb) →
    kf < ks →
    gevTs TS (i, ks) = some tsS →
    -- `j` acquires `tsS` and later fulfils `tsJ`
    gevReads TS (j, kr) a tsS →
    disciplined Tj kr kd →
    kr < kd → kd ≤ kjs →
    Tj.atAgs[kd]? = some agd →
    gevTs TS (j, kjs) = some tsJ →
    -- `l` acquires `tsJ`
    gevReads TS (l, kr2) aj tsJ →
    disciplined Tl kr2 k2 →
    kr2 < k2 →
    Tl.atAgs[k2]? = some ag2 →
    covered Tl k2 ts := by
  intro hij hjl hTi hTj hTl hts1 hm hb hlt1 hfen hlt2 htss hrd hdisc h1 h2 hagd htsj hrd2
    hdisc2 h3 hag2
  have hlts : ts < tsS :=
    releaseLt pstep TS hwf i Ti k1 kf ks ts tsS a1 m hTi hts1 hm hb hlt1 hfen hlt2 htss
  have hltj : tsS < tsJ :=
    acquireReleaseLt pstep TS hwf hfo j (i, ks) Tj kr kd kjs tsS tsJ a agd hij hTj hrd htss
      hdisc h1 h2 hagd htsj
  exact coveredMonoTs Tl k2 tsJ ts
    (acquireCovered pstep TS hwf hfo l (j, kjs) Tl kr2 k2 aj tsJ ag2 hjl hTl hrd2 htsj hdisc2
      h3 hag2)
    (by omega)

/-- THE n-HOP VERSION. -/
theorem coveredOfReleaseChain (hwf : ptracesWf pstep TS) (hfo : ptracesFwdOwn TS)
    (i j : Nat) (Ti Tj : Atrace P D) (k1 kf ks kr k2 ts tsS : Nat) (a1 : Int) (m : Wmsg)
    (a : Int) (ag2 : Wpagent P) (hs : List Hop) (elast : Gev) (tlast : Nat) :
    i ≠ j →
    TS.ptTrs[i]? = some Ti →
    TS.ptTrs[j]? = some Tj →
    -- `i`'s release site
    gevTs TS (i, k1) = some ts →
    TS.ptLog[ts - 1]? = some m → (msgByte m a1).isSome →
    k1 < kf →
    (∃ ev, Ti.atEvs[kf]? = some ev ∧ lbFencePwsw ev.aeLb) →
    kf < ks →
    gevTs TS (i, ks) = some tsS →
    -- the chain of intermediate release/acquire hops
    chainOk TS (i, ks) tsS hs →
    chainEnd (i, ks) tsS hs = (elast, tlast) →
    -- `j`'s final acquire
    elast.1 ≠ j →
    gevReads TS (j, kr) a tlast →
    disciplined Tj kr k2 →
    kr < k2 →
    Tj.atAgs[k2]? = some ag2 →
    covered Tj k2 ts := by
  intro _hne hTi hTj hts1 hm hb hlt1 hfen hlt2 htss hch hend hne' hrd hdisc hlt hag2
  have hlts : ts < tsS :=
    releaseLt pstep TS hwf i Ti k1 kf ks ts tsS a1 m hTi hts1 hm hb hlt1 hfen hlt2 htss
  obtain ⟨hle, htsl⟩ := chainLt pstep TS hwf hfo (i, ks) tsS hs hch
  rw [hend] at hle htsl
  dsimp only at hle htsl
  exact coveredMonoTs Tj k2 tlast ts
    (acquireCovered pstep TS hwf hfo j elast Tj kr k2 a tlast ag2 hne' hTj hrd htsl hdisc hlt hag2)
    (by omega)

/-! ### DELIVERABLE A3: THE THREE ARMS OF `eeOk` -/

/-- ARM (a), FENCE-COVER: a `pw ∧ sw` fence po-between `et` and `ey` —
`releaseLt` verbatim at the E edge's own `t̂`. -/
theorem eeOkFenceCover (hwf : ptracesWf pstep TS) (r : Gev) (a : Int) (e1 et ey : Gev)
    (y : Nat) (T : Atrace P D) (kf : Nat) :
    gERa TS r a e1 et →
    TS.ptTrs[et.1]? = some T →
    et.1 = ey.1 →
    et.2 < kf → kf < ey.2 →
    (∃ ev, T.atEvs[kf]? = some ev ∧ lbFencePwsw ev.aeLb) →
    gevTs TS ey = some y →
    rdFloor TS r a < y := by
  obtain ⟨ie, ke⟩ := et
  obtain ⟨iy, ky⟩ := ey
  intro hra hT hag hlt1 hlt2 hfen hy
  simp only at hag hlt1 hlt2
  subst hag
  obtain ⟨l, ts, tstar, that, _, _, _, _, _, hthat, ⟨m, hm, hb⟩, hfl⟩ := hra
  have := releaseLt pstep TS hwf ie T ke kf ky that y a m hT hthat hm hb hlt1 hfen hlt2 hy
  omega

/-- ARM (b), WAW-COVER: the writer's `wVwNew` at `et`'s PRE-state was already at
or above the floor — `coveredFulfilLt` verbatim. -/
theorem eeOkWawCover (hwf : ptracesWf pstep TS) (r : Gev) (a : Int) (e1 et ey : Gev)
    (y : Nat) (T : Atrace P D) :
    gERa TS r a e1 et →
    TS.ptTrs[et.1]? = some T →
    et.1 = ey.1 → et.2 ≤ ey.2 →
    covered T et.2 (rdFloor TS r a) →
    gevTs TS ey = some y →
    rdFloor TS r a < y := by
  obtain ⟨ie, ke⟩ := et
  obtain ⟨iy, ky⟩ := ey
  intro _ hT hag hle hcov hy
  simp only at hag hle
  subst hag
  exact coveredFulfilLt pstep TS hwf ie T ke ky (rdFloor TS r a) y hT hcov hle hy

/-- ARM (c), EMPTY FLOOR: fulfilled timestamps are positive. -/
theorem eeOkZeroFloor (hwf : ptracesWf pstep TS) (r : Gev) (a : Int) (ey : Gev) (y : Nat) :
    rdFloor TS r a = 0 → gevTs TS ey = some y →
    rdFloor TS r a < y := by
  intro hz hy
  rw [hz]
  exact gevTsPos pstep TS ey y hwf hy

/-- The three arms, as ONE per-(edge, later fulfil) side condition. -/
def eeArm (r : Gev) (a : Int) (et ey : Gev) : Prop :=
  rdFloor TS r a = 0 ∨
  (∃ (T : Atrace P D) (kf : Nat), TS.ptTrs[et.1]? = some T ∧
     et.2 < kf ∧ kf < ey.2 ∧
     ∃ ev, T.atEvs[kf]? = some ev ∧ lbFencePwsw ev.aeLb) ∨
  (∃ T : Atrace P D, TS.ptTrs[et.1]? = some T ∧ covered T et.2 (rdFloor TS r a))

/-- …and the assembly into `WeakRobustAcyc2.eeOk`. -/
theorem eeOkOfArms (hwf : ptracesWf pstep TS) :
    (∀ (r : Gev) (a : Int) (e1 et ey : Gev) (y : Nat),
       gERa TS r a e1 et → et.1 = ey.1 → et.2 < ey.2 →
       gevTs TS ey = some y → eeArm TS r a et ey) →
    eeOk TS := by
  intro harm r a e1 et ey y hra hag hlt hy
  rcases harm r a e1 et ey y hra hag hlt hy with hz | ⟨T, kf, hT, h1, h2, hfen⟩ | ⟨T, hT, hcov⟩
  · exact eeOkZeroFloor pstep TS hwf r a ey y hz hy
  · exact eeOkFenceCover pstep TS hwf r a e1 et ey y T kf hra hT hag h1 h2 hfen hy
  · exact eeOkWawCover pstep TS hwf r a e1 et ey y T hra hT hag (by omega) hcov hy

/-! ### DELIVERABLE A4: THE PER-BYTE PREMISES (`WeakRobustSer`) -/

/-- (i) EXCLUSIVITY, from the label alone: every writing event of the byte is an
`LRmw`. -/
def rmwWritten (a : Int) : Prop :=
  ∀ e t, writesB TS a e t →
    ∃ (aq rl : Bool) (base : Int) (tvs : List (Nat × BitVec 8)) (data : List (BitVec 8))
      (asrc vsrc : List Dsrc),
      gevLb TS e = some (LRmw aq rl base tvs data asrc vsrc)

theorem exclByteOfRmw (hwf : ptracesWf pstep TS) (a : Int) :
    rmwWritten TS a → exclByte TS a := by
  intro hrmw e t hw
  right
  obtain ⟨aq, rl, base, tvs, data, asrc, vsrc, hlb⟩ := hrmw e t hw
  obtain ⟨hts, m0, hm0, hb0⟩ := hw
  obtain ⟨T, ev, hT, hev', hlbe⟩ := gevLbSome TS e _ hlb
  have hev : gevEv TS e = some ev := by unfold gevEv; rw [hT]; exact hev'
  have hts' : ev.aeTs = some t := by
    unfold gevTs at hts; rw [hev] at hts; exact hts
  obtain ⟨_, ag, ag', st', f, _, _, _, _, hok, _⟩ := gevStep pstep TS e ev hwf hev
  rw [hlbe, hts'] at hok
  obtain ⟨ts', kc, hlen, _, hlog, _, _, _, _, hD⟩ := hok
  cases hD
  rw [hlog] at hm0; cases hm0
  unfold msgByte at hb0
  split at hb0
  · next hle =>
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hb0
    have hjlt : (a - base).toNat < tvs.length := by
      rw [hlen]; exact lookup_lt_Some hv
    obtain ⟨⟨tr, v'⟩, htv⟩ := Option.isSome_iff_exists.1 (lookup_lt_is_Some_2 hjlt)
    refine ⟨tr, LRmw aq rl base tvs data asrc vsrc, hlb, ?_⟩
    exact (memTvsReads _ _ _ _).2 ⟨(a - base).toNat, v', htv, by simp only at hle; omega⟩
  · simp at hb0

/-- (ii) SINGLE WRITER, from the LOG. -/
def logSingleWriter (a : Int) (i : Nat) : Prop :=
  ∀ (t : Nat) (m : Wmsg), TS.ptLog[t - 1]? = some m → (msgByte m a).isSome →
    m.wmTid = some i

theorem swByteOfLogSingleWriter (hwf : ptracesWf pstep TS) (a : Int) (i : Nat) :
    logSingleWriter TS a i → swByte TS a := by
  intro H e1 e2 t1 t2 hw1 hw2
  obtain ⟨m1, hm1, hb1, ht1⟩ := writesBAuthor pstep TS a e1 t1 hwf hw1
  obtain ⟨m2, hm2, hb2, ht2⟩ := writesBAuthor pstep TS a e2 t2 hwf hw2
  have E1 := H t1 m1 hm1 hb1
  have E2 := H t2 m2 hm2 hb2
  rw [ht1] at E1; rw [ht2] at E2
  exact Option.some.inj (E1.trans E2.symm)

/-- (iii) HANDOFF, from release/acquire CHAINS.  The chain's job is EXACTLY the
order conjunct `tr ≤ tStar` (through `chainLt`); the structural conjuncts are
site facts, and the endpoints' sync byte must be shared. -/
theorem handoffOfSyncChains (hwf : ptracesWf pstep TS) (hfo : ptracesFwdOwn TS)
    (sync : Int → Prop) (a : Int) :
    (∀ e1 e2 t1 t2,
       writesB TS a e1 t1 → writesB TS a e2 t2 →
       e1.1 ≠ e2.1 → t1 < t2 → coConsec TS a t1 t2 →
       ∃ (b : Int) (er : Gev) (tr : Nat) (hs : List Hop) (elast : Gev) (tlast : Nat)
         (rr : Gev) (tStar : Nat),
         sync b ∧
         writesB TS b er tr ∧ er.1 = e1.1 ∧ e1.2 ≤ er.2 ∧
         chainOk TS er tr hs ∧ chainEnd er tr hs = (elast, tlast) ∧
         gevReads TS rr b tStar ∧ rr.1 = e2.1 ∧ rr.2 ≤ e2.2 ∧
         tlast ≤ tStar) →
    handoff TS sync a := by
  intro hsite e1 e2 t1 t2 hw1 hw2 hne hlt hcc
  obtain ⟨b, er, tr, hs, elast, tlast, rr, tStar, hsync, her, hag1, hpo1, hch, hend, hrr, hag2,
    hpo2, hle⟩ := hsite e1 e2 t1 t2 hw1 hw2 hne hlt hcc
  have hchle := (chainLt pstep TS hwf hfo er tr hs hch).1
  rw [hend] at hchle
  dsimp only at hchle
  exact ⟨b, er, tr, rr, tStar, hsync, her, hag1, hpo1, hrr, hag2, hpo2, by omega⟩

/-- THE ZERO-HOP INSTANCE: a DIRECT release/acquire needs no chain at all. -/
theorem handoffOfDirectSync (hwf : ptracesWf pstep TS) (hfo : ptracesFwdOwn TS)
    (sync : Int → Prop) (a : Int) :
    (∀ e1 e2 t1 t2,
       writesB TS a e1 t1 → writesB TS a e2 t2 →
       e1.1 ≠ e2.1 → t1 < t2 → coConsec TS a t1 t2 →
       ∃ (b : Int) (er : Gev) (tr : Nat) (rr : Gev) (tStar : Nat),
         sync b ∧
         writesB TS b er tr ∧ er.1 = e1.1 ∧ e1.2 ≤ er.2 ∧
         gevReads TS rr b tStar ∧ rr.1 = e2.1 ∧ rr.2 ≤ e2.2 ∧
         tr ≤ tStar) →
    handoff TS sync a := by
  intro hsite
  apply handoffOfSyncChains pstep TS hwf hfo
  intro e1 e2 t1 t2 hw1 hw2 hne hlt hcc
  obtain ⟨b, er, tr, rr, tStar, hsync, her, hag1, hpo1, hrr, hag2, hpo2, hle⟩ :=
    hsite e1 e2 t1 t2 hw1 hw2 hne hlt hcc
  exact ⟨b, er, tr, [], er, tr, rr, tStar, hsync, her, hag1, hpo1, her.1, rfl, hrr, hag2, hpo2,
    hle⟩

/-- …and the packaging `ptracesBytesOk` wants. -/
theorem ptracesBytesOkOfArms (sync : Int → Prop) :
    (∀ b, sync b → swByte TS b ∨ exclByte TS b) →
    (∀ a, swByte TS a ∨ exclByte TS a ∨ handoff TS sync a) →
    ptracesBytesOk TS sync :=
  fun h1 h2 => ⟨h1, h2⟩

end disc

/-! ## DELIVERABLE A5: `devEpochOk` — WHAT IT ACTUALLY DEMANDS

THE PREMISE CHARACTERIZED HERE IS SUPERSEDED (A0′): `mainPremises` now carries
`WeakRobustOrd.devWitOk`, which the refuting bundle satisfies outright.  What
follows stands as the characterization of the SUFFICIENT condition
`devEpochOk`: a DOMINATION condition (`devDom`), not an ordering one.  Per edge
`e1 → e2`: every fabric access of the WRITER's agent po-before `e1` is matched
by one of the READER's agent po-before `e2` at a witness index at least as
large.  (1) It is not about promise reads (`devEpochOkDevfreeReader`); (2)
coverage cannot help — the missing ingredient is EXISTENTIAL.  The obstruction
is in the per-agent DEFINITION of `depoch`; repair (b),
`WeakRobustOrd.gdep3AcyclicOfWit`, is what landed. -/

section devepoch

variable {P D : Type}
variable (TS : Ptraces P D)

/-- The witness position that ACHIEVES the epoch, when it is nonzero. -/
theorem depGoWitness (l : List Gev) (e : Gev) (m : Nat) :
    depGo l e m = 0 ∨
    ∃ (i : Nat) (e' : Gev), l[i]? = some e' ∧ e'.1 = e.1 ∧ e'.2 ≤ e.2 ∧
      depGo l e m = m + i + 1 := by
  induction l generalizing m with
  | nil => left; rfl
  | cons x l ih =>
    simp only [depGo]
    by_cases hb : x.1 = e.1 ∧ x.2 ≤ e.2
    · rw [if_pos hb]
      rcases ih (m + 1) with hz | ⟨i, e', hi, hag, hle, heq⟩
      · right; refine ⟨0, x, rfl, hb.1, hb.2, ?_⟩; rw [hz]; omega
      · right; refine ⟨i + 1, e', by simpa using hi, hag, hle, ?_⟩; rw [heq]; omega
    · rw [if_neg hb]
      rcases ih (m + 1) with hz | ⟨i, e', hi, hag, hle, heq⟩
      · left; rw [hz]; omega
      · right; refine ⟨i + 1, e', by simpa using hi, hag, hle, ?_⟩; rw [heq]; omega

theorem depochWitness (DS : Pdevs D) (e : Gev) :
    depoch DS e = 0 ∨
    ∃ (m : Nat) (e' : Gev), DS.pdOrd[m]? = some e' ∧ e'.1 = e.1 ∧ e'.2 ≤ e.2 ∧
      depoch DS e = m + 1 := by
  unfold depoch
  rcases depGoWitness DS.pdOrd e 0 with hz | ⟨i, e', hi, hag, hle, heq⟩
  · exact Or.inl hz
  · right; exact ⟨i, e', hi, hag, hle, by rw [heq]; omega⟩

/-- THE DOMINATION CONDITION. -/
def devDom (DS : Pdevs D) (e1 e2 : Gev) : Prop :=
  ∀ (m : Nat) (ep : Gev), DS.pdOrd[m]? = some ep → ep.1 = e1.1 → ep.2 ≤ e1.2 →
    ∃ (m' : Nat) (ep' : Gev), DS.pdOrd[m']? = some ep' ∧ ep'.1 = e2.1 ∧
      ep'.2 ≤ e2.2 ∧ m ≤ m'

theorem depochLeOfDom (DS : Pdevs D) (e1 e2 : Gev) :
    devDom DS e1 e2 → depoch DS e1 ≤ depoch DS e2 := by
  intro hd
  rcases depochWitness DS e1 with hz | ⟨m, ep, hm, hag, hle, heq⟩
  · rw [hz]; exact Nat.zero_le _
  · obtain ⟨m', ep', hm', hag', hle', hmm⟩ := hd m ep hm hag hle
    have := depochLb DS e2 m' ep' hm' hag' hle'
    omega

theorem domOfDepochLe (DS : Pdevs D) (e1 e2 : Gev) :
    depoch DS e1 ≤ depoch DS e2 → devDom DS e1 e2 := by
  intro hle m ep hm hag hlp
  have hlb := depochLb DS e1 m ep hm hag hlp
  rcases depochWitness DS e2 with hz | ⟨m', ep', hm', hag', hle', heq⟩
  · omega
  · exact ⟨m', ep', hm', hag', hle', by omega⟩

/-- THE CHARACTERIZATION, both directions. -/
theorem devEpochOkOfDom (DS : Pdevs D) :
    (∀ e1 e2, (WeakRobustGraph.grf TS e1 e2 ∨ gE TS e1 e2) → devDom DS e1 e2) →
    devEpochOk TS DS :=
  fun H e1 e2 he => depochLeOfDom DS e1 e2 (H e1 e2 he)

theorem devDomOfDevEpochOk (DS : Pdevs D) :
    devEpochOk TS DS →
    ∀ e1 e2, (WeakRobustGraph.grf TS e1 e2 ∨ gE TS e1 e2) → devDom DS e1 e2 :=
  fun H e1 e2 he => domOfDepochLe DS e1 e2 (H e1 e2 he)

/-- THE FAILURE MODE: a reader with no fabric history forces the writer to have
none either. -/
theorem devEpochOkDevfreeReader (DS : Pdevs D) (e1 e2 : Gev) :
    devEpochOk TS DS → (WeakRobustGraph.grf TS e1 e2 ∨ gE TS e1 e2) →
    depoch DS e2 = 0 → depoch DS e1 = 0 := by
  intro H he hz
  have := H e1 e2 he
  omega

/-- THE ONE ARM THAT IS FREE: no edge SOURCE has a fabric access behind it. -/
theorem devEpochOkOfDevfreeSources (DS : Pdevs D) :
    (∀ e1 e2, (WeakRobustGraph.grf TS e1 e2 ∨ gE TS e1 e2) → depoch DS e1 = 0) →
    devEpochOk TS DS := by
  intro H e1 e2 he
  rw [H e1 e2 he]
  exact Nat.zero_le _

/-- THE TRANSPORT TO THE LANDED PREMISE (A0′). -/
theorem devWitOkOfDom (DS : Pdevs D) :
    ptracesWit TS DS →
    (∀ e1 e2, (WeakRobustGraph.grf TS e1 e2 ∨ gE TS e1 e2) → devDom DS e1 e2) →
    devWitOk TS DS :=
  fun hwit H => devWitOkOfEpoch TS DS hwit (devEpochOkOfDom TS DS H)

theorem devWitOkOfDevfreeSources (DS : Pdevs D) :
    ptracesWit TS DS →
    (∀ e1 e2, (WeakRobustGraph.grf TS e1 e2 ∨ gE TS e1 e2) → depoch DS e1 = 0) →
    devWitOk TS DS :=
  fun hwit H => devWitOkOfEpoch TS DS hwit (devEpochOkOfDevfreeSources TS DS H)

end devepoch

/-! ## DELIVERABLE A6: `badWf` FROM FINITE ANCESTRY

`length (anc R carrier x)` strictly decreases along `tc R` once `tc R` is
irreflexive (`ancMuLt`); strong induction on it produces a minimal element of
any DECIDABLE predicate (`tcMin`).  THE CIRCULARITY: `gdep3Acyclic` is what
`robustMain` establishes THROUGH `badWf`, so `badWfOfAcyclic` cannot remove
`badWf` from `mainPremises`; an independent argument needs a well-founded
measure from the OWNERSHIP structure (a Track-B/C fact). -/

section wfmin

variable {A : Type _} [DecidableEq A]
variable (R : A → A → Prop) [DecidableRel R]
variable (carrier : List A)

theorem ancSub (hcar : ∀ x y, R x y → x ∈ carrier) (hnd : carrier.Nodup) (x y : A) :
    x ∈ carrier → y ∈ carrier → tc R y x →
    ∀ z, z ∈ anc R carrier y → z ∈ anc R carrier x := by
  intro hx hy htc z hz
  rcases (elemOfAnc R carrier y hy hcar hnd z).1 hz with rfl | hzy
  · exact (elemOfAnc R carrier x hx hcar hnd z).2 (Or.inr htc)
  · exact (elemOfAnc R carrier x hx hcar hnd z).2 (Or.inr (tc_transitive hzy htc))

theorem ancMuLt (hcar : ∀ x y, R x y → x ∈ carrier) (hnd : carrier.Nodup)
    (hacyc : ∀ x, ¬ tc R x x) (x y : A) :
    x ∈ carrier → y ∈ carrier → tc R y x →
    (anc R carrier y).length < (anc R carrier x).length := by
  intro hx hy htc
  have hxnin : x ∉ anc R carrier y := by
    intro hin
    rcases (elemOfAnc R carrier y hy hcar hnd x).1 hin with heq | hxy
    · subst heq; exact hacyc x htc
    · exact hacyc x (tc_transitive hxy htc)
  have hnd' : (x :: anc R carrier y).Nodup :=
    List.nodup_cons.2 ⟨hxnin, ancIterNodup R carrier y hnd _⟩
  have hle : (x :: anc R carrier y).length ≤ (anc R carrier x).length :=
    submseteq_length (NoDup_submseteq hnd' (fun z hz => by
      rcases List.mem_cons.1 hz with heq | hz
      · subst heq; exact rootInAnc R carrier z
      · exact ancSub R carrier hcar hnd x y hx hy htc z hz))
  simp only [List.length_cons] at hle
  omega

/-- THE MINIMAL ELEMENT.  `Q` must be decidable: the search "is some
`Q`-element strictly below me" is what the induction step answers. -/
theorem tcMin (hcar : ∀ x y, R x y → x ∈ carrier) (hnd : carrier.Nodup)
    (hacyc : ∀ x, ¬ tc R x x) (Q : A → Prop) [DecidablePred Q] :
    (∀ x, Q x → x ∈ carrier) →
    ∀ x, Q x → ∃ y, Q y ∧ ∀ z, Q z → ¬ tc R z y := by
  intro hQc
  have hgen : ∀ (n : Nat) (x : A), Q x → (anc R carrier x).length ≤ n →
      ∃ y, Q y ∧ ∀ z, Q z → ¬ tc R z y := by
    intro n
    induction n with
    | zero =>
      intro x _ hmu
      exfalso
      have hpos : 0 < (anc R carrier x).length := List.length_pos_of_mem (rootInAnc R carrier x)
      omega
    | succ n ih =>
      intro x hx hmu
      if hex : ∃ z ∈ carrier, Q z ∧ z ∈ anc R carrier x ∧ z ≠ x then
        obtain ⟨z, _, hQz, hzanc, hzne⟩ := hex
        have htc : tc R z x := by
          rcases (elemOfAnc R carrier x (hQc x hx) hcar hnd z).1 hzanc with h | h
          · exact absurd h hzne
          · exact h
        apply ih z hQz
        have := ancMuLt R carrier hcar hnd hacyc x z (hQc x hx) (hQc z hQz) htc
        omega
      else
        refine ⟨x, hx, fun z hQz htc => hex ⟨z, hQc z hQz, hQz,
          (elemOfAnc R carrier x (hQc x hx) hcar hnd z).2 (Or.inr htc), fun heq => ?_⟩⟩
        subst heq
        exact hacyc z htc
  intro x hx
  exact hgen _ x hx (Nat.le_refl _)

end wfmin

section badwf

variable {P D : Type}
variable (TS : Ptraces P D) (DS : Pdevs D)

/-- "`e` is the TARGET of some bad edge". -/
def badTarget (nh : Nat) (e : Gev) : Prop := ∃ f1, bad nh TS DS f1 e

/-- No bad edges at all ⟹ `badWf` vacuously. -/
theorem badWfOfNoBad (nh : Nat) :
    (∀ e1 e2, ¬ bad nh TS DS e1 e2) → badWf nh TS DS :=
  fun H e1 e2 hb => (H e1 e2 hb).elim

/-- …and the finite-ancestry derivation (it consumes `gdep3Acyclic`, the
CONCLUSION of the theorem `badWf` is a premise of — see the header). -/
theorem badWfOfAcyclic (nh : Nat) :
    ptracesWit TS DS →
    gdep3Acyclic TS DS →
    (∀ e, Decidable (badTarget TS DS nh e)) →
    badWf nh TS DS := by
  intro hwit hacyc hdec e1 e2 hbad
  have hcar : ∀ x y, gdep3 TS DS x y → x ∈ gevEnum TS :=
    fun x y hd => (elemOfGevEnum TS x).2 (gdep3Wf TS DS x y hwit hd).1
  have hQc : ∀ e, badTarget TS DS nh e → e ∈ gevEnum TS := by
    rintro e ⟨f1, ⟨ts, a, _, hrd⟩, _⟩
    exact (elemOfGevEnum TS e).2 (gevReadsWf TS e a ts hrd)
  haveI : DecidablePred (badTarget TS DS nh) := hdec
  obtain ⟨y, ⟨g1, hg⟩, hmin⟩ :=
    tcMin (gdep3 TS DS) (gevEnum TS) hcar (nodupGevEnum TS) hacyc (badTarget TS DS nh) hQc e2
      ⟨e1, hbad⟩
  exact ⟨g1, y, hg, fun f1 f2 hb htc => hmin f2 ⟨f1, hb⟩ htc⟩

end badwf

/-! ## What Track B and Track C inherit from this file

- `disciplinedCovered` / `acquireCovered`: an acquire COVERS everything at or
  below the message it acquired, from the acquire on.
- `releaseLt`: the writer-side site fact; the ONE place a fence is load-bearing.
- `coveredFulfilLt` / `acquireReleaseLt` / `chainOk` / `chainEnd` / `chainLt`:
  the hop calculus (only the ORIGIN hop needs a fence).
- A1/A2 (`coveredOfRelease*`, `edgeOk*OfReleaseAcquire`), A3 (`eeOk*`,
  `eeArm`, `eeOkOfArms`), A4 (`rmwWritten` … `ptracesBytesOkOfArms`), A5 (a
  characterization plus a refutation, not a discharge), A6 (`tcMin`,
  `ancMuLt`, `badWfOfAcyclic`, `badWfOfNoBad`).
-/

end Weak
