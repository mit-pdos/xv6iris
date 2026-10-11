/-
Weak: **BLOCK STRUCTURE, THE CONE CUT, and COMPLETION** (lift stage L1 —
obstacles 1 and 2 of `claude-notes/completed/weak-memory-lift.md`).

Rocq: `iris/WeakRobustBlocks.v` @ xxvzwolszwmp.

The Rocq header, in substance.  φ is exported at INSTRUCTION boundaries; the
Layer-1 exhibit (`WeakRobustMain.badEdgeViolates`) stops at EVENT boundaries —
its promise-free run replays a downward-closed ANCESTOR CONE of the bad read,
and each agent is left CUT wherever the cone reached.  Two theorems bridge that:

  1. THE CONE-CUT THEOREM (`coneBoundaryThm`).  Every CROSS edge of `gdep2`
     emanates from a FULFIL (`crossEdgeFulfil`): `gpo` is same-agent, `grf` and
     `gE` pin `gevTs` of their source.  Hence the last processed event of any
     non-reader agent is a fulfil (`cutLastFulfil`), and under STORE-LAST a
     fulfil ends its block: the cut lands at a boundary, or at the one admitted
     mid-block fulfil, the walker's A/D write-back CAS.  `coneBoundarySub` is the
     sub-block form (post-A/D points admitted as boundaries; one disjunct).
  2. COMPLETION (`completeBlock` / `completeCut` / `completeReader` /
     `completeAgents`).  Under `imgTotal` a read is ALWAYS admissible (at the
     byte's latest write), so a cut agent's residual block runs to its next
     boundary in the promise-free machine, and the VIOLATION SURVIVES as long as
     the completed agent is not the violating message's author (`¬ pub` is
     per-author, `violatesAtAppend`).

The block discipline is abstract (a predicate on `(pstep, atBoundary)` plus the
A/D marker `ad`); the `sail_step` instantiation obligations are listed in the
Rocq header (`atBoundary p := sp_m p = None`, store-last, the A/D CAS is an
`LRmw` strictly inside its block, value-input-enabledness `LtsEnabled`, finite
never-stuck blocks `BlkFin`).  DEPENDENCY-FREE: no Iris, no Sail.

**Deviations from Rocq.**

1. NAMES: lowerCamelCase as `Weak/WeakMem.lean` deviation 1; records are
   `BlkShape`/`LtsEnabled`/`BlkFin` with camel fields.  No name of this file is
   in `notes/weak-port-dupnames.json`.  The binder `done` is `dn`.
2. VOCABULARY: as `Weak/WeakRobustSim.lean` deviation 2 (`l !! i` ↦ `l[i]?`,
   `<[i:=x]> l` ↦ `l.set i x`, `is_Some o` ↦ `o.isSome` (or `∃ x, o = some x`
   where Rocq destructs it), `S n` ↦ `n + 1`, `NoDup` ↦ `List.Nodup`,
   `tvs.*1` ↦ `tvs.map Prod.fst`, `Nat.max` ↦ `max`); `Forall P l` ↦
   `∀ x ∈ l, P x`; `Decision` instance binders ↦ `Decidable` instance binders.
3. SECTION VARIABLES: `pstep`/`pcls`/`dflt` are `variable`s, included exactly
   where Rocq's `Global Arguments` keep them (`dflt` via `include … in` where it
   is used only in the proof).  `pdev` is a Rocq section variable that no
   declaration of this file uses; it is not a parameter anywhere.
4. O2 / owner decision D4 — THE LEAN-ONLY LABEL `LIFetch base tvs`
   (`Weak/WeakPromise.lean` deviation 8, `wpPfStep.PFIFetch`):
   - `lbWrites (LIFetch ..) = false` (a fetch appends nothing);
     `lbLoads (LIFetch ..) = false`, consistent with
     `WeakRobustGraph.lbReads (LIFetch ..) = []` (a fetch is not a reads-of
     source of the dependency graph); `lbOk (LIFetch ..) = True`.
   - `LtsEnabled` gains a FOURTH field `leIfetch` (value-enabledness of a fetch:
     the program accepts any fetched answers of the same width), the exact twin
     of `leLoad`.  It is what `cstepAvailable`'s new `LIFetch` arm consumes (the
     completion fetches every byte at its latest write; at instruction view 0
     `ifetchOk` is just the value conjunct, `ifetchByteOk0`).
   - `wpPfStepShape` / `wpPfStepBnd` / `cstepAvailable` gain the `PFIFetch` /
     `LIFetch` arm (the state-identity arm, as `LSilent`).
   - NoFetch discharge (Lean-only): `leIfetchOfNoFetch` (the field is vacuous
     under `pstepNoFetch`) and `ltsEnabledOfNoFetch` (Rocq's three-field
     `LtsEnabled` constructor, for a fetch-free program).
   - No `fetchSrcOk` premise is needed anywhere in this file: nothing here
     replays a cone (`WeakRobustSim.QinvStep` is not used), so the
     `WeakRobustMain`/`WeakRobustSim` fetch-source premise does not arise.
5. PROOFS: the `rtc` closures (`cstepRtcRun`, `cstepsImg`, …, `cstepsLog`) go by
   tail induction (MachCSL `rtc` is built from the LAST step; Rocq: head);
   `cutLastFulfil`'s first-edge split uses the Lean-only `tcHeadInv`;
   `completeBlockAux` uses `Nat.strongRecOn` (Rocq: `lt_wf_ind`).  Statements
   unchanged.
6. Lean-only helpers (no Rocq twin): `tcHeadInv`, `cstepOfStep`, `cfgBndSet`, `cfgBndLookup`,
   `leIfetchOfNoFetch`, `ltsEnabledOfNoFetch`.

**Rocq → Lean name map.**  `lb_writes` ↦ `lbWrites`; `lb_loads` ↦ `lbLoads`;
`lb_ok` ↦ `lbOk`; `lookup_insert_self` ↦ `lookupInsertSelf`;
`lookup_insert_other` ↦ `lookupInsertOther`; `lb_writes_ts_none` ↦
`lbWritesTsNone`; `blk_shape` ↦ `BlkShape` (fields `bs_store_last` ↦
`bsStoreLast`, `bs_ad_rmw` ↦ `bsAdRmw`, `bs_ad_mid` ↦ `bsAdMid`);
`blk_trace_boundary` ↦ `blkTraceBoundary`; `at_boundary_ad` ↦ `atBoundaryAd`;
`at_boundary_ad_intro` ↦ `atBoundaryAdIntro`; `img_total_on` ↦ `imgTotalOn`;
`img_total` ↦ `imgTotal`; `img_total_on_all` ↦ `imgTotalOnAll`;
`latest_log_byte` ↦ `latestLogByte`; `byte_readable_latest` ↦
`byteReadableLatest`; `read_latest` ↦ `readLatest`; `read_latest_exists` ↦
`readLatestExists`; `read_latest_read_ok_d` ↦ `readLatestReadOkD`;
`read_latest_read_ok` ↦ `readLatestReadOk`; `read_latest_excl_ok` ↦
`readLatestExclOk`; `read_latest_ts_le` ↦ `readLatestTsLe`; `lts_enabled` ↦
`LtsEnabled` (fields `le_lb_ok` ↦ `leLbOk`, `le_load` ↦ `leLoad`, `le_rmw` ↦
`leRmw`; Lean-only `leIfetch`); `blk_fin` ↦ `BlkFin` (fields `bf_prog` ↦
`bfProg`, `bf_meas` ↦ `bfMeas`); `cstep`; `cstep_run` ↦ `cstepRun`;
`cstep_rtc_run` ↦ `cstepRtcRun`; `wp_pf_step_shape` ↦ `wpPfStepShape`;
`wp_pf_step_frame` ↦ `wpPfStepFrame`; `wp_pf_step_ags_len` ↦ `wpPfStepAgsLen`;
`wp_pf_step_obs_flr` ↦ `wpPfStepObsFlr`; `cfg_bnd` ↦ `cfgBnd`; `cfg_bnd_init`
↦ `cfgBndInit`; `read_ok_ts_le` ↦ `readOkTsLe`; `read_ok_forall` ↦
`readOkForall`; `wp_pf_step_bnd` ↦ `wpPfStepBnd`; `cstep_available` ↦
`cstepAvailable`; `cstep_bnd` ↦ `cstepBnd`; `cstep_img` ↦ `cstepImg`;
`cstep_frame` ↦ `cstepFrame`; `cstep_ags_len` ↦ `cstepAgsLen`; `cstep_obs_flr`
↦ `cstepObsFlr`; `csteps_img` ↦ `cstepsImg`; `csteps_bnd` ↦ `cstepsBnd`;
`csteps_frame` ↦ `cstepsFrame`; `csteps_ags_len` ↦ `cstepsAgsLen`;
`csteps_obs_flr` ↦ `cstepsObsFlr`; `csteps_log` ↦ `cstepsLog`;
`complete_block_aux` ↦ `completeBlockAux`; `complete_block` ↦ `completeBlock`;
`gdep2_src_fulfil_or_po` ↦ `gdep2SrcFulfilOrPo`; `cross_edge_fulfil` ↦
`crossEdgeFulfil`; `cone_of` ↦ `coneOf`; `cut_last_fulfil` ↦ `cutLastFulfil`;
`cone_boundary_thm` ↦ `coneBoundaryThm`; `cone_boundary_sub` ↦
`coneBoundarySub`; `violates_at` ↦ `violatesAt`; `violates_at_violation` ↦
`violatesAtViolation`; `violation_violates_at` ↦ `violationViolatesAt`;
`violation_hart_violates_at` ↦ `violationHartViolatesAt`;
`violates_at_append` ↦ `violatesAtAppend`; `complete_cut_persists` ↦
`completeCutPersists`; `complete_cut` ↦ `completeCut`; `complete_reader` ↦
`completeReader`; `complete_agents` ↦ `completeAgents`.

**Not ported:** nothing (every Rocq definition and lemma has a Lean twin).
-/
import Weak.WeakRobustMain

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std Wlabel

/-! ## §1 Block structure on the abstract LTS -/

/-- A label that APPENDS a message — the fulfil-carrying shapes. -/
def lbWrites (l : Wlabel) : Bool :=
  match l with
  | LStore .. | LRmw .. | LExStore .. => true
  | LSilent | LLoad .. | LFence .. | LDev .. | LRegW .. | LCtrl _ | LInstr | LExLoad ..
  | LIFetch .. => false

/-- A label that READS (a fetch is not a reads-of source: deviation 4). -/
def lbLoads (l : Wlabel) : Bool :=
  match l with
  | LLoad .. | LRmw .. | LExLoad .. => true
  | LSilent | LStore .. | LFence .. | LDev .. | LRegW .. | LCtrl _ | LInstr | LExStore ..
  | LIFetch .. => false

/-- The shape conditions the promise-free store/rmw rules impose on a label; the
two split labels are still refused (see the Rocq comment: the RMW split). -/
def lbOk (l : Wlabel) : Prop :=
  match l with
  | LStore _ _ data _ _ => data ≠ []
  | LRmw _ _ _ tvs data _ _ => data ≠ [] ∧ tvs.length = data.length
  | LExLoad .. | LExStore .. => False
  | LSilent | LLoad .. | LFence .. | LDev .. | LRegW .. | LCtrl _ | LInstr | LIFetch .. => True

theorem lookupInsertSelf {A : Type _} (l : List A) (i : Nat) (x y : A) :
    l[i]? = some y → (l.set i x)[i]? = some x :=
  fun h => list_lookup_insert (lookup_lt_Some h)

theorem lookupInsertOther {A : Type _} (l : List A) (i : Nat) (x : A) (j : Nat) :
    j ≠ i → (l.set i x)[j]? = l[j]? :=
  fun h => list_lookup_insert_ne (Ne.symm h)

theorem lbWritesTsNone {P : Type} (img : Image) (log : List Wmsg) (i : Nat) (ag : Wpagent P)
    (l : Wlabel) (f : Wstate → Wstate) (Dl : Option Nat) :
    astepOk img log i ag l f Dl → lbWrites l = false → Dl = none := by
  intro hok hw
  have h := astepOkTsNone img log i ag l f Dl hok
  cases l <;> first | exact h | simp [lbWrites] at hw

section shape

variable {P D : Type}
variable (pstep : P → D → Wlabel → P → D → Prop)
variable (dflt : D)
variable (atBoundary : P → Prop)
variable (ad : P → Wlabel → Prop)

/-- THE BLOCK DISCIPLINE (store-last; the A/D write-back is an `LRmw` strictly
inside its block). -/
structure BlkShape : Prop where
  bsStoreLast : ∀ p d l p' d',
    pstep p d l p' d' → lbWrites l = true → ¬ ad p l → atBoundary p'
  bsAdRmw : ∀ p d l p' d',
    pstep p d l p' d' → ad p l →
    ∃ aq rl base tvs data asrc vsrc, l = LRmw aq rl base tvs data asrc vsrc
  bsAdMid : ∀ p d l p' d', pstep p d l p' d' → ad p l → ¬ atBoundary p'

include dflt in
/-- STORE-LAST, on a trace: a non-A/D write event leaves its agent at a boundary. -/
theorem blkTraceBoundary (img : Image) (log : List Wmsg) (i : Nat) (T : Atrace P D) (k : Nat)
    (ev : Aev D) (ag ag' : Wpagent P) :
    BlkShape pstep atBoundary ad → atraceWf pstep img log i T →
    T.atEvs[k]? = some ev → T.atAgs[k]? = some ag → T.atAgs[k + 1]? = some ag' →
    lbWrites ev.aeLb = true → ¬ ad ag.paSt ev.aeLb →
    atBoundary ag'.paSt := by
  intro hbs hwf hev hag hag' hw hnad
  obtain ⟨ag0, ag0', st', f, hag0, hag0', hps, _, hagne⟩ :=
    astepsWfStep pstep img log i T.atAgs T.atEvs k ev hwf hev
  have h1 : ag0 = ag := Option.some.inj (hag0.symm.trans hag)
  have h2 : ag0' = ag' := Option.some.inj (hag0'.symm.trans hag')
  rw [h1] at hps
  obtain ⟨d, d', hps⟩ := astepProgStep pstep dflt ag ev st' hps
  rw [← h2, hagne]
  exact hbs.bsStoreLast _ _ _ _ _ hps hw hnad

/-- SUB-BLOCK BOUNDARIES: a boundary, or the point just after an A/D write-back. -/
def atBoundaryAd (p : P) : Prop :=
  atBoundary p ∨ ∃ q d l d', pstep q d l p d' ∧ ad q l

theorem atBoundaryAdIntro (p : P) : atBoundary p → atBoundaryAd pstep atBoundary ad p :=
  Or.inl

end shape

/-! ## §2 `imgTotal` and read admissibility -/

def imgTotalOn (A : Int → Prop) (img : Image) : Prop := ∀ a, A a → (img a).isSome

def imgTotal (img : Image) : Prop := ∀ a, (img a).isSome

theorem imgTotalOnAll (img : Image) : imgTotal img ↔ imgTotalOn (fun _ => True) img :=
  ⟨fun h a _ => h a, fun h a => h a trivial⟩

/-- Under a total image, the byte's LATEST write always holds a value. -/
theorem latestLogByte (img : Image) (log : List Wmsg) (a : Int) :
    (img a).isSome → (logByte img log (latestTs log a) a).isSome := by
  intro h
  exact latestTsSome img log a 0 (by rw [logByte0]; exact h)

/-- (i) READ ADMISSIBILITY, PER BYTE. -/
theorem byteReadableLatest (A : Int → Prop) (img : Image) (log : List Wmsg) (ws : Wstate)
    (vpre : Nat) (a : Int) :
    imgTotalOn A img → A a → max vpre (coh ws a) ≤ log.length →
    ∃ (t : Nat) (v : BitVec 8),
      logByte img log t a = some v ∧ readable img log ws vpre a t ∧
      ¬ writesIn log a t log.length := by
  intro hi hA hle
  have hs := latestLogByte img log a (hi a hA)
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hs
  exact ⟨latestTs log a, v, hv,
    latestReadable img log ws vpre a _ hle (latestTsLatest img log a hs), latestTsTop log a⟩

/-- The multi-byte form: a contiguous run of LATEST reads. -/
def readLatest (img : Image) (log : List Wmsg) (base : Int) (tvs : List (Nat × BitVec 8)) :
    Prop :=
  ∀ (j t : Nat) (v : BitVec 8), tvs[j]? = some (t, v) →
    logByte img log t (base + (j : Int)) = some v ∧
    ¬ writesIn log (base + (j : Int)) t log.length

theorem readLatestExists (img : Image) (log : List Wmsg) (base : Int) (n : Nat) :
    imgTotal img → ∃ tvs, tvs.length = n ∧ readLatest img log base tvs := by
  intro hi
  induction n with
  | zero => exact ⟨[], rfl, fun j t v hj => by simp at hj⟩
  | succ n ih =>
    obtain ⟨tvs, hlen, hrl⟩ := ih
    obtain ⟨v, hv⟩ :=
      Option.isSome_iff_exists.1 (latestLogByte img log (base + (n : Int)) (hi _))
    refine ⟨tvs ++ [(latestTs log (base + (n : Int)), v)], by simp [hlen], fun j t v' hj => ?_⟩
    by_cases hlt : j < n
    · rw [lookup_app_l (by omega)] at hj
      exact hrl j t v' hj
    · have hjn : j = n := by
        have := lookup_lt_Some hj
        simp only [List.length_append, List.length_singleton] at this
        omega
      rw [hjn] at hj ⊢
      rw [lookup_app_r (by omega), hlen, Nat.sub_self] at hj
      simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hj
      obtain ⟨rfl, rfl⟩ := hj
      exact ⟨hv, latestTsTop log _⟩

/-- THE LATEST READ IS ADMISSIBLE AT ANY PRE-VIEW, dependency view included. -/
theorem readLatestReadOkD (img : Image) (log : List Wmsg) (ws : Wstate) (aq lat : Bool)
    (base : Int) (tvs : List (Nat × BitVec 8)) (va : Nat) :
    wsBounded ws log.length → va ≤ log.length → readLatest img log base tvs →
    readOkD img log ws aq lat base tvs va := by
  intro hb hva hrl j t v hj
  obtain ⟨hlb, hnw⟩ := hrl j t v hj
  refine ⟨hlb, ⟨by simp [hlb], fun hw => hnw (writesInMonoHi log _ _ _ _ ?_ hw)⟩, fun _ => hnw⟩
  have hvp := loadVpreDBounded ws aq va log.length hb hva
  have hcoh := hb.2.2.2.2.2.2.1 (base + (j : Int))
  omega

theorem readLatestReadOk (img : Image) (log : List Wmsg) (ws : Wstate) (aq lat : Bool)
    (base : Int) (tvs : List (Nat × BitVec 8)) :
    wsBounded ws log.length → readLatest img log base tvs →
    readOk img log ws aq lat base tvs :=
  fun hb hrl => readLatestReadOkD img log ws aq lat base tvs 0 hb (Nat.zero_le _) hrl

theorem readLatestExclOk (img : Image) (log : List Wmsg) (i : Nat) (base : Int)
    (tvs : List (Nat × BitVec 8)) :
    readLatest img log base tvs → exclOk log i base tvs (log.length + 1) := by
  intro hrl j t v hj hw
  exact (hrl j t v hj).2 (writesInMonoHi log _ _ _ _ (by omega) (writesInByWritesIn log _ _ _ _ hw))

theorem readLatestTsLe (img : Image) (log : List Wmsg) (base : Int) (tvs : List (Nat × BitVec 8))
    (j t : Nat) (v : BitVec 8) :
    readLatest img log base tvs → tvs[j]? = some (t, v) → t ≤ log.length := by
  intro hrl hj
  exact logByteBounded img log t (base + (j : Int)) (by simp [(hrl j t v hj).1])

/-! ## §3 Promise-free completion of a block -/

section complete

variable {P D : Type}
variable (pstep : P → D → Wlabel → P → D → Prop)
variable (pcls : P → Wlabel → Wstate → WmClass)

/-- VALUE-ENABLEDNESS of the LTS (+ the Lean-only fetch field, deviation 4). -/
structure LtsEnabled : Prop where
  leLbOk : ∀ p d l p' d', pstep p d l p' d' → lbOk l
  leLoad : ∀ p d aq lat base tvs tvs' asrc p' d',
    List.length tvs = List.length tvs' → pstep p d (LLoad aq lat base tvs asrc) p' d' →
    ∃ p'' d'', pstep p d (LLoad aq lat base tvs' asrc) p'' d''
  leRmw : ∀ p d aq rl base tvs data tvs' asrc vsrc p' d',
    List.length tvs = List.length tvs' →
    pstep p d (LRmw aq rl base tvs data asrc vsrc) p' d' →
    ∃ data' p'' d'', data'.length = List.length data ∧
      pstep p d (LRmw aq rl base tvs' data' asrc vsrc) p'' d''
  leIfetch : ∀ p d base tvs tvs' p' d',
    List.length tvs = List.length tvs' → pstep p d (LIFetch base tvs) p' d' →
    ∃ p'' d'', pstep p d (LIFetch base tvs') p'' d''

/-- Lean-only (deviation 4): the fetch field is vacuous for a fetch-free program. -/
theorem leIfetchOfNoFetch :
    pstepNoFetch pstep →
    ∀ (p : P) (d : D) base tvs (tvs' : List (Nat × BitVec 8)) (p' : P) (d' : D),
      List.length tvs = List.length tvs' → pstep p d (LIFetch base tvs) p' d' →
      ∃ p'' d'', pstep p d (LIFetch base tvs') p'' d'' :=
  fun hnf p d base tvs _ p' d' _ hps => absurd rfl (hnf p d _ p' d' hps base tvs)

/-- Lean-only (deviation 4): Rocq's three-field constructor, for a fetch-free program. -/
theorem ltsEnabledOfNoFetch :
    pstepNoFetch pstep →
    (∀ p d l p' d', pstep p d l p' d' → lbOk l) →
    (∀ p d aq lat base tvs tvs' asrc p' d',
      List.length tvs = List.length tvs' → pstep p d (LLoad aq lat base tvs asrc) p' d' →
      ∃ p'' d'', pstep p d (LLoad aq lat base tvs' asrc) p'' d'') →
    (∀ p d aq rl base tvs data tvs' asrc vsrc p' d',
      List.length tvs = List.length tvs' →
      pstep p d (LRmw aq rl base tvs data asrc vsrc) p' d' →
      ∃ data' p'' d'', data'.length = List.length data ∧
        pstep p d (LRmw aq rl base tvs' data' asrc vsrc) p'' d'') →
    LtsEnabled pstep :=
  fun hnf h1 h2 h3 => ⟨h1, h2, h3, leIfetchOfNoFetch pstep hnf⟩

/-- A BLOCK IS A FINITE, NEVER-STUCK RUN. -/
structure BlkFin (atBoundary : P → Prop) (msr : P → Nat) : Prop where
  bfProg : ∀ p d, ¬ atBoundary p → ∃ l p' d', pstep p d l p' d'
  bfMeas : ∀ p d l p' d', pstep p d l p' d' → ¬ atBoundary p → msr p' < msr p

/-! ### The promise-free step, per agent -/

/-- A COMPLETION STEP by agent `i`, packaged with the log delta and its authorship. -/
def cstep (i : Nat) (c c' : Wpcfg P D) : Prop :=
  (∃ l, wpPfStep pstep pcls i l c c') ∧
  ∃ ms, c'.pcLog = c.pcLog ++ ms ∧ ∀ mq ∈ ms, mq.wmTid = some i

theorem cstepRun (i : Nat) (c c' : Wpcfg P D) :
    cstep pstep pcls i c c' → wpPfRun pstep pcls c c' :=
  fun ⟨⟨l, hs⟩, _⟩ => ⟨i, l, hs⟩

theorem cstepRtcRun (i : Nat) (c c' : Wpcfg P D) :
    rtc (cstep pstep pcls i) c c' → rtc (wpPfRun pstep pcls) c c' :=
  rtc_subrel (fun x y h => cstepRun pstep pcls i x y h)

/-- The step's SHAPE: image frozen, agent vector changed at `i` only, log grows. -/
theorem wpPfStepShape (i : Nat) (l : Wlabel) (c c' : Wpcfg P D) :
    wpPfStep pstep pcls i l c c' →
    c'.pcImg = c.pcImg ∧
    (∃ ag ag', c.pcAgs[i]? = some ag ∧ c'.pcAgs = c.pcAgs.set i ag' ∧ wsLe ag.paWs ag'.paWs) ∧
    (∃ ms, c'.pcLog = c.pcLog ++ ms ∧ ∀ mq ∈ ms, mq.wmTid = some i) := by
  intro h
  cases h with
  | PFSilent cfg ag st' dd hag _ =>
    exact ⟨rfl, ⟨ag, _, hag, rfl, wsLeRefl _⟩, [], by simp, by simp⟩
  | PFLoad cfg ag aq lat base tvs asrc st' dd hag _ _ =>
    exact ⟨rfl, ⟨ag, _, hag, rfl, loadPostRunDLe _ _ _ _ _⟩, [], by simp, by simp⟩
  | PFStore cfg ag rl base data asrc vsrc k st' dd hag _ _ _ =>
    exact ⟨rfl, ⟨ag, _, hag, rfl, storePostRunDLe _ _ _ _ _ _ _⟩, _, rfl, by simp⟩
  | PFRmw cfg ag aq rl base tvs data asrc vsrc k st' dd hag _ _ _ _ _ _ =>
    exact ⟨rfl, ⟨ag, _, hag, rfl,
      wsLeTrans (loadPostRunDLe _ _ _ _ _) (storePostRunDLe _ _ _ _ _ _ _)⟩, _, rfl,
      by simp⟩
  | PFFence cfg ag pr pw sr sw st' dd hag _ =>
    exact ⟨rfl, ⟨ag, _, hag, rfl, fencePostLe _ _ _ _ _⟩, [], by simp, by simp⟩
  | PFDev cfg ag st' dd hag _ =>
    exact ⟨rfl, ⟨ag, _, hag, rfl, wsLeRefl _⟩, [], by simp, by simp⟩
  | PFRegW cfg ag rd srcs st' dd hag _ =>
    exact ⟨rfl, ⟨ag, _, hag, rfl, regwPostLe _ _ _⟩, [], by simp, by simp⟩
  | PFCtrl cfg ag srcs st' dd hag _ =>
    exact ⟨rfl, ⟨ag, _, hag, rfl, ctrlPostLe _ _⟩, [], by simp, by simp⟩
  | PFInstr cfg ag st' dd hag _ =>
    exact ⟨rfl, ⟨ag, _, hag, rfl, instrPostLe _⟩, [], by simp, by simp⟩
  | PFExLoad cfg ag aq base tvs asrc st' dd hag _ _ =>
    exact ⟨rfl, ⟨ag, _, hag, rfl, exloadPostRunDLe _ _ _ _ _⟩, [], by simp, by simp⟩
  | PFExStore cfg ag rl base data asrc vsrc k R st' dd hag _ _ _ _ _ _ _ =>
    exact ⟨rfl, ⟨ag, _, hag, rfl, storePostRunDLe _ _ _ _ _ _ _⟩, _, rfl, by simp⟩
  | PFIFetch cfg ag base tvs st' dd hag _ _ =>
    exact ⟨rfl, ⟨ag, _, hag, rfl, wsLeRefl _⟩, [], by simp, by simp⟩

theorem wpPfStepFrame (i : Nat) (l : Wlabel) (c c' : Wpcfg P D) (j : Nat) :
    wpPfStep pstep pcls i l c c' → j ≠ i → c'.pcAgs[j]? = c.pcAgs[j]? := by
  intro hs hne
  obtain ⟨_, ⟨ag, ag', _, hins, _⟩, _⟩ := wpPfStepShape pstep pcls i l c c' hs
  rw [hins]
  exact lookupInsertOther _ _ _ _ hne

theorem wpPfStepAgsLen (i : Nat) (l : Wlabel) (c c' : Wpcfg P D) :
    wpPfStep pstep pcls i l c c' → c'.pcAgs.length = c.pcAgs.length := by
  intro hs
  obtain ⟨_, ⟨ag, ag', _, hins, _⟩, _⟩ := wpPfStepShape pstep pcls i l c c' hs
  rw [hins]
  exact length_insert

/-- The COHERENCE FLOOR only grows. -/
theorem wpPfStepObsFlr (i : Nat) (l : Wlabel) (c c' : Wpcfg P D) (j : Nat) (a : Int) :
    wpPfStep pstep pcls i l c c' → obsFlr c j a ≤ obsFlr c' j a := by
  intro hs
  obtain ⟨_, ⟨ag, ag', hag, hins, hle⟩, _⟩ := wpPfStepShape pstep pcls i l c c' hs
  unfold obsFlr
  rw [hins]
  by_cases hji : j = i
  · rw [hji, hag, lookupInsertSelf _ _ _ _ hag]
    exact wsLeCoh _ _ a hle
  · rw [lookupInsertOther _ _ _ _ hji]
    all_goals exact Nat.le_refl _

/-! ### Boundedness of the configuration -/

def cfgBnd (c : Wpcfg P D) : Prop :=
  ∀ (j : Nat) (ag : Wpagent P), c.pcAgs[j]? = some ag → wsBounded ag.paWs c.pcLog.length

/-- Lean-only helper: `cfgBnd` read at one agent. -/
theorem cfgBndLookup {c : Wpcfg P D} {j : Nat} {ag : Wpagent P} (h : cfgBnd c)
    (hag : c.pcAgs[j]? = some ag) : wsBounded ag.paWs c.pcLog.length := by
  unfold cfgBnd at h
  exact h j ag hag

theorem cfgBndInit (img : Image) (d0 : D) (ps : List P) : cfgBnd (wpInit img d0 ps) := by
  intro j ag hag
  simp only [wpInit, List.getElem?_map] at hag
  cases hp : ps[j]? with
  | none => rw [hp] at hag; cases hag
  | some p =>
    rw [hp] at hag
    cases hag
    exact wsBoundedInit _

theorem readOkTsLe (img : Image) (log : List Wmsg) (ws : Wstate) (aq lat : Bool) (base : Int)
    (tvs : List (Nat × BitVec 8)) (va j t : Nat) (v : BitVec 8) :
    readOkD img log ws aq lat base tvs va → tvs[j]? = some (t, v) → t ≤ log.length := by
  intro hro hj
  exact logByteBounded img log t (base + (j : Int)) (by simp [(hro j t v hj).1])

theorem readOkForall (img : Image) (log : List Wmsg) (ws : Wstate) (aq lat : Bool) (base : Int)
    (tvs : List (Nat × BitVec 8)) (va : Nat) :
    readOkD img log ws aq lat base tvs va → ∀ t ∈ tvs.map Prod.fst, t ≤ log.length := by
  intro hro t ht
  obtain ⟨⟨t0, v0⟩, hmem, rfl⟩ := List.mem_map.1 ht
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hmem
  exact readOkTsLe img log ws aq lat base tvs va j t0 v0 hro hj

/-- Lean-only helper: one agent's record replaced, the log possibly extended. -/
theorem cfgBndSet (c : Wpcfg P D) (log' : List Wmsg) (i : Nat) (ag ag' : Wpagent P) :
    cfgBnd c → c.pcAgs[i]? = some ag → c.pcLog.length ≤ log'.length →
    wsBounded ag'.paWs log'.length →
    ∀ (j : Nat) (ag2 : Wpagent P), (c.pcAgs.set i ag')[j]? = some ag2 → wsBounded ag2.paWs log'.length := by
  intro hb hag hlen hb' j ag2 hag2
  by_cases hji : j = i
  · rw [hji, lookupInsertSelf _ _ _ _ hag] at hag2
    cases hag2
    exact hb'
  · rw [lookupInsertOther _ _ _ _ hji] at hag2
    exact wsBoundedMono _ _ _ (cfgBndLookup hb hag2) hlen

theorem wpPfStepBnd (i : Nat) (l : Wlabel) (c c' : Wpcfg P D) :
    wpPfStep pstep pcls i l c c' → cfgBnd c → cfgBnd c' := by
  intro hs hb
  cases hs with
  | PFSilent cfg ag st' dd hag _ =>
    exact cfgBndSet c _ i ag _ hb hag (Nat.le_refl _) (cfgBndLookup (c := c) (ag := ag) hb hag)
  | PFLoad cfg ag aq lat base tvs asrc st' dd hag _ hro =>
    have hbag := cfgBndLookup hb hag
    exact cfgBndSet c _ i ag _ hb hag (Nat.le_refl _)
      (loadPostRunDBounded _ _ _ _ _ _ hbag (srcsViewBounded _ _ asrc hbag)
        (readOkForall _ _ _ _ _ _ _ _ hro))
  | PFStore cfg ag rl base data asrc vsrc k st' dd hag _ _ _ =>
    have hbag := cfgBndLookup hb hag
    have hva := srcsViewBounded _ _ asrc hbag
    have hvd := srcsViewBounded _ _ vsrc hbag
    exact cfgBndSet c _ i ag _ hb hag
      (by simp only [List.length_append, List.length_singleton]; omega)
      (storePostRunDBounded _ _ _ _ _ _ _ _ _ hbag
        (by simp only [List.length_append, List.length_singleton]; omega)
        (by simp only [List.length_append, List.length_singleton]; omega)
        (by simp only [List.length_append, List.length_singleton]; omega)
        (by simp only [List.length_append, List.length_singleton]; omega))
  | PFRmw cfg ag aq rl base tvs data asrc vsrc k st' dd hag _ _ _ hro _ _ =>
    have hbag := cfgBndLookup hb hag
    have hva := srcsViewBounded _ _ asrc hbag
    have hvd := srcsViewBounded _ _ vsrc hbag
    exact cfgBndSet c _ i ag _ hb hag
      (by simp only [List.length_append, List.length_singleton]; omega)
      (storePostRunDBounded _ _ _ _ _ _ _ c.pcLog.length _
        (loadPostRunDBounded _ _ _ _ _ _ hbag hva (readOkForall _ _ _ _ _ _ _ _ hro))
        (by simp only [List.length_append, List.length_singleton]; omega)
        (by simp only [List.length_append, List.length_singleton]; omega)
        (by simp only [List.length_append, List.length_singleton]; omega)
        (by simp only [List.length_append, List.length_singleton]; omega))
  | PFFence cfg ag pr pw sr sw st' dd hag _ =>
    exact cfgBndSet c _ i ag _ hb hag (Nat.le_refl _)
      (fencePostBounded _ _ _ _ _ _ (cfgBndLookup (c := c) (ag := ag) hb hag))
  | PFDev cfg ag st' dd hag _ =>
    exact cfgBndSet c _ i ag _ hb hag (Nat.le_refl _) (cfgBndLookup (c := c) (ag := ag) hb hag)
  | PFRegW cfg ag rd srcs st' dd hag _ =>
    have hbag := cfgBndLookup hb hag
    exact cfgBndSet c _ i ag _ hb hag (Nat.le_refl _)
      (regwPostBounded _ _ _ _ hbag (srcsViewBounded _ _ srcs hbag))
  | PFCtrl cfg ag srcs st' dd hag _ =>
    have hbag := cfgBndLookup hb hag
    exact cfgBndSet c _ i ag _ hb hag (Nat.le_refl _)
      (ctrlPostBounded _ _ _ hbag (srcsViewBounded _ _ srcs hbag))
  | PFInstr cfg ag st' dd hag _ =>
    exact cfgBndSet c _ i ag _ hb hag (Nat.le_refl _) (instrPostBounded _ _ (cfgBndLookup (c := c) (ag := ag) hb hag))
  | PFExLoad cfg ag aq base tvs asrc st' dd hag _ hro =>
    have hbag := cfgBndLookup hb hag
    exact cfgBndSet c _ i ag _ hb hag (Nat.le_refl _)
      (exloadPostRunDBounded _ _ _ _ _ _ hbag (srcsViewBounded _ _ asrc hbag)
        (readOkForall _ _ _ _ _ _ _ _ hro))
  | PFExStore cfg ag rl base data asrc vsrc k R st' dd hag _ _ _ _ _ _ _ =>
    have hbag := cfgBndLookup hb hag
    have hva := srcsViewBounded _ _ asrc hbag
    have hvd := srcsViewBounded _ _ vsrc hbag
    exact cfgBndSet c _ i ag _ hb hag
      (by simp only [List.length_append, List.length_singleton]; omega)
      (storePostRunDBounded _ _ _ _ _ _ _ _ _ hbag
        (by simp only [List.length_append, List.length_singleton]; omega)
        (by simp only [List.length_append, List.length_singleton]; omega)
        (by simp only [List.length_append, List.length_singleton]; omega)
        (by simp only [List.length_append, List.length_singleton]; omega))
  | PFIFetch cfg ag base tvs st' dd hag _ _ =>
    exact cfgBndSet c _ i ag _ hb hag (Nat.le_refl _) (cfgBndLookup (c := c) (ag := ag) hb hag)

/-! ### ONE completion step is always available -/

/-- Lean-only helper: a pf step of `i` is a completion step of `i`. -/
theorem cstepOfStep (i : Nat) (l : Wlabel) (c c' : Wpcfg P D) :
    wpPfStep pstep pcls i l c c' → cstep pstep pcls i c c' :=
  fun hs => ⟨⟨l, hs⟩, (wpPfStepShape pstep pcls i l c c' hs).2.2⟩

/-- THE ADMISSIBILITY THEOREM: under a total image and a bounded agent, ANY step the
program offers can be taken in the promise-free machine (reads at the latest writes). -/
theorem cstepAvailable (i : Nat) (c : Wpcfg P D) (ag : Wpagent P) (l : Wlabel) (p' : P) (dd : D) :
    LtsEnabled pstep → imgTotal c.pcImg →
    wsBounded ag.paWs c.pcLog.length →
    c.pcAgs[i]? = some ag → pstep ag.paSt c.pcDev l p' dd →
    ∃ c' ag', cstep pstep pcls i c c' ∧ c'.pcAgs[i]? = some ag' ∧
      ∃ l' d', pstep ag.paSt c.pcDev l' ag'.paSt d' := by
  intro hen hi hb hag hps
  cases l with
  | LSilent =>
    exact ⟨_, _, cstepOfStep pstep pcls _ _ _ _ (wpPfStep.PFSilent c ag p' dd hag hps),
      lookupInsertSelf _ _ _ _ hag, _, dd, hps⟩
  | LLoad aq lat base tvs asrc =>
    obtain ⟨tvs', hlen', hrl⟩ := readLatestExists c.pcImg c.pcLog base tvs.length hi
    obtain ⟨p'', dd', hps'⟩ := hen.leLoad _ _ aq lat base tvs tvs' asrc p' dd hlen'.symm hps
    have hro : readOkD c.pcImg c.pcLog ag.paWs aq lat base tvs' (srcsView ag.paWs asrc) :=
      readLatestReadOkD _ _ _ aq lat base tvs' _ hb (srcsViewBounded _ _ asrc hb) hrl
    exact ⟨_, _, cstepOfStep pstep pcls _ _ _ _
      (wpPfStep.PFLoad c ag aq lat base tvs' asrc p'' dd' hag hps' hro),
      lookupInsertSelf _ _ _ _ hag, _, dd', hps'⟩
  | LStore rl base data asrc vsrc =>
    have hne : data ≠ [] := hen.leLbOk _ _ _ _ _ hps
    exact ⟨_, _, cstepOfStep pstep pcls _ _ _ _
      (wpPfStep.PFStore c ag rl base data asrc vsrc _ p' dd hag hps hne rfl),
      lookupInsertSelf _ _ _ _ hag, _, dd, hps⟩
  | LRmw aq rl base tvs data asrc vsrc =>
    obtain ⟨hnedata, _⟩ : data ≠ [] ∧ tvs.length = data.length := hen.leLbOk _ _ _ _ _ hps
    obtain ⟨tvs', hlen', hrl⟩ := readLatestExists c.pcImg c.pcLog base tvs.length hi
    obtain ⟨data', p'', dd', hlend', hps'⟩ :=
      hen.leRmw _ _ aq rl base tvs data tvs' asrc vsrc p' dd hlen'.symm hps
    -- D-2r: the read half is at the plain floor
    have hro : readOk c.pcImg c.pcLog ag.paWs aq false base tvs' :=
      readLatestReadOk _ _ _ aq false base tvs' hb hrl
    have hex : exclOk c.pcLog i base tvs' (c.pcLog.length + 1) :=
      readLatestExclOk c.pcImg c.pcLog i base tvs' hrl
    have hne' : data' ≠ [] := by
      intro hnil
      rw [hnil] at hlend'
      apply hnedata
      cases data with
      | nil => rfl
      | cons _ _ => simp at hlend'
    have hlen2 : tvs'.length = data'.length := by
      have := hen.leLbOk _ _ _ _ _ hps
      simp only [lbOk] at this
      omega
    exact ⟨_, _, cstepOfStep pstep pcls _ _ _ _
      (wpPfStep.PFRmw c ag aq rl base tvs' data' asrc vsrc _ p'' dd' hag hps' hne' hlen2 hro hex
        rfl),
      lookupInsertSelf _ _ _ _ hag, _, dd', hps'⟩
  | LFence pr pw sr sw =>
    exact ⟨_, _, cstepOfStep pstep pcls _ _ _ _
      (wpPfStep.PFFence c ag pr pw sr sw p' dd hag hps), lookupInsertSelf _ _ _ _ hag, _, dd, hps⟩
  | LDev =>
    exact ⟨_, _, cstepOfStep pstep pcls _ _ _ _ (wpPfStep.PFDev c ag p' dd hag hps),
      lookupInsertSelf _ _ _ _ hag, _, dd, hps⟩
  | LRegW rd srcs =>
    exact ⟨_, _, cstepOfStep pstep pcls _ _ _ _ (wpPfStep.PFRegW c ag rd srcs p' dd hag hps),
      lookupInsertSelf _ _ _ _ hag, _, dd, hps⟩
  | LCtrl srcs =>
    exact ⟨_, _, cstepOfStep pstep pcls _ _ _ _ (wpPfStep.PFCtrl c ag srcs p' dd hag hps),
      lookupInsertSelf _ _ _ _ hag, _, dd, hps⟩
  | LInstr =>
    exact ⟨_, _, cstepOfStep pstep pcls _ _ _ _ (wpPfStep.PFInstr c ag p' dd hag hps),
      lookupInsertSelf _ _ _ _ hag, _, dd, hps⟩
  -- THE RMW SPLIT: `lbOk` still refutes the two split labels
  | LExLoad => exact (hen.leLbOk _ _ _ _ _ hps).elim
  | LExStore => exact (hen.leLbOk _ _ _ _ _ hps).elim
  -- O2 (deviation 4): every byte fetched at its latest write
  | LIFetch base tvs =>
    obtain ⟨tvs', hlen', hrl⟩ := readLatestExists c.pcImg c.pcLog base tvs.length hi
    obtain ⟨p'', dd', hps'⟩ := hen.leIfetch _ _ base tvs tvs' p' dd hlen'.symm hps
    have hif : ifetchOk c.pcImg c.pcLog 0 base tvs' :=
      fun j t v hj => (ifetchByteOk0 _ _ _ _ _).2 (hrl j t v hj).1
    exact ⟨_, _, cstepOfStep pstep pcls _ _ _ _
      (wpPfStep.PFIFetch c ag base tvs' p'' dd' hag hps' hif),
      lookupInsertSelf _ _ _ _ hag, _, dd', hps'⟩

theorem cstepBnd (i : Nat) (c c' : Wpcfg P D) :
    cstep pstep pcls i c c' → cfgBnd c → cfgBnd c' :=
  fun ⟨⟨l, hs⟩, _⟩ => wpPfStepBnd pstep pcls i l c c' hs

theorem cstepImg (i : Nat) (c c' : Wpcfg P D) : cstep pstep pcls i c c' → c'.pcImg = c.pcImg :=
  fun ⟨⟨l, hs⟩, _⟩ => (wpPfStepShape pstep pcls i l c c' hs).1

theorem cstepFrame (i : Nat) (c c' : Wpcfg P D) (j : Nat) :
    cstep pstep pcls i c c' → j ≠ i → c'.pcAgs[j]? = c.pcAgs[j]? :=
  fun ⟨⟨l, hs⟩, _⟩ hne => wpPfStepFrame pstep pcls i l c c' j hs hne

theorem cstepAgsLen (i : Nat) (c c' : Wpcfg P D) :
    cstep pstep pcls i c c' → c'.pcAgs.length = c.pcAgs.length :=
  fun ⟨⟨l, hs⟩, _⟩ => wpPfStepAgsLen pstep pcls i l c c' hs

theorem cstepObsFlr (i : Nat) (c c' : Wpcfg P D) (j : Nat) (a : Int) :
    cstep pstep pcls i c c' → obsFlr c j a ≤ obsFlr c' j a :=
  fun ⟨⟨l, hs⟩, _⟩ => wpPfStepObsFlr pstep pcls i l c c' j a hs

/-! The `rtc` closures. -/

theorem cstepsImg (i : Nat) (c c' : Wpcfg P D) :
    rtc (cstep pstep pcls i) c c' → c'.pcImg = c.pcImg := by
  intro h
  induction h with
  | refl => rfl
  | tail _ hs ih => exact (cstepImg pstep pcls i _ _ hs).trans ih

theorem cstepsBnd (i : Nat) (c c' : Wpcfg P D) :
    rtc (cstep pstep pcls i) c c' → cfgBnd c → cfgBnd c' := by
  intro h
  induction h with
  | refl => exact id
  | tail _ hs ih => exact fun hb => cstepBnd pstep pcls i _ _ hs (ih hb)

theorem cstepsFrame (i : Nat) (c c' : Wpcfg P D) (j : Nat) :
    rtc (cstep pstep pcls i) c c' → j ≠ i → c'.pcAgs[j]? = c.pcAgs[j]? := by
  intro h hne
  induction h with
  | refl => rfl
  | tail _ hs ih => exact (cstepFrame pstep pcls i _ _ j hs hne).trans ih

theorem cstepsAgsLen (i : Nat) (c c' : Wpcfg P D) :
    rtc (cstep pstep pcls i) c c' → c'.pcAgs.length = c.pcAgs.length := by
  intro h
  induction h with
  | refl => rfl
  | tail _ hs ih => exact (cstepAgsLen pstep pcls i _ _ hs).trans ih

theorem cstepsObsFlr (i : Nat) (c c' : Wpcfg P D) (j : Nat) (a : Int) :
    rtc (cstep pstep pcls i) c c' → obsFlr c j a ≤ obsFlr c' j a := by
  intro h
  induction h with
  | refl => exact Nat.le_refl _
  | tail _ hs ih => exact Nat.le_trans ih (cstepObsFlr pstep pcls i _ _ j a hs)

theorem cstepsLog (i : Nat) (c c' : Wpcfg P D) :
    rtc (cstep pstep pcls i) c c' →
    ∃ ms, c'.pcLog = c.pcLog ++ ms ∧ ∀ mq ∈ ms, mq.wmTid = some i := by
  intro h
  induction h with
  | refl => exact ⟨[], by simp, by simp⟩
  | tail _ hs ih =>
    obtain ⟨ms, hms, hall⟩ := ih
    obtain ⟨_, ms', hms', hall'⟩ := hs
    refine ⟨ms ++ ms', by rw [hms', hms, List.append_assoc], fun mq hmq => ?_⟩
    rcases List.mem_append.1 hmq with h | h
    · exact hall mq h
    · exact hall' mq h

/-! ### THE BLOCK COMPLETION THEOREM -/

/-- The induction runs on the MEASURE (a bound `n`). -/
theorem completeBlockAux (atBoundary : P → Prop) [∀ p, Decidable (atBoundary p)]
    (msr : P → Nat) (i n : Nat) :
    LtsEnabled pstep → BlkFin pstep atBoundary msr →
    ∀ (c : Wpcfg P D) (ag : Wpagent P), msr ag.paSt ≤ n →
      imgTotal c.pcImg → cfgBnd c → c.pcAgs[i]? = some ag →
      ∃ c' ag', rtc (cstep pstep pcls i) c c' ∧ c'.pcAgs[i]? = some ag' ∧
        atBoundary ag'.paSt := by
  intro hen hfin
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro c ag hn hi hb hag
    by_cases hbd : atBoundary ag.paSt
    · exact ⟨c, ag, rtc_refl _, hag, hbd⟩
    obtain ⟨l, p', dd, hps⟩ := hfin.bfProg ag.paSt c.pcDev hbd
    obtain ⟨c1, ag1, hstep, hag1, l', d', hps'⟩ :=
      cstepAvailable pstep pcls i c ag l p' dd hen hi (cfgBndLookup (c := c) (ag := ag) hb hag) hag hps
    have hlt : msr ag1.paSt < msr ag.paSt := hfin.bfMeas _ _ _ _ _ hps' hbd
    obtain ⟨c', ag', hrun, hag', hbd'⟩ :=
      ih (msr ag1.paSt) (by omega) c1 ag1 (Nat.le_refl _)
        (by rw [cstepImg pstep pcls i c c1 hstep]; exact hi)
        (cstepBnd pstep pcls i c c1 hstep hb) hag1
    exact ⟨c', ag', rtc_l hstep hrun, hag', hbd'⟩

theorem completeBlock (atBoundary : P → Prop) [∀ p, Decidable (atBoundary p)]
    (msr : P → Nat) (i : Nat) (c : Wpcfg P D) (ag : Wpagent P) :
    LtsEnabled pstep → BlkFin pstep atBoundary msr →
    imgTotal c.pcImg → cfgBnd c → c.pcAgs[i]? = some ag →
    ∃ c' ag', rtc (cstep pstep pcls i) c c' ∧ c'.pcAgs[i]? = some ag' ∧
      atBoundary ag'.paSt :=
  fun hen hfin hi hb hag =>
    completeBlockAux pstep pcls atBoundary msr i (msr ag.paSt) hen hfin c ag (Nat.le_refl _)
      hi hb hag

end complete

/-! ## §4 The cone-cut theorem -/

/-- Lean-only helper: the FIRST edge of a `tc` path. -/
theorem tcHeadInv {A : Type _} {R : A → A → Prop} {x z : A} :
    tc R x z → ∃ y, R x y ∧ (y = z ∨ tc R y z) := by
  intro h
  induction h with
  | single h => exact ⟨_, h, Or.inl rfl⟩
  | tail _ hyz ih =>
    obtain ⟨y, hxy, hy⟩ := ih
    refine ⟨y, hxy, Or.inr ?_⟩
    rcases hy with rfl | hy
    · exact tc_once hyz
    · exact tc_r hy hyz

section cone

variable {P D : Type}
variable (pstep : P → D → Wlabel → P → D → Prop)
variable (dflt : D)

/-- THE STRUCTURAL FACT: only `gpo` can leave a non-fulfil. -/
theorem gdep2SrcFulfilOrPo (TS : Ptraces P D) (e1 e2 : Gev) :
    gdep2 TS e1 e2 → (∃ ts, gevTs TS e1 = some ts) ∨ WeakRobustGraph.gpo TS e1 e2 := by
  rintro ((hpo | ⟨ts, a, hts, _⟩) | ⟨r, l, a, ts, tstar, that, _, _, _, _, h1, _⟩)
  · exact Or.inr hpo
  · exact Or.inl ⟨ts, hts⟩
  · exact Or.inl ⟨tstar, h1⟩

/-- EVERY CROSS EDGE EMANATES FROM A FULFIL. -/
theorem crossEdgeFulfil (TS : Ptraces P D) (e1 e2 : Gev) :
    gdep2 TS e1 e2 → e1.1 ≠ e2.1 → ∃ ts, gevTs TS e1 = some ts := by
  intro hd hne
  rcases gdep2SrcFulfilOrPo TS e1 e2 hd with h | ⟨hag, _⟩
  · exact h
  · exact absurd hag hne

/-- THE CONE: the processed set is exactly the wf strict ancestry of `r`. -/
def coneOf (TS : Ptraces P D) (dn : List Gev) (r : Gev) : Prop :=
  ∀ e, e ∈ dn ↔ (gevWf TS e ∧ tc (gdep2 TS) e r)

/-- THE CUT IS A FULFIL, for any agent other than the reader. -/
theorem cutLastFulfil (TS : Ptraces P D) (dn : List Gev) (r : Gev) (j : Nat) (T : Atrace P D)
    (m : Nat) :
    ptracesWf pstep TS → qorder TS dn → coneOf TS dn r → j ≠ r.1 →
    TS.ptTrs[j]? = some T → nproc dn j = m + 1 →
    m < T.atEvs.length →
    ∃ ts, gevTs TS (j, m) = some ts := by
  intro _ hq hcone hne hT hn hlen
  have hwfm : gevWf TS (j, m) := (gevWfBounds TS (j, m)).2 ⟨T, hT, hlen⟩
  have hin : (j, m) ∈ dn := (qorderMem TS dn j m hq).2 ⟨hwfm, by omega⟩
  have htc : tc (gdep2 TS) (j, m) r := ((hcone _).1 hin).2
  obtain ⟨y, hd, hy⟩ := tcHeadInv htc
  rcases gdep2SrcFulfilOrPo TS (j, m) y hd with hf | hpo
  · exact hf
  exfalso
  obtain ⟨hag, hlt, _, hwfy⟩ := hpo
  dsimp only at hag hlt
  have hyin : y ∈ dn := by
    refine (hcone y).2 ⟨hwfy, ?_⟩
    rcases hy with hyr | h
    · rw [hyr] at hag; exact absurd hag hne
    · exact h
  have hy2 : (j, y.2) ∈ dn := by
    rw [hag]
    exact hyin
  have := ((qorderMem TS dn j y.2 hq).1 hy2).2
  omega

include dflt in
/-- THE CONE-CUT THEOREM: every NON-READER cut lands at a block boundary, or at a
mid-block A/D write-back CAS (an `LRmw` fulfil). -/
theorem coneBoundaryThm (atBoundary : P → Prop) (ad : P → Wlabel → Prop)
    [∀ p l, Decidable (ad p l)]
    (TS : Ptraces P D) (dn : List Gev) (r : Gev) (j : Nat) (T : Atrace P D) (agn : Wpagent P) :
    ptracesWf pstep TS →
    BlkShape pstep atBoundary ad →
    (∀ (i : Nat) (T0 : Atrace P D) (ag0 : Wpagent P), TS.ptTrs[i]? = some T0 → T0.atAgs[0]? = some ag0 → atBoundary ag0.paSt) →
    qorder TS dn → coneOf TS dn r → j ≠ r.1 →
    TS.ptTrs[j]? = some T → T.atAgs[nproc dn j]? = some agn →
    atBoundary agn.paSt ∨
    (∃ m ag ev,
       nproc dn j = m + 1 ∧
       T.atAgs[m]? = some ag ∧ T.atEvs[m]? = some ev ∧
       (∃ ts, ev.aeTs = some ts) ∧
       (∃ aq rl base tvs data asrc vsrc, ev.aeLb = LRmw aq rl base tvs data asrc vsrc) ∧
       ad ag.paSt ev.aeLb) := by
  intro hwf hbs hinit hq hcone hne hT hagn
  have hatr : atraceWf pstep TS.ptImg TS.ptLog j T := hwf j T hT
  have hlens : T.atAgs.length = T.atEvs.length + 1 := astepsWfLen pstep _ _ _ _ _ hatr
  cases hn : nproc dn j with
  | zero =>
    rw [hn] at hagn
    exact Or.inl (hinit j T agn hT hagn)
  | succ m =>
    rw [hn] at hagn
    have hmlt : m < T.atEvs.length := by
      have := lookup_lt_Some hagn
      omega
    obtain ⟨ts, hts⟩ := cutLastFulfil pstep TS dn r j T m hwf hq hcone hne hT hn hmlt
    obtain ⟨T', ev, hT', hev, htsev⟩ := gevTsSome TS (j, m) ts hts
    dsimp only at hT' hev
    have hTT : T' = T := Option.some.inj (hT'.symm.trans hT)
    rw [hTT] at hev
    obtain ⟨ag, hag⟩ :=
      Option.isSome_iff_exists.1 (lookup_lt_is_Some_2 (l := T.atAgs) (i := m) (by omega))
    obtain ⟨ag0, ag0', st', f, hag0, _, hps, hok, _⟩ :=
      astepsWfStep pstep _ _ _ _ _ m ev hatr hev
    have h1 : ag0 = ag := Option.some.inj (hag0.symm.trans hag)
    rw [h1] at hps hok
    have hw : lbWrites ev.aeLb = true := by
      cases hlw : lbWrites ev.aeLb
      · rw [lbWritesTsNone _ _ _ _ _ _ _ hok hlw] at htsev
        cases htsev
      · rfl
    by_cases had : ad ag.paSt ev.aeLb
    · refine Or.inr ⟨m, ag, ev, rfl, hag, hev, ⟨ts, htsev⟩, ?_, had⟩
      obtain ⟨dd, dd', hps⟩ := astepProgStep pstep dflt ag ev st' hps
      exact hbs.bsAdRmw _ _ _ _ _ hps had
    · exact Or.inl (blkTraceBoundary pstep dflt atBoundary ad _ _ j T m ev ag agn hbs hatr hev
        hag hagn hw had)

include dflt in
/-- THE SUB-BLOCK FORM: with post-A/D points admitted as boundaries, EVERY non-reader
cut is a boundary. -/
theorem coneBoundarySub (atBoundary : P → Prop) (ad : P → Wlabel → Prop)
    [∀ p l, Decidable (ad p l)]
    (TS : Ptraces P D) (dn : List Gev) (r : Gev) (j : Nat) (T : Atrace P D) (agn : Wpagent P) :
    ptracesWf pstep TS →
    BlkShape pstep atBoundary ad →
    (∀ (i : Nat) (T0 : Atrace P D) (ag0 : Wpagent P), TS.ptTrs[i]? = some T0 → T0.atAgs[0]? = some ag0 → atBoundary ag0.paSt) →
    qorder TS dn → coneOf TS dn r → j ≠ r.1 →
    TS.ptTrs[j]? = some T → T.atAgs[nproc dn j]? = some agn →
    atBoundaryAd pstep atBoundary ad agn.paSt := by
  intro hwf hbs hinit hq hcone hne hT hagn
  rcases coneBoundaryThm pstep dflt atBoundary ad TS dn r j T agn hwf hbs hinit hq hcone hne hT
      hagn with hb | ⟨m, ag, ev, hn, hag, hev, _, _, had⟩
  · exact Or.inl hb
  have hatr : atraceWf pstep TS.ptImg TS.ptLog j T := hwf j T hT
  obtain ⟨ag0, ag0', st', f, hag0, hag0', hps, _, hagne⟩ :=
    astepsWfStep pstep _ _ _ _ _ m ev hatr hev
  have h1 : ag0 = ag := Option.some.inj (hag0.symm.trans hag)
  rw [h1] at hps
  obtain ⟨dd, dd', hps⟩ := astepProgStep pstep dflt ag ev st' hps
  rw [hn] at hagn
  have h2 : ag0' = agn := Option.some.inj (hag0'.symm.trans hagn)
  refine Or.inr ⟨ag.paSt, dd, ev.aeLb, dd', ?_, had⟩
  rw [← h2, hagne]
  exact hps

end cone

/-! ## §5 The completion lemmas: the violation survives -/

section persist

variable {P D : Type}
variable (pstep : P → D → Wlabel → P → D → Prop)
variable (pcls : P → Wlabel → Wstate → WmClass)

/-- `WeakRobust.violation` with its witness NAMED. -/
def violatesAt (c : Wpcfg P D) (p : Nat) (m : Wmsg) (i j : Nat) (a : Int) : Prop :=
  c.pcLog[p]? = some m ∧ m.wmTid = some i ∧ clsOf m = .SCowned ∧
  ¬ pubOf c (p + 1) ∧ j ≠ i ∧ (msgByte m a).isSome ∧
  p + 1 ≤ obsFlr c j a

theorem violatesAtViolation (c : Wpcfg P D) (p : Nat) (m : Wmsg) (i j : Nat) (a : Int) :
    violatesAt c p m i j a → violation clsOf (pubOf (P := P) (D := D)) c :=
  fun h => ⟨p, m, i, j, a, h⟩

theorem violationViolatesAt (c : Wpcfg P D) :
    violation clsOf (pubOf (P := P) (D := D)) c →
    ∃ p m i j a, violatesAt c p m i j a :=
  fun ⟨p, m, i, j, a, h⟩ => ⟨p, m, i, j, a, h⟩

/-- …and the HART-RESTRICTED violation has such a witness with both indices bounded. -/
theorem violationHartViolatesAt (nh : Nat) (c : Wpcfg P D) :
    violationHart clsOf (pubOf (P := P) (D := D)) nh c →
    ∃ p m i j a, violatesAt c p m i j a ∧ i < nh ∧ j < nh := by
  rintro ⟨p, m, i, j, a, hlog, htid, ⟨i', hi', hilt⟩, hcls, hpub, hne, ⟨j', hj', hjlt⟩,
    hbyte, hobs⟩
  have hii : i' = i := Option.some.inj (hi'.symm.trans htid)
  have hjj : j' = j := (Option.some.inj hj').symm
  refine ⟨p, m, i, j, a, ⟨hlog, htid, hcls, hpub, hne, hbyte, hobs⟩, ?_, ?_⟩
  · rw [← hii]; exact hilt
  · rw [← hjj]; exact hjlt

/-! ### THE PERSISTENCE CORE -/

theorem violatesAtAppend (c c' : Wpcfg P D) (p : Nat) (m : Wmsg) (i j : Nat) (a : Int)
    (ms : List Wmsg) :
    c'.pcLog = c.pcLog ++ ms →
    (∀ mq ∈ ms, mq.wmTid ≠ some i ∨ mq.wmAk ≠ .WCrel) →
    obsFlr c j a ≤ obsFlr c' j a →
    violatesAt c p m i j a → violatesAt c' p m i j a := by
  rintro hlog hall hflr ⟨hp, htid, hcls, hpub, hne, hbyte, hobs⟩
  have hp' : c'.pcLog[p]? = some m := by
    rw [hlog]
    exact lookup_app_l_Some hp
  refine ⟨hp', htid, hcls, ?_, hne, hbyte, by omega⟩
  rintro ⟨p2, m2, heq, hlog2, hwp⟩
  have hp2 : p2 = p := by omega
  rw [hp2] at hlog2 hwp
  rw [hp'] at hlog2
  have hm2 : m2 = m := (Option.some.inj hlog2).symm
  rw [hm2] at hwp
  apply hpub
  refine ⟨p, m, rfl, hp, ?_⟩
  obtain ⟨q, mq, hle, hq, htidq, hrel⟩ := hwp
  refine ⟨q, mq, hle, ?_, htidq, hrel⟩
  by_cases hlt : q < c.pcLog.length
  · rw [hlog, lookup_app_l hlt] at hq
    exact hq
  · exfalso
    rw [hlog, lookup_app_r (by omega)] at hq
    have hmem : mq ∈ ms := List.mem_iff_getElem?.2 ⟨_, hq⟩
    rcases hall mq hmem with h | h
    · exact h (htidq.trans htid)
    · exact h hrel

/-- A violation survives ANY agent's completion, as long as that agent is not the
violating message's AUTHOR. -/
theorem completeCutPersists (k : Nat) (c c' : Wpcfg P D) (p : Nat) (m : Wmsg) (i j : Nat)
    (a : Int) :
    rtc (cstep pstep pcls k) c c' → k ≠ i →
    violatesAt c p m i j a → violatesAt c' p m i j a := by
  intro hrun hne hv
  obtain ⟨ms, hlog, hall⟩ := cstepsLog pstep pcls k c c' hrun
  refine violatesAtAppend c c' p m i j a ms hlog ?_ (cstepsObsFlr pstep pcls k c c' j a hrun) hv
  intro mq hmq
  left
  rw [hall mq hmq]
  intro h
  exact hne (Option.some.inj h)

/-! ### THE TWO PACKAGED LEMMAS L3 CONSUMES -/

/-- COMPLETE A CUT AGENT (any agent other than the violating message's author). -/
theorem completeCut (atBoundary : P → Prop) [∀ p, Decidable (atBoundary p)] (msr : P → Nat)
    (k : Nat) (c : Wpcfg P D) (ag : Wpagent P) (p : Nat) (m : Wmsg) (i j : Nat) (a : Int) :
    LtsEnabled pstep → BlkFin pstep atBoundary msr →
    imgTotal c.pcImg → cfgBnd c →
    c.pcAgs[k]? = some ag → k ≠ i →
    violatesAt c p m i j a →
    ∃ c' ag',
      rtc (wpPfRun pstep pcls) c c' ∧
      c'.pcAgs[k]? = some ag' ∧ atBoundary ag'.paSt ∧
      violatesAt c' p m i j a ∧
      c'.pcImg = c.pcImg ∧ cfgBnd c' ∧
      c'.pcAgs.length = c.pcAgs.length ∧
      (∀ j', j' ≠ k → c'.pcAgs[j']? = c.pcAgs[j']?) := by
  intro hen hfin hi hb hag hne hv
  obtain ⟨c', ag', hrun, hag', hbd⟩ :=
    completeBlock pstep pcls atBoundary msr k c ag hen hfin hi hb hag
  exact ⟨c', ag', cstepRtcRun pstep pcls k c c' hrun, hag', hbd,
    completeCutPersists pstep pcls k c c' p m i j a hrun hne hv,
    cstepsImg pstep pcls k c c' hrun, cstepsBnd pstep pcls k c c' hrun hb,
    cstepsAgsLen pstep pcls k c c' hrun,
    fun j' hj' => cstepsFrame pstep pcls k c c' j' hrun hj'⟩

/-- COMPLETE THE READER (mid-block by necessity; `j ≠ i` is a conjunct of the violation). -/
theorem completeReader (atBoundary : P → Prop) [∀ p, Decidable (atBoundary p)]
    (msr : P → Nat) (c : Wpcfg P D) (ag : Wpagent P) (p : Nat) (m : Wmsg) (i j : Nat)
    (a : Int) :
    LtsEnabled pstep → BlkFin pstep atBoundary msr →
    imgTotal c.pcImg → cfgBnd c →
    c.pcAgs[j]? = some ag →
    violatesAt c p m i j a →
    ∃ c' ag',
      rtc (wpPfRun pstep pcls) c c' ∧
      c'.pcAgs[j]? = some ag' ∧ atBoundary ag'.paSt ∧
      violatesAt c' p m i j a ∧
      c'.pcImg = c.pcImg ∧ cfgBnd c' ∧
      c'.pcAgs.length = c.pcAgs.length ∧
      (∀ j', j' ≠ j → c'.pcAgs[j']? = c.pcAgs[j']?) :=
  fun hen hfin hi hb hag hv =>
    completeCut pstep pcls atBoundary msr j c ag p m i j a hen hfin hi hb hag hv.2.2.2.2.1 hv

/-! ### ALL CUT AGENTS AT ONCE -/

theorem completeAgents (atBoundary : P → Prop) [∀ p, Decidable (atBoundary p)]
    (msr : P → Nat) (ks : List Nat) (c : Wpcfg P D) (p : Nat) (m : Wmsg) (i j : Nat) (a : Int) :
    LtsEnabled pstep → BlkFin pstep atBoundary msr →
    imgTotal c.pcImg → cfgBnd c →
    ks.Nodup → (∀ k, k ∈ ks → k ≠ i) →
    violatesAt c p m i j a →
    ∃ c',
      rtc (wpPfRun pstep pcls) c c' ∧
      violatesAt c' p m i j a ∧
      c'.pcImg = c.pcImg ∧ cfgBnd c' ∧
      c'.pcAgs.length = c.pcAgs.length ∧
      (∀ k ag, k ∈ ks → c'.pcAgs[k]? = some ag → atBoundary ag.paSt) ∧
      (∀ k, k ∉ ks → c'.pcAgs[k]? = c.pcAgs[k]?) := by
  intro hen hfin
  induction ks generalizing c with
  | nil =>
    intro _ hb _ _ hv
    exact ⟨c, rtc_refl _, hv, rfl, hb, rfl, fun k ag hk => by simp at hk, fun _ _ => rfl⟩
  | cons k ks ih =>
    intro hi hb hnd hks hv
    obtain ⟨hnk, hnd⟩ := List.nodup_cons.1 hnd
    have hks' : ∀ k0, k0 ∈ ks → k0 ≠ i := fun k0 hk0 => hks k0 (List.mem_cons_of_mem _ hk0)
    cases hag : c.pcAgs[k]? with
    | none =>
      obtain ⟨c', hrun, hv', himg, hb', hlen, hbd, hfr⟩ := ih c hi hb hnd hks' hv
      refine ⟨c', hrun, hv', himg, hb', hlen, ?_, ?_⟩
      · intro k0 ag0 hk0 hag0
        rcases List.mem_cons.1 hk0 with heq | hk0
        · rw [heq, hfr k hnk, hag] at hag0
          cases hag0
        · exact hbd k0 ag0 hk0 hag0
      · intro k0 hk0
        exact hfr k0 (fun h => hk0 (List.mem_cons_of_mem _ h))
    | some ag =>
      obtain ⟨c1, ag1, hrun1, hag1, hbd1, hv1, himg1, hb1, hlen1, hfr1⟩ :=
        completeCut pstep pcls atBoundary msr k c ag p m i j a hen hfin hi hb hag
          (hks k (by simp)) hv
      obtain ⟨c', hrun, hv', himg, hb', hlen, hbd, hfr⟩ :=
        ih c1 (by rw [himg1]; exact hi) hb1 hnd hks' hv1
      refine ⟨c', rtc_transitive hrun1 hrun, hv', himg.trans himg1, hb', hlen.trans hlen1, ?_, ?_⟩
      · intro k0 ag0 hk0 hag0
        rcases List.mem_cons.1 hk0 with heq | hk0
        · rw [heq, hfr k hnk, hag1] at hag0
          cases hag0
          exact hbd1
        · exact hbd k0 ag0 hk0 hag0
      · intro k0 hk0
        rw [hfr k0 (fun h => hk0 (List.mem_cons_of_mem _ h))]
        exact hfr1 k0 (fun h => hk0 (by rw [h]; simp))

end persist

end Weak
