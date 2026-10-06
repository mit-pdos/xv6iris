/-
Weak: **the EXTENDED dependency graph D⁺ = gdep ∪ gE and its SUBSET topological
sort** (M6 W2b, design items (ii) and (iv)), plus the FABRIC-ORDERED graph
`gdep3 = gdep2 ∪ gdev` (G3) and its acyclicity criteria.

Rocq: `iris/WeakRobustOrd.v` @ xxvzwolszwmp.

The Rocq header, in substance.  W2b's delay simulation replays a traced
behavior as a promise-free run processing the events in a topological order of
the dependency graph; a toposort of `gdep = gpo ∪ grf` alone is NOT enough (the
"floor inversion" counterexample: a stale write with a high timestamp sorted
below an acquired message blocks the very read the behavior performed).  The
fix is a BIGGER graph: for every read `r` of byte `a` the behavior's read floor
is `F(r,a) = max (load_vpre, coh a)` at `r`'s pre-state; the FLOOR-PROTECTION
edges `gE` order the fulfil of every LEAF of that floor before the fulfil of
every byte-`a` write strictly above it.  Leaves, not maxima: π is not monotone,
so only pointwise statements about σ on leaves transport (`WeakRobustProv`).

THE DELIVERABLES.  (1) TRACE-PREFIX LEAF STATES `preLstate`, bridged to the
real `Wstate` by `preLstateLrel` (via `astepsWsFold` and `lrelAevsPostId`).
(2) READ FLOORS `rdLeaves`/`rdFloor` (guarded on the label being a read) and
the E edges `gE`, the graph `gdep2`; every E edge is timestamp-increasing
(`gETsLt`).  (3) DECIDABILITY of `gE`/`gdep2`/`gdep3`, every existential
bounded.  (4) THE SUBSET TOPOSORT over an arbitrary edge relation `R` on a
DOWNWARD-CLOSED subset `S` (`topoSortS`, the induction principle
`toposortIndS`), the full case as one instantiation (`topoSortFull`,
`toposortIndFull`).  (5) THE FABRIC-ORDERED GRAPH `gdep3`, the rank criterion
`gdep3AcyclicOfRank`, the instances (same-agent, dev-free, empty witness), the
DEVICE EPOCH (`depoch`, the residue `devEpochOk`) and the exact condition
`devWitOk` (A0′, `gdep3AcyclicOfWit`), implied by the epoch one
(`devWitOkOfEpoch`).  DEPENDENCY-FREE: no Iris, no Sail.

**Deviations from Rocq.**

1. NAMES: lowerCamelCase as `Weak/WeakMem.lean` deviation 1.  No name of this
   file is in `notes/weak-port-dupnames.json`.  Rocq's `lb_aq` here is
   `WeakRobustAcyc.lb_aq` (the last import), i.e. `WeakRobustAcyc.lbAq`.
2. VOCABULARY: as `WeakRobustLin` deviation 2 (`l !! i` ↦ `l[i]?`, `NoDup` ↦
   `List.Nodup`, `Exists` ↦ bounded `∃ x ∈ l`, `Decision` ↦ `Decidable`,
   `RelDecision` ↦ `DecidableRel`, `filter` ↦ `List.filter (decide ∘ S)`),
   `is_Some o` ↦ `o.isSome`, `S m` ↦ `m + 1`, `Nat.max` ↦ `max`,
   `bool_decide (p) then a else b` ↦ `if p then a else b`, `PDevs d []` ↦
   `⟨d, []⟩`.  `Corollary`/`Theorem` ↦ `theorem`.
3. O2 / owner decision D4 (`LIFetch`, `Weak/WeakPromise.lean` deviation 8):
   `rdLeaves` maps `LIFetch` to `[]` (a fetch is not a reads-of source,
   `WeakRobustGraph` deviation 4), and `rdFloorWs`'s label guard maps it to
   `False`.  For every Rocq label the definitions agree.
4. SECTION VARIABLES: Rocq's `subset` section (`TS R RelDecision Rwf Rpo S
   Decision`) and `ordwf` section (`pstep`, `pdev`) become explicit (resp.
   instance) arguments of exactly the declarations whose Rocq closure keeps
   them, in Rocq's order; `pdev` is unused (no statement mentions it).
   `toposortIndS`'s step binder `done` is `dn` (`WeakRobustLin` deviation 4).
5. `tc` is core `Relation.TransGen` (built from the LAST step): `tcSubrel`,
   `tcRankLe`, `tcUnionRank`, `depochTcGdep2Le` and `tcGdep3Wit` go by tail
   induction (Rocq: head-style `induction 1`); statements unchanged.
   `toposortIndS`'s bounded induction is kept.
6. Lean-only helper (no Rocq twin): `memRdLeaves` (the read-arm unfolding of
   `rdLeaves`, used by `rdLeavesLeaf`).

**Rocq → Lean name map.**  `tc_subrel` ↦ `tcSubrel`; `tc_rank_le` ↦
`tcRankLe`; `tc_union_rank` ↦ `tcUnionRank`; `acyclic_union_rank` ↦
`acyclicUnionRank`; `pre_lstate` ↦ `preLstate`; `pre_lstate_tr` ↦
`preLstateTr`; `pre_lstate_leaf_occurs` ↦ `preLstateLeafOccurs`; `rd_leaves` ↦
`rdLeaves`; `rd_leaves_leaf` ↦ `rdLeavesLeaf`; `rd_floor` ↦ `rdFloor`;
`rd_leaves_wf` ↦ `rdLeavesWf`; `msg_writes` ↦ `msgWrites`; `msg_writes_dec` ↦
`msgWritesDec`; `gE_at` ↦ `gEAt`; `gE` ↦ `gE`; `gdep2` ↦ `gdep2`;
`gdep2_acyclic` ↦ `gdep2Acyclic`; `gdep_gdep2` ↦ `gdepGdep2`; `gE_gdep2` ↦
`gEGdep2`; `gpo_gdep2` ↦ `gpoGdep2`; `grf_gdep2` ↦ `grfGdep2`;
`tc_gdep_gdep2` ↦ `tcGdepGdep2`; `gdep2_acyclic_gdep` ↦ `gdep2AcyclicGdep`;
`gE_at_wf_r` ↦ `gEAtWfR`; `gE_wf` ↦ `gEWf`; `gdep2_wf` ↦ `gdep2Wf`;
`gE_ts_lt` ↦ `gETsLt`; `gE_ts_lt_ex` ↦ `gETsLtEx`; `gE_at_dec` ↦ `gEAtDec`;
`gE_dec` ↦ `gEDec`; `gdep2_dec` ↦ `gdep2Dec`; `gE_rel_dec` ↦ `gERelDec`;
`gdep2_rel_dec` ↦ `gdep2RelDec`; `gdep3` ↦ `gdep3`; `gdep3_acyclic` ↦
`gdep3Acyclic`; `gdep2_gdep3` ↦ `gdep2Gdep3`; `gdev_gdep3` ↦ `gdevGdep3`;
`gdep_gdep3` ↦ `gdepGdep3`; `gpo_gdep3` ↦ `gpoGdep3`; `grf_gdep3` ↦
`grfGdep3`; `gE_gdep3` ↦ `gEGdep3`; `tc_gdep2_gdep3` ↦ `tcGdep2Gdep3`;
`gdep3_acyclic_gdep2` ↦ `gdep3AcyclicGdep2`; `gdep3_wf` ↦ `gdep3Wf`;
`gdep3_dec` ↦ `gdep3Dec`; `gdep3_rel_dec` ↦ `gdep3RelDec`;
`gdep3_acyclic_of_rank` ↦ `gdep3AcyclicOfRank`; `gdep3_same_agent_gdep2` ↦
`gdep3SameAgentGdep2`; `gdep3_acyclic_same_agent` ↦ `gdep3AcyclicSameAgent`;
`gdep3_no_gdev_gdep2` ↦ `gdep3NoGdevGdep2`; `gdep3_acyclic_no_gdev` ↦
`gdep3AcyclicNoGdev`; `gdev_devfree` ↦ `gdevDevfree`; `gdep3_acyclic_devfree`
↦ `gdep3AcyclicDevfree`; `gdep3_nil_gdep2` ↦ `gdep3NilGdep2`;
`gdep3_acyclic_nodev` ↦ `gdep3AcyclicNodev`; `dep_go` ↦ `depGo`; `dep_go_lb`
↦ `depGoLb`; `dep_go_ub` ↦ `depGoUb`; `dep_go_mono` ↦ `depGoMono`; `depoch`
↦ `depoch`; `depoch_lb` ↦ `depochLb`; `depoch_dev` ↦ `depochDev`;
`depoch_gpo_le` ↦ `depochGpoLe`; `depoch_gdev_lt` ↦ `depochGdevLt`;
`dev_epoch_ok` ↦ `devEpochOk`; `dev_epoch_ok_nil` ↦ `devEpochOkNil`;
`depoch_gdep2_le` ↦ `depochGdep2Le`; `tc_gdep3_epoch` ↦ `tcGdep3Epoch`;
`gdep3_acyclic_at_epoch` ↦ `gdep3AcyclicAtEpoch`; `gdep3_acyclic_epoch` ↦
`gdep3AcyclicEpoch`; `dev_wit_ok` ↦ `devWitOk`; `dev_wit_ok_nil` ↦
`devWitOkNil`; `dev_wit_ok_short` ↦ `devWitOkShort`; `dev_wit_ok_devfree` ↦
`devWitOkDevfree`; `depoch_tc_gdep2_le` ↦ `depochTcGdep2Le`;
`dev_wit_ok_of_epoch` ↦ `devWitOkOfEpoch`; `tc_gdep3_wit` ↦ `tcGdep3Wit`;
`gdep3_acyclic_at_wit` ↦ `gdep3AcyclicAtWit`; `gdep3_acyclic_of_wit` ↦
`gdep3AcyclicOfWit`; `dc` ↦ `dc`; `sub_ok` ↦ `subOk`; `dc_full` ↦ `dcFull`;
`sub_ok_full` ↦ `subOkFull`; `dc_mono` ↦ `dcMono`; `topo_order_S` ↦
`topoOrderS`; `gev_enum_S` ↦ `gevEnumS`; `elem_of_gev_enum_S` ↦
`elemOfGevEnumS`; `NoDup_gev_enum_S` ↦ `nodupGevEnumS`; `topo_sort_S` ↦
`topoSortS`; `topo_sort_S_pack` ↦ `topoSortSPack`; `topo_order_S_wf` ↦
`topoOrderSWf`; `topo_order_S_index_unique` ↦ `topoOrderSIndexUnique`;
`topo_prefix_closed_S` ↦ `topoPrefixClosedS`; `topo_pred_done_S` ↦
`topoPredDoneS`; `topo_not_in_prefix_S` ↦ `topoNotInPrefixS`;
`topo_agent_lt_S` ↦ `topoAgentLtS`; `topo_agent_mono_S` ↦ `topoAgentMonoS`;
`dc_agent_prefix` ↦ `dcAgentPrefix`; `sub_ok_agent_prefix` ↦
`subOkAgentPrefix`; `toposort_ind_S` ↦ `toposortIndS`; `topo_sort_full` ↦
`topoSortFull`; `toposort_ind_full` ↦ `toposortIndFull`; `ptraces_ws_init` ↦
`ptracesWsInit`; `ptraces_of_ws_init` ↦ `ptracesOfWsInit`; `pre_lstate_lrel`
↦ `preLstateLrel`; `rd_floor_ws` ↦ `rdFloorWs`.

**Not ported:** nothing.
-/
import Weak.WeakRobustProv
import Weak.WeakRobustAcyc
import Weak.WeakRobustLin

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std Wlabel

/-! ## A RANK CRITERION FOR THE ACYCLICITY OF A UNION

`R` splits into a part a rank never DECREASES along and a part it strictly
INCREASES along; then any `R` cycle is a cycle of the first part. -/

theorem tcSubrel {A : Type _} (R R' : A → A → Prop) :
    (∀ u v, R u v → R' u v) → ∀ x y, tc R x y → tc R' x y := by
  intro hsub x y h
  induction h with
  | single h => exact tc_once (hsub _ _ h)
  | tail _ h ih => exact tc_r ih (hsub _ _ h)

theorem tcRankLe {A : Type _} (R : A → A → Prop) (rk : A → Nat) :
    (∀ u v, R u v → rk u ≤ rk v) → ∀ x y, tc R x y → rk x ≤ rk y := by
  intro hle x y h
  induction h with
  | single h => exact hle _ _ h
  | tail _ h ih => exact Nat.le_trans ih (hle _ _ h)

theorem tcUnionRank {A : Type _} (R R1 R2 : A → A → Prop) (rk : A → Nat) :
    (∀ u v, R u v → R1 u v ∨ R2 u v) →
    (∀ u v, R1 u v → rk u ≤ rk v) →
    (∀ u v, R2 u v → rk u < rk v) →
    ∀ x y, tc R x y → tc R1 x y ∨ rk x < rk y := by
  intro hsplit hle hlt x y h
  induction h with
  | single h =>
    rcases hsplit _ _ h with h1 | h2
    · exact Or.inl (tc_once h1)
    · exact Or.inr (hlt _ _ h2)
  | @tail b c _ h ih =>
    rcases hsplit _ _ h with h1 | h2
    · rcases ih with ih | ih
      · exact Or.inl (tc_r ih h1)
      · have := hle _ _ h1; exact Or.inr (by omega)
    · rcases ih with ih | ih
      · have := tcRankLe R1 rk hle _ _ ih; have := hlt _ _ h2; exact Or.inr (by omega)
      · have := hlt _ _ h2; exact Or.inr (by omega)

theorem acyclicUnionRank {A : Type _} (R R1 R2 : A → A → Prop) (rk : A → Nat) :
    (∀ u v, R u v → R1 u v ∨ R2 u v) →
    (∀ u v, R1 u v → rk u ≤ rk v) →
    (∀ u v, R2 u v → rk u < rk v) →
    (∀ e, ¬ tc R1 e e) →
    ∀ e, ¬ tc R e e := by
  intro hsplit hle hlt hacyc e hc
  rcases tcUnionRank R R1 R2 rk hsplit hle hlt e e hc with hc1 | hlt'
  · exact hacyc e hc1
  · omega

section ord

variable {P D : Type}

/-! ## DELIVERABLE 1: TRACE-PREFIX LEAF STATES -/

/-- The leaf state of `e`'s trace STRICTLY BEFORE `e` (`linit`, junk, for an
ill-formed `e`). -/
def preLstate (TS : Ptraces P D) (e : Gev) : Lstate :=
  match TS.ptTrs[e.1]? with
  | some T => laevsPost (T.atEvs.take e.2) linit
  | none => linit

theorem preLstateTr (TS : Ptraces P D) (e : Gev) (T : Atrace P D) :
    TS.ptTrs[e.1]? = some T →
    preLstate TS e = laevsPost (T.atEvs.take e.2) linit := by
  intro h; unfold preLstate; rw [h]

/-- Every leaf of a prefix leaf state is a timestamp SOME event of that prefix
read or fulfilled. -/
theorem preLstateLeafOccurs (TS : Ptraces P D) (e : Gev) (T : Atrace P D) (t : Nat) :
    TS.ptTrs[e.1]? = some T → lstateLeaf (preLstate TS e) t →
    evTsOccurs (T.atEvs.take e.2) t := by
  intro hT hl
  rw [preLstateTr TS e T hT] at hl
  exact laevsLeavesOccur _ t hl

/-! ## DELIVERABLE 2: READ FLOORS and the E EDGES -/

/-- The floor-leaf list of read `r` at byte `a`, GUARDED on the label (a
non-read event has no floor).  D2: the address-dependency leaves come first. -/
def rdLeaves (TS : Ptraces P D) (r : Gev) (a : Int) : List Nat :=
  match gevLb TS r with
  | some l =>
    match l with
    | LLoad .. | LRmw .. | LExLoad .. =>
      lsrcsView (preLstate TS r) (lbRasrc l)
        ++ lfloor (preLstate TS r) (WeakRobustAcyc.lbAq l) a
    | LSilent | LStore .. | LFence .. | LDev | LRegW .. | LCtrl _ | LInstr | LExStore ..
    | LIFetch .. => []
  | none => []

/-- Lean-only helper (deviation 6): the read-arm unfolding of `rdLeaves`. -/
theorem memRdLeaves (TS : Ptraces P D) (r : Gev) (a : Int) (t : Nat) :
    t ∈ rdLeaves TS r a →
    ∃ l, gevLb TS r = some l ∧
      t ∈ lsrcsView (preLstate TS r) (lbRasrc l)
        ++ lfloor (preLstate TS r) (WeakRobustAcyc.lbAq l) a := by
  unfold rdLeaves
  cases hl : gevLb TS r with
  | none => intro h; cases h
  | some l =>
    cases l <;> first | (intro h; exact ⟨_, rfl, h⟩) | (intro h; cases h)

theorem rdLeavesLeaf (TS : Ptraces P D) (r : Gev) (a : Int) (t : Nat) :
    t ∈ rdLeaves TS r a → lstateLeaf (preLstate TS r) t := by
  intro h
  obtain ⟨l, _, h⟩ := memRdLeaves TS r a t h
  rcases List.mem_append.1 h with h | h
  · exact lsrcsViewLeaf _ _ _ h
  · unfold lfloor at h
    rcases List.mem_append.1 h with h | h
    · exact lloadVpreLeaf _ _ _ h
    · exact lcohLeaf _ _ _ h

/-- The behavior's OWN floor number at that read. -/
def rdFloor (TS : Ptraces P D) (r : Gev) (a : Int) : Nat := lval id (rdLeaves TS r a)

theorem rdLeavesWf (TS : Ptraces P D) (r : Gev) (a : Int) (t : Nat) :
    t ∈ rdLeaves TS r a → gevWf TS r := by
  intro h
  obtain ⟨l, hl, _⟩ := memRdLeaves TS r a t h
  exact gevLbWf TS r l hl

/-- "`t` is a write of byte `a` at the log position timestamp `t` names". -/
def msgWrites (TS : Ptraces P D) (t : Nat) (a : Int) : Prop :=
  ∃ m, TS.ptLog[t - 1]? = some m ∧ (msgByte m a).isSome

instance msgWritesDec (TS : Ptraces P D) (t : Nat) (a : Int) : Decidable (msgWrites TS t a) :=
  match hm : TS.ptLog[t - 1]? with
  | none => isFalse (by
      rintro ⟨m', hm', _⟩
      rw [hm] at hm'; cases hm')
  | some m =>
    if hb : (msgByte m a).isSome then isTrue ⟨m, hm, hb⟩
    else isFalse (by
      rintro ⟨m', hm', hs⟩
      rw [hm] at hm'; cases hm'
      exact hb hs)

/-- THE FLOOR-PROTECTION EDGE, for a FIXED witnessing read `r`. -/
def gEAt (TS : Ptraces P D) (r e1 e2 : Gev) : Prop :=
  ∃ (l : Wlabel) (a : Int) (ts tstar that : Nat),
    gevLb TS r = some l ∧ (a, ts) ∈ lbReads l ∧
    tstar ∈ rdLeaves TS r a ∧ 0 < tstar ∧
    gevTs TS e1 = some tstar ∧
    gevTs TS e2 = some that ∧
    msgWrites TS that a ∧
    rdFloor TS r a < that

def gE (TS : Ptraces P D) (e1 e2 : Gev) : Prop := ∃ r, gEAt TS r e1 e2

/-- THE EXTENDED DEPENDENCY GRAPH D⁺. -/
def gdep2 (TS : Ptraces P D) (e1 e2 : Gev) : Prop := gdep TS e1 e2 ∨ gE TS e1 e2

def gdep2Acyclic (TS : Ptraces P D) : Prop := ∀ e, ¬ tc (gdep2 TS) e e

theorem gdepGdep2 (TS : Ptraces P D) (e1 e2 : Gev) : gdep TS e1 e2 → gdep2 TS e1 e2 := Or.inl
theorem gEGdep2 (TS : Ptraces P D) (e1 e2 : Gev) : gE TS e1 e2 → gdep2 TS e1 e2 := Or.inr
theorem gpoGdep2 (TS : Ptraces P D) (e1 e2 : Gev) :
    WeakRobustGraph.gpo TS e1 e2 → gdep2 TS e1 e2 := fun h => Or.inl (Or.inl h)
theorem grfGdep2 (TS : Ptraces P D) (e1 e2 : Gev) :
    WeakRobustGraph.grf TS e1 e2 → gdep2 TS e1 e2 := fun h => Or.inl (Or.inr h)

theorem tcGdepGdep2 (TS : Ptraces P D) (x y : Gev) : tc (gdep TS) x y → tc (gdep2 TS) x y :=
  tcSubrel _ _ (gdepGdep2 TS) x y

theorem gdep2AcyclicGdep (TS : Ptraces P D) : gdep2Acyclic TS → gdepAcyclic TS :=
  fun hac e hc => hac e (tcGdepGdep2 TS e e hc)

/-- The witnessing read of an E edge is a real event. -/
theorem gEAtWfR (TS : Ptraces P D) (r e1 e2 : Gev) : gEAt TS r e1 e2 → gevWf TS r := by
  rintro ⟨l, a, ts, tstar, that, hl, -⟩
  exact gevLbWf TS r l hl

theorem gEWf (TS : Ptraces P D) (e1 e2 : Gev) : gE TS e1 e2 → gevWf TS e1 ∧ gevWf TS e2 := by
  rintro ⟨r, l, a, ts, tstar, that, -, -, -, -, h1, h2, -⟩
  exact ⟨gevTsWf TS e1 _ h1, gevTsWf TS e2 _ h2⟩

theorem gdep2Wf (TS : Ptraces P D) (e1 e2 : Gev) :
    gdep2 TS e1 e2 → gevWf TS e1 ∧ gevWf TS e2 := by
  rintro (hd | hE)
  · exact gdepWf TS e1 e2 hd
  · exact gEWf TS e1 e2 hE

/-- EVERY E EDGE IS TIMESTAMP-INCREASING. -/
theorem gETsLt (TS : Ptraces P D) (e1 e2 : Gev) (t1 t2 : Nat) :
    gE TS e1 e2 → gevTs TS e1 = some t1 → gevTs TS e2 = some t2 → t1 < t2 := by
  rintro ⟨r, l, a, ts, tstar, that, -, -, hleaf, -, h1, h2, -, hlt⟩ ht1 ht2
  rw [h1] at ht1; cases ht1
  rw [h2] at ht2; cases ht2
  have hle : id t1 ≤ rdFloor TS r a := lvalGe id _ _ hleaf
  simp only [id] at hle
  omega

theorem gETsLtEx (TS : Ptraces P D) (e1 e2 : Gev) :
    gE TS e1 e2 → ∃ t1 t2, gevTs TS e1 = some t1 ∧ gevTs TS e2 = some t2 ∧ t1 < t2 := by
  intro hE
  obtain ⟨r, l, a, ts, tstar, that, -, -, -, -, h1, h2, -⟩ := id hE
  exact ⟨tstar, that, h1, h2, gETsLt TS e1 e2 tstar that hE h1 h2⟩

/-! ## DELIVERABLE 3: DECIDABILITY -/

instance gEAtDec (TS : Ptraces P D) (r e1 e2 : Gev) : Decidable (gEAt TS r e1 e2) :=
  match hl : gevLb TS r, h1 : gevTs TS e1, h2 : gevTs TS e2 with
  | none, _, _ => isFalse (by
      rintro ⟨l', -, -, -, -, hl', -⟩
      rw [hl] at hl'; cases hl')
  | some _, none, _ => isFalse (by
      rintro ⟨_, _, _, _, _, _, _, _, _, h1', _⟩
      rw [h1] at h1'; cases h1')
  | some _, some _, none => isFalse (by
      rintro ⟨_, _, _, _, _, _, _, _, _, _, h2', _⟩
      rw [h2] at h2'; cases h2')
  | some l, some tstar, some that =>
    if hex : 0 < tstar ∧ ∃ p ∈ lbReads l,
        tstar ∈ rdLeaves TS r p.1 ∧ msgWrites TS that p.1 ∧ rdFloor TS r p.1 < that then
      isTrue (by
        obtain ⟨hpos, ⟨a, ts⟩, hin, hleaf, hw, hlt⟩ := hex
        exact ⟨l, a, ts, tstar, that, hl, hin, hleaf, hpos, h1, h2, hw, hlt⟩)
    else
      isFalse (by
        rintro ⟨l', a, ts, tstar', that', hl', hin, hleaf, hpos, h1', h2', hw, hlt⟩
        rw [hl] at hl'; cases hl'
        rw [h1] at h1'; cases h1'
        rw [h2] at h2'; cases h2'
        exact hex ⟨hpos, (a, ts), hin, hleaf, hw, hlt⟩)

instance gEDec (TS : Ptraces P D) (e1 e2 : Gev) : Decidable (gE TS e1 e2) :=
  decidable_of_iff (∃ r ∈ gevEnum TS, gEAt TS r e1 e2)
    ⟨fun ⟨r, _, h⟩ => ⟨r, h⟩,
     fun ⟨r, h⟩ => ⟨r, (elemOfGevEnum TS r).2 (gEAtWfR TS r e1 e2 h), h⟩⟩

instance gdep2Dec (TS : Ptraces P D) (e1 e2 : Gev) : Decidable (gdep2 TS e1 e2) :=
  inferInstanceAs (Decidable (gdep TS e1 e2 ∨ gE TS e1 e2))

instance gERelDec (TS : Ptraces P D) : DecidableRel (gE TS) := fun _ _ => inferInstance
instance gdep2RelDec (TS : Ptraces P D) : DecidableRel (gdep2 TS) := fun _ _ => inferInstance

/-! ## THE FABRIC-ORDERED GRAPH D⁺⁺ = gdep2 ∪ gdev (G3)

ACYCLICITY IS A NEW OBLIGATION, NOT A COROLLARY (an rf edge may point
BACKWARDS in time in the promising machine).  Supplied here: the rank
criterion and the instances that discharge it outright. -/

def gdep3 (TS : Ptraces P D) (DS : Pdevs D) (e1 e2 : Gev) : Prop :=
  gdep2 TS e1 e2 ∨ gdev TS DS e1 e2

def gdep3Acyclic (TS : Ptraces P D) (DS : Pdevs D) : Prop := ∀ e, ¬ tc (gdep3 TS DS) e e

theorem gdep2Gdep3 (TS : Ptraces P D) (DS : Pdevs D) (e1 e2 : Gev) :
    gdep2 TS e1 e2 → gdep3 TS DS e1 e2 := Or.inl
theorem gdevGdep3 (TS : Ptraces P D) (DS : Pdevs D) (e1 e2 : Gev) :
    gdev TS DS e1 e2 → gdep3 TS DS e1 e2 := Or.inr
theorem gdepGdep3 (TS : Ptraces P D) (DS : Pdevs D) (e1 e2 : Gev) :
    gdep TS e1 e2 → gdep3 TS DS e1 e2 := fun h => gdep2Gdep3 TS DS e1 e2 (gdepGdep2 TS e1 e2 h)
theorem gpoGdep3 (TS : Ptraces P D) (DS : Pdevs D) (e1 e2 : Gev) :
    WeakRobustGraph.gpo TS e1 e2 → gdep3 TS DS e1 e2 :=
  fun h => gdep2Gdep3 TS DS e1 e2 (gpoGdep2 TS e1 e2 h)
theorem grfGdep3 (TS : Ptraces P D) (DS : Pdevs D) (e1 e2 : Gev) :
    WeakRobustGraph.grf TS e1 e2 → gdep3 TS DS e1 e2 :=
  fun h => gdep2Gdep3 TS DS e1 e2 (grfGdep2 TS e1 e2 h)
theorem gEGdep3 (TS : Ptraces P D) (DS : Pdevs D) (e1 e2 : Gev) :
    gE TS e1 e2 → gdep3 TS DS e1 e2 := fun h => gdep2Gdep3 TS DS e1 e2 (gEGdep2 TS e1 e2 h)

theorem tcGdep2Gdep3 (TS : Ptraces P D) (DS : Pdevs D) (x y : Gev) :
    tc (gdep2 TS) x y → tc (gdep3 TS DS) x y :=
  tcSubrel _ _ (gdep2Gdep3 TS DS) x y

theorem gdep3AcyclicGdep2 (TS : Ptraces P D) (DS : Pdevs D) :
    gdep3Acyclic TS DS → gdep2Acyclic TS :=
  fun hac e hc => hac e (tcGdep2Gdep3 TS DS e e hc)

theorem gdep3Wf (TS : Ptraces P D) (DS : Pdevs D) (e1 e2 : Gev) :
    ptracesWit TS DS → gdep3 TS DS e1 e2 → gevWf TS e1 ∧ gevWf TS e2 := by
  rintro hwit (h2 | hd)
  · exact gdep2Wf TS e1 e2 h2
  · exact gdevWf TS DS e1 e2 hwit hd

instance gdep3Dec (TS : Ptraces P D) (DS : Pdevs D) (e1 e2 : Gev) :
    Decidable (gdep3 TS DS e1 e2) :=
  inferInstanceAs (Decidable (gdep2 TS e1 e2 ∨ gdev TS DS e1 e2))
instance gdep3RelDec (TS : Ptraces P D) (DS : Pdevs D) : DecidableRel (gdep3 TS DS) :=
  fun _ _ => inferInstance

/-- THE CRITERION. -/
theorem gdep3AcyclicOfRank (TS : Ptraces P D) (DS : Pdevs D) (rk : Gev → Nat) :
    (∀ x y, gdep2 TS x y → rk x ≤ rk y) →
    (∀ x y, gdev TS DS x y → rk x < rk y) →
    gdep2Acyclic TS →
    gdep3Acyclic TS DS :=
  fun hle hlt hacyc e =>
    acyclicUnionRank (gdep3 TS DS) (gdep2 TS) (gdev TS DS) rk (fun _ _ h => h) hle hlt hacyc e

/-- INSTANCE 1: a witness that never crosses agents adds NOTHING. -/
theorem gdep3SameAgentGdep2 (TS : Ptraces P D) (DS : Pdevs D) (e1 e2 : Gev) :
    ptracesWit TS DS → (∀ x y, gdev TS DS x y → x.1 = y.1) →
    gdep3 TS DS e1 e2 → gdep2 TS e1 e2 := by
  rintro hwit hsa (h2 | hd)
  · exact h2
  · exact gpoGdep2 TS e1 e2 (gdevGpo TS DS e1 e2 hwit hd (hsa _ _ hd))

theorem gdep3AcyclicSameAgent (TS : Ptraces P D) (DS : Pdevs D) :
    ptracesWit TS DS → (∀ x y, gdev TS DS x y → x.1 = y.1) →
    gdep2Acyclic TS → gdep3Acyclic TS DS :=
  fun hwit hsa hacyc e hc =>
    hacyc e (tcSubrel _ _ (fun u v => gdep3SameAgentGdep2 TS DS u v hwit hsa) e e hc)

/-- INSTANCE 2 (the dev-free collapse). -/
theorem gdep3NoGdevGdep2 (TS : Ptraces P D) (DS : Pdevs D) (e1 e2 : Gev) :
    (∀ x y, ¬ gdev TS DS x y) → gdep3 TS DS e1 e2 → gdep2 TS e1 e2 := by
  rintro hno (h2 | hd)
  · exact h2
  · exact absurd hd (hno e1 e2)

theorem gdep3AcyclicNoGdev (TS : Ptraces P D) (DS : Pdevs D) :
    (∀ x y, ¬ gdev TS DS x y) → gdep2Acyclic TS → gdep3Acyclic TS DS :=
  fun hno hacyc e hc =>
    hacyc e (tcSubrel _ _ (fun u v => gdep3NoGdevGdep2 TS DS u v hno) e e hc)

theorem gdevDevfree (TS : Ptraces P D) (DS : Pdevs D) :
    ptracesWit TS DS →
    (∀ (i : Nat) (T : Atrace P D) (k : Nat) (ev : Aev D), TS.ptTrs[i]? = some T →
       T.atEvs[k]? = some ev → ev.aeDev = none) →
    ∀ x y, ¬ gdev TS DS x y := by
  rintro ⟨hW1, -⟩ hdf x y ⟨m, hm, -⟩
  obtain ⟨ev, hev, hs⟩ := hW1 m x hm
  unfold evAt at hev
  cases hT : TS.ptTrs[x.1]? with
  | none => rw [hT] at hev; cases hev
  | some T =>
    rw [hT] at hev
    rw [hdf x.1 T x.2 ev hT hev] at hs
    cases hs

theorem gdep3AcyclicDevfree (TS : Ptraces P D) (DS : Pdevs D) :
    ptracesWit TS DS →
    (∀ (i : Nat) (T : Atrace P D) (k : Nat) (ev : Aev D), TS.ptTrs[i]? = some T →
       T.atEvs[k]? = some ev → ev.aeDev = none) →
    gdep2Acyclic TS → gdep3Acyclic TS DS :=
  fun hwit hdf => gdep3AcyclicNoGdev TS DS (gdevDevfree TS DS hwit hdf)

theorem gdep3NilGdep2 (TS : Ptraces P D) (d : D) (e1 e2 : Gev) :
    gdep3 TS ⟨d, []⟩ e1 e2 → gdep2 TS e1 e2 :=
  gdep3NoGdevGdep2 TS ⟨d, []⟩ e1 e2 (fun x y => gdevNil TS d x y)

theorem gdep3AcyclicNodev (TS : Ptraces P D) (d : D) :
    gdep2Acyclic TS → gdep3Acyclic TS ⟨d, []⟩ :=
  gdep3AcyclicNoGdev TS ⟨d, []⟩ (fun x y => gdevNil TS d x y)

/-! ## THE DEVICE EPOCH (G5a)

SUPERSEDED AS A PREMISE (A0′) by `devWitOk` below; kept as the sufficient
condition with the per-edge shape.  The epoch of an event is the witness
position just past the LAST fabric-touching event of its own agent at or before
it.  `gpo` never lowers it, `gdev` raises it by one; an `grf`/`gE` edge may
lower it, which is the named residue `devEpochOk`. -/

/-- `depGo l e m`: `m + i + 1` for the LAST position `i` of `l` holding an event
of `e`'s agent at or before `e`, and `0` if there is none. -/
def depGo : List Gev → Gev → Nat → Nat
  | [], _, _ => 0
  | e' :: l', e, m =>
    max (if e'.1 = e.1 ∧ e'.2 ≤ e.2 then m + 1 else 0) (depGo l' e (m + 1))

theorem depGoLb (l : List Gev) (e : Gev) (m i : Nat) (e' : Gev) :
    l[i]? = some e' → e'.1 = e.1 → e'.2 ≤ e.2 → m + i + 1 ≤ depGo l e m := by
  induction l generalizing m i with
  | nil => intro hi; simp at hi
  | cons x l ih =>
    intro hi hag hle
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst hi
      simp only [depGo, if_pos (And.intro hag hle)]
      omega
    | succ i =>
      simp only [List.getElem?_cons_succ] at hi
      have := ih (m + 1) i hi hag hle
      simp only [depGo]
      omega

theorem depGoUb (l : List Gev) (e : Gev) (m N : Nat) :
    (∀ (i : Nat) (e' : Gev), l[i]? = some e' → e'.1 = e.1 → e'.2 ≤ e.2 → m + i + 1 ≤ N) →
    depGo l e m ≤ N := by
  induction l generalizing m with
  | nil => intro _; simp [depGo]
  | cons x l ih =>
    intro h
    simp only [depGo]
    apply Nat.max_le.2
    constructor
    · split
      · next hc =>
        have := h 0 x rfl hc.1 hc.2
        omega
      · omega
    · apply ih
      intro i e' hi hag hle
      have := h (i + 1) e' (by simpa using hi) hag hle
      omega

theorem depGoMono (l : List Gev) (e1 e2 : Gev) (m : Nat) :
    e1.1 = e2.1 → e1.2 ≤ e2.2 → depGo l e1 m ≤ depGo l e2 m := by
  intro hag hle
  induction l generalizing m with
  | nil => exact Nat.le_refl _
  | cons x l ih =>
    simp only [depGo]
    have := ih (m + 1)
    have hhead : (if x.1 = e1.1 ∧ x.2 ≤ e1.2 then m + 1 else 0)
        ≤ (if x.1 = e2.1 ∧ x.2 ≤ e2.2 then m + 1 else 0) := by
      split
      · next hc => rw [if_pos ⟨hc.1.trans hag, by omega⟩]; exact Nat.le_refl _
      · exact Nat.zero_le _
    omega

def depoch (DS : Pdevs D) (e : Gev) : Nat := depGo DS.pdOrd e 0

theorem depochLb (DS : Pdevs D) (e : Gev) (m : Nat) (e' : Gev) :
    DS.pdOrd[m]? = some e' → e'.1 = e.1 → e'.2 ≤ e.2 → m + 1 ≤ depoch DS e := by
  intro hm hag hle
  have := depGoLb DS.pdOrd e 0 m e' hm hag hle
  unfold depoch
  omega

/-- A LISTED event's epoch is its own witness index plus one. -/
theorem depochDev (TS : Ptraces P D) (DS : Pdevs D) (m : Nat) (e : Gev) :
    ptracesWit TS DS → DS.pdOrd[m]? = some e → depoch DS e = m + 1 := by
  rintro ⟨-, -, hW3, -⟩ hm
  have hlb : m + 1 ≤ depoch DS e := depochLb DS e m e hm rfl (Nat.le_refl _)
  have hub : depoch DS e ≤ m + 1 := by
    apply depGoUb
    intro i e' hi hag hle
    by_cases him : i ≤ m
    · omega
    · exfalso
      have hi' : DS.pdOrd[i]? = some (e.1, e'.2) := by rw [← hag]; exact hi
      have := hW3 m i e.1 e.2 e'.2 (by omega) hm hi'
      omega
  omega

theorem depochGpoLe (TS : Ptraces P D) (DS : Pdevs D) (e1 e2 : Gev) :
    WeakRobustGraph.gpo TS e1 e2 → depoch DS e1 ≤ depoch DS e2 := by
  rintro ⟨hag, hlt, -, -⟩
  exact depGoMono _ _ _ _ hag (by omega)

theorem depochGdevLt (TS : Ptraces P D) (DS : Pdevs D) (e1 e2 : Gev) :
    ptracesWit TS DS → gdev TS DS e1 e2 → depoch DS e1 < depoch DS e2 := by
  rintro hwit ⟨m, hm1, hm2⟩
  rw [depochDev TS DS m e1 hwit hm1, depochDev TS DS (m + 1) e2 hwit hm2]
  omega

/-- THE NAMED RESIDUE: no reads-from and no floor-protection edge runs
BACKWARDS across a fabric access. -/
def devEpochOk (TS : Ptraces P D) (DS : Pdevs D) : Prop :=
  ∀ e1 e2, (WeakRobustGraph.grf TS e1 e2 ∨ gE TS e1 e2) → depoch DS e1 ≤ depoch DS e2

theorem devEpochOkNil (TS : Ptraces P D) (d : D) : devEpochOk TS ⟨d, []⟩ :=
  fun _ _ _ => Nat.le_refl _

theorem depochGdep2Le (TS : Ptraces P D) (DS : Pdevs D) (e1 e2 : Gev) :
    devEpochOk TS DS → gdep2 TS e1 e2 → depoch DS e1 ≤ depoch DS e2 := by
  rintro hok ((hpo | hrf) | hE)
  · exact depochGpoLe TS DS e1 e2 hpo
  · exact hok e1 e2 (Or.inl hrf)
  · exact hok e1 e2 (Or.inr hE)

/-- THE SPLIT: a `gdep3` PATH is a `gdep2` path or it strictly raised the
epoch. -/
theorem tcGdep3Epoch (TS : Ptraces P D) (DS : Pdevs D) (x y : Gev) :
    ptracesWit TS DS → devEpochOk TS DS →
    tc (gdep3 TS DS) x y →
    tc (gdep2 TS) x y ∨ depoch DS x < depoch DS y :=
  fun hwit hok =>
    tcUnionRank (gdep3 TS DS) (gdep2 TS) (gdev TS DS) (depoch DS) (fun _ _ h => h)
      (fun u v => depochGdep2Le TS DS u v hok)
      (fun u v => depochGdevLt TS DS u v hwit) x y

/-- POINTWISE: an event off every `gdep2` cycle is off every `gdep3` cycle. -/
theorem gdep3AcyclicAtEpoch (TS : Ptraces P D) (DS : Pdevs D) (e : Gev) :
    ptracesWit TS DS → devEpochOk TS DS →
    ¬ tc (gdep2 TS) e e → ¬ tc (gdep3 TS DS) e e := by
  intro hwit hok hac hc
  rcases tcGdep3Epoch TS DS e e hwit hok hc with hc2 | hlt
  · exact hac hc2
  · omega

theorem gdep3AcyclicEpoch (TS : Ptraces P D) (DS : Pdevs D) :
    ptracesWit TS DS → devEpochOk TS DS →
    gdep2Acyclic TS → gdep3Acyclic TS DS :=
  fun hwit hok hac e => gdep3AcyclicAtEpoch TS DS e hwit hok (hac e)

/-! ## A0′: `devWitOk` — THE EXACT CONDITION ACYCLICITY NEEDS

THE WITNESS ORDER IS `gdep2`-CONSISTENT: no `gdep2` path runs from a later
listed fabric event back to an earlier one.  Free when the witness has fewer
than two entries, free on a dev-free bundle, and implied by `devEpochOk`. -/

def devWitOk (TS : Ptraces P D) (DS : Pdevs D) : Prop :=
  ∀ (m1 m2 : Nat) (e1 e2 : Gev), m1 < m2 →
    DS.pdOrd[m1]? = some e1 → DS.pdOrd[m2]? = some e2 →
    ¬ tc (gdep2 TS) e2 e1

theorem devWitOkNil (TS : Ptraces P D) (d : D) : devWitOk TS ⟨d, []⟩ := by
  intro m1 m2 e1 e2 _ hm1
  simp at hm1

/-- FREE ON THE §A5 REFUTING BUNDLE: one entry admits no pair `m1 < m2`. -/
theorem devWitOkShort (TS : Ptraces P D) (DS : Pdevs D) :
    DS.pdOrd.length ≤ 1 → devWitOk TS DS := by
  intro hlen m1 m2 e1 e2 hlt _ hm2
  have hb : m2 < DS.pdOrd.length := lookup_lt_Some hm2
  omega

/-- FREE ON A DEV-FREE BUNDLE. -/
theorem devWitOkDevfree (TS : Ptraces P D) (DS : Pdevs D) :
    ptracesWit TS DS →
    (∀ (i : Nat) (T : Atrace P D) (k : Nat) (ev : Aev D), TS.ptTrs[i]? = some T →
       T.atEvs[k]? = some ev → ev.aeDev = none) →
    devWitOk TS DS := by
  rintro ⟨hW1, -⟩ hdf m1 m2 e1 e2 _ hm1 _
  obtain ⟨ev, hev, hs⟩ := hW1 m1 e1 hm1
  unfold evAt at hev
  cases hT : TS.ptTrs[e1.1]? with
  | none => rw [hT] at hev; cases hev
  | some T =>
    rw [hT] at hev
    rw [hdf e1.1 T e1.2 ev hT hev] at hs
    cases hs

/-- The epoch never falls along a `gdep2` PATH under `devEpochOk`. -/
theorem depochTcGdep2Le (TS : Ptraces P D) (DS : Pdevs D) (e1 e2 : Gev) :
    devEpochOk TS DS → tc (gdep2 TS) e1 e2 → depoch DS e1 ≤ depoch DS e2 := by
  intro hok h
  induction h with
  | single h => exact depochGdep2Le TS DS _ _ hok h
  | tail _ h ih => exact Nat.le_trans ih (depochGdep2Le TS DS _ _ hok h)

theorem devWitOkOfEpoch (TS : Ptraces P D) (DS : Pdevs D) :
    ptracesWit TS DS → devEpochOk TS DS → devWitOk TS DS := by
  intro hwit hok m1 m2 e1 e2 hlt hm1 hm2 hc
  have hle := depochTcGdep2Le TS DS e2 e1 hok hc
  rw [depochDev TS DS m1 e1 hwit hm1, depochDev TS DS m2 e2 hwit hm2] at hle
  omega

/-- THE SPLIT, the `devWitOk` analogue of `tcGdep3Epoch`: a `gdep3` path is a
`gdep2` path, or it ENTERS the witness at `m1` and LEAVES it at a strictly
later `m2`, with plain `gdep2` runs on either side. -/
theorem tcGdep3Wit (TS : Ptraces P D) (DS : Pdevs D) (x y : Gev) :
    ptracesWit TS DS → devWitOk TS DS →
    tc (gdep3 TS DS) x y →
    tc (gdep2 TS) x y ∨
    ∃ (m1 m2 : Nat) (e1 e2 : Gev),
      DS.pdOrd[m1]? = some e1 ∧ DS.pdOrd[m2]? = some e2 ∧
      m1 < m2 ∧ rtc (gdep2 TS) x e1 ∧ rtc (gdep2 TS) e2 y := by
  intro hwit hok h
  induction h with
  | single hxy =>
    rcases hxy with h2 | ⟨m, hm, hsm⟩
    · exact Or.inl (tc_once h2)
    · exact Or.inr ⟨m, m + 1, _, _, hm, hsm, by omega, rtc_refl _, rtc_refl _⟩
  | @tail z y' _ hzy ih =>
    rcases hzy with h2 | ⟨m, hm, hsm⟩
    · rcases ih with hxz | ⟨m1, m2, e1, e2, hm1, hm2, hlt, hxe1, he2z⟩
      · exact Or.inl (tc_r hxz h2)
      · exact Or.inr ⟨m1, m2, e1, e2, hm1, hm2, hlt, hxe1, rtc_r he2z h2⟩
    · rcases ih with hxz | ⟨m1, m2, e1, e2, hm1, hm2, hlt, hxe1, he2z⟩
      · exact Or.inr ⟨m, m + 1, z, y', hm, hsm, by omega, tc_rtc hxz, rtc_refl _⟩
      · have hle : m2 ≤ m := by
          rcases rtc_tc.1 he2z with heq | htc
          · subst heq
            have := pdOrdIndexInj TS DS m2 m e2 hwit hm2 hm
            omega
          · by_cases hlt' : m < m2
            · exact absurd htc (hok m m2 z e2 hlt' hm hm2)
            · omega
        exact Or.inr ⟨m1, m + 1, e1, y', hm1, hsm, by omega, hxe1, rtc_refl _⟩

/-- POINTWISE, the form the EXHIBIT's cone consumes. -/
theorem gdep3AcyclicAtWit (TS : Ptraces P D) (DS : Pdevs D) (e : Gev) :
    ptracesWit TS DS → devWitOk TS DS →
    ¬ tc (gdep2 TS) e e → ¬ tc (gdep3 TS DS) e e := by
  intro hwit hok hac hc
  rcases tcGdep3Wit TS DS e e hwit hok hc with hc2 | ⟨m1, m2, e1, e2, hm1, hm2, hlt, hee1, he2e⟩
  · exact hac hc2
  · have he21 : rtc (gdep2 TS) e2 e1 := rtc_transitive he2e hee1
    rcases rtc_tc.1 he21 with heq | htc
    · subst heq
      have := pdOrdIndexInj TS DS m1 m2 e2 hwit hm1 hm2
      omega
    · exact hok m1 m2 e1 e2 hlt hm1 hm2 htc

/-- …and the global theorem: THE criterion the fabric-ordered graph is landed
on (A0′). -/
theorem gdep3AcyclicOfWit (TS : Ptraces P D) (DS : Pdevs D) :
    ptracesWit TS DS → gdep2Acyclic TS → devWitOk TS DS →
    gdep3Acyclic TS DS :=
  fun hwit hac hok e => gdep3AcyclicAtWit TS DS e hwit hok (hac e)

/-! ## DELIVERABLE 4, part 1: the SUBSET vocabulary (generalized over `R`) -/

/-- DOWNWARD CLOSURE under `R`. -/
def dc (TS : Ptraces P D) (R : Gev → Gev → Prop) (S : Gev → Prop) : Prop :=
  ∀ e e', S e → R e' e → gevWf TS e' → S e'

/-- A WELL-FORMED SUBSET: downward closed, and made of real events. -/
def subOk (TS : Ptraces P D) (R : Gev → Gev → Prop) (S : Gev → Prop) : Prop :=
  dc TS R S ∧ (∀ e, S e → gevWf TS e)

theorem dcFull (TS : Ptraces P D) (R : Gev → Gev → Prop) : dc TS R (gevWf TS) :=
  fun _ _ _ _ hwf => hwf

theorem subOkFull (TS : Ptraces P D) (R : Gev → Gev → Prop) : subOk TS R (gevWf TS) :=
  ⟨dcFull TS R, fun _ h => h⟩

/-- `dc` only ever SHRINKS when the relation grows. -/
theorem dcMono (TS : Ptraces P D) (R R' : Gev → Gev → Prop) (S : Gev → Prop) :
    (∀ x y, R x y → R' x y) → dc TS R' S → dc TS R S :=
  fun hsub hdc e e' hS hr hwf => hdc e e' hS (hsub _ _ hr) hwf

/-- The packaged conclusion of the subset sort. -/
def topoOrderS (TS : Ptraces P D) (R : Gev → Gev → Prop) (S : Gev → Prop)
    (order : List Gev) : Prop :=
  order.Nodup ∧
  (∀ e, e ∈ order ↔ (gevWf TS e ∧ S e)) ∧
  (∀ x y (i j : Nat), order[i]? = some x → order[j]? = some y → R x y → i < j)

end ord

/-! ## DELIVERABLE 4, part 2: THE SUBSET TOPOSORT -/

section subset

variable {P D : Type}

/-- THE CARRIER: the wf events satisfying `S`. -/
def gevEnumS (TS : Ptraces P D) (S : Gev → Prop) [DecidablePred S] : List Gev :=
  (gevEnum TS).filter (fun e => decide (S e))

theorem elemOfGevEnumS (TS : Ptraces P D) (S : Gev → Prop) [DecidablePred S] (e : Gev) :
    e ∈ gevEnumS TS S ↔ (gevWf TS e ∧ S e) := by
  rw [gevEnumS, List.mem_filter, elemOfGevEnum, decide_eq_true_iff]

theorem nodupGevEnumS (TS : Ptraces P D) (S : Gev → Prop) [DecidablePred S] :
    (gevEnumS TS S).Nodup :=
  (nodupGevEnum TS).filter _

/-- THE SORT: `WeakRobustLin`'s generic `topoSort` on the filtered carrier. -/
theorem topoSortS (TS : Ptraces P D) (R : Gev → Gev → Prop) [DecidableRel R]
    (S : Gev → Prop) [DecidablePred S] :
    (∀ e, ¬ tc R e e) →
    ∃ order : List Gev,
      order.Nodup ∧
      (∀ e, e ∈ order ↔ (gevWf TS e ∧ S e)) ∧
      (∀ x y (i j : Nat), order[i]? = some x → order[j]? = some y → R x y → i < j) := by
  intro hacyc
  obtain ⟨order, hnd, hmem, hord⟩ := topoSort R (gevEnumS TS S) hacyc (nodupGevEnumS TS S)
  exact ⟨order, hnd, fun e => (hmem e).trans (elemOfGevEnumS TS S e),
    fun x y i j hi hj hr => hord i j x y hi hj hr⟩

theorem topoSortSPack (TS : Ptraces P D) (R : Gev → Gev → Prop) [DecidableRel R]
    (S : Gev → Prop) [DecidablePred S] :
    (∀ e, ¬ tc R e e) → ∃ order, topoOrderS TS R S order := by
  intro hacyc
  obtain ⟨order, h1, h2, h3⟩ := topoSortS TS R S hacyc
  exact ⟨order, h1, h2, h3⟩

/-! ### Prefix closure — where DOWNWARD CLOSURE is spent -/

theorem topoOrderSWf (TS : Ptraces P D) (R : Gev → Gev → Prop) (S : Gev → Prop)
    (order : List Gev) (e : Gev) :
    topoOrderS TS R S order → e ∈ order → gevWf TS e ∧ S e :=
  fun ⟨_, hmem, _⟩ he => (hmem e).1 he

theorem topoOrderSIndexUnique (TS : Ptraces P D) (R : Gev → Gev → Prop) (S : Gev → Prop)
    (order : List Gev) (i j : Nat) (e : Gev) :
    topoOrderS TS R S order → order[i]? = some e → order[j]? = some e → i = j :=
  fun ⟨hnd, _, _⟩ hi hj => NoDup_lookup hnd hi hj

/-- No `R` edge points from OUTSIDE a prefix INTO it. -/
theorem topoPrefixClosedS (TS : Ptraces P D) (R : Gev → Gev → Prop)
    (Rwf : ∀ x y, R x y → gevWf TS x ∧ gevWf TS y) (S : Gev → Prop)
    (order : List Gev) (n : Nat) (x y : Gev) :
    topoOrderS TS R S order → dc TS R S →
    R x y → y ∈ order.take n → x ∈ order.take n := by
  rintro ⟨_, hmem, hord⟩ hdc hd hy
  obtain ⟨j, hj, hjn⟩ := elem_of_take.1 hy
  have hys : gevWf TS y ∧ S y := (hmem y).1 (elem_of_list_lookup_2 hj)
  have hxwf : gevWf TS x := (Rwf x y hd).1
  have hxs : S x := hdc y x hys.2 hd hxwf
  obtain ⟨i, hi⟩ := elem_of_list_lookup_1 ((hmem x).2 ⟨hxwf, hxs⟩)
  have hlt : i < j := hord x y i j hi hj hd
  exact elem_of_take.2 ⟨i, hi, by omega⟩

/-- The same fact at the exact step the induction takes. -/
theorem topoPredDoneS (TS : Ptraces P D) (R : Gev → Gev → Prop) (S : Gev → Prop)
    (order : List Gev) (n : Nat) (e : Gev) :
    topoOrderS TS R S order → dc TS R S → order[n]? = some e →
    ∀ e', R e' e → gevWf TS e' → e' ∈ order.take n := by
  rintro ⟨_, hmem, hord⟩ hdc hn e' hd hwf'
  have hes : gevWf TS e ∧ S e := (hmem e).1 (elem_of_list_lookup_2 hn)
  have hs' : S e' := hdc e e' hes.2 hd hwf'
  obtain ⟨i, hi⟩ := elem_of_list_lookup_1 ((hmem e').2 ⟨hwf', hs'⟩)
  have hlt : i < n := hord e' e i n hi hn hd
  exact elem_of_take.2 ⟨i, hi, hlt⟩

theorem topoNotInPrefixS (TS : Ptraces P D) (R : Gev → Gev → Prop) (S : Gev → Prop)
    (order : List Gev) (n : Nat) (e : Gev) :
    topoOrderS TS R S order → order[n]? = some e → e ∉ order.take n := by
  rintro ⟨hnd, _, _⟩ hn he
  obtain ⟨i, hi, hin⟩ := elem_of_take.1 he
  have heq : i = n := NoDup_lookup hnd hi hn
  omega

/-! ### PER-AGENT MONOTONICITY in the subset order -/

theorem topoAgentLtS (TS : Ptraces P D) (R : Gev → Gev → Prop)
    (Rpo : ∀ x y, WeakRobustGraph.gpo TS x y → R x y) (S : Gev → Prop)
    (order : List Gev) (i j : Nat) (x y : Gev) :
    topoOrderS TS R S order → order[i]? = some x → order[j]? = some y →
    x.1 = y.1 → x.2 < y.2 → i < j := by
  rintro ⟨_, hmem, hord⟩ hi hj hag hk
  exact hord x y i j hi hj (Rpo x y ⟨hag, hk, ((hmem x).1 (elem_of_list_lookup_2 hi)).1,
    ((hmem y).1 (elem_of_list_lookup_2 hj)).1⟩)

theorem topoAgentMonoS (TS : Ptraces P D) (R : Gev → Gev → Prop)
    (Rpo : ∀ x y, WeakRobustGraph.gpo TS x y → R x y) (S : Gev → Prop)
    (order : List Gev) (i j : Nat) (x y : Gev) :
    topoOrderS TS R S order → order[i]? = some x → order[j]? = some y →
    x.1 = y.1 → (i < j ↔ x.2 < y.2) := by
  intro ho hi hj hag
  refine ⟨fun hij => ?_, topoAgentLtS TS R Rpo S order i j x y ho hi hj hag⟩
  rcases Nat.lt_trichotomy x.2 y.2 with hlt | heq | hgt
  · exact hlt
  · exfalso
    have hxy : x = y := Prod.ext hag heq
    subst hxy
    have := topoOrderSIndexUnique TS R S order i j x ho hi hj
    omega
  · exfalso
    have := topoAgentLtS TS R Rpo S order j i y x ho hj hi hag.symm hgt
    omega

/-- PER-AGENT PREFIX CLOSURE of the SUBSET itself. -/
theorem dcAgentPrefix (TS : Ptraces P D) (R : Gev → Gev → Prop)
    (Rpo : ∀ x y, WeakRobustGraph.gpo TS x y → R x y) (S : Gev → Prop) (j k k' : Nat) :
    dc TS R S → S (j, k) → gevWf TS (j, k) → gevWf TS (j, k') →
    k' < k → S (j, k') :=
  fun hdc hS hwf hwf' hlt => hdc (j, k) (j, k') hS (Rpo _ _ ⟨rfl, hlt, hwf', hwf⟩) hwf'

theorem subOkAgentPrefix (TS : Ptraces P D) (R : Gev → Gev → Prop)
    (Rpo : ∀ x y, WeakRobustGraph.gpo TS x y → R x y) (S : Gev → Prop) (j k k' : Nat) :
    subOk TS R S → S (j, k) → gevWf TS (j, k') → k' < k → S (j, k') :=
  fun ⟨hdc, hsub⟩ hS hwf' hlt => dcAgentPrefix TS R Rpo S j k k' hdc hS (hsub _ hS) hwf' hlt

/-! ### THE INDUCTION PRINCIPLE -/

theorem toposortIndS (TS : Ptraces P D) (R : Gev → Gev → Prop) [DecidableRel R]
    (S : Gev → Prop) [DecidablePred S] (Q : List Gev → Prop) :
    (∀ e, ¬ tc R e e) → dc TS R S →
    Q [] →
    (∀ dn e,
       Q dn →
       gevWf TS e → S e → e ∉ dn →
       (∀ e', R e' e → gevWf TS e' → e' ∈ dn) →
       Q (dn ++ [e])) →
    ∃ order,
      Q order ∧
      order.Nodup ∧
      (∀ e, e ∈ order ↔ (gevWf TS e ∧ S e)) ∧
      (∀ x y (i j : Nat), order[i]? = some x → order[j]? = some y → R x y → i < j) := by
  intro hacyc hdc hnil hstep
  obtain ⟨order, ho⟩ := topoSortSPack TS R S hacyc
  -- BOUNDED by the order's length (Rocq keeps the successor constructor out of
  -- this proof; the bound makes the step's lookup total).
  have hpre : ∀ n, n ≤ order.length → Q (order.take n) := by
    intro n
    induction n with
    | zero => intro _; rw [take_0]; exact hnil
    | succ n ih =>
      intro hn
      obtain ⟨e, he⟩ := Option.isSome_iff_exists.1
        (lookup_lt_is_Some_2 (l := order) (i := n) (by omega))
      rw [take_S_r he]
      have hes : gevWf TS e ∧ S e := topoOrderSWf TS R S order e ho (elem_of_list_lookup_2 he)
      exact hstep _ e (ih (by omega)) hes.1 hes.2
        (topoNotInPrefixS TS R S order n e ho he)
        (fun e' hd hwf' => topoPredDoneS TS R S order n e ho hdc he e' hd hwf')
  obtain ⟨hnd, hmem, hord⟩ := ho
  refine ⟨order, ?_, hnd, hmem, hord⟩
  have hq := hpre order.length (Nat.le_refl _)
  rwa [take_ge (Nat.le_refl _)] at hq

end subset

/-! ## THE FULL CASE, as ONE instantiation (`S := gevWf TS`) -/

theorem topoSortFull {P D : Type} (TS : Ptraces P D) (R : Gev → Gev → Prop) [DecidableRel R] :
    (∀ e, ¬ tc R e e) →
    ∃ order : List Gev,
      order.Nodup ∧
      (∀ e, e ∈ order ↔ gevWf TS e) ∧
      (∀ x y (i j : Nat), order[i]? = some x → order[j]? = some y → R x y → i < j) := by
  intro hacyc
  obtain ⟨order, hnd, hmem, hord⟩ := topoSortS TS R (gevWf TS) hacyc
  exact ⟨order, hnd, fun e => (hmem e).trans (and_self_iff), hord⟩

theorem toposortIndFull {P D : Type} (TS : Ptraces P D) (R : Gev → Gev → Prop) [DecidableRel R]
    (Q : List Gev → Prop) :
    (∀ e, ¬ tc R e e) →
    Q [] →
    (∀ dn e,
       Q dn → gevWf TS e → e ∉ dn →
       (∀ e', R e' e → gevWf TS e' → e' ∈ dn) →
       Q (dn ++ [e])) →
    ∃ order,
      Q order ∧
      order.Nodup ∧
      (∀ e, e ∈ order ↔ gevWf TS e) ∧
      (∀ x y (i j : Nat), order[i]? = some x → order[j]? = some y → R x y → i < j) := by
  intro hacyc hnil hstep
  obtain ⟨order, hq, hnd, hmem, hord⟩ :=
    toposortIndS TS R (gevWf TS) Q hacyc (dcFull TS R) hnil
      (fun dn e hq hwf _ hnot hpred => hstep dn e hq hwf hnot hpred)
  exact ⟨order, hq, hnd, fun e => (hmem e).trans and_self_iff, hord⟩

/-! ## DELIVERABLE 1 (continued): the bridge to the real `Wstate` -/

section ordwf

variable {P D : Type}

/-- Every trace of the bundle starts from `wsInit`. -/
def ptracesWsInit (TS : Ptraces P D) : Prop :=
  ∀ (i : Nat) (T : Atrace P D) (ag0 : Wpagent P), TS.ptTrs[i]? = some T →
    T.atAgs[0]? = some ag0 → ag0.paWs = wsInit

theorem ptracesOfWsInit (pstep : P → D → Wlabel → P → D → Prop) (TS : Ptraces P D)
    (mid c : Wpcfg P D) :
    ptracesOf pstep TS mid c → cfgWsInit mid → ptracesWsInit TS := by
  rintro ⟨-, -, -, -, hfst, -⟩ hinit i T ag0 hT hag0
  have h0 := hfst i T hT
  rw [hag0] at h0
  exact hinit i ag0 h0.symm

/-- THE CORRESPONDENCE: `preLstate TS e` is the `id`-leaf-mirror of the
behavior's own `Wstate` at `e`'s pre-state. -/
theorem preLstateLrel (pstep : P → D → Wlabel → P → D → Prop) (TS : Ptraces P D) (e : Gev)
    (T : Atrace P D) (ag : Wpagent P) :
    ptracesWf pstep TS → ptracesWsInit TS →
    TS.ptTrs[e.1]? = some T → T.atAgs[e.2]? = some ag →
    lrel id (preLstate TS e) ag.paWs := by
  intro hwf hinit hT hag
  have hwfi := hwf e.1 T hT
  obtain ⟨ag0, hag0⟩ := Option.isSome_iff_exists.1
    (atraceFirstIsSome pstep TS.ptImg TS.ptLog e.1 T hwfi)
  have hws0 : ag0.paWs = wsInit := hinit e.1 T ag0 hT hag0
  have hfold : ag.paWs = aevsPost id (T.atEvs.take e.2) ag0.paWs :=
    astepsWsFold pstep TS.ptImg TS.ptLog e.1 T.atAgs T.atEvs e.2 ag0 ag hwfi hag0 hag
  rw [preLstateTr TS e T hT, hfold, hws0]
  exact lrelAevsPostId _

/-- …hence the read floor computed from the trace IS the behavior's own floor
number. -/
theorem rdFloorWs (pstep : P → D → Wlabel → P → D → Prop) (TS : Ptraces P D) (r : Gev)
    (T : Atrace P D) (ag : Wpagent P) (l : Wlabel) (a : Int) :
    ptracesWf pstep TS → ptracesWsInit TS →
    TS.ptTrs[r.1]? = some T → T.atAgs[r.2]? = some ag →
    gevLb TS r = some l →
    (match l with
     | LLoad .. | LRmw .. | LExLoad .. => True
     | LSilent | LStore .. | LFence .. | LDev | LRegW .. | LCtrl _ | LInstr | LExStore ..
     | LIFetch .. => False) →
    rdFloor TS r a
    = max (loadVpreD ag.paWs (WeakRobustAcyc.lbAq l) (srcsView ag.paWs (lbRasrc l)))
          (coh ag.paWs a) := by
  intro hwf hinit hT hag hl hrd
  have hrel : lrel id (preLstate TS r) ag.paWs := preLstateLrel pstep TS r T ag hwf hinit hT hag
  rw [lrelFloorD id (preLstate TS r) ag.paWs (WeakRobustAcyc.lbAq l) a (lbRasrc l) hrel]
  unfold rdFloor rdLeaves
  rw [hl]
  cases l <;> first | rfl | exact (hrd : False).elim

end ordwf

end Weak
