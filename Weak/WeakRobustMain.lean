/-
Weak: **THE ASSEMBLED LAYER-1 ROBUSTNESS THEOREM** (M6 W2c): the robustness capstone.

Rocq: `iris/WeakRobustMain.v` @ xxvzwolszwmp.

The Rocq header, in substance.  The pieces of W2a/W2b (the dependency graph
and its extension, `WeakRobustGraph`/`WeakRobustOrd`; the acyclicity walk over
`gdep2`, `WeakRobustAcyc2`; the byte classification and co-serialization,
`WeakRobustSer`; the π-permuted simulation, `WeakRobustSim`) are assembled into
the theorem W2c asks for:

  (1) the per-edge premise WEAKENED from `rfEdgesOk` to "`edgeOk` OR `bad`"
      (`edgesSplit`), where `bad` is the OWNED-UNPUBLISHED CROSS READ (the
      shape the Layer-2 violation predicate φ refutes); A0 weakens it further
      to exactly what the walk consumes (`edgesSplitMs`: the later fulfil is a
      MILESTONE SOURCE, coverage is `fcov` at the fulfil), and A0'' to readers
      ON A CYCLE (`edgesSplitCyc`, the form the package carries);
  (2) THE EXHIBIT (`badEdgeViolates`): a `bad` edge whose target has
      bad-target-free strict ancestry (`badMin`) yields a promise-free run to a
      HART-restricted VIOLATING configuration: the ancestor cone of the target
      is sorted (`coneQinv`, the restricted toposort over `gdep3 ∩ U²`, whose
      acyclicity is the RELATIVIZED walk `gdep2AcyclicOn`), replayed by
      `WeakRobustSim.QinvStep`, and ONE more step appends the bad read; under
      `pfViolationFreeHart` no bad edge exists (`noBadEdge`), so `gdep2`
      (`gdep2AcyclicMain`) and `gdep3` (`gdep3AcyclicMain`, via the fabric
      witness consistency `devWitOk`) are acyclic;
  (3) the honest residue `badWf`: whenever a bad edge exists, SOME bad edge is
      minimal (a "bad SCC" has no exhibit);
  (4) W2c proper: `robustMain` (every behavior of a lat-free,
      timestamp-oblivious program with violation-free pf runs is matched by a
      pf run with the same program states and flat memory) and the transport
      corollary over COMPLETABLE prefixes, `robustTransport`.

THE ANCESTOR CONE is computed, not reflected: `anc` iterates "add every carrier
element with an edge into the current set" `|carrier|` times, saturates
(pigeonhole on a `Nodup` sublist) and `e ∈ anc ↔ e = root ∨ tc R e root`.
PUBLICATION is the LOG predicate `wpublished` (`pubOf`), and a PUBLISHING EVENT
is a fulfil whose message is release-class (`pubEvent`); the machine reading
(`pubEventRaises`, the `wPub` raise) and the `wPub` fold lemmas are recorded,
not consumed.  `bad` quantifies its "no publishing ancestor" over `gdep3`, the
relation the cone is closed under.  DEPENDENCY-FREE: no Iris, no Sail.

**Deviations from Rocq.**

1. NAMES: lowerCamelCase as `Weak/WeakMem.lean` deviation 1 (capitalised Rocq
   names keep their capital: `Ucone`, `Rcone`, `Ucone_iff` ↦ `UconeIff`, ...).
   File-qualified (in `notes/weak-port-dupnames.json`): `lb_rl` ↦
   `WeakRobustMain.lbRl`, `w_pub_foldl_load` ↦ `WeakRobustMain.wPubFoldlLoad`,
   `w_pub_load_post_bytes` ↦ `WeakRobustMain.wPubLoadPostBytes`.  `grf` is
   `WeakRobustGraph.grf`, `gpo` is `WeakRobustGraph.gpo`.
2. VOCABULARY: as `Weak/WeakRobustSim.lean` deviation 2 (`l !! i` ↦ `l[i]?`,
   `is_Some o` ↦ `o.isSome`, `NoDup` ↦ `List.Nodup`, `S n` ↦ `n + 1`,
   `PDevs d []` ↦ `⟨d, []⟩`); `Exists (λ y, R e y) l` ↦ `∃ y ∈ l, R e y`;
   `filter` ↦ `List.filter (decide ∘ ·)`; `Decision`/`RelDecision` ↦
   `DecidablePred`/`DecidableRel` instances (`UconeDec`, `RconeDec`).
3. SECTION VARIABLES: the Rocq `closure`/`cone`/`exhibit`/`main` sections'
   parameters are explicit arguments; the section HYPOTHESES are explicit
   arguments of exactly the declarations whose Rocq proof uses them, in Rocq's
   order.  `pdev` is not a parameter of the cone/exhibit lemmas: Rocq threads it
   only into `Qinv_step`/`pf_log_pi`/`pi_mem`/`pi_lt_of_tc`, whose Lean twins
   take no `pdev` (`WeakRobustSim` deviation 3); likewise those twins take no
   `Hnag`, so `coneQinv`/`coneQinvNil`/`badEdgeViolates` keep `hnag` (Rocq
   uses it there) but do not consume it (`_hnag`).
4. `violation_hart` in Lean (`Weak/WeakRobust.lean`) states the hart bounds as
   `tidHart nh m.wmTid` / `tidHart nh (some j)`; the exhibit discharges exactly
   those.  `tc` is core `Relation.TransGen` (built from the LAST step): `ancTc`
   and `tcRcone` go by tail induction (Rocq: head), `tcGdep3Nil` by plain tail
   induction (Rocq: `tc_subrel`).  Statements unchanged.
5. O2 / owner decision D4: THE FETCH-SOURCE PREMISE.  `WeakRobustSim`'s replay
   (`QinvStep`, `simFull`) carries the Lean-only premise `fetchSrcOk TS` (every
   nonzero timestamp an i-cache fetch answers is fulfilled `tc gdep2`-before the
   fetch; `WeakRobustSim` deviation 4).  Nothing in this file knows the program,
   so it CANNOT be discharged here in general; it is KEPT as a premise, and the
   following statements GAINED it (each as the LAST hypothesis before the
   conclusion unless noted):
   - `coneQinv`, `coneQinvNil` (`hfetch`, after `hd0` resp. the dev-free
     premise);
   - `badEdgeViolates`, `noBadEdge`, `gdep2AcyclicMain`, `gdep3AcyclicMain`
     (`hfetch`, after `hsplit`: the exhibit replays the cone);
   - `robustMainAcyc` (`fetchSrcOk TS`, after `clsCanonical pcls TS`),
     `robustMainBundle` (`fetchSrcOk TS`, after `pfViolationFreeHart`);
   - `robustMain` (a per-bundle premise `∀ mid TS DS, … → fetchSrcOk TS`, after
     `pfViolationFreeHart`, the shape of `WeakRobustSim.wpBehaviorRobustDev`'s)
     and `robustTransport` (`∀ cend mid TS DS, … → fetchSrcOk TS`, same place).
   `mainPremises` is UNCHANGED (the fetch premise is a separate bundle-level
   premise, like `clsCanonical`).  NOT affected (no replay): Layers 0–4, the
   relativized walk, `coneAcyc*OfMin*`, `mainPremisesNil`.
   DISCHARGES (Lean-only, deviation 6): `fetchSrcOkOfNoFetch` (a program that
   never fetches, `pstepNoFetch`), `fetchSrcOkTsZero` (fetches answer only
   never-written bytes, timestamp 0); the capstones in fetch-free form,
   `robustMainBundleNoFetch`, `robustMainNoFetch`, `robustTransportNoFetch`,
   carry `pstepNoFetch pstep` instead and are otherwise Rocq's statements.
6. Lean-only declarations (no Rocq twin): `pstepNoFetch` (Stage C: moved here from
   `WeakPromiseBridge`, whose bridges no longer take it), `fetchSrcOkOfNoFetch`,
   `fetchSrcOkTsZero`, `robustMainBundleNoFetch`, `robustMainNoFetch`,
   `robustTransportNoFetch`.
7. `lb_rl`'s Lean-only `LIFetch` arm is `false` (a fetch carries no `rl` bit);
   `aevPost`'s `LIFetch` arm is the identity, so `wPubAevPostLt` gains a
   trivial arm.

**Rocq → Lean name map.**  `lb_rl` ↦ `WeakRobustMain.lbRl`; `w_pub_foldl_load` ↦
`WeakRobustMain.wPubFoldlLoad`; `w_pub_load_post_bytes` ↦
`WeakRobustMain.wPubLoadPostBytes`; `w_pub_load_post_run` ↦ `wPubLoadPostRun`;
`w_pub_load_post_run_d` ↦ `wPubLoadPostRunD`; `w_pub_foldl_store` ↦
`wPubFoldlStore`; `w_pub_foldl_store_eq` ↦ `wPubFoldlStoreEq`;
`w_pub_foldl_store_d` ↦ `wPubFoldlStoreD`; `w_pub_foldl_store_d_eq` ↦
`wPubFoldlStoreDEq`; `w_pub_store_post_run_d_le` ↦ `wPubStorePostRunDLe`;
`w_pub_store_post_run_d_eq` ↦ `wPubStorePostRunDEq`;
`w_pub_store_post_bytes_le` ↦ `wPubStorePostBytesLe`;
`w_pub_store_post_bytes_eq` ↦ `wPubStorePostBytesEq`; `w_pub_store_post_run_le`
↦ `wPubStorePostRunLe`; `w_pub_store_post_run_eq` ↦ `wPubStorePostRunEq`;
`w_pub_aev_post_lt` ↦ `wPubAevPostLt`; `w_pub_aevs_post_lt` ↦ `wPubAevsPostLt`;
`cls_of` ↦ `clsOf`; `pub_of` ↦ `pubOf`; `pre_ws` ↦ `preWs`; `pub_event` ↦
`pubEvent`; `pub_event_raises` ↦ `pubEventRaises`; `bad`; `edges_split` ↦
`edgesSplit`; `rf_edges_ok_on` ↦ `rfEdgesOkOn`; `rf_edges_ok_on_full` ↦
`rfEdgesOkOnFull`; `edges_split_ms` ↦ `edgesSplitMs`; `rf_edges_ok_on_ms` ↦
`rfEdgesOkOnMs`; `edges_split_edges_split_ms` ↦ `edgesSplitEdgesSplitMs`;
`rf_edges_ok_on_ms_full` ↦ `rfEdgesOkOnMsFull`; `on_cyc` ↦ `onCyc`;
`on_cyc_mr` ↦ `onCycMr`; `edges_split_cyc` ↦ `edgesSplitCyc`;
`edges_split_ms_cyc` ↦ `edgesSplitMsCyc`; `edges_split_edges_split_cyc` ↦
`edgesSplitEdgesSplitCyc`; `bad_min` ↦ `badMin`; `bad_wf` ↦ `badWf`;
`gmile_gdep2` ↦ `gmileGdep2`; `mile_mu_gain_on` ↦ `mileMuGainOn`;
`on_cycle2_on` ↦ `onCycle2On`; `on_cycle2_advance_on` ↦ `onCycle2AdvanceOn`;
`on_cycle2_on_bounded` ↦ `onCycle2OnBounded`; `on_cycle2_on_empty` ↦
`onCycle2OnEmpty`; `gdep2_acyclic_on` ↦ `gdep2AcyclicOn`;
`gdep2_acyclic_on_cyc` ↦ `gdep2AcyclicOnCyc`; `bad_wf_strong` ↦ `badWfStrong`;
`gdep2_acyclic_bad_free` ↦ `gdep2AcyclicBadFree`; `anc_new` ↦ `ancNew`;
`anc_step` ↦ `ancStep`; `anc_iter` ↦ `ancIter`; `anc`; `elem_of_anc_new` ↦
`elemOfAncNew`; `anc_iter_carrier` ↦ `ancIterCarrier`; `anc_iter_nodup` ↦
`ancIterNodup`; `anc_iter_mono` ↦ `ancIterMono`; `anc_iter_mono_le` ↦
`ancIterMonoLe`; `anc_iter_sound` ↦ `ancIterSound`; `anc_grow` ↦ `ancGrow`;
`anc_new_nil` ↦ `ancNewNil`; `root_in_anc` ↦ `rootInAnc`; `anc_closed` ↦
`ancClosed`; `anc_tc` ↦ `ancTc`; `elem_of_anc` ↦ `elemOfAnc`; `ancr`; `Ucone`;
`Ucone_dec` ↦ `UconeDec`; `r_in_enum` ↦ `rInEnum`; `elem_of_ancr` ↦
`elemOfAncr`; `Ucone_iff` ↦ `UconeIff`; `Ucone_wf` ↦ `UconeWf`; `Ucone_dc` ↦
`UconeDc`; `Ucone_sub_ok` ↦ `UconeSubOk`; `Rcone`; `Rcone_dec` ↦ `RconeDec`;
`tc_Rcone` ↦ `tcRcone`; `Rcone_acyc` ↦ `RconeAcyc`; `cone_Qinv` ↦ `coneQinv`;
`aev_post_coh_read` ↦ `aevPostCohRead`; `astep_read_log_byte` ↦
`astepReadLogByte`; `rf_edges_ok_on_min` ↦ `rfEdgesOkOnMin`;
`rtc_gdep2_gdep3` ↦ `rtcGdep2Gdep3`; `anc_mr` ↦ `ancMr`; `cone_acyc2_of_min` ↦
`coneAcyc2OfMin`; `cone_acyc_of_min` ↦ `coneAcycOfMin`; `tc_gdep3_nil` ↦
`tcGdep3Nil`; `cone_acyc_of_min_nil` ↦ `coneAcycOfMinNil`; `cone_Qinv_nil` ↦
`coneQinvNil`; `bad_edge_violates` ↦ `badEdgeViolates`; `no_bad_edge` ↦
`noBadEdge`; `gdep2_acyclic_main` ↦ `gdep2AcyclicMain`; `gdep3_acyclic_main` ↦
`gdep3AcyclicMain`; `main_premises` ↦ `mainPremises`; `main_premises_nil` ↦
`mainPremisesNil`; `robust_main_acyc` ↦ `robustMainAcyc`; `robust_main_bundle`
↦ `robustMainBundle`; `robust_main` ↦ `robustMain`; `completable`;
`robust_transport` ↦ `robustTransport`.

**Not ported:** nothing (every Rocq definition and lemma has a Lean twin).
-/
import Weak.WeakRobust
import Weak.WeakRobustAcyc2
import Weak.WeakRobustSim

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std Wlabel

/-! ## LAYER 0: how a fold of trace events moves `wPub` and `wRelp` -/

/-- The `rl` bit of a store/rmw label; `false` for everything else. -/
def WeakRobustMain.lbRl (l : Wlabel) : Bool :=
  match l with
  | LStore rl _ _ _ _ => rl
  | LRmw _ rl _ _ _ _ _ => rl
  | LExStore rl _ _ _ _ => rl
  | LSilent | LLoad .. | LFence .. | LDev | LRegW .. | LCtrl _ | LInstr | LExLoad ..
  | LIFetch .. => false

/-! ### the per-byte folds -/

theorem WeakRobustMain.wPubFoldlLoad (aq : Bool) (v : Nat) (ats : List (Int × Nat)) :
    ∀ w, (ats.foldl (fun w at_ => loadPostAt w aq v at_.1 at_.2) w).wPub = w.wPub := by
  induction ats with
  | nil => intro w; rfl
  | cons x xs ih => intro w; exact ih _

theorem WeakRobustMain.wPubLoadPostBytes (ws : Wstate) (aq : Bool) (ats : List (Int × Nat)) :
    (loadPostBytes ws aq ats).wPub = ws.wPub :=
  WeakRobustMain.wPubFoldlLoad _ _ _ _

theorem wPubLoadPostRun (ws : Wstate) (aq : Bool) (base : Int) (ts : List Nat) :
    (loadPostRun ws aq base ts).wPub = ws.wPub :=
  WeakRobustMain.wPubLoadPostBytes _ _ _

theorem wPubLoadPostRunD (ws : Wstate) (aq : Bool) (va : Nat) (base : Int) (ts : List Nat) :
    (loadPostRunD ws aq va base ts).wPub = ws.wPub :=
  WeakRobustMain.wPubFoldlLoad _ _ _ _

theorem wPubFoldlStore (rl : Bool) (as_ : List Int) (t : Nat) :
    ∀ w, (as_.foldl (fun w a => storePost w rl a t) w).wPub ≤ max w.wPub t := by
  induction as_ with
  | nil => intro w; simp only [List.foldl]; omega
  | cons a as_ ih =>
    intro w
    have h := ih (storePost w rl a t)
    have hp : (storePost w rl a t).wPub ≤ max w.wPub t := by
      simp only [storePost]; split <;> omega
    simp only [List.foldl]
    omega

theorem wPubFoldlStoreEq (rl : Bool) (as_ : List Int) (t : Nat) :
    ∀ w, w.wRelp = false → rl = false →
      (as_.foldl (fun w a => storePost w rl a t) w).wPub = w.wPub := by
  induction as_ with
  | nil => intro w _ _; rfl
  | cons a as_ ih =>
    intro w hrp hrl
    have hrp' : (storePost w rl a t).wRelp = false := rfl
    simp only [List.foldl]
    rw [ih (storePost w rl a t) hrp' hrl]
    simp [storePost, hrp, hrl]

theorem wPubFoldlStoreD (rl : Bool) (vf : Nat) (as_ : List Int) (t : Nat) :
    ∀ w, (as_.foldl (fun w a => storePostD w rl vf a t) w).wPub ≤ max w.wPub t := by
  induction as_ with
  | nil => intro w; simp only [List.foldl]; omega
  | cons a as_ ih =>
    intro w
    have h := ih (storePostD w rl vf a t)
    have hp : (storePostD w rl vf a t).wPub ≤ max w.wPub t := by
      simp only [storePostD]; split <;> omega
    simp only [List.foldl]
    omega

theorem wPubFoldlStoreDEq (rl : Bool) (vf : Nat) (as_ : List Int) (t : Nat) :
    ∀ w, w.wRelp = false → rl = false →
      (as_.foldl (fun w a => storePostD w rl vf a t) w).wPub = w.wPub := by
  induction as_ with
  | nil => intro w _ _; rfl
  | cons a as_ ih =>
    intro w hrp hrl
    have hrp' : (storePostD w rl vf a t).wRelp = false := rfl
    simp only [List.foldl]
    rw [ih (storePostD w rl vf a t) hrp' hrl]
    simp [storePostD, hrp, hrl]

theorem wPubStorePostRunDLe (rl : Bool) (va vd : Nat) (base : Int) (n t : Nat) (w : Wstate) :
    (storePostRunD w rl va vd base n t).wPub ≤ max w.wPub t :=
  wPubFoldlStoreD rl _ _ t w

theorem wPubStorePostRunDEq (rl : Bool) (va vd : Nat) (base : Int) (n t : Nat) (w : Wstate) :
    w.wRelp = false → rl = false →
    (storePostRunD w rl va vd base n t).wPub = w.wPub :=
  fun hrp hrl => wPubFoldlStoreDEq rl _ _ t w hrp hrl

theorem wPubStorePostBytesLe (rl : Bool) (as_ : List Int) (t : Nat) (w : Wstate) :
    (storePostBytes w rl as_ t).wPub ≤ max w.wPub t :=
  wPubFoldlStore rl as_ t w

theorem wPubStorePostBytesEq (rl : Bool) (as_ : List Int) (t : Nat) (w : Wstate) :
    w.wRelp = false → rl = false → (storePostBytes w rl as_ t).wPub = w.wPub :=
  wPubFoldlStoreEq rl as_ t w

theorem wPubStorePostRunLe (rl : Bool) (base : Int) (n t : Nat) (w : Wstate) :
    (storePostRun w rl base n t).wPub ≤ max w.wPub t :=
  wPubStorePostBytesLe rl _ t w

theorem wPubStorePostRunEq (rl : Bool) (base : Int) (n t : Nat) (w : Wstate) :
    w.wRelp = false → rl = false → (storePostRun w rl base n t).wPub = w.wPub :=
  fun hrp hrl => wPubStorePostBytesEq rl _ t w hrp hrl

/-! ### the event folds -/

/-- ONE event keeps `wPub` below `N` unless it RAISES — and a raising event is a
fulfil whose label carries `rl` or whose pre-state has `wRelp` armed. -/
theorem wPubAevPostLt {D : Type} (σ : Nat → Nat) (ev : Aev D) (w : Wstate) (N : Nat) :
    w.wPub < N →
    (∀ ts, ev.aeTs = some ts →
       (WeakRobustMain.lbRl ev.aeLb = true ∨ w.wRelp = true) → σ ts < N) →
    (aevPost σ ev w).wPub < N := by
  intro hlt hraise
  obtain ⟨lb, ots, dv⟩ := ev
  cases lb with
  | LSilent => exact hlt
  | LLoad aq lat base tvs asrc =>
    show (loadPostRunD w aq _ base _).wPub < N
    rw [wPubLoadPostRunD]; exact hlt
  | LStore rl base data asrc vsrc =>
    cases ots with
    | none => exact hlt
    | some ts =>
      show (storePostRunD w rl _ _ base data.length (σ ts)).wPub < N
      by_cases hr : w.wRelp = true ∨ rl = true
      · have hσ : σ ts < N := hraise ts rfl (by
          rcases hr with h | h
          · exact Or.inr h
          · exact Or.inl h)
        have := wPubStorePostRunDLe rl (srcsView w asrc) (srcsView w vsrc) base data.length
          (σ ts) w
        omega
      · have hrp : w.wRelp = false := by
          cases h : w.wRelp
          · rfl
          · exact absurd (Or.inl h) hr
        have hrl : rl = false := by
          cases h : rl
          · rfl
          · exact absurd (Or.inr h) hr
        rw [wPubStorePostRunDEq rl _ _ base data.length (σ ts) w hrp hrl]
        exact hlt
  | LRmw aq rl base tvs data asrc vsrc =>
    cases ots with
    | none => exact hlt
    | some ts =>
      show (storePostRunD (loadPostRunD w aq (srcsView w asrc) base ((tvs.map Prod.fst).map σ))
        rl _ _ base data.length (σ ts)).wPub < N
      have hp0 := wPubLoadPostRunD w aq (srcsView w asrc) base ((tvs.map Prod.fst).map σ)
      have hr0 := loadPostRunDRelp w aq (srcsView w asrc) base ((tvs.map Prod.fst).map σ)
      by_cases hr : w.wRelp = true ∨ rl = true
      · have hσ : σ ts < N := hraise ts rfl (by
          rcases hr with h | h
          · exact Or.inr h
          · exact Or.inl h)
        have := wPubStorePostRunDLe rl (srcsView w asrc) (srcsView w vsrc) base data.length
          (σ ts) (loadPostRunD w aq (srcsView w asrc) base ((tvs.map Prod.fst).map σ))
        omega
      · have hrp : (loadPostRunD w aq (srcsView w asrc) base ((tvs.map Prod.fst).map σ)).wRelp
            = false := by
          rw [hr0]
          cases h : w.wRelp
          · rfl
          · exact absurd (Or.inl h) hr
        have hrl : rl = false := by
          cases h : rl
          · rfl
          · exact absurd (Or.inr h) hr
        rw [wPubStorePostRunDEq rl _ _ base data.length (σ ts) _ hrp hrl, hp0]
        exact hlt
  | LFence pr pw sr sw => exact hlt
  | LDev => exact hlt
  | LRegW rd srcs => exact hlt
  | LCtrl srcs => exact hlt
  | LInstr => exact hlt
  -- THE RMW SPLIT (S2): `LLoad`'s / `LStore`'s arm verbatim
  | LExLoad aq base tvs asrc =>
    show (exloadPostRunD w aq _ base _).wPub < N
    have : (exloadPostRunD w aq (srcsView w asrc) base ((tvs.map Prod.fst).map σ)).wPub
        = w.wPub := WeakRobustMain.wPubFoldlLoad _ _ _ w
    rw [this]; exact hlt
  | LExStore rl base data asrc vsrc =>
    cases ots with
    | none => exact hlt
    | some ts =>
      show (storePostRunD w rl _ _ base data.length (σ ts)).wPub < N
      by_cases hr : w.wRelp = true ∨ rl = true
      · have hσ : σ ts < N := hraise ts rfl (by
          rcases hr with h | h
          · exact Or.inr h
          · exact Or.inl h)
        have := wPubStorePostRunDLe rl (srcsView w asrc) (srcsView w vsrc) base data.length
          (σ ts) w
        omega
      · have hrp : w.wRelp = false := by
          cases h : w.wRelp
          · rfl
          · exact absurd (Or.inl h) hr
        have hrl : rl = false := by
          cases h : rl
          · rfl
          · exact absurd (Or.inr h) hr
        rw [wPubStorePostRunDEq rl _ _ base data.length (σ ts) w hrp hrl]
        exact hlt
  | LIFetch base tvs => exact hlt

/-- …hence a whole processed prefix does, provided every raising event in it has
its transported timestamp below `N`. -/
theorem wPubAevsPostLt {D : Type} (σ : Nat → Nat) (evs : List (Aev D)) :
    ∀ (w : Wstate) (N : Nat),
      w.wPub < N →
      (∀ (k : Nat) (ev : Aev D) (ts : Nat), evs[k]? = some ev → ev.aeTs = some ts →
         (WeakRobustMain.lbRl ev.aeLb = true ∨
          (aevsPost σ (evs.take k) w).wRelp = true) →
         σ ts < N) →
      (aevsPost σ evs w).wPub < N := by
  induction evs with
  | nil => intro w N hw _; exact hw
  | cons ev evs ih =>
    intro w N hw hall
    show (aevsPost σ evs (aevPost σ ev w)).wPub < N
    apply ih
    · exact wPubAevPostLt σ ev w N hw (fun ts hts hr => hall 0 ev ts rfl hts hr)
    · intro k ev' ts hk hts hr
      exact hall (k + 1) ev' ts hk hts hr

/-! ## LAYER 1: the Layer-2 parameters, instantiated -/

/-- The class, read off the message's inert `wmAk` field. -/
def clsOf (m : Wmsg) : StoreClass :=
  match m.wmAk with
  | .WCplain => .SCowned
  | .WCrel => .SCfenced
  | .WCexcl => .SCexcl

/-- `pubOf c ts`: the message at timestamp `ts` has been published by ITS OWN
author — the LOG predicate `wpublished` (a later release-class message of the
same author). -/
def pubOf {P D : Type} (c : Wpcfg P D) (ts : Nat) : Prop :=
  ∃ (p : Nat) (m : Wmsg), ts = p + 1 ∧ c.pcLog[p]? = some m ∧ wpublished c.pcLog m.wmTid p

/-! ## LAYER 2: the per-edge split — `edgeOk` or `bad` -/

section split

variable {P D : Type}

/-- The author's pre-state at an event; `wsInit` off the trace (junk, never
reached under `gevWf`). -/
def preWs (TS : Ptraces P D) (e : Gev) : Wstate :=
  match TS.ptTrs[e.1]? with
  | some T =>
    match T.atAgs[e.2]? with
    | some ag => ag.paWs
    | none => wsInit
  | none => wsInit

/-- A PUBLISHING EVENT: a fulfil whose MESSAGE IS RELEASE-CLASS. -/
def pubEvent (TS : Ptraces P D) (e : Gev) : Prop :=
  ∃ (ts : Nat) (m : Wmsg), gevTs TS e = some ts ∧ TS.ptLog[ts - 1]? = some m ∧
    m.wmAk = .WCrel

/-- The MACHINE reading, RECORDED ONLY (nothing consumes it): the fulfil raises
`wPub`. -/
def pubEventRaises (TS : Ptraces P D) (e : Gev) : Prop :=
  (gevTs TS e).isSome ∧
  ∃ l, gevLb TS e = some l ∧
    (WeakRobustMain.lbRl l = true ∨ (preWs TS e).wRelp = true)

/-- `bad nh TS DS e1 e2` — the OWNED-UNPUBLISHED CROSS READ, writer and reader
both harts, no publishing event of the author po-at-or-after its fulfil in the
reader's strict `gdep3`-ancestry. -/
def bad (nh : Nat) (TS : Ptraces P D) (DS : Pdevs D) (e1 e2 : Gev) : Prop :=
  WeakRobustGraph.grf TS e1 e2 ∧ e1.1 ≠ e2.1 ∧ e1.1 < nh ∧ e2.1 < nh ∧
  (∃ (ts : Nat) (m : Wmsg), gevTs TS e1 = some ts ∧ TS.ptLog[ts - 1]? = some m ∧
    m.wmAk = .WCplain) ∧
  ¬ (∃ ep : Gev, ep.1 = e1.1 ∧ e1.2 ≤ ep.2 ∧ pubEvent TS ep ∧ tc (gdep3 TS DS) ep e2)

/-- THE WEAKENED PER-EDGE PREMISE. -/
def edgesSplit (nh : Nat) (TS : Ptraces P D) (DS : Pdevs D) : Prop :=
  ∀ (e1 e2 : Gev) (T : Atrace P D) (ts : Nat) (a : Int) (k' : Nat) (ev' : Aev D),
    gevTs TS e1 = some ts → gevReads TS e2 a ts → e1.1 ≠ e2.1 →
    TS.ptTrs[e2.1]? = some T →
    e2.2 < k' →
    T.atEvs[k']? = some ev' → ev'.aeTs.isSome →
    edgeOk T e2.2 k' ts ∨ bad nh TS DS e1 e2

/-- …and the RELATIVIZED strong premise: `edgeOk` at every cross edge whose
READER satisfies `W`. -/
def rfEdgesOkOn (TS : Ptraces P D) (W : Gev → Prop) : Prop :=
  ∀ (e1 e2 : Gev) (T : Atrace P D) (ts : Nat) (a : Int) (k' : Nat) (ev' : Aev D),
    gevTs TS e1 = some ts → gevReads TS e2 a ts → e1.1 ≠ e2.1 → W e2 →
    TS.ptTrs[e2.1]? = some T →
    e2.2 < k' →
    T.atEvs[k']? = some ev' → ev'.aeTs.isSome →
    edgeOk T e2.2 k' ts

theorem rfEdgesOkOnFull (TS : Ptraces P D) (W : Gev → Prop) :
    rfEdgesOk TS → rfEdgesOkOn TS W :=
  fun H e1 e2 T ts a k' ev' hts hrd hne _ hT hlt hev hsome =>
    H e1 e2 T ts a k' ev' hts hrd hne hT hlt hev hsome

/-! ### A0: the split premise, relativized to the walk's milestone fulfils -/

def edgesSplitMs (nh : Nat) (TS : Ptraces P D) (DS : Pdevs D) : Prop :=
  ∀ (e1 e2 : Gev) (T : Atrace P D) (ts : Nat) (a : Int) (k' : Nat) (ev' : Aev D),
    gevTs TS e1 = some ts → gevReads TS e2 a ts → e1.1 ≠ e2.1 →
    TS.ptTrs[e2.1]? = some T →
    e2.2 < k' →
    T.atEvs[k']? = some ev' → ev'.aeTs.isSome →
    (∃ y, gmile TS (e2.1, k') y) →
    edgeOkF T e2.2 k' ts ∨ bad nh TS DS e1 e2

/-- …and the `W`-relativized strong premise in the same shape. -/
def rfEdgesOkOnMs (TS : Ptraces P D) (W : Gev → Prop) : Prop :=
  ∀ (e1 e2 : Gev) (T : Atrace P D) (ts : Nat) (a : Int) (k' : Nat) (ev' : Aev D),
    gevTs TS e1 = some ts → gevReads TS e2 a ts → e1.1 ≠ e2.1 → W e2 →
    TS.ptTrs[e2.1]? = some T →
    e2.2 < k' →
    T.atEvs[k']? = some ev' → ev'.aeTs.isSome →
    (∃ y, gmile TS (e2.1, k') y) →
    edgeOkF T e2.2 k' ts

theorem edgesSplitEdgesSplitMs (pstep : P → D → Wlabel → P → D → Prop)
    (nh : Nat) (TS : Ptraces P D) (DS : Pdevs D) :
    ptracesWf pstep TS → edgesSplit nh TS DS → edgesSplitMs nh TS DS := by
  intro hwf H e1 e2 T ts a k' ev' hts hrd hne hT hlt hev hsome _
  rcases H e1 e2 T ts a k' ev' hts hrd hne hT hlt hev hsome with hok | hbad
  · exact Or.inl (edgeOkEdgeOkF pstep TS.ptImg TS.ptLog e2.1 T e2.2 k' ts ev' (hwf _ _ hT)
      (by omega) hev hsome hok)
  · exact Or.inr hbad

theorem rfEdgesOkOnMsFull (pstep : P → D → Wlabel → P → D → Prop)
    (TS : Ptraces P D) (W : Gev → Prop) :
    ptracesWf pstep TS → rfEdgesOkOn TS W → rfEdgesOkOnMs TS W := by
  intro hwf H e1 e2 T ts a k' ev' hts hrd hne hW hT hlt hev hsome _
  exact edgeOkEdgeOkF pstep TS.ptImg TS.ptLog e2.1 T e2.2 k' ts ev' (hwf _ _ hT) (by omega)
    hev hsome (H e1 e2 T ts a k' ev' hts hrd hne hW hT hlt hev hsome)

/-! ### A0'': the cycle-relativized premise -/

/-- The cycle predicate. -/
def onCyc (TS : Ptraces P D) (e : Gev) : Prop := tc (gdep2 TS) e e

theorem onCycMr (TS : Ptraces P D) (u x : Gev) :
    onCyc TS u → rtc (gdep2 TS) u x → rtc (gdep2 TS) x u → onCyc TS x :=
  fun hWu hux hxu => tc_rtc_l hxu (tc_rtc_r hWu hux)

/-- `edgesSplitMs` with the reader restricted to a cycle. -/
def edgesSplitCyc (nh : Nat) (TS : Ptraces P D) (DS : Pdevs D) : Prop :=
  ∀ (e1 e2 : Gev) (T : Atrace P D) (ts : Nat) (a : Int) (k' : Nat) (ev' : Aev D),
    gevTs TS e1 = some ts → gevReads TS e2 a ts → e1.1 ≠ e2.1 →
    onCyc TS e2 →
    TS.ptTrs[e2.1]? = some T →
    e2.2 < k' →
    T.atEvs[k']? = some ev' → ev'.aeTs.isSome →
    (∃ y, gmile TS (e2.1, k') y) →
    edgeOkF T e2.2 k' ts ∨ bad nh TS DS e1 e2

theorem edgesSplitMsCyc (nh : Nat) (TS : Ptraces P D) (DS : Pdevs D) :
    edgesSplitMs nh TS DS → edgesSplitCyc nh TS DS :=
  fun H e1 e2 T ts a k' ev' hts hrd hne _ hT hlt hev hsome hms =>
    H e1 e2 T ts a k' ev' hts hrd hne hT hlt hev hsome hms

theorem edgesSplitEdgesSplitCyc (pstep : P → D → Wlabel → P → D → Prop)
    (nh : Nat) (TS : Ptraces P D) (DS : Pdevs D) :
    ptracesWf pstep TS → edgesSplit nh TS DS → edgesSplitCyc nh TS DS :=
  fun hwf H => edgesSplitMsCyc nh TS DS (edgesSplitEdgesSplitMs pstep nh TS DS hwf H)

/-- THE RESIDUE: no bad edge's target is a STRICT ancestor of `e2`… -/
def badMin (nh : Nat) (TS : Ptraces P D) (DS : Pdevs D) (e2 : Gev) : Prop :=
  ∀ f1 f2, bad nh TS DS f1 f2 → ¬ tc (gdep3 TS DS) f2 e2

/-- …and whenever a bad edge exists, some bad edge is minimal. -/
def badWf (nh : Nat) (TS : Ptraces P D) (DS : Pdevs D) : Prop :=
  ∀ e1 e2, bad nh TS DS e1 e2 →
    ∃ f1 f2, bad nh TS DS f1 f2 ∧ badMin nh TS DS f2

end split

/-! ## LAYER 3: THE RELATIVIZED WALK

KEEP IN SYNC with `WeakRobustAcyc2`: `mileMuGainOn` / `onCycle2AdvanceOn` /
`onCycle2OnEmpty` are its `mileMuGain` / `onCycle2Advance` / `onCycle2Empty`
with `W`-guarded premises. -/

section walk

variable {P D : Type}
variable (pstep : P → D → Wlabel → P → D → Prop)

theorem gmileGdep2 (TS : Ptraces P D) (x y : Gev) : gmile TS x y → gdep2 TS x y := by
  rintro (⟨hd, _⟩ | he)
  · exact gdepGdep2 TS x y hd
  · exact gEGdep2 TS x y he

/-- THE GAIN LEMMA, relativized: the entry milestone's target `u` must satisfy
`W`. -/
theorem mileMuGainOn (TS : Ptraces P D) (W : Gev → Prop) (mu : Nat) (v u x : Gev) (tx : Nat) :
    ptracesWf pstep TS → ptracesFwdOwn TS →
    rfEdgesOkOnMs TS W → eeOk TS →
    W u → mileMu TS mu v u → u.1 = x.1 → u.2 ≤ x.2 →
    (∃ y, gmile TS x y) →
    gevTs TS x = some tx →
    mu < tx := by
  rintro hwf hfo hrf hee hWu (⟨a, hts1, hrd, hne⟩ | ⟨r, a, hra, rfl⟩) hag hle hms htx
  · -- CROSS-RF ENTRY: S1, with the reader `u` satisfying `W`.
    obtain ⟨T, hT, _⟩ := (gevWfBounds TS u).1 (gevReadsWf TS u a mu hrd)
    have hTx : TS.ptTrs[x.1]? = some T := by rw [← hag]; exact hT
    obtain ⟨ev, hev, hinr⟩ := gevReadsEv TS u a mu T hT hrd
    obtain ⟨evx, hevx, htsx⟩ := gevTsEv TS x tx T hTx htx
    obtain ⟨base, data, kc, hm⟩ := gevTsMsg pstep TS v mu hwf hts1
    have hunf : readUnforwarded TS.ptLog u.1 ev.aeLb mu :=
      Or.inr ⟨⟨base, data, some v.1, kc⟩, v.1, hm, rfl, hne⟩
    exact atraceS1LeF pstep TS.ptImg TS.ptLog u.1 T u.2 x.2 ev evx a mu tx (hwf u.1 T hT)
      (fun n ag hag' => hfo u.1 T n ag hT hag') hev hinr hunf hevx htsx hle
      (fun hklt => hrf v u T mu a x.2 evx hts1 hrd hne hWu hT hklt hevx (by rw [htsx]; rfl)
        (by obtain ⟨y, hy⟩ := hms; exact ⟨y, by rw [hag]; exact hy⟩))
  · -- gE ENTRY: no discipline premise at all.
    by_cases heq : u.2 = x.2
    · have hux : u = x := Prod.ext hag heq
      subst hux
      obtain ⟨l, ts, tstar, that, -, -, -, -, -, h6, -, hlt⟩ := hra
      rw [h6] at htx
      cases htx
      exact hlt
    · exact hee r a v u x tx hra hag (by omega) htx

def onCycle2On (TS : Ptraces P D) (W : Gev → Prop) (mu : Nat) : Prop :=
  ∃ v u, mileMu TS mu v u ∧ rtc (gdep2 TS) u v ∧ W u

theorem onCycle2AdvanceOn (TS : Ptraces P D) (W : Gev → Prop) (mu : Nat) :
    ptracesWf pstep TS → ptracesFwdOwn TS →
    rfEdgesOkOnMs TS W → eeOk TS →
    (∀ u x, W u → rtc (gdep2 TS) u x → rtc (gdep2 TS) x u → W x) →
    onCycle2On TS W mu → ∃ mu', mu < mu' ∧ onCycle2On TS W mu' := by
  rintro hwf hfo hrf hee hcl ⟨v, u, hm, hpath, hWu⟩
  rcases rtcGdep2FirstMile pstep TS u v hwf hpath with
    ⟨hag, hle⟩ | ⟨x, y, hag, hle, hux, hmile, hyv⟩
  · exfalso
    obtain ⟨tv, htv, hlev⟩ := mileMuSrcTs TS mu v u hm
    have hgt := mileMuGainOn pstep TS W mu v u v tv hwf hfo hrf hee hWu hm hag hle
      ⟨u, mileMuGmile TS mu v u hm⟩ htv
    omega
  · have hedge := mileMuGdep2 TS mu v u hm
    have hyx : rtc (gdep2 TS) y x := rtc_transitive hyv (rtc_l hedge hux)
    -- the exit milestone's TARGET inherits `W`
    have hWy : W y := hcl u y hWu (rtc_r hux (gmileGdep2 TS x y hmile)) (rtc_r hyv hedge)
    have hgm : gmile TS x y := hmile
    rcases hmile with ⟨hd, hne⟩ | ⟨r', hat⟩
    · have hrfxy : WeakRobustGraph.grf TS x y := by
        rcases hd with ⟨hag', _⟩ | hrf'
        · exact absurd hag' hne
        · exact hrf'
      obtain ⟨ts2, a2, hts2, hrd2⟩ := hrfxy
      have hlt := mileMuGainOn pstep TS W mu v u x ts2 hwf hfo hrf hee hWu hm hag hle
        ⟨y, hgm⟩ hts2
      exact ⟨ts2, hlt, x, y, Or.inl ⟨a2, hts2, hrd2, hne⟩, hyx, hWy⟩
    · obtain ⟨a', hra'⟩ := gEAtGERa TS r' x y hat
      have hra'' := hra'
      obtain ⟨l', ts', tstar', that', -, -, hleaf', -, h5', -⟩ := hra''
      have hlt := mileMuGainOn pstep TS W mu v u x tstar' hwf hfo hrf hee hWu hm hag hle
        ⟨y, hgm⟩ h5'
      have hle' : tstar' ≤ rdFloor TS r' a' := lvalGe id _ _ hleaf'
      exact ⟨rdFloor TS r' a', by omega, x, y, Or.inr ⟨r', a', hra', rfl⟩, hyx, hWy⟩

theorem onCycle2OnBounded (TS : Ptraces P D) (W : Gev → Prop) (mu : Nat) :
    ptracesWf pstep TS → onCycle2On TS W mu → mu ≤ TS.ptLog.length := by
  rintro hwf ⟨v, u, hm, -⟩
  exact mileMuBounded pstep TS mu v u hwf hm

theorem onCycle2OnEmpty (TS : Ptraces P D) (W : Gev → Prop) :
    ptracesWf pstep TS → ptracesFwdOwn TS →
    rfEdgesOkOnMs TS W → eeOk TS →
    (∀ u x, W u → rtc (gdep2 TS) u x → rtc (gdep2 TS) x u → W x) →
    ∀ mu, ¬ onCycle2On TS W mu := by
  intro hwf hfo hrf hee hcl
  have hgen : ∀ n mu, TS.ptLog.length - mu ≤ n → ¬ onCycle2On TS W mu := by
    intro n
    induction n with
    | zero =>
      intro mu hn hoc
      have hb := onCycle2OnBounded pstep TS W mu hwf hoc
      obtain ⟨mu', hlt, hoc'⟩ := onCycle2AdvanceOn pstep TS W mu hwf hfo hrf hee hcl hoc
      have hb' := onCycle2OnBounded pstep TS W mu' hwf hoc'
      omega
    | succ n ih =>
      intro mu hn hoc
      obtain ⟨mu', hlt, hoc'⟩ := onCycle2AdvanceOn pstep TS W mu hwf hfo hrf hee hcl hoc
      have hb' := onCycle2OnBounded pstep TS W mu' hwf hoc'
      exact ih mu' (by omega) hoc'
  exact fun mu => hgen _ mu (Nat.le_refl _)

/-- THE RELATIVIZED THEOREM: no `gdep2` cycle passes through a `W`-event. -/
theorem gdep2AcyclicOn (TS : Ptraces P D) (W : Gev → Prop) :
    ptracesWf pstep TS → ptracesFwdOwn TS →
    rfEdgesOkOnMs TS W → eeOk TS →
    (∀ u x, W u → rtc (gdep2 TS) u x → rtc (gdep2 TS) x u → W x) →
    ∀ e, W e → ¬ tc (gdep2 TS) e e := by
  intro hwf hfo hrf hee hcl e hWe hc
  rcases tcGdep2Split pstep TS e e hwf hc with ⟨-, hlt⟩ | ⟨x, y, hrx, hmile, hry⟩
  · exact absurd hlt (Nat.lt_irrefl _)
  · have hWy : W y := hcl e y hWe (rtc_r hrx (gmileGdep2 TS x y hmile)) hry
    obtain ⟨mu, hm⟩ := gmileMileMu TS x y hmile
    exact onCycle2OnEmpty pstep TS W hwf hfo hrf hee hcl mu
      ⟨x, y, hm, rtc_transitive hry hrx, hWy⟩

/-- A0'': THE PREMISE MAY ALWAYS ASSUME ITS READER IS ON A CYCLE. -/
theorem gdep2AcyclicOnCyc (TS : Ptraces P D) (W : Gev → Prop) :
    ptracesWf pstep TS → ptracesFwdOwn TS →
    rfEdgesOkOnMs TS (fun e => W e ∧ onCyc TS e) → eeOk TS →
    (∀ u x, W u → rtc (gdep2 TS) u x → rtc (gdep2 TS) x u → W x) →
    ∀ e, W e → ¬ tc (gdep2 TS) e e := by
  intro hwf hfo hrf hee hcl
  have hcl2 : ∀ u x, (W u ∧ onCyc TS u) → rtc (gdep2 TS) u x →
      rtc (gdep2 TS) x u → (W x ∧ onCyc TS x) :=
    fun u x ⟨hWu, hcu⟩ hux hxu => ⟨hcl u x hWu hux hxu, onCycMr TS u x hcu hux hxu⟩
  intro e hWe hc
  exact gdep2AcyclicOn pstep TS (fun e0 => W e0 ∧ onCyc TS e0) hwf hfo hrf hee hcl2 e
    ⟨hWe, hc⟩ hc

end walk

/-- THE STRONG-RESIDUE SHORTCUT (recorded, not used below). -/
def badWfStrong {P D : Type} (nh : Nat) (TS : Ptraces P D) (DS : Pdevs D) : Prop :=
  ∀ e1 e2, bad nh TS DS e1 e2 → ¬ tc (gdep2 TS) e2 e2

theorem gdep2AcyclicBadFree {P D : Type} (pstep : P → D → Wlabel → P → D → Prop)
    (nh : Nat) (TS : Ptraces P D) (DS : Pdevs D) :
    ptracesWf pstep TS → ptracesFwdOwn TS → eeOk TS →
    edgesSplitCyc nh TS DS → badWfStrong nh TS DS →
    gdep2Acyclic TS := by
  intro hwf hfo hee hsplit hbs
  have hrf : rfEdgesOkOnMs TS (fun e => True ∧ onCyc TS e) := by
    intro e1 e2 T ts a k' ev' hts hrd hne ⟨_, hW⟩ hT hlt hev hsome hms
    rcases hsplit e1 e2 T ts a k' ev' hts hrd hne hW hT hlt hev hsome hms with hok | hbad
    · exact hok
    · exact absurd hW (hbs e1 e2 hbad)
  intro e
  exact gdep2AcyclicOnCyc pstep TS (fun _ => True) hwf hfo hrf hee
    (fun _ _ _ _ _ => trivial) e trivial

/-! ## LAYER 4: THE ANCESTOR CONE, CONCRETELY (generic) -/

section closure

variable {A : Type _} [DecidableEq A]
variable (R : A → A → Prop) [DecidableRel R]
variable (carrier : List A) (root : A)

def ancNew (l : List A) : List A :=
  carrier.filter (fun e => decide (e ∉ l ∧ ∃ y ∈ l, R e y))

def ancStep (l : List A) : List A := l ++ ancNew R carrier l

def ancIter : Nat → List A
  | 0 => [root]
  | n + 1 => ancStep R carrier (ancIter n)

def anc : List A := ancIter R carrier root carrier.length

theorem elemOfAncNew (l : List A) (x : A) :
    x ∈ ancNew R carrier l ↔ (x ∉ l ∧ (∃ y, y ∈ l ∧ R x y)) ∧ x ∈ carrier := by
  simp only [ancNew, List.mem_filter, decide_eq_true_iff]
  exact ⟨fun ⟨h1, h2⟩ => ⟨h2, h1⟩, fun ⟨h1, h2⟩ => ⟨h2, h1⟩⟩

theorem ancIterCarrier (hroot : root ∈ carrier) (n : Nat) (x : A) :
    x ∈ ancIter R carrier root n → x ∈ carrier := by
  induction n with
  | zero =>
    intro hx
    rw [ancIter, List.mem_singleton] at hx
    rw [hx]; exact hroot
  | succ n ih =>
    intro hx
    rw [ancIter, ancStep, List.mem_append] at hx
    rcases hx with hx | hx
    · exact ih hx
    · exact ((elemOfAncNew R carrier _ x).1 hx).2

theorem ancIterNodup (hnd : carrier.Nodup) (n : Nat) : (ancIter R carrier root n).Nodup := by
  induction n with
  | zero => exact List.nodup_cons.2 ⟨List.not_mem_nil, List.nodup_nil⟩
  | succ n ih =>
    rw [ancIter, ancStep]
    refine List.nodup_append.2 ⟨ih, hnd.filter _, ?_⟩
    intro x hx y hy hxy
    subst hxy
    exact ((elemOfAncNew R carrier _ x).1 hy).1.1 hx

theorem ancIterMono (n : Nat) (x : A) :
    x ∈ ancIter R carrier root n → x ∈ ancIter R carrier root (n + 1) := by
  intro hx
  rw [ancIter, ancStep, List.mem_append]
  exact Or.inl hx

theorem ancIterMonoLe (n m : Nat) (x : A) :
    n ≤ m → x ∈ ancIter R carrier root n → x ∈ ancIter R carrier root m := by
  intro hle hx
  induction m with
  | zero =>
    have hn : n = 0 := by omega
    subst hn; exact hx
  | succ m ih =>
    by_cases hnm : n = m + 1
    · subst hnm; exact hx
    · exact ancIterMono R carrier root m x (ih (by omega))

/-- SOUNDNESS: everything the iteration collects is `root` or a
`tc`-predecessor of it. -/
theorem ancIterSound (n : Nat) :
    ∀ x, x ∈ ancIter R carrier root n → x = root ∨ tc R x root := by
  induction n with
  | zero =>
    intro x hx
    rw [ancIter, List.mem_singleton] at hx
    exact Or.inl hx
  | succ n ih =>
    intro x hx
    rw [ancIter, ancStep, List.mem_append] at hx
    rcases hx with hx | hx
    · exact ih x hx
    · obtain ⟨⟨_, y, hy, hR⟩, _⟩ := (elemOfAncNew R carrier _ x).1 hx
      right
      rcases ih y hy with rfl | htc
      · exact tc_once hR
      · exact tc_l hR htc

/-- SATURATION: either the round-`n` set already has `n+1` elements or the
iteration has stopped by round `n`. -/
theorem ancGrow (n : Nat) :
    n + 1 ≤ (ancIter R carrier root n).length ∨
    ∃ m, m ≤ n ∧ ancNew R carrier (ancIter R carrier root m) = [] := by
  induction n with
  | zero => left; simp [ancIter]
  | succ n ih =>
    rcases ih with hlen | ⟨m, hm, hnil⟩
    · by_cases hnil : ancNew R carrier (ancIter R carrier root n) = []
      · exact Or.inr ⟨n, by omega, hnil⟩
      · left
        rw [ancIter, ancStep, List.length_append]
        have hpos : 0 < (ancNew R carrier (ancIter R carrier root n)).length := by
          cases h : ancNew R carrier (ancIter R carrier root n) with
          | nil => exact absurd h hnil
          | cons _ _ => simp
        omega
    · exact Or.inr ⟨m, by omega, hnil⟩

theorem ancNewNil (hroot : root ∈ carrier) (hnd : carrier.Nodup) :
    ancNew R carrier (anc R carrier root) = [] := by
  rcases ancGrow R carrier root carrier.length with hlen | ⟨m, hm, hnil⟩
  · exfalso
    have hle : (ancIter R carrier root carrier.length).length ≤ carrier.length :=
      submseteq_length (NoDup_submseteq (ancIterNodup R carrier root hnd _)
        (fun x hx => ancIterCarrier R carrier root hroot _ x hx))
    omega
  · have hstab : ∀ d, ancIter R carrier root (m + d) = ancIter R carrier root m := by
      intro d
      induction d with
      | zero => rfl
      | succ d ih =>
        rw [← Nat.add_assoc, ancIter, ih, ancStep, hnil, List.append_nil]
    have hd : carrier.length = m + (carrier.length - m) := by omega
    rw [anc, hd, hstab]
    exact hnil

theorem rootInAnc : root ∈ anc R carrier root :=
  ancIterMonoLe R carrier root 0 _ root (Nat.zero_le _) (List.mem_singleton.2 rfl)

theorem ancClosed (hroot : root ∈ carrier) (hcar : ∀ x y, R x y → x ∈ carrier)
    (hnd : carrier.Nodup) (x y : A) :
    y ∈ anc R carrier root → R x y → x ∈ anc R carrier root := by
  intro hy hR
  by_cases hx : x ∈ anc R carrier root
  · exact hx
  · exfalso
    have hin : x ∈ ancNew R carrier (anc R carrier root) :=
      (elemOfAncNew R carrier _ x).2 ⟨⟨hx, y, hy, hR⟩, hcar x y hR⟩
    rw [ancNewNil R carrier root hroot hnd] at hin
    exact List.not_mem_nil hin

/-- COMPLETENESS: every `tc`-predecessor of an element of `anc` is in `anc`. -/
theorem ancTc (hroot : root ∈ carrier) (hcar : ∀ x y, R x y → x ∈ carrier)
    (hnd : carrier.Nodup) (x y : A) :
    tc R x y → y ∈ anc R carrier root → x ∈ anc R carrier root := by
  intro h
  induction h with
  | single hR => exact fun hy => ancClosed R carrier root hroot hcar hnd _ _ hy hR
  | tail _ hR ih => exact fun hy => ih (ancClosed R carrier root hroot hcar hnd _ _ hy hR)

theorem elemOfAnc (hroot : root ∈ carrier) (hcar : ∀ x y, R x y → x ∈ carrier)
    (hnd : carrier.Nodup) (x : A) :
    x ∈ anc R carrier root ↔ (x = root ∨ tc R x root) := by
  constructor
  · exact ancIterSound R carrier root _ x
  · rintro (rfl | htc)
    · exact rootInAnc R carrier x
    · exact ancTc R carrier root hroot hcar hnd x root htc (rootInAnc R carrier root)

end closure

/-! ## LAYER 5: THE CONE, SORTED — `Qinv` over the strict ancestry of one event -/

section cone

variable {P D : Type}
variable (pstep : P → D → Wlabel → P → D → Prop)
variable (pcls : P → Wlabel → Wstate → WmClass)
variable (TS : Ptraces P D) (DS : Pdevs D) (img : Image) (d0 : D) (ps : List P)
variable (r : Gev)

def ancr : List Gev := anc (gdep3 TS DS) (gevEnum TS) r

def Ucone (e : Gev) : Prop := e ∈ ancr TS DS r ∧ e ≠ r

instance UconeDec : DecidablePred (Ucone TS DS r) :=
  fun e => inferInstanceAs (Decidable (e ∈ ancr TS DS r ∧ e ≠ r))

theorem rInEnum (hrwf : gevWf TS r) : r ∈ gevEnum TS := (elemOfGevEnum TS r).2 hrwf

theorem elemOfAncr (hwit : ptracesWit TS DS) (hrwf : gevWf TS r) (e : Gev) :
    e ∈ ancr TS DS r ↔ (e = r ∨ tc (gdep3 TS DS) e r) :=
  elemOfAnc (gdep3 TS DS) (gevEnum TS) r (rInEnum TS r hrwf)
    (fun x y hd => (elemOfGevEnum TS x).2 (gdep3Wf TS DS x y hwit hd).1)
    (nodupGevEnum TS) e

theorem UconeIff (hwit : ptracesWit TS DS) (hrwf : gevWf TS r)
    (hrr : ¬ tc (gdep3 TS DS) r r) (e : Gev) :
    Ucone TS DS r e ↔ (gevWf TS e ∧ tc (gdep3 TS DS) e r) := by
  constructor
  · rintro ⟨hin, hne⟩
    refine ⟨(elemOfGevEnum TS e).1
      (ancIterCarrier (gdep3 TS DS) (gevEnum TS) r (rInEnum TS r hrwf) _ e hin), ?_⟩
    rcases (elemOfAncr TS DS r hwit hrwf e).1 hin with heq | htc
    · exact absurd heq hne
    · exact htc
  · rintro ⟨_, htc⟩
    refine ⟨(elemOfAncr TS DS r hwit hrwf e).2 (Or.inr htc), ?_⟩
    rintro rfl
    exact hrr htc

theorem UconeWf (hwit : ptracesWit TS DS) (hrwf : gevWf TS r)
    (hrr : ¬ tc (gdep3 TS DS) r r) (e : Gev) : Ucone TS DS r e → gevWf TS e :=
  fun h => ((UconeIff TS DS r hwit hrwf hrr e).1 h).1

theorem UconeDc (hwit : ptracesWit TS DS) (hrwf : gevWf TS r)
    (hrr : ¬ tc (gdep3 TS DS) r r) : dc TS (gdep3 TS DS) (Ucone TS DS r) := by
  intro e e' hU hd hwf'
  have htc := ((UconeIff TS DS r hwit hrwf hrr e).1 hU).2
  exact (UconeIff TS DS r hwit hrwf hrr e').2 ⟨hwf', tc_l hd htc⟩

theorem UconeSubOk (hwit : ptracesWit TS DS) (hrwf : gevWf TS r)
    (hrr : ¬ tc (gdep3 TS DS) r r) : subOk TS (gdep3 TS DS) (Ucone TS DS r) :=
  ⟨UconeDc TS DS r hwit hrwf hrr, UconeWf TS DS r hwit hrwf hrr⟩

/-- The RESTRICTED relation and its acyclicity. -/
def Rcone (x y : Gev) : Prop := gdep3 TS DS x y ∧ Ucone TS DS r x ∧ Ucone TS DS r y

instance RconeDec : DecidableRel (Rcone TS DS r) :=
  fun x y => inferInstanceAs (Decidable (gdep3 TS DS x y ∧ Ucone TS DS r x ∧ Ucone TS DS r y))

theorem tcRcone (x y : Gev) :
    tc (Rcone TS DS r) x y → tc (gdep3 TS DS) x y ∧ Ucone TS DS r x := by
  intro h
  induction h with
  | single h => exact ⟨tc_once h.1, h.2.1⟩
  | tail _ h ih => exact ⟨tc_r ih.1 h.1, ih.2⟩

theorem RconeAcyc (hwit : ptracesWit TS DS) (hrwf : gevWf TS r)
    (hrr : ¬ tc (gdep3 TS DS) r r)
    (hconeacyc : ∀ e, tc (gdep3 TS DS) e r → ¬ tc (gdep3 TS DS) e e) (x : Gev) :
    ¬ tc (Rcone TS DS r) x x := by
  intro hc
  obtain ⟨htc, hU⟩ := tcRcone TS DS r x x hc
  exact hconeacyc x ((UconeIff TS DS r hwit hrwf hrr x).1 hU).2 htc

/-- THE CONE ORDER: a topological order of the cone, and the simulation invariant
established over the whole of it.  (O2: `hfetch`, deviation 5.) -/
theorem coneQinv (hwf : ptracesWf pstep TS) (hwsi : ptracesWsInit TS) (hco : ∀ a, coTc TS a)
    (hwfl : writesFulfilled TS) (hlf : latFreeProg pstep) (hobl : tsOblivious pstep)
    (hcls : clsCanonical pcls TS) (hclsobl : pclsObl pcls) (himg : TS.ptImg = img)
    (_hnag : TS.ptTrs.length = ps.length)
    (hdata : ∀ (p : Nat) (m : Wmsg), TS.ptLog[p]? = some m → m.wmData ≠ [])
    (hps0 : ∀ (j : Nat) (T : Atrace P D) (ag0 : Wpagent P), TS.ptTrs[j]? = some T →
      T.atAgs[0]? = some ag0 → ps[j]? = some ag0.paSt)
    (hwit : ptracesWit TS DS) (hd0 : DS.pdInit = d0) (hfetch : fetchSrcOk TS)
    (hrwf : gevWf TS r) (hrr : ¬ tc (gdep3 TS DS) r r)
    (hconeacyc : ∀ e, tc (gdep3 TS DS) e r → ¬ tc (gdep3 TS DS) e e) :
    ∃ order,
      Qinv pstep pcls TS DS img d0 ps order ∧
      (∀ e, e ∈ order ↔ (gevWf TS e ∧ tc (gdep3 TS DS) e r)) := by
  obtain ⟨order, hnd, hmem0, hord⟩ :=
    topoSort (Rcone TS DS r) (gevEnumS TS (Ucone TS DS r))
      (RconeAcyc TS DS r hwit hrwf hrr hconeacyc) (nodupGevEnumS TS _)
  have hmem : ∀ e, e ∈ order ↔ (gevWf TS e ∧ Ucone TS DS r e) := fun e =>
    (hmem0 e).trans (elemOfGevEnumS TS _ e)
  have hpre : ∀ n, n ≤ order.length → Qinv pstep pcls TS DS img d0 ps (order.take n) := by
    intro n
    induction n with
    | zero =>
      intro _
      rw [List.take_zero]
      exact QinvNil pstep pcls TS DS img d0 ps hwf hps0 hd0
    | succ n ih =>
      intro hn
      obtain ⟨e, he⟩ := Option.isSome_iff_exists.1
        (lookup_lt_is_Some_2 (l := order) (i := n) (by omega))
      rw [take_S_r he]
      have hein : e ∈ order := elem_of_list_lookup.2 ⟨n, he⟩
      have hes := (hmem e).1 hein
      refine QinvStep pstep pcls TS DS img d0 ps hwf hwsi hco hwfl hlf hobl hcls hclsobl himg
        hdata hwit hfetch (order.take n) e (ih (by omega)) hes.1 ?_ ?_
      · -- not already processed
        intro hin
        obtain ⟨i, hi, hilt⟩ := elem_of_take.1 hin
        have := NoDup_lookup hnd hi he
        omega
      · -- every predecessor is processed — the cone is `gdep3`-closed
        intro e' hd hwf'
        have hU' := UconeDc TS DS r hwit hrwf hrr e e' hes.2 hd hwf'
        have he' : e' ∈ order := (hmem e').2 ⟨hwf', hU'⟩
        obtain ⟨i, hi⟩ := elem_of_list_lookup.1 he'
        have hlt : i < n := hord i n e' e hi he ⟨hd, hU', hes.2⟩
        exact elem_of_take.2 ⟨i, hi, hlt⟩
  have hQ := hpre order.length (Nat.le_refl _)
  rw [take_ge (Nat.le_refl _)] at hQ
  refine ⟨order, hQ, fun e => ?_⟩
  rw [hmem e]
  constructor
  · rintro ⟨hw, hU⟩
    exact ⟨hw, ((UconeIff TS DS r hwit hrwf hrr e).1 hU).2⟩
  · rintro ⟨hw, htc⟩
    exact ⟨hw, (UconeIff TS DS r hwit hrwf hrr e).2 ⟨hw, htc⟩⟩

end cone

/-! ## LAYER 6: two exhibit helpers -/

theorem aevPostCohRead {D : Type} (σ : Nat → Nat) (ev : Aev D) (w : Wstate) (base : Int)
    (tvs : List (Nat × BitVec 8)) (jb t : Nat) (v : BitVec 8) :
    tvs[jb]? = some (t, v) →
    ((∃ aq lat asrc, ev.aeLb = LLoad aq lat base tvs asrc) ∨
     (∃ aq rl data asrc vsrc ts,
        ev.aeLb = LRmw aq rl base tvs data asrc vsrc ∧ ev.aeTs = some ts) ∨
     -- THE RMW SPLIT (S2): the exclusive read is a third reading shape
     (∃ aq asrc, ev.aeLb = LExLoad aq base tvs asrc)) →
    σ t ≤ coh (aevPost σ ev w) (base + (jb : Int)) := by
  intro htv hlb
  have hfm : ((tvs.map Prod.fst).map σ)[jb]? = some (σ t) := by simp [htv]
  rcases hlb with ⟨aq, lat, asrc, hlb⟩ | ⟨aq, rl, data, asrc, vsrc, ts, hlb, hts⟩ | ⟨aq, asrc, hlb⟩
  · simp only [aevPost, hlb]
    exact loadPostRunDCoh _ _ _ _ _ jb (σ t) hfm
  · simp only [aevPost, hlb, hts]
    exact Nat.le_trans (loadPostRunDCoh _ _ _ _ _ jb (σ t) hfm)
      (wsLeCoh _ _ _ (storePostRunDLe _ _ _ _ _ _ _))
  · simp only [aevPost, hlb]
    exact exloadPostRunDCoh _ _ _ _ _ jb (σ t) hfm

theorem astepReadLogByte {P : Type} (img : Image) (log : List Wmsg) (i : Nat) (ag : Wpagent P)
    (l : Wlabel) (f : Wstate → Wstate) (Dl : Option Nat) (base : Int)
    (tvs : List (Nat × BitVec 8)) (jb t : Nat) (v : BitVec 8) :
    astepOk img log i ag l f Dl →
    ((∃ aq lat asrc, l = LLoad aq lat base tvs asrc) ∨
     (∃ aq rl data asrc vsrc, l = LRmw aq rl base tvs data asrc vsrc) ∨
     -- THE RMW SPLIT (S2)
     (∃ aq asrc, l = LExLoad aq base tvs asrc)) →
    tvs[jb]? = some (t, v) →
    logByte img log t (base + (jb : Int)) = some v := by
  intro hok hlb htv
  rcases hlb with ⟨aq, lat, asrc, rfl⟩ | ⟨aq, rl, data, asrc, vsrc, rfl⟩ | ⟨aq, asrc, rfl⟩
  · exact (hok.1 jb t v htv).1
  · obtain ⟨_, _, _, _, _, hro, _⟩ := hok
    exact (hro jb t v htv).1
  · exact (hok.1 jb t v htv).1

/-! ## LAYER 5b: THE MINIMAL-BAD-TARGET CONE IS ACYCLIC -/

/-- A0'': the cone premise is served at `W ∩ onCyc`. -/
theorem rfEdgesOkOnMin {P D : Type} (TS : Ptraces P D) (DS : Pdevs D) (nh : Nat) (b2 : Gev) :
    edgesSplitCyc nh TS DS → badMin nh TS DS b2 →
    rfEdgesOkOnMs TS (fun e => tc (gdep3 TS DS) e b2 ∧ onCyc TS e) := by
  intro hsplit hmin f1 f2 T ts a k' ev' hts hrd hne ⟨hW, hcy⟩ hT hlt hev hsome hms
  rcases hsplit f1 f2 T ts a k' ev' hts hrd hne hcy hT hlt hev hsome hms with hok | hbad
  · exact hok
  · exact absurd hW (hmin f1 f2 hbad)

theorem rtcGdep2Gdep3 {P D : Type} (TS : Ptraces P D) (DS : Pdevs D) (x y : Gev) :
    rtc (gdep2 TS) x y → rtc (gdep3 TS DS) x y :=
  rtc_subrel (fun a b h => gdep2Gdep3 TS DS a b h)

theorem ancMr {P D : Type} (TS : Ptraces P D) (DS : Pdevs D) (b2 : Gev) :
    ∀ u x, tc (gdep3 TS DS) u b2 → rtc (gdep2 TS) u x → rtc (gdep2 TS) x u →
      tc (gdep3 TS DS) x b2 :=
  fun _ _ hW _ hxu => tc_rtc_l (rtcGdep2Gdep3 TS DS _ _ hxu) hW

theorem coneAcyc2OfMin {P D : Type} (pstep : P → D → Wlabel → P → D → Prop)
    (TS : Ptraces P D) (DS : Pdevs D) (nh : Nat) (b2 : Gev) :
    ptracesWf pstep TS → ptracesFwdOwn TS → eeOk TS →
    edgesSplitCyc nh TS DS → badMin nh TS DS b2 →
    ∀ e, tc (gdep3 TS DS) e b2 → ¬ tc (gdep2 TS) e e :=
  fun hwf hfo hee hsplit hmin =>
    gdep2AcyclicOnCyc pstep TS (fun e => tc (gdep3 TS DS) e b2) hwf hfo
      (rfEdgesOkOnMin TS DS nh b2 hsplit hmin) hee (ancMr TS DS b2)

theorem coneAcycOfMin {P D : Type} (pstep : P → D → Wlabel → P → D → Prop)
    (TS : Ptraces P D) (DS : Pdevs D) (nh : Nat) (b2 : Gev) :
    ptracesWf pstep TS → ptracesFwdOwn TS → eeOk TS →
    ptracesWit TS DS → devWitOk TS DS →
    edgesSplitCyc nh TS DS → badMin nh TS DS b2 →
    ∀ e, tc (gdep3 TS DS) e b2 → ¬ tc (gdep3 TS DS) e e :=
  fun hwf hfo hee hwit hwok hsplit hmin e he =>
    gdep3AcyclicAtWit TS DS e hwit hwok
      (coneAcyc2OfMin pstep TS DS nh b2 hwf hfo hee hsplit hmin e he)

/-- THE DEV-FREE READINGS: with an empty witness `gdep3` IS `gdep2`. -/
theorem tcGdep3Nil {P D : Type} (TS : Ptraces P D) (d : D) (x y : Gev) :
    tc (gdep3 TS ⟨d, []⟩) x y → tc (gdep2 TS) x y := by
  intro h
  induction h with
  | single h => exact tc_once (gdep3NilGdep2 TS d _ _ h)
  | tail _ h ih => exact tc_r ih (gdep3NilGdep2 TS d _ _ h)

theorem coneAcycOfMinNil {P D : Type} (pstep : P → D → Wlabel → P → D → Prop)
    (TS : Ptraces P D) (d : D) (nh : Nat) (b2 : Gev) :
    ptracesWf pstep TS → ptracesFwdOwn TS → eeOk TS →
    (∀ (i : Nat) (T : Atrace P D) (k : Nat) (ev : Aev D), TS.ptTrs[i]? = some T →
       T.atEvs[k]? = some ev → ev.aeDev = none) →
    edgesSplitCyc nh TS ⟨d, []⟩ → badMin nh TS ⟨d, []⟩ b2 →
    ∀ e, tc (gdep2 TS) e b2 → ¬ tc (gdep2 TS) e e := by
  intro hwf hfo hee hdf hsplit hmin e he hc
  exact coneAcycOfMin pstep TS ⟨d, []⟩ nh b2 hwf hfo hee (ptracesWitNil TS d hdf)
    (devWitOkNil TS d) hsplit hmin e (tcGdep2Gdep3 TS _ e b2 he) (tcGdep2Gdep3 TS _ e e hc)

/-- (O2: `hfetch`, deviation 5.) -/
theorem coneQinvNil {P D : Type} (pstep : P → D → Wlabel → P → D → Prop)
    (pcls : P → Wlabel → Wstate → WmClass)
    (TS : Ptraces P D) (img : Image) (d0 : D) (ps : List P) :
    ptracesWf pstep TS → ptracesWsInit TS → (∀ a, coTc TS a) →
    writesFulfilled TS → latFreeProg pstep → tsOblivious pstep →
    clsCanonical pcls TS → pclsObl pcls →
    TS.ptImg = img → TS.ptTrs.length = ps.length →
    (∀ (p : Nat) (m : Wmsg), TS.ptLog[p]? = some m → m.wmData ≠ []) →
    (∀ (j : Nat) (T : Atrace P D) (ag0 : Wpagent P), TS.ptTrs[j]? = some T →
       T.atAgs[0]? = some ag0 → ps[j]? = some ag0.paSt) →
    (∀ (j : Nat) (T : Atrace P D) (k : Nat) (ev : Aev D), TS.ptTrs[j]? = some T →
       T.atEvs[k]? = some ev → ev.aeDev = none) →
    fetchSrcOk TS →
    ∀ r, gevWf TS r → ¬ tc (gdep2 TS) r r →
    (∀ e, tc (gdep2 TS) e r → ¬ tc (gdep2 TS) e e) →
    ∃ order,
      Qinv pstep pcls TS ⟨d0, []⟩ img d0 ps order ∧
      (∀ e, e ∈ order ↔ (gevWf TS e ∧ tc (gdep2 TS) e r)) := by
  intro hwf hwsi hco hwfl hlf hobl hcls hclsobl himg hnag hdata hps0 hdf hfetch r hrwf hrr hcone
  obtain ⟨order, hQ, hmem⟩ :=
    coneQinv pstep pcls TS ⟨d0, []⟩ img d0 ps r hwf hwsi hco hwfl hlf hobl hcls hclsobl himg
      hnag hdata hps0 (ptracesWitNil TS d0 hdf) rfl hfetch hrwf
      (fun hc => hrr (tcGdep3Nil TS d0 r r hc))
      (fun e he hc => hcone e (tcGdep3Nil TS d0 e r he) (tcGdep3Nil TS d0 e e hc))
  refine ⟨order, hQ, fun e => ?_⟩
  rw [hmem e]
  exact ⟨fun ⟨h1, h2⟩ => ⟨h1, tcGdep3Nil TS d0 e r h2⟩,
    fun ⟨h1, h2⟩ => ⟨h1, tcGdep2Gdep3 TS _ e r h2⟩⟩

/-! ## THE EXHIBIT -/

section exhibit

variable {P D : Type}
variable (pstep : P → D → Wlabel → P → D → Prop)
variable (pcls : P → Wlabel → Wstate → WmClass)
variable (TS : Ptraces P D) (DS : Pdevs D) (img : Image) (d0 : D) (ps : List P)

/-- THE EXHIBIT: a minimal bad edge builds a promise-free run to a
HART-RESTRICTED VIOLATING configuration.  (O2: `hfetch`, deviation 5.) -/
theorem badEdgeViolates (hwf : ptracesWf pstep TS) (hwsi : ptracesWsInit TS)
    (hco : ∀ a, coTc TS a) (hwfl : writesFulfilled TS) (hlf : latFreeProg pstep)
    (hobl : tsOblivious pstep) (hcls : clsCanonical pcls TS) (hclsobl : pclsObl pcls)
    (himg : TS.ptImg = img) (hnag : TS.ptTrs.length = ps.length)
    (hdata : ∀ (p : Nat) (m : Wmsg), TS.ptLog[p]? = some m → m.wmData ≠ [])
    (hps0 : ∀ (j : Nat) (T : Atrace P D) (ag0 : Wpagent P), TS.ptTrs[j]? = some T →
      T.atAgs[0]? = some ag0 → ps[j]? = some ag0.paSt)
    (hwit : ptracesWit TS DS) (hd0 : DS.pdInit = d0) (hwok : devWitOk TS DS)
    (hfo : ptracesFwdOwn TS) (hee : eeOk TS) (nh : Nat) (hsplit : edgesSplitCyc nh TS DS)
    (hfetch : fetchSrcOk TS) (b1 b2 : Gev) :
    bad nh TS DS b1 b2 → badMin nh TS DS b2 →
    ∃ cf, rtc (wpPfRun pstep pcls) (wpInit img d0 ps) cf ∧
      violationHart clsOf pubOf nh cf := by
  intro hbad hmin
  have hbad' := hbad
  obtain ⟨hrf, hne, hh1, hh2, ⟨t, m, hts1, hlogm, hak⟩, hnopub⟩ := hbad'
  obtain ⟨t', a, hts1', hrd2⟩ := hrf
  rw [hts1] at hts1'
  cases hts1'
  have hrr : ¬ tc (gdep3 TS DS) b2 b2 := hmin b1 b2 hbad
  have hb2wf := gevReadsWf TS b2 a t hrd2
  have hb1wf := gevTsWf TS b1 t hts1
  have htpos := gevTsPos pstep TS b1 t hwf hts1
  -- the cone, sorted, plus the bad read itself
  obtain ⟨order, hQ, hmem⟩ :=
    coneQinv pstep pcls TS DS img d0 ps b2 hwf hwsi hco hwfl hlf hobl hcls hclsobl himg hnag
      hdata hps0 hwit hd0 hfetch hb2wf hrr
      (coneAcycOfMin pstep TS DS nh b2 hwf hfo hee hwit hwok hsplit hmin)
  have hq := QinvOrder pstep pcls TS DS img d0 ps order hQ
  have hb2nin : b2 ∉ order := fun hin => hrr ((hmem b2).1 hin).2
  have hpre3 : ∀ e', gdep3 TS DS e' b2 → gevWf TS e' → e' ∈ order :=
    fun e' hd hw' => (hmem e').2 ⟨hw', tc_once hd⟩
  have hpre2 : ∀ e', gdep2 TS e' b2 → gevWf TS e' → e' ∈ order :=
    fun e' hd hw' => hpre3 e' (gdep2Gdep3 TS DS e' b2 hd) hw'
  have hQ' := QinvStep pstep pcls TS DS img d0 ps hwf hwsi hco hwfl hlf hobl hcls hclsobl himg
    hdata hwit hfetch order b2 hQ hb2wf hb2nin hpre3
  have hq' := QinvOrder pstep pcls TS DS img d0 ps (order ++ [b2]) hQ'
  obtain ⟨cf, hrun, -, hclog, -, hcags, -⟩ :=
    QinvRun pstep pcls TS DS img d0 ps (order ++ [b2]) hQ'
  refine ⟨cf, hrun, ?_⟩
  -- the bad message and its pf position
  have hb1in : b1 ∈ order := (hmem b1).2 ⟨hb1wf,
    tc_once (gdep2Gdep3 TS DS b1 b2 (grfGdep2 TS b1 b2 ⟨t, a, hts1, hrd2⟩))⟩
  have hb1in' : b1 ∈ order ++ [b2] := List.mem_append_left _ hb1in
  have htfl : t ∈ fl TS (order ++ [b2]) := (elemOfFl TS _ t).2 ⟨b1, hb1in', hts1⟩
  obtain ⟨hp1, -, hp3⟩ := pfLogPi pstep TS hwf (order ++ [b2]) t hq' htfl
  have hmsgeq : msgAt TS t = m := msgAtEq TS t m hlogm
  obtain ⟨base0, data0, kc, hm0⟩ := gevTsMsg pstep TS b1 t hwf hts1
  have hmeq : m = ⟨base0, data0, some b1.1, kc⟩ := by
    rw [hlogm] at hm0; exact Option.some.inj hm0
  have htid : m.wmTid = some b1.1 := by rw [hmeq]
  -- the reader's event and the byte it read
  obtain ⟨T2, hT2, -⟩ := (gevWfBounds TS b2).1 hb2wf
  obtain ⟨ev2, hev2, hinrd⟩ := gevReadsEv TS b2 a t T2 hT2 hrd2
  have hatr2 := hwf b2.1 T2 hT2
  obtain ⟨ag2, -, -, f2, -, -, -, hok2, -⟩ :=
    astepsWfStep pstep TS.ptImg TS.ptLog b2.1 T2.atAgs T2.atEvs b2.2 ev2 hatr2 hev2
  have hshape : ∃ (base : Int) (tvs : List (Nat × BitVec 8)) (jb : Nat) (v : BitVec 8),
      a = base + (jb : Int) ∧ tvs[jb]? = some (t, v) ∧
      ((∃ aq lat asrc, ev2.aeLb = LLoad aq lat base tvs asrc) ∨
       (∃ aq rl data asrc vsrc ts,
          ev2.aeLb = LRmw aq rl base tvs data asrc vsrc ∧ ev2.aeTs = some ts) ∨
       -- THE RMW SPLIT (S2): the exclusive read is a third reading shape
       (∃ aq asrc, ev2.aeLb = LExLoad aq base tvs asrc)) := by
    obtain ⟨lb2, ots2, dv2⟩ := ev2
    cases lb2 with
    | LLoad aq lat base tvs asrc =>
      obtain ⟨jb, v, htv, rfl⟩ := (memTvsReads base tvs a t).1 hinrd
      exact ⟨base, tvs, jb, v, rfl, htv, Or.inl ⟨aq, lat, asrc, rfl⟩⟩
    | LRmw aq rl base tvs data asrc vsrc =>
      obtain ⟨jb, v, htv, rfl⟩ := (memTvsReads base tvs a t).1 hinrd
      obtain ⟨ts2, k2, _, _, _, _, _, _, _, hts2⟩ := hok2
      exact ⟨base, tvs, jb, v, rfl, htv, Or.inr (Or.inl ⟨aq, rl, data, asrc, vsrc, ts2, rfl, hts2⟩)⟩
    | LExLoad aq base tvs asrc =>
      obtain ⟨jb, v, htv, rfl⟩ := (memTvsReads base tvs a t).1 hinrd
      exact ⟨base, tvs, jb, v, rfl, htv, Or.inr (Or.inr ⟨aq, asrc, rfl⟩)⟩
    | LSilent => simp [lbReads] at hinrd
    | LStore => simp [lbReads] at hinrd
    | LFence => simp [lbReads] at hinrd
    | LDev => simp [lbReads] at hinrd
    | LRegW => simp [lbReads] at hinrd
    | LCtrl => simp [lbReads] at hinrd
    | LInstr => simp [lbReads] at hinrd
    | LExStore => simp [lbReads] at hinrd
    | LIFetch => simp [lbReads] at hinrd
  obtain ⟨base, tvs, jb, v, ha, htv, hlbsh⟩ := hshape
  -- the message really writes that byte
  have hlbv : logByte TS.ptImg TS.ptLog t (base + (jb : Int)) = some v := by
    refine astepReadLogByte TS.ptImg TS.ptLog b2.1 ag2 ev2.aeLb f2 ev2.aeTs base tvs jb t v
      hok2 ?_ htv
    rcases hlbsh with ⟨aq, lat, asrc, hl⟩ | ⟨aq, rl, data, asrc, vsrc, _, hl, _⟩ | ⟨aq, asrc, hl⟩
    · exact Or.inl ⟨aq, lat, asrc, hl⟩
    · exact Or.inr (Or.inl ⟨aq, rl, data, asrc, vsrc, hl⟩)
    · exact Or.inr (Or.inr ⟨aq, asrc, hl⟩)
  have hbyte : (msgByte m (base + (jb : Int))).isSome := by
    rw [logBytePos TS.ptImg TS.ptLog t m _ htpos hlogm] at hlbv
    rw [hlbv]; rfl
  -- the reader's coherence floor
  have hnproc2 : nproc (order ++ [b2]) b2.1 = b2.2 + 1 := by
    rw [nprocAppEq order b2, nprocCur TS order b2 hq hb2wf hb2nin hpre2]
  obtain ⟨agn2, -, hlk2⟩ := hcags b2.1 T2 hT2
  rw [hnproc2, take_S_r hev2, aevsPostApp] at hlk2
  have hcoh : pi TS (order ++ [b2]) t ≤
      coh (aevPost (pi TS (order ++ [b2])) ev2
        (aevsPost (pi TS (order ++ [b2])) (T2.atEvs.take b2.2) wsInit)) (base + (jb : Int)) :=
    aevPostCohRead _ ev2 _ base tvs jb t v htv hlbsh
  -- the violating configuration
  refine ⟨pi TS (order ++ [b2]) t - 1, m, b1.1, b2.1, base + (jb : Int), ?_, htid,
    ⟨b1.1, htid, hh1⟩, ?_, ?_, fun h => hne h.symm, ⟨b2.1, rfl, hh2⟩, hbyte, ?_⟩
  · rw [hclog, hp3, hmsgeq]
  · simp only [clsOf, hak]
  · -- NOT PUBLISHED: a direct reading of `bad`'s no-publishing-ancestor conjunct
    rintro ⟨p', m', heq, hlogp, hpub⟩
    have hp' : p' = pi TS (order ++ [b2]) t - 1 := by omega
    subst hp'
    rw [hclog, hp3, hmsgeq] at hlogp
    cases hlogp
    rw [htid] at hpub
    obtain ⟨q, mq, hle, hq0, htidq, hrelq⟩ := hpub
    rw [hclog, WeakRobustSim.pfLog, list_lookup_fmap] at hq0
    cases hfl0 : (fl TS (order ++ [b2]))[q]? with
    | none => rw [hfl0] at hq0; cases hq0
    | some t0 =>
      rw [hfl0] at hq0
      simp only [Option.map_some, Option.some.injEq] at hq0
      subst hq0
      have ht0in : t0 ∈ fl TS (order ++ [b2]) := elem_of_list_lookup.2 ⟨q, hfl0⟩
      -- … hence a processed FULFIL, and its author is the bad writer
      obtain ⟨ep, hepin, hepts, heplog, heptid⟩ := flMsg pstep TS hwf _ t0 hq' ht0in
      have hepag : ep.1 = b1.1 := by
        rw [heptid] at htidq; exact Option.some.inj htidq
      have hpiq : pi TS (order ++ [b2]) t0 = q + 1 := piMem pstep TS hwf _ q t0 hq' hfl0
      -- it is po-AT-OR-AFTER the author's own fulfil
      have hepge : b1.2 ≤ ep.2 := by
        rcases Nat.lt_or_ge ep.2 b1.2 with hlt | hge
        · exfalso
          have htcb1 : tc (gdep2 TS) ep b1 :=
            tc_once (gpoGdep2 TS ep b1 ⟨hepag, hlt, gevTsWf TS ep t0 hepts, hb1wf⟩)
          have := piLtOfTc pstep TS hwf _ ep b1 t0 t hq' hb1in' htcb1 hepts hts1
          omega
        · exact hge
      -- and it is a STRICT ANCESTOR of the reader
      have hepord : ep ∈ order := by
        rcases List.mem_append.1 hepin with h | h
        · exact h
        · exfalso
          rw [List.mem_singleton] at h
          apply hne
          rw [← hepag, h]
      exact hnopub ⟨ep, hepag, hepge, ⟨t0, msgAt TS t0, hepts, heplog, hrelq⟩,
        ((hmem ep).1 hepord).2⟩
  · simp only [obsFlr, hlk2]
    omega

/-- …hence, under `pfViolationFreeHart`, NO bad edge exists at all. -/
theorem noBadEdge (hwf : ptracesWf pstep TS) (hwsi : ptracesWsInit TS)
    (hco : ∀ a, coTc TS a) (hwfl : writesFulfilled TS) (hlf : latFreeProg pstep)
    (hobl : tsOblivious pstep) (hcls : clsCanonical pcls TS) (hclsobl : pclsObl pcls)
    (himg : TS.ptImg = img) (hnag : TS.ptTrs.length = ps.length)
    (hdata : ∀ (p : Nat) (m : Wmsg), TS.ptLog[p]? = some m → m.wmData ≠ [])
    (hps0 : ∀ (j : Nat) (T : Atrace P D) (ag0 : Wpagent P), TS.ptTrs[j]? = some T →
      T.atAgs[0]? = some ag0 → ps[j]? = some ag0.paSt)
    (hwit : ptracesWit TS DS) (hd0 : DS.pdInit = d0) (hwok : devWitOk TS DS)
    (hfo : ptracesFwdOwn TS) (hee : eeOk TS) (nh : Nat) (hsplit : edgesSplitCyc nh TS DS)
    (hfetch : fetchSrcOk TS) :
    pfViolationFreeHart clsOf pubOf nh pstep pcls img d0 ps → badWf nh TS DS →
    ∀ e1 e2, ¬ bad nh TS DS e1 e2 := by
  intro hvf hbwf e1 e2 hbad
  obtain ⟨f1, f2, hbadf, hmin⟩ := hbwf e1 e2 hbad
  obtain ⟨cf, hrun, hviol⟩ := badEdgeViolates pstep pcls TS DS img d0 ps hwf hwsi hco hwfl hlf
    hobl hcls hclsobl himg hnag hdata hps0 hwit hd0 hwok hfo hee nh hsplit hfetch f1 f2
    hbadf hmin
  exact hvf cf hrun hviol

/-- …so the per-edge premise is the full `rfEdgesOk` after all, and the extended
graph is acyclic. -/
theorem gdep2AcyclicMain (hwf : ptracesWf pstep TS) (hwsi : ptracesWsInit TS)
    (hco : ∀ a, coTc TS a) (hwfl : writesFulfilled TS) (hlf : latFreeProg pstep)
    (hobl : tsOblivious pstep) (hcls : clsCanonical pcls TS) (hclsobl : pclsObl pcls)
    (himg : TS.ptImg = img) (hnag : TS.ptTrs.length = ps.length)
    (hdata : ∀ (p : Nat) (m : Wmsg), TS.ptLog[p]? = some m → m.wmData ≠ [])
    (hps0 : ∀ (j : Nat) (T : Atrace P D) (ag0 : Wpagent P), TS.ptTrs[j]? = some T →
      T.atAgs[0]? = some ag0 → ps[j]? = some ag0.paSt)
    (hwit : ptracesWit TS DS) (hd0 : DS.pdInit = d0) (hwok : devWitOk TS DS)
    (hfo : ptracesFwdOwn TS) (hee : eeOk TS) (nh : Nat) (hsplit : edgesSplitCyc nh TS DS)
    (hfetch : fetchSrcOk TS) :
    pfViolationFreeHart clsOf pubOf nh pstep pcls img d0 ps → badWf nh TS DS →
    gdep2Acyclic TS := by
  intro hvf hbwf
  have hrf : rfEdgesOkOnMs TS (fun e => True ∧ onCyc TS e) := by
    intro e1 e2 T ts b k' ev' hts hrd hne ⟨_, hW⟩ hT hlt hev hsome hms
    rcases hsplit e1 e2 T ts b k' ev' hts hrd hne hW hT hlt hev hsome hms with hok | hbad
    · exact hok
    · exact (noBadEdge pstep pcls TS DS img d0 ps hwf hwsi hco hwfl hlf hobl hcls hclsobl himg
        hnag hdata hps0 hwit hd0 hwok hfo hee nh hsplit hfetch hvf hbwf e1 e2 hbad).elim
  intro e
  exact gdep2AcyclicOnCyc pstep TS (fun _ => True) hwf hfo hrf hee
    (fun _ _ _ _ _ => trivial) e trivial

/-- …and the FABRIC-ORDERED graph is acyclic too, by A0′. -/
theorem gdep3AcyclicMain (hwf : ptracesWf pstep TS) (hwsi : ptracesWsInit TS)
    (hco : ∀ a, coTc TS a) (hwfl : writesFulfilled TS) (hlf : latFreeProg pstep)
    (hobl : tsOblivious pstep) (hcls : clsCanonical pcls TS) (hclsobl : pclsObl pcls)
    (himg : TS.ptImg = img) (hnag : TS.ptTrs.length = ps.length)
    (hdata : ∀ (p : Nat) (m : Wmsg), TS.ptLog[p]? = some m → m.wmData ≠ [])
    (hps0 : ∀ (j : Nat) (T : Atrace P D) (ag0 : Wpagent P), TS.ptTrs[j]? = some T →
      T.atAgs[0]? = some ag0 → ps[j]? = some ag0.paSt)
    (hwit : ptracesWit TS DS) (hd0 : DS.pdInit = d0) (hwok : devWitOk TS DS)
    (hfo : ptracesFwdOwn TS) (hee : eeOk TS) (nh : Nat) (hsplit : edgesSplitCyc nh TS DS)
    (hfetch : fetchSrcOk TS) :
    pfViolationFreeHart clsOf pubOf nh pstep pcls img d0 ps → badWf nh TS DS →
    gdep3Acyclic TS DS :=
  fun hvf hbwf => gdep3AcyclicOfWit TS DS hwit
    (gdep2AcyclicMain pstep pcls TS DS img d0 ps hwf hwsi hco hwfl hlf hobl hcls hclsobl himg
      hnag hdata hps0 hwit hd0 hwok hfo hee nh hsplit hfetch hvf hbwf) hwok

end exhibit

/-! ## LAYER 7: THE ASSEMBLED THEOREM, and W2c's transport -/

/-- The premise package, per traced bundle. -/
def mainPremises {P D : Type} (nh : Nat) (TS : Ptraces P D) (DS : Pdevs D) : Prop :=
  edgesSplitCyc nh TS DS ∧ badWf nh TS DS ∧ eeOk TS ∧
  devWitOk TS DS ∧
  (∃ sync, ptracesBytesOk TS sync)

/-- THE DEV-FREE READING of the package. -/
theorem mainPremisesNil {P D : Type} (nh : Nat) (TS : Ptraces P D) (d : D) :
    edgesSplitCyc nh TS ⟨d, []⟩ → badWf nh TS ⟨d, []⟩ → eeOk TS →
    (∃ sync, ptracesBytesOk TS sync) →
    mainPremises nh TS ⟨d, []⟩ :=
  fun h1 h2 h3 h4 => ⟨h1, h2, h3, devWitOkNil TS d, h4⟩

/-! ### O2 (deviation 5): discharging the fetch-source premise -/

/-- The program-level fetch-freedom predicate (Lean-only; Stage C relocated it here from
`WeakPromiseBridge`, whose bridges no longer need it). -/
def pstepNoFetch {P D : Type} (pstep : P → D → Wlabel → P → D → Prop) : Prop :=
  ∀ p d l p' d', pstep p d l p' d' → ∀ base tvs, l ≠ .LIFetch base tvs

/-- A program that never fetches has a vacuous fetch-source premise
(Lean-only). -/
theorem fetchSrcOkOfNoFetch {P D : Type} (pstep : P → D → Wlabel → P → D → Prop) (d0 : D)
    (TS : Ptraces P D) :
    ptracesWf pstep TS → pstepNoFetch pstep → fetchSrcOk TS := by
  intro hwf hnf
  refine fetchSrcOkNoFetch TS (fun e base tvs hlb => ?_)
  obtain ⟨T, ev, hT, hev, hl⟩ := gevLbSome TS e _ hlb
  obtain ⟨ag, -, st', -, -, -, hps, -, -⟩ :=
    astepsWfStep pstep TS.ptImg TS.ptLog e.1 T.atAgs T.atEvs e.2 ev (hwf e.1 T hT) hev
  obtain ⟨d, d', hst⟩ := astepProgStep pstep d0 ag ev st' hps
  exact hnf _ _ _ _ _ hst base tvs hl

/-- Fetches that answer only never-written bytes (timestamp 0) have a vacuous
fetch-source premise (Lean-only). -/
theorem fetchSrcOkTsZero {P D : Type} (TS : Ptraces P D) :
    (∀ (e : Gev) (base : Int) (tvs : List (Nat × BitVec 8)) (j t : Nat) (v : BitVec 8),
       gevLb TS e = some (LIFetch base tvs) → tvs[j]? = some (t, v) → t = 0) →
    fetchSrcOk TS :=
  fun h e base tvs j t v hl htv hpos => absurd (h e base tvs j t v hl htv) (by omega)

section main

variable {P D : Type}
variable (pstep : P → D → Wlabel → P → D → Prop)
variable (pcls : P → Wlabel → Wstate → WmClass)
variable (pdev : P → Wlabel → P → Bool)

/-- A0'': THE ACYCLICITY-CONSUMING FORM.  (O2: `fetchSrcOk TS`, deviation 5.) -/
theorem robustMainAcyc (img : Image) (d0 : D) (ps : List P) (c mid : Wpcfg P D)
    (TS : Ptraces P D) (DS : Pdevs D) :
    latFreeProg pstep → tsOblivious pstep →
    pclsObl pcls →
    rtc (wpPromiseStep (P := P) (D := D)) (wpInit img d0 ps) mid →
    ptracesDevOf pstep pdev TS DS mid c →
    (∀ (p : Nat) (m : Wmsg) (i : Nat), mid.pcLog[p]? = some m → m.wmTid = some i →
       ∃ T, TS.ptTrs[i]? = some T ∧
         (∃ (k : Nat) (ev : Aev D), T.atEvs[k]? = some ev ∧ ev.aeTs = some (p + 1)) ∧
         (∀ (k1 k2 : Nat) (ev1 ev2 : Aev D),
            T.atEvs[k1]? = some ev1 → ev1.aeTs = some (p + 1) →
            T.atEvs[k2]? = some ev2 → ev2.aeTs = some (p + 1) → k1 = k2)) →
    (∀ a, coTc TS a) →
    gdep3Acyclic TS DS →
    clsCanonical pcls TS →
    fetchSrcOk TS →
    ∃ cf, rtc (wpPfRun pstep pcls) (wpInit img d0 ps) cf ∧
      progOf cf = progOf c ∧ (∀ a, memOf cf a = memOf c a) := by
  intro hlf hobl hclsobl hprom hofd hacct hco hacyc hcls hfetch
  have hwit : ptracesWit TS DS := ptracesDevOfWit pstep pdev TS DS mid c hofd
  have hdinit : DS.pdInit = mid.pcDev := hofd.2.1
  have hof := hofd.1
  have hwf : ptracesWf pstep TS := ptracesOfWf pstep TS mid c hof
  have hla : logAuthored mid.pcLog :=
    logAuthoredPromiseRun _ _ (logAuthoredInit img d0 ps) hprom
  have hwfl : writesFulfilled TS := ptracesOfWritesFulfilled pstep TS mid c hof hla hacct
  have hlne : logNe mid.pcLog := logNePromiseRun _ _ (logNeInit img d0 ps) hprom
  have hwsi : ptracesWsInit TS :=
    ptracesOfWsInit pstep TS mid c hof (cfgWsInitPromiseRun _ _ (cfgWsInitInit img d0 ps) hprom)
  obtain ⟨hpimg, hplen, hpdev, hpst⟩ := promiseRunShape (wpInit img d0 ps) mid hprom
  have hd01 : DS.pdInit = d0 := by rw [hdinit, hpdev]; rfl
  obtain ⟨himg0, hlog0, hlent, _, hfst, hlst, hclogc, hcimgc, hclenc⟩ := hof
  have himg1 : TS.ptImg = img := by rw [himg0, hpimg]; rfl
  have hlen1 : TS.ptTrs.length = ps.length := by rw [hlent, hplen]; simp [wpInit]
  have hdata1 : ∀ (p : Nat) (m : Wmsg), TS.ptLog[p]? = some m → m.wmData ≠ [] := by
    rw [hlog0]; exact hlne
  have hps1 : ∀ (j : Nat) (T : Atrace P D) (ag0 : Wpagent P), TS.ptTrs[j]? = some T →
      T.atAgs[0]? = some ag0 → ps[j]? = some ag0.paSt := by
    intro j T ag0 hT hag0
    have hmid : mid.pcAgs[j]? = some ag0 := by rw [← hfst j T hT]; exact hag0
    obtain ⟨ag, hag, hst⟩ := hpst j ag0 hmid
    simp only [wpInit, List.getElem?_map] at hag
    cases hp0 : ps[j]? with
    | none => rw [hp0] at hag; cases hag
    | some p0 =>
      rw [hp0] at hag
      simp only [Option.map_some, Option.some.injEq] at hag
      subst hag
      rw [hst]
  exact simFull pstep pcls TS DS img d0 ps hwf hwsi hco hwfl hlf hobl hcls hclsobl himg1 hlen1
    hdata1 hps1 hwit hd01 hfetch c hacyc (by rw [himg0, hcimgc]) (by rw [hlog0, hclogc])
    (by rw [hclenc, hplen]; simp [wpInit]) hlst

/-- THE BUNDLE FORM (M5/B4).  (O2: `fetchSrcOk TS`, deviation 5.) -/
theorem robustMainBundle (nh : Nat) (img : Image) (d0 : D) (ps : List P) (c mid : Wpcfg P D)
    (TS : Ptraces P D) (DS : Pdevs D) :
    latFreeProg pstep → tsOblivious pstep →
    pclsObl pcls →
    rtc (wpPromiseStep (P := P) (D := D)) (wpInit img d0 ps) mid →
    ptracesDevOf pstep pdev TS DS mid c →
    (∀ (p : Nat) (m : Wmsg) (i : Nat), mid.pcLog[p]? = some m → m.wmTid = some i →
       ∃ T, TS.ptTrs[i]? = some T ∧
         (∃ (k : Nat) (ev : Aev D), T.atEvs[k]? = some ev ∧ ev.aeTs = some (p + 1)) ∧
         (∀ (k1 k2 : Nat) (ev1 ev2 : Aev D),
            T.atEvs[k1]? = some ev1 → ev1.aeTs = some (p + 1) →
            T.atEvs[k2]? = some ev2 → ev2.aeTs = some (p + 1) → k1 = k2)) →
    mainPremises nh TS DS →
    clsCanonical pcls TS →
    pfViolationFreeHart clsOf pubOf nh pstep pcls img d0 ps →
    fetchSrcOk TS →
    ∃ cf, rtc (wpPfRun pstep pcls) (wpInit img d0 ps) cf ∧
      progOf cf = progOf c ∧ (∀ a, memOf cf a = memOf c a) := by
  intro hlf hobl hclsobl hprom hofd hacct hpkg hcls hvf hfetch
  have hwit : ptracesWit TS DS := ptracesDevOfWit pstep pdev TS DS mid c hofd
  have hdinit : DS.pdInit = mid.pcDev := hofd.2.1
  obtain ⟨hsplit, hbwf, hee, hwok, sync, hbytes⟩ := hpkg
  have hof := hofd.1
  -- the derived bundle facts — as in `wpBehaviorRobust`
  have hwf : ptracesWf pstep TS := ptracesOfWf pstep TS mid c hof
  have hla : logAuthored mid.pcLog :=
    logAuthoredPromiseRun _ _ (logAuthoredInit img d0 ps) hprom
  have hwfl : writesFulfilled TS := ptracesOfWritesFulfilled pstep TS mid c hof hla hacct
  have hlne : logNe mid.pcLog := logNePromiseRun _ _ (logNeInit img d0 ps) hprom
  have hinit : cfgWsInit mid := cfgWsInitPromiseRun _ _ (cfgWsInitInit img d0 ps) hprom
  have hwsi : ptracesWsInit TS := ptracesOfWsInit pstep TS mid c hof hinit
  have hfo : ptracesFwdOwn TS := ptracesOfFwdOwn pstep TS mid c hinit hof
  have hco : ∀ a, coTc TS a := coSerializedPkg pstep TS sync hwf hwfl hbytes
  obtain ⟨hpimg, hplen, hpdev, hpst⟩ := promiseRunShape (wpInit img d0 ps) mid hprom
  have hd01 : DS.pdInit = d0 := by rw [hdinit, hpdev]; rfl
  obtain ⟨himg0, hlog0, hlent, _, hfst, -, -, -, -⟩ := hof
  have himg1 : TS.ptImg = img := by rw [himg0, hpimg]; rfl
  have hlen1 : TS.ptTrs.length = ps.length := by rw [hlent, hplen]; simp [wpInit]
  have hdata1 : ∀ (p : Nat) (m : Wmsg), TS.ptLog[p]? = some m → m.wmData ≠ [] := by
    rw [hlog0]; exact hlne
  have hps1 : ∀ (j : Nat) (T : Atrace P D) (ag0 : Wpagent P), TS.ptTrs[j]? = some T →
      T.atAgs[0]? = some ag0 → ps[j]? = some ag0.paSt := by
    intro j T ag0 hT hag0
    have hmid : mid.pcAgs[j]? = some ag0 := by rw [← hfst j T hT]; exact hag0
    obtain ⟨ag, hag, hst⟩ := hpst j ag0 hmid
    simp only [wpInit, List.getElem?_map] at hag
    cases hp0 : ps[j]? with
    | none => rw [hp0] at hag; cases hag
    | some p0 =>
      rw [hp0] at hag
      simp only [Option.map_some, Option.some.injEq] at hag
      subst hag
      rw [hst]
  -- THE ACYCLICITY: the exhibit rules out every bad edge
  have hacyc : gdep3Acyclic TS DS :=
    gdep3AcyclicMain pstep pcls TS DS img d0 ps hwf hwsi hco hwfl hlf hobl hcls hclsobl himg1
      hlen1 hdata1 hps1 hwit hd01 hwok hfo hee nh hsplit hfetch hvf hbwf
  exact robustMainAcyc pstep pcls pdev img d0 ps c mid TS DS hlf hobl hclsobl hprom hofd hacct
    hco hacyc hcls hfetch

/-- THE LAYER-1 ROBUSTNESS THEOREM, in its per-behavior form.  (O2: the
per-bundle `fetchSrcOk` premise, deviation 5.) -/
theorem robustMain (nh : Nat) (img : Image) (d0 : D) (ps : List P) (c : Wpcfg P D) :
    pdevOk pstep pdev →
    latFreeProg pstep → tsOblivious pstep →
    pclsObl pcls →
    wpBehavior pstep img d0 ps c →
    (∀ (mid : Wpcfg P D) (TS : Ptraces P D) (DS : Pdevs D),
       rtc (wpPromiseStep (P := P) (D := D)) (wpInit img d0 ps) mid →
       ptracesDevOf pstep pdev TS DS mid c →
       mainPremises nh TS DS) →
    (∀ (mid : Wpcfg P D) (TS : Ptraces P D) (DS : Pdevs D),
       rtc (wpPromiseStep (P := P) (D := D)) (wpInit img d0 ps) mid →
       ptracesDevOf pstep pdev TS DS mid c →
       clsCanonical pcls TS) →
    pfViolationFreeHart clsOf pubOf nh pstep pcls img d0 ps →
    (∀ (mid : Wpcfg P D) (TS : Ptraces P D) (DS : Pdevs D),
       rtc (wpPromiseStep (P := P) (D := D)) (wpInit img d0 ps) mid →
       ptracesDevOf pstep pdev TS DS mid c →
       fetchSrcOk TS) →
    ∃ cf, rtc (wpPfRun pstep pcls) (wpInit img d0 ps) cf ∧
      progOf cf = progOf c ∧ (∀ a, memOf cf a = memOf c a) := by
  intro hpok hlf hobl hclsobl hb hprem hpcan hvf hpfetch
  obtain ⟨mid, TS, DS, hprom, hofd, _, hacct⟩ :=
    wpBehaviorFulfilOnceDev pstep pdev img d0 ps c hpok hlf hb
  exact robustMainBundle pstep pcls pdev nh img d0 ps c mid TS DS hlf hobl hclsobl hprom hofd
    hacct (hprem mid TS DS hprom hofd) (hpcan mid TS DS hprom hofd) hvf
    (hpfetch mid TS DS hprom hofd)

/-! ### W2c PROPER: the transport, over COMPLETABLE prefixes -/

def completable (img : Image) (d0 : D) (ps : List P) (c : Wpcfg P D) : Prop :=
  rtc (wpstep pstep) (wpInit img d0 ps) c ∧
  ∃ cend, rtc (wpstep pstep) c cend ∧ noPromises cend

/-- (O2: the per-completion `fetchSrcOk` premise, deviation 5.) -/
theorem robustTransport (nh : Nat) (img : Image) (d0 : D) (ps : List P) (c : Wpcfg P D) :
    pdevOk pstep pdev →
    latFreeProg pstep → tsOblivious pstep →
    pclsObl pcls →
    completable pstep img d0 ps c →
    (∀ (cend mid : Wpcfg P D) (TS : Ptraces P D) (DS : Pdevs D),
       wpBehavior pstep img d0 ps cend →
       rtc (wpPromiseStep (P := P) (D := D)) (wpInit img d0 ps) mid →
       ptracesDevOf pstep pdev TS DS mid cend →
       mainPremises nh TS DS) →
    (∀ (cend mid : Wpcfg P D) (TS : Ptraces P D) (DS : Pdevs D),
       wpBehavior pstep img d0 ps cend →
       rtc (wpPromiseStep (P := P) (D := D)) (wpInit img d0 ps) mid →
       ptracesDevOf pstep pdev TS DS mid cend →
       clsCanonical pcls TS) →
    pfViolationFreeHart clsOf pubOf nh pstep pcls img d0 ps →
    (∀ (cend mid : Wpcfg P D) (TS : Ptraces P D) (DS : Pdevs D),
       wpBehavior pstep img d0 ps cend →
       rtc (wpPromiseStep (P := P) (D := D)) (wpInit img d0 ps) mid →
       ptracesDevOf pstep pdev TS DS mid cend →
       fetchSrcOk TS) →
    ∃ cend cf,
      rtc (wpstep pstep) c cend ∧ noPromises cend ∧
      rtc (wpPfRun pstep pcls) (wpInit img d0 ps) cf ∧
      progOf cf = progOf cend ∧ (∀ a, memOf cf a = memOf cend a) := by
  rintro hpok hlf hobl hclsobl ⟨hpre, cend, hrest, hnp⟩ hprem hpcan hvf hpfetch
  have hbeh : wpBehavior pstep img d0 ps cend := ⟨rtc_transitive hpre hrest, hnp⟩
  obtain ⟨cf, hrun, hprog, hmem⟩ := robustMain pstep pcls pdev nh img d0 ps cend hpok hlf hobl
    hclsobl hbeh (fun mid TS DS => hprem cend mid TS DS hbeh)
    (fun mid TS DS => hpcan cend mid TS DS hbeh) hvf
    (fun mid TS DS => hpfetch cend mid TS DS hbeh)
  exact ⟨cend, cf, hrest, hnp, hrun, hprog, hmem⟩

/-! ### The fetch-free capstones (Lean-only, deviation 5): `pstepNoFetch`
discharges `fetchSrcOk` -/

theorem robustMainBundleNoFetch (nh : Nat) (img : Image) (d0 : D) (ps : List P)
    (c mid : Wpcfg P D) (TS : Ptraces P D) (DS : Pdevs D) :
    pstepNoFetch pstep →
    latFreeProg pstep → tsOblivious pstep →
    pclsObl pcls →
    rtc (wpPromiseStep (P := P) (D := D)) (wpInit img d0 ps) mid →
    ptracesDevOf pstep pdev TS DS mid c →
    (∀ (p : Nat) (m : Wmsg) (i : Nat), mid.pcLog[p]? = some m → m.wmTid = some i →
       ∃ T, TS.ptTrs[i]? = some T ∧
         (∃ (k : Nat) (ev : Aev D), T.atEvs[k]? = some ev ∧ ev.aeTs = some (p + 1)) ∧
         (∀ (k1 k2 : Nat) (ev1 ev2 : Aev D),
            T.atEvs[k1]? = some ev1 → ev1.aeTs = some (p + 1) →
            T.atEvs[k2]? = some ev2 → ev2.aeTs = some (p + 1) → k1 = k2)) →
    mainPremises nh TS DS →
    clsCanonical pcls TS →
    pfViolationFreeHart clsOf pubOf nh pstep pcls img d0 ps →
    ∃ cf, rtc (wpPfRun pstep pcls) (wpInit img d0 ps) cf ∧
      progOf cf = progOf c ∧ (∀ a, memOf cf a = memOf c a) :=
  fun hnf hlf hobl hclsobl hprom hofd hacct hpkg hcls hvf =>
    robustMainBundle pstep pcls pdev nh img d0 ps c mid TS DS hlf hobl hclsobl hprom hofd hacct
      hpkg hcls hvf
      (fetchSrcOkOfNoFetch pstep d0 TS (ptracesOfWf pstep TS mid c hofd.1) hnf)

theorem robustMainNoFetch (nh : Nat) (img : Image) (d0 : D) (ps : List P) (c : Wpcfg P D) :
    pstepNoFetch pstep →
    pdevOk pstep pdev →
    latFreeProg pstep → tsOblivious pstep →
    pclsObl pcls →
    wpBehavior pstep img d0 ps c →
    (∀ (mid : Wpcfg P D) (TS : Ptraces P D) (DS : Pdevs D),
       rtc (wpPromiseStep (P := P) (D := D)) (wpInit img d0 ps) mid →
       ptracesDevOf pstep pdev TS DS mid c →
       mainPremises nh TS DS) →
    (∀ (mid : Wpcfg P D) (TS : Ptraces P D) (DS : Pdevs D),
       rtc (wpPromiseStep (P := P) (D := D)) (wpInit img d0 ps) mid →
       ptracesDevOf pstep pdev TS DS mid c →
       clsCanonical pcls TS) →
    pfViolationFreeHart clsOf pubOf nh pstep pcls img d0 ps →
    ∃ cf, rtc (wpPfRun pstep pcls) (wpInit img d0 ps) cf ∧
      progOf cf = progOf c ∧ (∀ a, memOf cf a = memOf c a) :=
  fun hnf hpok hlf hobl hclsobl hb hprem hpcan hvf =>
    robustMain pstep pcls pdev nh img d0 ps c hpok hlf hobl hclsobl hb hprem hpcan hvf
      (fun mid TS _ _ hofd =>
        fetchSrcOkOfNoFetch pstep d0 TS (ptracesOfWf pstep TS mid c hofd.1) hnf)

theorem robustTransportNoFetch (nh : Nat) (img : Image) (d0 : D) (ps : List P)
    (c : Wpcfg P D) :
    pstepNoFetch pstep →
    pdevOk pstep pdev →
    latFreeProg pstep → tsOblivious pstep →
    pclsObl pcls →
    completable pstep img d0 ps c →
    (∀ (cend mid : Wpcfg P D) (TS : Ptraces P D) (DS : Pdevs D),
       wpBehavior pstep img d0 ps cend →
       rtc (wpPromiseStep (P := P) (D := D)) (wpInit img d0 ps) mid →
       ptracesDevOf pstep pdev TS DS mid cend →
       mainPremises nh TS DS) →
    (∀ (cend mid : Wpcfg P D) (TS : Ptraces P D) (DS : Pdevs D),
       wpBehavior pstep img d0 ps cend →
       rtc (wpPromiseStep (P := P) (D := D)) (wpInit img d0 ps) mid →
       ptracesDevOf pstep pdev TS DS mid cend →
       clsCanonical pcls TS) →
    pfViolationFreeHart clsOf pubOf nh pstep pcls img d0 ps →
    ∃ cend cf,
      rtc (wpstep pstep) c cend ∧ noPromises cend ∧
      rtc (wpPfRun pstep pcls) (wpInit img d0 ps) cf ∧
      progOf cf = progOf cend ∧ (∀ a, memOf cf a = memOf cend a) :=
  fun hnf hpok hlf hobl hclsobl hcomp hprem hpcan hvf =>
    robustTransport pstep pcls pdev nh img d0 ps c hpok hlf hobl hclsobl hcomp hprem hpcan hvf
      (fun cend mid TS _ _ _ hofd =>
        fetchSrcOkOfNoFetch pstep d0 TS (ptracesOfWf pstep TS mid cend hofd.1) hnf)

end main

/-! ## What W3/W5 inherit from this file

- `clsOf` / `pubOf`: the instantiation of `WeakRobust`'s two Layer-2 parameters;
  φ's obligation is `pfViolationFreeHart clsOf pubOf nh`.
- `bad` / `edgesSplitMs` / `edgesSplitCyc` / `badWf`: the weakened per-edge
  premise and the honest residue.
- `badEdgeViolates`: the exhibit, the sole consumer of `pfViolationFreeHart`.
- `gdep2AcyclicOn` / `rfEdgesOkOnMs`: the relativized walk.
- `robustMain` and `robustTransport`: the assembled theorem and W2c's
  completable-prefix corollary — in Lean carrying the O2 `fetchSrcOk` premise
  (deviation 5), discharged for fetch-free programs by the `…NoFetch` forms. -/

end Weak
