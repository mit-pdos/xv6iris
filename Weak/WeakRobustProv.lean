/-
Weak: **view provenance for the W2b simulation** (M6 W2b (i)).

Rocq: `iris/WeakRobustProv.v` @ xxvzwolszwmp.

The Rocq header, in substance.  THE PROBLEM: the W2b simulation replays a
traced full-machine behavior as a PROMISE-FREE run whose log is a permutation
π of the behavior's timestamps, so the pf agent's `Wstate` is the same
per-event fold with every leaf timestamp transported through π.  π is not
monotone (`π (max S) ≠ max (S.map π)`), so no "the pf views are π of the
behavior's views" lemma can hold.  THE FIX: for every `Wstate` component,
compute from the TRACE ALONE the LEAF SET of message timestamps the component
is the `max` of (the mirror `Lstate`), and state the valuation lemma for an
ARBITRARY transport σ: `lrel σ S w` says every component of `w` is `lval σ`
(the max of σ over the leaves) of the corresponding component of `S`.  `lrel`
is preserved by every step function, with the mirror step on the leaf side and
the σ-TRANSPORTED step on the `Wstate` side (`lrelAevPost`, `lrelAevsPost`).
σ = `id` recovers the behavior's own `Wstate` (`astepsWsFold`: the
behavior's per-agent `Wstate` IS the `id`-fold of its trace prefix); σ = π
gives the promise-free run's.  Injectivity of σ is spent in exactly one place,
`lrelFwdView` (the forward bank's hit/miss is decided on `σ t = σ tf` on the
`Wstate` side and on `t = tf` on the leaf side).  `σ 0 = 0` is used nowhere
here: `sigmaOk` is the packaged consumer-facing notion, the hypothesis of the
top-level theorems; the per-step lemmas take `Function.Injective σ`.  The
provenance bound `laevsLeavesOccur` needs no `t ≠ 0` side condition (`linit`
is leaf-free).  The `coh` component of `lstateLeaf` is stated on
`get? S.lCoh a` (interchangeable with `lcoh S a` by `lcohLeaf`).  The inner
byte folds are related through `tats σ`, aligned by `tatsRun`.  Also here:
`wRelp` is σ-independent (`wRelpAevsPostIndep`), and the reservation of the
σ-fold is the σ-retimed recorded one (`aevsPostRes`) whose recorded column
names an earlier `LExLoad` (`aevsPostResSrc`).  Dependency-free: no Iris, no
Sail.

**Deviations from Rocq.**

1. NAMES: lowerCamelCase as `Weak/WeakMem.lean` deviation 1; the record
   `lstate` ↦ the structure `Lstate` (constructor `LState` ↦ `Lstate.mk`,
   fields `l_coh` ↦ `lCoh`, ...).  No name of this file is in
   `notes/weak-port-dupnames.json`.
2. VOCABULARY: as `WeakMem` deviation 2 (`tvs.*1` ↦ `tvs.map Prod.fst`,
   `σ <$> l` ↦ `l.map σ`, `gmap` ↦ `GMapF` with `get?`/`insert`, `wreg` ↦
   `Nat`, `Inj eq eq σ` ↦ `Function.Injective σ`, `default [] o` ↦
   `o.getD []`, `seq` ↦ `List.range'`, `zip_with` ↦ `List.zipWith`).
   `Corollary` ↦ `theorem`; `Local Lemma fmap_zip_with_gen` is an ordinary
   theorem (`WeakMem` deviation 5); `rev_ind` is `snocInd`.
3. O2 / owner decision D4 (`Weak/WeakPromise.lean` deviation 8): the Lean
   label alphabet has the extra `LIFetch base tvs`.  Both folds treat it as
   the identity (`aevPost σ ⟨LIFetch .., ..⟩ w = w`, `laevPost` likewise),
   exactly as `astepOk`'s `LIFetch` arm (`f = id`); every case analysis over
   labels gains that (trivial) case.  For every Rocq label the definitions
   agree.
4. SECTION VARIABLES: `pstep` is an explicit argument of `astepsWsFold` only
   (`astepOkAevPost` does not mention it); `pdev` is unused (Rocq declares it
   in the section, no statement mentions it).
5. Not imported: `Weak.WeakAxiomatic` (Rocq imports it first only so that
   `WeakPromise`'s label constructors shadow its `Lbl` ones; Lean names are
   qualified, as `Weak/WeakRobustGraph.lean` deviation 7).
6. Lean-only helpers (no Rocq twin): `leafVrOld` … `leafTbank` (the eleven
   introduction forms of `lstateLeaf`, used where Rocq calls `naive_solver`),
   `memIteOr`, and the local tactic `leaf_tac`.

**Name map** (Rocq → Lean): `tlabel_ts` ↦ `tlabelTs`; `tlabel_ts_fst` ↦
`tlabelTsFst`; `aev_post` ↦ `aevPost`; `aevs_post` ↦ `aevsPost`;
`aevs_post_nil` ↦ `aevsPostNil`; `aevs_post_app` ↦ `aevsPostApp`;
`w_relp_foldl_load` ↦ `wRelpFoldlLoad`; `w_relp_load_post_bytes` ↦
`wRelpLoadPostBytes`; `w_relp_load_post_run` ↦ `wRelpLoadPostRun`;
`w_relp_load_post_run_d` ↦ `wRelpLoadPostRunD`; `w_relp_exload_post_run_d` ↦
`wRelpExloadPostRunD`; `w_relp_foldl_store` ↦ `wRelpFoldlStore`;
`w_relp_store_post_bytes_indep` ↦ `wRelpStorePostBytesIndep`;
`w_relp_store_post_run_indep` ↦ `wRelpStorePostRunIndep`;
`w_relp_foldl_store_d` ↦ `wRelpFoldlStoreD`; `w_relp_store_post_run_d_indep` ↦
`wRelpStorePostRunDIndep`; `w_relp_aev_post_indep` ↦ `wRelpAevPostIndep`;
`w_relp_aevs_post_indep` ↦ `wRelpAevsPostIndep`; `res_cols` ↦ `resCols`;
`res_cols_inv` ↦ `resColsInv`; `aev_post_res` ↦ `aevPostRes`; `aevs_post_res`
↦ `aevsPostRes`; `aevs_post_res_init` ↦ `aevsPostResInit`; `aevs_post_res_src`
↦ `aevsPostResSrc`; `astep_ok_aev_post` ↦ `astepOkAevPost`; `asteps_ws_fold` ↦
`astepsWsFold`; `lstate` ↦ `Lstate`; `LState` ↦ `Lstate.mk`; `l_coh` ↦
`Lstate.lCoh`; `l_vrOld` ↦ `Lstate.lVrOld`; `l_vwOld` ↦ `Lstate.lVwOld`;
`l_vrNew` ↦ `Lstate.lVrNew`; `l_vwNew` ↦ `Lstate.lVwNew`; `l_vRel` ↦
`Lstate.lVRel`; `l_fwd` ↦ `Lstate.lFwd`; `l_regv` ↦ `Lstate.lRegv`; `l_vcap` ↦
`Lstate.lVcap`; `l_ldv` ↦ `Lstate.lLdv`; `l_tbank` ↦ `Lstate.lTbank`; `lval`;
`lcoh`; `lregv`; `linit`; `lval_nil` ↦ `lvalNil`; `lval_cons` ↦ `lvalCons`;
`lval_singleton` ↦ `lvalSingleton`; `lval_app` ↦ `lvalApp`; `lval_ge` ↦
`lvalGe`; `lval_le_iff` ↦ `lvalLeIff`; `lval_lt` ↦ `lvalLt`; `lcoh_ins_eq` ↦
`lcohInsEq`; `lcoh_ins_ne` ↦ `lcohInsNe`; `lload_vpre` ↦ `lloadVpre`;
`ldsrc_view` ↦ `ldsrcView`; `lsrcs_view` ↦ `lsrcsView`; `lload_vpre_d` ↦
`lloadVpreD`; `lfwd_view` ↦ `lfwdView`; `lload_post_at` ↦ `lloadPostAt`;
`lstore_post_d` ↦ `lstorePostD`; `lstore_post` ↦ `lstorePost`;
`lstore_post_d_vfL` ↦ `lstorePostDVfL`; `lfence_post` ↦ `lfencePost`;
`lregw_post` ↦ `lregwPost`; `lctrl_post` ↦ `lctrlPost`; `linstr_post` ↦
`linstrPost`; `lload_post_bytes_d` ↦ `lloadPostBytesD`; `lload_post_bytes` ↦
`lloadPostBytes`; `lstore_post_bytes_d` ↦ `lstorePostBytesD`;
`lstore_post_bytes` ↦ `lstorePostBytes`; `lload_post_run_d` ↦
`lloadPostRunD`; `lload_post_run` ↦ `lloadPostRun`; `lexload_post_run_d` ↦
`lexloadPostRunD`; `lstore_post_run_d` ↦ `lstorePostRunD`; `lstore_post_run` ↦
`lstorePostRun`; `laev_post` ↦ `laevPost`; `laevs_post` ↦ `laevsPost`;
`laevs_post_nil` ↦ `laevsPostNil`; `laevs_post_app` ↦ `laevsPostApp`;
`sigma_ok` ↦ `sigmaOk`; `sigma_ok_id` ↦ `sigmaOkId`; `lrel`; `lrel_init` ↦
`lrelInit`; `lrel_tbank` ↦ `lrelTbank`; `lrel_srcs_view` ↦ `lrelSrcsView`;
`lrel_fwd_view` ↦ `lrelFwdView`; `lrel_load_vpre` ↦ `lrelLoadVpre`;
`lrel_load_vpre_d` ↦ `lrelLoadVpreD`; `lrel_load_post_at` ↦ `lrelLoadPostAt`;
`lrel_store_post_d` ↦ `lrelStorePostD`; `lrel_store_post` ↦ `lrelStorePost`;
`lrel_regw_post` ↦ `lrelRegwPost`; `lrel_ctrl_post` ↦ `lrelCtrlPost`;
`lrel_instr_post` ↦ `lrelInstrPost`; `lrel_fence_post` ↦ `lrelFencePost`;
`tats`; `fmap_zip_with_gen` ↦ `fmapZipWithGen`; `tats_run` ↦ `tatsRun`;
`lrel_load_fold` ↦ `lrelLoadFold`; `lrel_load_post_run` ↦ `lrelLoadPostRun`;
`lrel_load_post_run_d` ↦ `lrelLoadPostRunD`; `lrel_store_fold` ↦
`lrelStoreFold`; `lrel_store_fold_d` ↦ `lrelStoreFoldD`; `lrel_ws_res_set` ↦
`lrelWsResSet`; `lrel_lexload_post_run_d` ↦ `lrelLexloadPostRunD`;
`lrel_store_post_run` ↦ `lrelStorePostRun`; `lrel_store_post_run_d` ↦
`lrelStorePostRunD`; `lrel_aev_post` ↦ `lrelAevPost`; `lrel_aevs_post` ↦
`lrelAevsPost`; `lrel_aevs_post_init` ↦ `lrelAevsPostInit`;
`lrel_aevs_post_id` ↦ `lrelAevsPostId`; `aev_ts_occurs` ↦ `aevTsOccurs`;
`ev_ts_occurs` ↦ `evTsOccurs`; `ev_ts_occurs_cons` ↦ `evTsOccursCons`;
`lstate_leaf` ↦ `lstateLeaf`; `lcoh_leaf` ↦ `lcohLeaf`; `lregv_leaf` ↦
`lregvLeaf`; `lsrcs_view_leaf` ↦ `lsrcsViewLeaf`; `linit_no_leaf` ↦
`linitNoLeaf`; `lload_vpre_leaf` ↦ `lloadVpreLeaf`; `lload_vpre_d_leaf` ↦
`lloadVpreDLeaf`; `lfwd_view_leaf` ↦ `lfwdViewLeaf`; `lload_post_at_leaf` ↦
`lloadPostAtLeaf`; `lstore_post_d_leaf` ↦ `lstorePostDLeaf`;
`lstore_post_leaf` ↦ `lstorePostLeaf`; `lregw_post_leaf` ↦ `lregwPostLeaf`;
`lctrl_post_leaf` ↦ `lctrlPostLeaf`; `linstr_post_leaf` ↦ `linstrPostLeaf`;
`lfence_post_leaf` ↦ `lfencePostLeaf`; `lload_fold_leaf` ↦ `lloadFoldLeaf`;
`lload_post_bytes_leaf` ↦ `lloadPostBytesLeaf`; `lload_post_bytes_d_leaf` ↦
`lloadPostBytesDLeaf`; `lstore_fold_leaf` ↦ `lstoreFoldLeaf`;
`lstore_fold_d_leaf` ↦ `lstoreFoldDLeaf`; `lstore_post_run_leaf` ↦
`lstorePostRunLeaf`; `lstore_post_run_d_leaf` ↦ `lstorePostRunDLeaf`;
`run_ats_ts` ↦ `runAtsTs`; `lload_post_run_leaf` ↦ `lloadPostRunLeaf`;
`lload_post_run_d_leaf` ↦ `lloadPostRunDLeaf`; `lexload_post_run_d_leaf` ↦
`lexloadPostRunDLeaf`; `tvs_fst_reads` ↦ `tvsFstReads`; `laev_post_leaf` ↦
`laevPostLeaf`; `laevs_post_leaf` ↦ `laevsPostLeaf`; `laevs_leaves_occur` ↦
`laevsLeavesOccur`; `lfloor`; `lrel_floor` ↦ `lrelFloor`; `lrel_floor_d` ↦
`lrelFloorD`.

**Not ported:** nothing (the Rocq `Add Printing Constructor lstate` and the
`Global Arguments` lines have no Lean counterpart).

**Statements checked** (diffed against Rocq by hand): all of them.
-/
import Weak.WeakMem
import Weak.WeakPromise
import Weak.WeakPromiseFact
import Weak.WeakRobustTrace
import Weak.WeakRobustGraph

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std

/-! ## A. The σ-transported event fold -/

/-- A label's read half with its timestamps transported. -/
def tlabelTs (σ : Nat → Nat) (tvs : List (Nat × BitVec 8)) : List (Nat × BitVec 8) :=
  tvs.map (fun tv => (σ tv.1, tv.2))

theorem tlabelTsFst (σ : Nat → Nat) (tvs : List (Nat × BitVec 8)) :
    (tlabelTs σ tvs).map Prod.fst = (tvs.map Prod.fst).map σ := by
  simp [tlabelTs]

/-- ONE event's `Wstate` update, with every leaf timestamp transported
through σ.  The `none` arms of a store/rmw are junk (a wf trace never takes
them: `astepOk` forces `aeTs` to be `some` there).  The dependency-only arms
read the operand views off the REPLAYED `w`, as `astepOk`'s `f` does.  The
exclusive read is `LLoad`'s arm plus the reservation; the conditional write
is `LStore`'s verbatim (S2).  `LIFetch` is the identity (deviation 3). -/
def aevPost {D : Type} (σ : Nat → Nat) (ev : Aev D) (w : Wstate) : Wstate :=
  match ev.aeLb with
  | .LSilent => w
  | .LLoad aq _ base tvs asrc =>
      loadPostRunD w aq (srcsView w asrc) base ((tvs.map Prod.fst).map σ)
  | .LStore rl base data asrc vsrc =>
      match ev.aeTs with
      | some ts => storePostRunD w rl (srcsView w asrc) (srcsView w vsrc) base data.length (σ ts)
      | none => w
  | .LRmw aq rl base tvs data asrc vsrc =>
      match ev.aeTs with
      | some ts =>
          storePostRunD (loadPostRunD w aq (srcsView w asrc) base ((tvs.map Prod.fst).map σ))
            rl (srcsView w asrc) (srcsView w vsrc) base data.length (σ ts)
      | none => w
  | .LFence pr pw sr sw => fencePost w pr pw sr sw
  | .LDev .. => w
  | .LRegW rd srcs => regwPost w rd (srcsView w srcs)
  | .LCtrl srcs => ctrlPost w (srcsView w srcs)
  | .LInstr => instrPost w
  | .LExLoad aq base tvs asrc =>
      exloadPostRunD w aq (srcsView w asrc) base ((tvs.map Prod.fst).map σ)
  | .LExStore rl base data asrc vsrc =>
      match ev.aeTs with
      | some ts => storePostRunD w rl (srcsView w asrc) (srcsView w vsrc) base data.length (σ ts)
      | none => w
  | .LIFetch _ _ => w

def aevsPost {D : Type} (σ : Nat → Nat) (evs : List (Aev D)) (w : Wstate) : Wstate :=
  evs.foldl (fun w ev => aevPost σ ev w) w

theorem aevsPostNil {D : Type} (σ : Nat → Nat) (w : Wstate) : aevsPost (D := D) σ [] w = w := rfl

theorem aevsPostApp {D : Type} (σ : Nat → Nat) (evs : List (Aev D)) (ev : Aev D) (w : Wstate) :
    aevsPost σ (evs ++ [ev]) w = aevPost σ ev (aevsPost σ evs w) := by
  simp only [aevsPost, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-! ## `wRelp` IS σ-INDEPENDENT

No `Wstate` rule computes the release-pending flag from a timestamp, so the
π-transported fold and the behavior's own `id`-fold agree on it (what makes
`pclsObl`'s "`clsf` may read `wRelp`" licence usable; moved here in Rocq from
`WeakRobustMain` with the G6a class pinning). -/

theorem wRelpFoldlLoad (aq : Bool) (v : Nat) (ats : List (Int × Nat)) :
    ∀ w, (ats.foldl (fun w at_ => loadPostAt w aq v at_.1 at_.2) w).wRelp = w.wRelp := by
  induction ats with
  | nil => intro w; rfl
  | cons p ats ih => intro w; exact ih _

theorem wRelpLoadPostBytes (ws : Wstate) (aq : Bool) (ats : List (Int × Nat)) :
    (loadPostBytes ws aq ats).wRelp = ws.wRelp := wRelpFoldlLoad aq _ ats ws

theorem wRelpLoadPostRun (ws : Wstate) (aq : Bool) (base : Int) (ts : List Nat) :
    (loadPostRun ws aq base ts).wRelp = ws.wRelp := wRelpLoadPostBytes ws aq _

theorem wRelpLoadPostRunD (ws : Wstate) (aq : Bool) (va : Nat) (base : Int) (ts : List Nat) :
    (loadPostRunD ws aq va base ts).wRelp = ws.wRelp := loadPostRunDRelp ws aq va base ts

/-- THE RMW SPLIT (S2): the exclusive read is the load plus a `wRes` write,
which `wRelp` does not see. -/
theorem wRelpExloadPostRunD (ws : Wstate) (aq : Bool) (va : Nat) (base : Int) (ts : List Nat) :
    (exloadPostRunD ws aq va base ts).wRelp = ws.wRelp := exloadPostRunDRelp ws aq va base ts

/-- `wRelp` after a store run depends on the PRE-state's `wRelp` and on the
byte list, never on the timestamp. -/
theorem wRelpFoldlStore (rl : Bool) (as_ : List Int) :
    ∀ (w w' : Wstate) (t t' : Nat), w.wRelp = w'.wRelp →
      (as_.foldl (fun w a => storePost w rl a t) w).wRelp
      = (as_.foldl (fun w a => storePost w rl a t') w').wRelp := by
  induction as_ with
  | nil => intro w w' t t' h; exact h
  | cons a as_ ih => intro w w' t t' _; exact ih _ _ t t' rfl

theorem wRelpStorePostBytesIndep (rl : Bool) (as_ : List Int) (w w' : Wstate) (t t' : Nat) :
    w.wRelp = w'.wRelp →
    (storePostBytes w rl as_ t).wRelp = (storePostBytes w' rl as_ t').wRelp :=
  wRelpFoldlStore rl as_ w w' t t'

theorem wRelpStorePostRunIndep (rl : Bool) (base : Int) (n : Nat) :
    ∀ (w w' : Wstate) (t t' : Nat), w.wRelp = w'.wRelp →
      (storePostRun w rl base n t).wRelp = (storePostRun w' rl base n t').wRelp :=
  fun w w' t t' h => wRelpStorePostBytesIndep rl _ w w' t t' h

/-- The dependency-carrying twin: `storePostD` clears `wRelp` exactly as
`storePost` does and the banked view never reaches it. -/
theorem wRelpFoldlStoreD (rl : Bool) (as_ : List Int) :
    ∀ (w w' : Wstate) (vf vf' t t' : Nat), w.wRelp = w'.wRelp →
      (as_.foldl (fun w a => storePostD w rl vf a t) w).wRelp
      = (as_.foldl (fun w a => storePostD w rl vf' a t') w').wRelp := by
  induction as_ with
  | nil => intro w w' vf vf' t t' h; exact h
  | cons a as_ ih => intro w w' vf vf' t t' _; exact ih _ _ vf vf' t t' rfl

theorem wRelpStorePostRunDIndep (rl : Bool) (base : Int) (n : Nat) :
    ∀ (w w' : Wstate) (va vd va' vd' t t' : Nat), w.wRelp = w'.wRelp →
      (storePostRunD w rl va vd base n t).wRelp
      = (storePostRunD w' rl va' vd' base n t').wRelp :=
  fun w w' _ _ _ _ t t' h => wRelpFoldlStoreD rl _ w w' _ _ t t' h

/-- σ-INDEPENDENCE of `wRelp`: no `Wstate` rule computes the release-pending
flag from a timestamp. -/
theorem wRelpAevPostIndep {D : Type} (σ σ' : Nat → Nat) (ev : Aev D) (w w' : Wstate) :
    w.wRelp = w'.wRelp → (aevPost σ ev w).wRelp = (aevPost σ' ev w').wRelp := by
  intro h
  obtain ⟨lb, ts, dd⟩ := ev
  cases lb with
  | LLoad => simp only [aevPost, wRelpLoadPostRunD, h]
  | LStore =>
    cases ts
    · exact h
    · exact wRelpStorePostRunDIndep _ _ _ _ _ _ _ _ _ _ _ h
  | LRmw =>
    cases ts
    · exact h
    · exact wRelpStorePostRunDIndep _ _ _ _ _ _ _ _ _ _ _
        (by simp only [wRelpLoadPostRunD, h])
  | LFence => simp only [aevPost, fencePost, h]
  | LExLoad => simp only [aevPost, wRelpExloadPostRunD, h]
  | LExStore =>
    cases ts
    · exact h
    · exact wRelpStorePostRunDIndep _ _ _ _ _ _ _ _ _ _ _ h
  | _ => exact h

theorem wRelpAevsPostIndep {D : Type} (σ σ' : Nat → Nat) (evs : List (Aev D)) :
    ∀ w w', w.wRelp = w'.wRelp → (aevsPost σ evs w).wRelp = (aevsPost σ' evs w').wRelp := by
  induction evs with
  | nil => intro w w' h; exact h
  | cons ev evs ih => intro w w' h; exact ih _ _ (wRelpAevPostIndep σ σ' ev w w' h)

/-! ## THE RESERVATION UNDER σ (T2-2a)

The conditional write's machine arm (`PFExStore`) reads the acting agent's
reservation, so the pf replay owes two facts about the π-transported fold.
(1) `aevsPostRes`: `rvBase` survives and `rvTs` is the σ-image of the
recorded column (`rvView` is a view, related in the `lrel` sense, and no
consumer reads it).  Every arm "clears", "keeps" or "sets from the label",
and the first two take the same branch on both sides because the folds
differ only in timestamps, never in a length.  (2) `aevsPostResSrc`: a
reservation in the RECORDED fold was set by an `LExLoad` event of the same
prefix whose read column IS `rvTs` (what lets `exclOkTsPf` find the window's
`gevReads` facts). -/

def resCols (σ : Nat → Nat) (r r' : Option Wresv) : Prop :=
  match r, r' with
  | none, none => True
  | some R, some R' => R.rvBase = R'.rvBase ∧ R.rvTs = R'.rvTs.map σ
  | _, _ => False

theorem resColsInv (σ : Nat → Nat) (r : Option Wresv) (R' : Wresv) :
    resCols σ r (some R') →
    ∃ R, r = some R ∧ R.rvBase = R'.rvBase ∧ R.rvTs = R'.rvTs.map σ := by
  intro h
  cases r with
  | none => exact h.elim
  | some R => exact ⟨R, rfl, h⟩

theorem aevPostRes {D : Type} (σ : Nat → Nat) (ev : Aev D) (w w' : Wstate) :
    resCols σ w.wRes w'.wRes → resCols σ (aevPost σ ev w).wRes (aevPost id ev w').wRes := by
  intro Heq
  obtain ⟨lb, ts, dd⟩ := ev
  cases lb with
  | LLoad aq lat base tvs asrc =>
    simp only [aevPost, loadPostRunDRes]
    cases tvs
    · exact Heq
    · trivial
  | LStore rl base data asrc vsrc =>
    cases ts
    · exact Heq
    · simp only [aevPost, storePostRunDRes]
      cases data
      · exact Heq
      · trivial
  | LRmw aq rl base tvs data asrc vsrc =>
    cases ts
    · exact Heq
    · simp only [aevPost, storePostRunDRes]
      cases data
      · simp only [loadPostRunDRes]
        cases tvs
        · exact Heq
        · trivial
      · trivial
  | LFence pr pw sr sw =>
    simp only [aevPost, fencePostRes]
    by_cases hc : (pr || pw || sr || sw) = true
    · rw [if_pos hc, if_pos hc]; trivial
    · rw [if_neg hc, if_neg hc]; exact Heq
  | LInstr => trivial
  | LExLoad aq base tvs asrc =>
    simp only [aevPost, exloadPostRunDRes]
    simp [resCols]
  | LExStore rl base data asrc vsrc =>
    cases ts
    · exact Heq
    · simp only [aevPost, storePostRunDRes]
      cases data
      · exact Heq
      · trivial
  | _ => exact Heq

theorem aevsPostRes {D : Type} (σ : Nat → Nat) (evs : List (Aev D)) :
    ∀ w w', resCols σ w.wRes w'.wRes →
      resCols σ (aevsPost σ evs w).wRes (aevsPost id evs w').wRes := by
  induction evs with
  | nil => intro w w' h; exact h
  | cons ev evs ih => intro w w' h; exact ih _ _ (aevPostRes σ ev w w' h)

theorem aevsPostResInit {D : Type} (σ : Nat → Nat) (evs : List (Aev D)) :
    resCols σ (aevsPost σ evs wsInit).wRes (aevsPost id evs wsInit).wRes :=
  aevsPostRes σ evs wsInit wsInit trivial

/-- (2) THE SOURCE OF A RECORDED RESERVATION. -/
theorem aevsPostResSrc {D : Type} (evs : List (Aev D)) (w : Wstate) (R : Wresv) :
    w.wRes = none → (aevsPost id evs w).wRes = some R →
    ∃ (m : Nat) (ev : Aev D) (aq : Bool) (tvs : List (Nat × BitVec 8)) (asrc : List Dsrc),
      evs[m]? = some ev ∧ ev.aeLb = .LExLoad aq R.rvBase tvs asrc ∧
      R.rvTs = tvs.map Prod.fst := by
  intro Hw
  induction evs using snocInd with
  | h0 => intro h; rw [aevsPostNil, Hw] at h; cases h
  | hs evs ev IH =>
    rw [aevsPostApp]
    have Hprev : (aevsPost id evs w).wRes = some R →
        ∃ (m : Nat) (ev' : Aev D) (aq : Bool) (tvs : List (Nat × BitVec 8)) (asrc : List Dsrc),
          (evs ++ [ev])[m]? = some ev' ∧ ev'.aeLb = .LExLoad aq R.rvBase tvs asrc ∧
          R.rvTs = tvs.map Prod.fst := by
      intro HW
      obtain ⟨m, ev', aq, tvs, asrc, Hm, Hl, Hts⟩ := IH HW
      exact ⟨m, ev', aq, tvs, asrc, lookup_app_l_Some Hm, Hl, Hts⟩
    obtain ⟨lb, ts, dd⟩ := ev
    cases lb with
    | LLoad aq lat base tvs asrc =>
      simp only [aevPost, loadPostRunDRes]
      cases tvs
      · exact Hprev
      · intro h; cases h
    | LStore rl base data asrc vsrc =>
      cases ts
      · exact Hprev
      · simp only [aevPost, storePostRunDRes]
        cases data
        · exact Hprev
        · intro h; cases h
    | LRmw aq rl base tvs data asrc vsrc =>
      cases ts
      · exact Hprev
      · simp only [aevPost, storePostRunDRes]
        cases data
        · simp only [loadPostRunDRes]
          cases tvs
          · exact Hprev
          · intro h; cases h
        · intro h; cases h
    | LFence pr pw sr sw =>
      simp only [aevPost, fencePostRes]
      by_cases hc : (pr || pw || sr || sw) = true
      · rw [if_pos hc]; intro h; cases h
      · rw [if_neg hc]; exact Hprev
    | LInstr => intro h; cases h
    | LExLoad xaq xbase xtvs xasrc =>
      simp only [aevPost, exloadPostRunDRes]
      intro h
      obtain rfl := Option.some.inj h
      exact ⟨evs.length, _, xaq, xtvs, xasrc, list_lookup_middle rfl, rfl, by simp⟩
    | LExStore rl base data asrc vsrc =>
      cases ts
      · exact Hprev
      · simp only [aevPost, storePostRunDRes]
        cases data
        · exact Hprev
        · intro h; cases h
    | _ => exact Hprev

/-! ## B. Behavior correspondence: the behavior's own `Wstate` IS the
`id`-fold of its trace prefix -/

/-- `astepOk` pins the step's `Wstate` update to exactly `aevPost id` of the
event. -/
theorem astepOkAevPost {P D : Type} (img : Image) (log : List Wmsg) (i : Nat) (ag : Wpagent P)
    (ev : Aev D) (f : Wstate → Wstate) :
    astepOk img log i ag ev.aeLb f ev.aeTs → ∀ w, f w = aevPost id ev w := by
  obtain ⟨lb, ts, dd⟩ := ev
  intro h w
  cases lb with
  | LLoad =>
    obtain ⟨-, rfl, -⟩ := h
    simp only [aevPost, List.map_id]
  | LStore =>
    obtain ⟨ts', k, -, -, -, rfl, rfl⟩ := h
    rfl
  | LRmw =>
    obtain ⟨ts', k, -, -, -, -, -, -, rfl, rfl⟩ := h
    simp only [aevPost, List.map_id, id]
  | LExLoad =>
    obtain ⟨-, rfl, -⟩ := h
    simp only [aevPost, List.map_id]
  | LExStore =>
    obtain ⟨ts', k, R, -, -, -, -, -, -, -, rfl, rfl⟩ := h
    rfl
  | LIFetch => obtain ⟨-, rfl, -⟩ := h; rfl
  | _ => obtain ⟨rfl, -⟩ := h; rfl

/-- THE CORRESPONDENCE.  Every prefix of a wf trace folds the agent's
`Wstate` forward by `aevPost id`. -/
theorem astepsWsFold {P D : Type} (pstep : P → D → Wlabel → P → D → Prop) (img : Image)
    (log : List Wmsg) (i : Nat) (ags : List (Wpagent P)) (evs : List (Aev D)) (k : Nat)
    (ag0 agk : Wpagent P) :
    astepsWf pstep img log i ags evs → ags[0]? = some ag0 → ags[k]? = some agk →
    agk.paWs = aevsPost id (evs.take k) ag0.paWs := by
  intro Hwf H0
  induction k generalizing agk with
  | zero => intro Hk; rw [H0] at Hk; cases Hk; rfl
  | succ k IH =>
    intro Hk
    have Hlen := Hwf.1
    have Hkl := lookup_lt_Some Hk
    obtain ⟨ag, Hag⟩ :=
      Option.isSome_iff_exists.1 (lookup_lt_is_Some_2 (l := ags) (i := k) (by omega))
    obtain ⟨ev, Hev⟩ :=
      Option.isSome_iff_exists.1 (lookup_lt_is_Some_2 (l := evs) (i := k) (by omega))
    obtain ⟨agA, agB, st', f, HagA, HagB, -, Hok, Heq⟩ :=
      astepsWfStep pstep img log i ags evs k ev Hwf Hev
    rw [Hag] at HagA; cases HagA
    rw [Hk] at HagB; cases HagB
    have Htake : evs.take (k + 1) = evs.take k ++ [ev] := by
      rw [List.take_add_one, Hev]; rfl
    rw [Heq, Htake, aevsPostApp, ← IH ag Hag]
    exact astepOkAevPost img log i ag ev f Hok ag.paWs

/-! ## C. The leaf-state mirror

Leaves are `List Nat`; duplicates are harmless because every component is
read off with a `max`. -/

/-- The leaf state.  `lFwd` holds the RAW store timestamp plus the view
leaves.  The three D2 components are views (joins of timestamps), so all
three get leaf lists, unlike `wRelp` (σ-independent, above); `regwPost`'s
overwrite and `instrPost`'s reset are mirrored by an insert and by `[]`.
`lTbank` mirrors W-TV's translation bank: produced per read byte by
`lloadPostAt` (appending the mirrored `lfwdView`), reset by `linstrPost`,
consumed by the run-level wrappers, which push it into `lVcap` alongside the
address leaves (`WeakMem`'s `max vaddr ws.wTbank` with `max` ↦ `++`). -/
structure Lstate where
  lCoh : GMapF Int (List Nat)
  lVrOld : List Nat
  lVwOld : List Nat
  lVrNew : List Nat
  lVwNew : List Nat
  lVRel : List Nat
  lFwd : GMapF Int (Nat × List Nat)
  lRegv : GMapF Nat (List Nat)
  lVcap : List Nat
  lLdv : List Nat
  lTbank : List Nat

/-- The valuation of a leaf set under a transport σ. -/
def lval (σ : Nat → Nat) (L : List Nat) : Nat :=
  L.foldr (fun t n => max (σ t) n) 0

def lcoh (S : Lstate) (a : Int) : List Nat := (get? S.lCoh a).getD []

def lregv (S : Lstate) (r : Nat) : List Nat := (get? S.lRegv r).getD []

def linit : Lstate :=
  { lCoh := ∅, lVrOld := [], lVwOld := [], lVrNew := [], lVwNew := [], lVRel := [],
    lFwd := ∅, lRegv := ∅, lVcap := [], lLdv := [], lTbank := [] }

/-! ### Basic laws of `lval` -/

theorem lvalNil (σ : Nat → Nat) : lval σ [] = 0 := rfl

theorem lvalCons (σ : Nat → Nat) (t : Nat) (L : List Nat) :
    lval σ (t :: L) = max (σ t) (lval σ L) := rfl

theorem lvalSingleton (σ : Nat → Nat) (t : Nat) : lval σ [t] = σ t := Nat.max_zero _

theorem lvalApp (σ : Nat → Nat) (L1 L2 : List Nat) :
    lval σ (L1 ++ L2) = max (lval σ L1) (lval σ L2) := by
  induction L1 with
  | nil => exact (Nat.zero_max _).symm
  | cons t L1 ih => rw [List.cons_append, lvalCons, lvalCons, ih]; omega

theorem lvalGe (σ : Nat → Nat) (L : List Nat) (t : Nat) : t ∈ L → σ t ≤ lval σ L := by
  induction L with
  | nil => intro h; cases h
  | cons u L ih =>
    intro h
    rw [lvalCons]
    rcases List.mem_cons.1 h with rfl | h
    · omega
    · have := ih h; omega

theorem lvalLeIff (σ : Nat → Nat) (L : List Nat) (n : Nat) :
    lval σ L ≤ n ↔ ∀ t, t ∈ L → σ t ≤ n := by
  induction L with
  | nil => simp [lvalNil]
  | cons u L ih => rw [lvalCons, Nat.max_le, ih, List.forall_mem_cons]

theorem lvalLt (σ : Nat → Nat) (L : List Nat) (n : Nat) :
    (∀ t, t ∈ L → σ t < n) → 0 < n → lval σ L < n := by
  intro Hall Hn
  have Hle : lval σ L ≤ n - 1 :=
    (lvalLeIff σ L (n - 1)).2 (fun t Ht => by have := Hall t Ht; omega)
  omega

/-! ### `lcoh` under an insert (mirrors `cohUpdEq` / `cohUpdNe`) -/

theorem lcohInsEq (m : GMapF Int (List Nat)) (rO wO rN wN R : List Nat)
    (fwd : GMapF Int (Nat × List Nat)) (rg : GMapF Nat (List Nat)) (vc ld tb : List Nat)
    (a : Int) (L : List Nat) :
    lcoh { lCoh := insert m a L, lVrOld := rO, lVwOld := wO, lVrNew := rN, lVwNew := wN,
           lVRel := R, lFwd := fwd, lRegv := rg, lVcap := vc, lLdv := ld, lTbank := tb } a
    = L := by
  simp only [lcoh, lookupInsert, Option.getD_some]

theorem lcohInsNe (m : GMapF Int (List Nat)) (rO wO rN wN R : List Nat)
    (fwd : GMapF Int (Nat × List Nat)) (rg : GMapF Nat (List Nat)) (vc ld tb : List Nat)
    (a a' : Int) (L : List Nat) :
    a' ≠ a →
    lcoh { lCoh := insert m a L, lVrOld := rO, lVwOld := wO, lVrNew := rN, lVwNew := wN,
           lVRel := R, lFwd := fwd, lRegv := rg, lVcap := vc, lLdv := ld, lTbank := tb } a'
    = (get? m a').getD [] := by
  intro h
  simp only [lcoh, lookupInsertNe (Ne.symm h)]

/-! ### The mirrored step functions

Structurally identical to `WeakMem`'s, with `max` ↦ `++` and each timestamp
↦ the singleton leaf list `[t]`, RAW, untransported. -/

def lloadVpre (S : Lstate) (aq : Bool) : List Nat :=
  S.lVrNew ++ (if aq then S.lVRel else [])

/-- The mirrored operand views: `srcsView` with `max` ↦ `++`. -/
def ldsrcView (S : Lstate) (x : Dsrc) : List Nat :=
  match x with
  | .DReg r => lregv S r
  | .DLdRes => S.lLdv

def lsrcsView (S : Lstate) (srcs : List Dsrc) : List Nat :=
  srcs.foldr (fun x L => ldsrcView S x ++ L) []

def lloadVpreD (S : Lstate) (aq : Bool) (vaddrL : List Nat) : List Nat :=
  vaddrL ++ lloadVpre S aq

/-- THE FORWARD BANK, mirrored.  The hit/miss decision is taken on the RAW
timestamps; `lrelFwdView` is where injectivity of σ makes that agree with the
`Wstate` side's decision on the transported ones. -/
def lfwdView (S : Lstate) (aq : Bool) (a : Int) (t : Nat) : List Nat :=
  if aq then [t]
  else match get? S.lFwd a with
    | some (tf, V) => if t = tf then V else [t]
    | none => [t]

/-- W-TV production: the bank takes the FORWARDED view, not `vpostL`. -/
def lloadPostAt (S : Lstate) (aq : Bool) (vpreL : List Nat) (a : Int) (t : Nat) : Lstate :=
  let vpostL := vpreL ++ lfwdView S aq a t
  { lCoh := insert S.lCoh a (lcoh S a ++ (vpostL ++ [t]))
    lVrOld := S.lVrOld ++ vpostL
    lVwOld := S.lVwOld
    lVrNew := if aq then S.lVrNew ++ vpostL else S.lVrNew
    lVwNew := if aq then S.lVwNew ++ vpostL else S.lVwNew
    lVRel := S.lVRel
    lFwd := S.lFwd
    lRegv := S.lRegv
    lVcap := S.lVcap
    lLdv := S.lLdv ++ vpostL
    lTbank := S.lTbank ++ lfwdView S aq a t }

/-- `vfL` mirrors `storePostD`'s dead `vf` parameter: since D-7r the machine
banks the view column `0`, so the mirror banks the EMPTY leaf list. -/
def lstorePostD (S : Lstate) (rl : Bool) (vfL : List Nat) (a : Int) (t : Nat) : Lstate :=
  { lCoh := insert S.lCoh a (lcoh S a ++ [t])
    lVrOld := S.lVrOld
    lVwOld := S.lVwOld ++ [t]
    lVrNew := S.lVrNew
    lVwNew := S.lVwNew
    lVRel := if rl then S.lVRel ++ [t] else S.lVRel
    lFwd := insert S.lFwd a (t, [])
    lRegv := S.lRegv
    lVcap := S.lVcap
    lLdv := S.lLdv
    lTbank := S.lTbank }

def lstorePost (S : Lstate) (rl : Bool) (a : Int) (t : Nat) : Lstate :=
  lstorePostD S rl [] a t

/-- The D-7r collapse, mirrored (`storePostDVf`'s twin). -/
theorem lstorePostDVfL (S : Lstate) (rl : Bool) (vfL : List Nat) (a : Int) (t : Nat) :
    lstorePostD S rl vfL a t = lstorePost S rl a t := rfl

def lfencePost (S : Lstate) (pr pw sr sw : Bool) : Lstate :=
  let v1L := (if pr then S.lVrOld else []) ++ (if pw then S.lVwOld else [])
  { lCoh := S.lCoh
    lVrOld := S.lVrOld
    lVwOld := S.lVwOld
    lVrNew := if sr then S.lVrNew ++ v1L else S.lVrNew
    lVwNew := if sw then S.lVwNew ++ v1L else S.lVwNew
    lVRel := S.lVRel
    lFwd := S.lFwd
    lRegv := S.lRegv
    lVcap := S.lVcap
    lLdv := S.lLdv
    lTbank := S.lTbank }

/-- The three dependency-only effects, mirrored. -/
def lregwPost (S : Lstate) (rd : Nat) (vL : List Nat) : Lstate :=
  { S with lRegv := insert S.lRegv rd vL }

def lctrlPost (S : Lstate) (vL : List Nat) : Lstate :=
  { S with lVcap := vL ++ S.lVcap }

def linstrPost (S : Lstate) : Lstate :=
  { S with lLdv := [], lTbank := [] }

/-- The multi-byte folds, mirroring `loadPostBytes` / `storePostBytes`
EXACTLY, including the compute-`vpre`-ONCE-from-the-PRE-state structure. -/
def lloadPostBytesD (S : Lstate) (aq : Bool) (vaddrL : List Nat) (ats : List (Int × Nat)) :
    Lstate :=
  ats.foldl (fun S' at_ => lloadPostAt S' aq (lloadVpreD S aq vaddrL) at_.1 at_.2) S

def lloadPostBytes (S : Lstate) (aq : Bool) (ats : List (Int × Nat)) : Lstate :=
  ats.foldl (fun S' at_ => lloadPostAt S' aq (lloadVpre S aq) at_.1 at_.2) S

def lstorePostBytesD (S : Lstate) (rl : Bool) (vfL : List Nat) (as_ : List Int) (t : Nat) :
    Lstate :=
  as_.foldl (fun S' a => lstorePostD S' rl vfL a t) S

def lstorePostBytes (S : Lstate) (rl : Bool) (as_ : List Int) (t : Nat) : Lstate :=
  as_.foldl (fun S' a => lstorePost S' rl a t) S

/-- W-TV's CONSUMPTION, mirrored: the run-level wrapper pushes the ENTRY
state's bank into `lVcap` next to the address leaves. -/
def lloadPostRunD (S : Lstate) (aq : Bool) (vaddrL : List Nat) (base : Int) (ts : List Nat) :
    Lstate :=
  lctrlPost
    (lloadPostBytesD S aq vaddrL
      (List.zipWith (fun (j : Nat) t => (base + (j : Int), t)) (List.range' 0 ts.length) ts))
    (vaddrL ++ S.lTbank)

def lloadPostRun (S : Lstate) (aq : Bool) (base : Int) (ts : List Nat) : Lstate :=
  lctrlPost
    (lloadPostBytes S aq
      (List.zipWith (fun (j : Nat) t => (base + (j : Int), t)) (List.range' 0 ts.length) ts))
    S.lTbank

/-- D-2r, MIRRORED (`exloadPostRunD`): the EXCLUSIVE read's address leaves
reach the CONTROL view only; its byte fold is the PLAIN one. -/
def lexloadPostRunD (S : Lstate) (aq : Bool) (vaddrL : List Nat) (base : Int)
    (ts : List Nat) : Lstate :=
  lctrlPost
    (lloadPostBytes S aq
      (List.zipWith (fun (j : Nat) t => (base + (j : Int), t)) (List.range' 0 ts.length) ts))
    (vaddrL ++ S.lTbank)

def lstorePostRunD (S : Lstate) (rl : Bool) (vaddrL vdataL : List Nat) (base : Int)
    (n t : Nat) : Lstate :=
  lctrlPost
    (lstorePostBytesD S rl (vaddrL ++ vdataL) ((List.range' 0 n).map (fun j : Nat => base + (j : Int))) t)
    (vaddrL ++ S.lTbank)

def lstorePostRun (S : Lstate) (rl : Bool) (base : Int) (n t : Nat) : Lstate :=
  lctrlPost
    (lstorePostBytes S rl ((List.range' 0 n).map (fun j : Nat => base + (j : Int))) t)
    S.lTbank

/-- The event fold, mirrored.  No σ: leaves are raw.  The mirror has no
reservation component: `lrel` does not constrain `wRes` (S4 relates the
reservation COLUMNS through `resCols` instead); `lTbank` IS mirrored. -/
def laevPost {D : Type} (ev : Aev D) (S : Lstate) : Lstate :=
  match ev.aeLb with
  | .LSilent => S
  | .LLoad aq _ base tvs asrc =>
      lloadPostRunD S aq (lsrcsView S asrc) base (tvs.map Prod.fst)
  | .LStore rl base data asrc vsrc =>
      match ev.aeTs with
      | some ts => lstorePostRunD S rl (lsrcsView S asrc) (lsrcsView S vsrc) base data.length ts
      | none => S
  | .LRmw aq rl base tvs data asrc vsrc =>
      match ev.aeTs with
      | some ts =>
          lstorePostRunD (lloadPostRunD S aq (lsrcsView S asrc) base (tvs.map Prod.fst))
            rl (lsrcsView S asrc) (lsrcsView S vsrc) base data.length ts
      | none => S
  | .LFence pr pw sr sw => lfencePost S pr pw sr sw
  | .LDev .. => S
  | .LRegW rd srcs => lregwPost S rd (lsrcsView S srcs)
  | .LCtrl srcs => lctrlPost S (lsrcsView S srcs)
  | .LInstr => linstrPost S
  | .LExLoad aq base tvs asrc =>
      lexloadPostRunD S aq (lsrcsView S asrc) base (tvs.map Prod.fst)
  | .LExStore rl base data asrc vsrc =>
      match ev.aeTs with
      | some ts => lstorePostRunD S rl (lsrcsView S asrc) (lsrcsView S vsrc) base data.length ts
      | none => S
  | .LIFetch _ _ => S

def laevsPost {D : Type} (evs : List (Aev D)) (S : Lstate) : Lstate :=
  evs.foldl (fun S ev => laevPost ev S) S

theorem laevsPostNil {D : Type} (S : Lstate) : laevsPost (D := D) [] S = S := rfl

theorem laevsPostApp {D : Type} (evs : List (Aev D)) (ev : Aev D) (S : Lstate) :
    laevsPost (evs ++ [ev]) S = laevPost ev (laevsPost evs S) := by
  simp only [laevsPost, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-! ## D. The relation and the transport theorem -/

def sigmaOk (σ : Nat → Nat) : Prop := σ 0 = 0 ∧ Function.Injective σ

theorem sigmaOkId : sigmaOk id := ⟨rfl, fun _ _ h => h⟩

/-- The D2 conjuncts and W-TV's bank are appended LAST, so positional
destructuring patterns keep their meaning. -/
def lrel (σ : Nat → Nat) (S : Lstate) (w : Wstate) : Prop :=
  (∀ a, coh w a = lval σ (lcoh S a)) ∧
  w.wVrOld = lval σ S.lVrOld ∧
  w.wVwOld = lval σ S.lVwOld ∧
  w.wVrNew = lval σ S.lVrNew ∧
  w.wVwNew = lval σ S.lVwNew ∧
  w.wVRel = lval σ S.lVRel ∧
  (∀ a, match get? S.lFwd a, get? w.wFwd a with
        | some (tf, V), some (tf', vf) => tf' = σ tf ∧ vf = lval σ V
        | none, none => True
        | _, _ => False) ∧
  (∀ r, regv w r = lval σ (lregv S r)) ∧
  w.wVcap = lval σ S.lVcap ∧
  w.wLdv = lval σ S.lLdv ∧
  w.wTbank = lval σ S.lTbank

theorem lrelInit (σ : Nat → Nat) : lrel σ linit wsInit :=
  ⟨fun _ => rfl, rfl, rfl, rfl, rfl, rfl, fun _ => trivial, fun _ => rfl, rfl, rfl, rfl⟩

/-- The W-TV bank's conjunct, projected: the run-level wrappers consume the
ENTRY state's bank, so every one of them needs it. -/
theorem lrelTbank (σ : Nat → Nat) (S : Lstate) (w : Wstate) :
    lrel σ S w → w.wTbank = lval σ S.lTbank :=
  fun ⟨_, _, _, _, _, _, _, _, _, _, h⟩ => h

/-- THE OPERAND VIEW TRANSPORTS: a label's operand list is a list of NAMES,
whose view is a join of register views on the `Wstate` side and their
concatenation on the mirror side; `lrel`'s pointwise conjuncts identify the
two, one register at a time. -/
theorem lrelSrcsView (σ : Nat → Nat) (S : Lstate) (w : Wstate) (srcs : List Dsrc) :
    lrel σ S w → srcsView w srcs = lval σ (lsrcsView S srcs) := by
  rintro ⟨-, -, -, -, -, -, -, Hrg, -, Hld, -⟩
  induction srcs with
  | nil => rfl
  | cons x srcs IH =>
    show max (dsrcView w x) (srcsView w srcs) = lval σ (ldsrcView S x ++ lsrcsView S srcs)
    rw [lvalApp, IH]
    congr 1
    cases x with
    | DReg r => exact Hrg r
    | DLdRes => exact Hld

/-- THE ONE PLACE INJECTIVITY IS SPENT. -/
theorem lrelFwdView (σ : Nat → Nat) (S : Lstate) (w : Wstate) (aq : Bool) (a : Int) (t : Nat) :
    Function.Injective σ → lrel σ S w →
    fwdView w aq a (σ t) = lval σ (lfwdView S aq a t) := by
  rintro Hinj ⟨-, -, -, -, -, -, Hfwd, -⟩
  cases aq
  · simp only [fwdView, lfwdView, Bool.false_eq_true, ↓reduceIte]
    have H := Hfwd a
    revert H
    cases get? S.lFwd a with
    | none =>
      cases get? w.wFwd a with
      | none => intro _; exact (lvalSingleton σ t).symm
      | some p => intro h; cases h
    | some q =>
      obtain ⟨tf, V⟩ := q
      cases get? w.wFwd a with
      | none => intro h; cases h
      | some p =>
        obtain ⟨tf', vf⟩ := p
        rintro ⟨rfl, rfl⟩
        dsimp only
        by_cases Ht : t = tf
        · rw [if_pos (congrArg σ Ht), if_pos Ht]
        · rw [if_neg (fun h => Ht (Hinj h)), if_neg Ht, lvalSingleton]
  · exact (lvalSingleton σ t).symm

theorem lrelLoadVpre (σ : Nat → Nat) (S : Lstate) (w : Wstate) (aq : Bool) :
    lrel σ S w → loadVpre w aq = lval σ (lloadVpre S aq) := by
  rintro ⟨-, -, -, HrN, -, HR, -⟩
  cases aq <;> simp only [loadVpre, lloadVpre, lvalApp, HrN, HR, Bool.false_eq_true,
    ↓reduceIte, lvalNil]

theorem lrelLoadVpreD (σ : Nat → Nat) (S : Lstate) (w : Wstate) (aq : Bool) (vaddr : Nat)
    (vaddrL : List Nat) :
    lrel σ S w → vaddr = lval σ vaddrL →
    loadVpreD w aq vaddr = lval σ (lloadVpreD S aq vaddrL) := by
  rintro Hrel rfl
  simp only [loadVpreD, lloadVpreD, lvalApp, lrelLoadVpre σ S w aq Hrel]

/-! ### Preservation, step by step -/

theorem lrelLoadPostAt (σ : Nat → Nat) (S : Lstate) (w : Wstate) (aq : Bool) (vpreL : List Nat)
    (vpre : Nat) (a : Int) (t : Nat) :
    Function.Injective σ → lrel σ S w → vpre = lval σ vpreL →
    lrel σ (lloadPostAt S aq vpreL a t) (loadPostAt w aq vpre a (σ t)) := by
  intro Hinj Hrel Hvp
  have Hfv := lrelFwdView σ S w aq a t Hinj Hrel
  obtain ⟨Hcoh, HrO, HwO, HrN, HwN, HR, Hfwd, Hrg, Hvc, Hld, Htb⟩ := Hrel
  subst Hvp
  refine ⟨fun a' => ?_, ?_, HwO, ?_, ?_, HR, Hfwd, Hrg, Hvc, ?_, ?_⟩
  · by_cases Ha : a' = a
    · subst Ha
      rw [cohLoadPostAtEq]
      simp only [lloadPostAt]
      rw [lcohInsEq]
      simp only [lvalApp, lvalSingleton]
      rw [← Hcoh a', ← Hfv]
    · rw [cohLoadPostAtNe _ _ _ _ _ _ Ha]
      simp only [lloadPostAt]
      rw [lcohInsNe _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ha]
      exact Hcoh a'
  all_goals cases aq <;> simp only [loadPostAt, lloadPostAt, lvalApp, HrO, HrN, HwN, Hld, Htb,
    Hfv, Bool.false_eq_true, ↓reduceIte]

/-- D-7r: the two banked view columns are `0` and `[]`; the premise
`vf = lval σ vfL` the dependency-carrying bank needed is GONE. -/
theorem lrelStorePostD (σ : Nat → Nat) (S : Lstate) (w : Wstate) (rl : Bool) (vf : Nat)
    (vfL : List Nat) (a : Int) (t : Nat) :
    lrel σ S w → lrel σ (lstorePostD S rl vfL a t) (storePostD w rl vf a (σ t)) := by
  rintro ⟨Hcoh, HrO, HwO, HrN, HwN, HR, Hfwd, Hrg, Hvc, Hld, Htb⟩
  rw [storePostDVf]
  refine ⟨fun a' => ?_, HrO, ?_, HrN, HwN, ?_, fun a' => ?_, Hrg, Hvc, Hld, Htb⟩
  · by_cases Ha : a' = a
    · subst Ha
      rw [cohStorePostEq]
      simp only [lstorePostD]
      rw [lcohInsEq, lvalApp, lvalSingleton, Hcoh a']
    · rw [cohStorePostNe _ _ _ _ _ Ha]
      simp only [lstorePostD]
      rw [lcohInsNe _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ha]
      exact Hcoh a'
  · simp only [storePost, lstorePostD, lvalApp, lvalSingleton, HwO]
  · cases rl <;> simp only [storePost, lstorePostD, lvalApp, lvalSingleton, HR,
      Bool.false_eq_true, ↓reduceIte]
  · by_cases Ha : a' = a
    · subst Ha
      simp [storePost, lstorePostD, lookupInsert, lvalNil]
    · simp only [storePost, lstorePostD, lookupInsertNe (Ne.symm Ha)]
      exact Hfwd a'

theorem lrelStorePost (σ : Nat → Nat) (S : Lstate) (w : Wstate) (rl : Bool) (a : Int) (t : Nat) :
    lrel σ S w → lrel σ (lstorePost S rl a t) (storePost w rl a (σ t)) :=
  fun Hrel => lrelStorePostD σ S w rl 0 [] a t Hrel

/-- The three dependency-only effects. -/
theorem lrelRegwPost (σ : Nat → Nat) (S : Lstate) (w : Wstate) (rd v : Nat) (vL : List Nat) :
    lrel σ S w → v = lval σ vL → lrel σ (lregwPost S rd vL) (regwPost w rd v) := by
  rintro ⟨Hcoh, HrO, HwO, HrN, HwN, HR, Hfwd, Hrg, Hvc, Hld, Htb⟩ rfl
  refine ⟨Hcoh, HrO, HwO, HrN, HwN, HR, Hfwd, fun r => ?_, Hvc, Hld, Htb⟩
  by_cases Hr : r = rd
  · subst Hr
    simp only [regv, lregv, regwPost, lregwPost, lookupInsert, Option.getD_some]
  · simp only [regv, lregv, regwPost, lregwPost, lookupInsertNe (Ne.symm Hr)]
    exact Hrg r

theorem lrelCtrlPost (σ : Nat → Nat) (S : Lstate) (w : Wstate) (v : Nat) (vL : List Nat) :
    lrel σ S w → v = lval σ vL → lrel σ (lctrlPost S vL) (ctrlPost w v) := by
  rintro ⟨Hcoh, HrO, HwO, HrN, HwN, HR, Hfwd, Hrg, Hvc, Hld, Htb⟩ rfl
  refine ⟨Hcoh, HrO, HwO, HrN, HwN, HR, Hfwd, Hrg, ?_, Hld, Htb⟩
  show max (lval σ vL) w.wVcap = lval σ (vL ++ S.lVcap)
  rw [lvalApp, Hvc]

theorem lrelInstrPost (σ : Nat → Nat) (S : Lstate) (w : Wstate) :
    lrel σ S w → lrel σ (linstrPost S) (instrPost w) :=
  fun ⟨Hcoh, HrO, HwO, HrN, HwN, HR, Hfwd, Hrg, Hvc, _, _⟩ =>
    ⟨Hcoh, HrO, HwO, HrN, HwN, HR, Hfwd, Hrg, Hvc, rfl, rfl⟩

theorem lrelFencePost (σ : Nat → Nat) (S : Lstate) (w : Wstate) (pr pw sr sw : Bool) :
    lrel σ S w → lrel σ (lfencePost S pr pw sr sw) (fencePost w pr pw sr sw) := by
  rintro ⟨Hcoh, HrO, HwO, HrN, HwN, HR, Hfwd, Hrg, Hvc, Hld, Htb⟩
  have Hv1 : max (if pr then w.wVrOld else 0) (if pw then w.wVwOld else 0)
      = lval σ ((if pr then S.lVrOld else []) ++ (if pw then S.lVwOld else [])) := by
    rw [lvalApp]
    cases pr <;> cases pw <;> simp only [HrO, HwO, Bool.false_eq_true, ↓reduceIte, lvalNil]
  refine ⟨Hcoh, HrO, HwO, ?_, ?_, HR, Hfwd, Hrg, Hvc, Hld, Htb⟩
  · cases sr <;> simp only [fencePost, lfencePost, lvalApp, HrN, Hv1, Bool.false_eq_true,
      ↓reduceIte]
  · cases sw <;> simp only [fencePost, lfencePost, lvalApp, HwN, Hv1, Bool.false_eq_true,
      ↓reduceIte]

/-! ### Preservation through the byte folds

The `Wstate` fold runs over the SAME address list with TRANSPORTED
timestamps; `tats` is that map, and `tatsRun` aligns the two contiguous-run
`zipWith`s (where `List.length_map` is spent). -/

def tats (σ : Nat → Nat) (ats : List (Int × Nat)) : List (Int × Nat) :=
  ats.map (fun p => (p.1, σ p.2))

theorem fmapZipWithGen {A B C D : Type} (f : A → B → C) (g : C → D) (l : List A) (k : List B) :
    (List.zipWith f l k).map g = List.zipWith (fun x y => g (f x y)) l k := by
  induction l generalizing k with
  | nil => rfl
  | cons x l ih =>
    cases k with
    | nil => rfl
    | cons y k => simp only [List.zipWith_cons_cons, List.map_cons, ih]

theorem tatsRun (σ : Nat → Nat) (base : Int) (ts : List Nat) :
    tats σ (List.zipWith (fun (j : Nat) (t : Nat) => (base + (j : Int), t))
      (List.range' 0 ts.length) ts)
    = List.zipWith (fun (j : Nat) (t : Nat) => (base + (j : Int), t))
        (List.range' 0 (ts.map σ).length) (ts.map σ) := by
  simp only [tats, List.length_map, fmapZipWithGen]
  generalize List.range' 0 ts.length = l
  induction l generalizing ts with
  | nil => rfl
  | cons j l ih =>
    cases ts with
    | nil => rfl
    | cons t ts => simp only [List.zipWith_cons_cons, List.map_cons, ih]

/-- The pre-view is computed ONCE from the pre-state, so the inner induction
carries "`vpre = lval σ vpreL`" as its own premise. -/
theorem lrelLoadFold (σ : Nat → Nat) (aq : Bool) (vpre : Nat) (vpreL : List Nat)
    (ats : List (Int × Nat)) :
    Function.Injective σ →
    ∀ S w, lrel σ S w → vpre = lval σ vpreL →
      lrel σ (ats.foldl (fun S' at_ => lloadPostAt S' aq vpreL at_.1 at_.2) S)
             ((tats σ ats).foldl (fun w' at_ => loadPostAt w' aq vpre at_.1 at_.2) w) := by
  intro Hinj
  induction ats with
  | nil => intro S w Hrel _; exact Hrel
  | cons p ats IH =>
    intro S w Hrel Hvp
    exact IH _ _ (lrelLoadPostAt σ S w aq vpreL vpre p.1 p.2 Hinj Hrel Hvp) Hvp

theorem lrelLoadPostRun (σ : Nat → Nat) (S : Lstate) (w : Wstate) (aq : Bool) (base : Int)
    (ts : List Nat) :
    Function.Injective σ → lrel σ S w →
    lrel σ (lloadPostRun S aq base ts) (loadPostRun w aq base (ts.map σ)) := by
  intro Hinj Hrel
  unfold lloadPostRun loadPostRun lloadPostBytes loadPostBytes
  rw [← tatsRun]
  exact lrelCtrlPost σ _ _ _ _
    (lrelLoadFold σ aq _ _ _ Hinj S w Hrel (lrelLoadVpre σ S w aq Hrel)) (lrelTbank σ S w Hrel)

theorem lrelLoadPostRunD (σ : Nat → Nat) (S : Lstate) (w : Wstate) (aq : Bool) (vaddr : Nat)
    (vaddrL : List Nat) (base : Int) (ts : List Nat) :
    Function.Injective σ → lrel σ S w → vaddr = lval σ vaddrL →
    lrel σ (lloadPostRunD S aq vaddrL base ts) (loadPostRunD w aq vaddr base (ts.map σ)) := by
  intro Hinj Hrel Hva
  unfold lloadPostRunD loadPostRunD lloadPostBytesD loadPostBytesD loadRunAts
  rw [← tatsRun]
  exact lrelCtrlPost σ _ _ _ _
    (lrelLoadFold σ aq _ _ _ Hinj S w Hrel (lrelLoadVpreD σ S w aq vaddr vaddrL Hrel Hva))
    (by rw [lvalApp, ← Hva, ← lrelTbank σ S w Hrel])

theorem lrelStoreFold (σ : Nat → Nat) (rl : Bool) (t : Nat) (as_ : List Int) :
    ∀ S w, lrel σ S w →
      lrel σ (as_.foldl (fun S' a => lstorePost S' rl a t) S)
             (as_.foldl (fun w' a => storePost w' rl a (σ t)) w) := by
  induction as_ with
  | nil => intro S w Hrel; exact Hrel
  | cons a as_ IH => intro S w Hrel; exact IH _ _ (lrelStorePost σ S w rl a t Hrel)

theorem lrelStoreFoldD (σ : Nat → Nat) (rl : Bool) (vf : Nat) (vfL : List Nat) (t : Nat)
    (as_ : List Int) :
    ∀ S w, lrel σ S w →
      lrel σ (as_.foldl (fun S' a => lstorePostD S' rl vfL a t) S)
             (as_.foldl (fun w' a => storePostD w' rl vf a (σ t)) w) := by
  induction as_ with
  | nil => intro S w Hrel; exact Hrel
  | cons a as_ IH => intro S w Hrel; exact IH _ _ (lrelStorePostD σ S w rl vf vfL a t Hrel)

/-- THE RMW SPLIT (S2): `lrel` mentions none of `wRes`'s components, so a
reservation write is transparent to it. -/
theorem lrelWsResSet (σ : Nat → Nat) (S : Lstate) (w : Wstate) (r : Option Wresv) :
    lrel σ S w → lrel σ S (wsResSet w r) := fun Hrel => Hrel

/-- D-2r: the exclusive read's mirror.  The address leaves enter the CONTROL
view exactly as above; the FOLD is the plain one, so its pre-view obligation
is `lrelLoadVpre`, not `lrelLoadVpreD`. -/
theorem lrelLexloadPostRunD (σ : Nat → Nat) (S : Lstate) (w : Wstate) (aq : Bool) (vaddr : Nat)
    (vaddrL : List Nat) (base : Int) (ts : List Nat) :
    Function.Injective σ → lrel σ S w → vaddr = lval σ vaddrL →
    lrel σ (lexloadPostRunD S aq vaddrL base ts) (exloadPostRunD w aq vaddr base (ts.map σ)) := by
  intro Hinj Hrel Hva
  unfold lexloadPostRunD exloadPostRunD
  apply lrelWsResSet
  unfold lloadPostBytes loadPostBytes
  rw [← tatsRun]
  exact lrelCtrlPost σ _ _ _ _
    (lrelLoadFold σ aq _ _ _ Hinj S w Hrel (lrelLoadVpre σ S w aq Hrel))
    (by rw [lvalApp, ← Hva, ← lrelTbank σ S w Hrel])

theorem lrelStorePostRun (σ : Nat → Nat) (S : Lstate) (w : Wstate) (rl : Bool) (base : Int)
    (n t : Nat) :
    lrel σ S w → lrel σ (lstorePostRun S rl base n t) (storePostRun w rl base n (σ t)) :=
  fun Hrel => lrelCtrlPost σ _ _ _ _ (lrelStoreFold σ rl t _ S w Hrel) (lrelTbank σ S w Hrel)

/-- D-7r: the DATA view's transport premise is gone with the bank it fed;
only the ADDRESS view, which still moves `wVcap` through `ctrlPost`, has to
transport. -/
theorem lrelStorePostRunD (σ : Nat → Nat) (S : Lstate) (w : Wstate) (rl : Bool) (va : Nat)
    (vaL : List Nat) (vd : Nat) (vdL : List Nat) (base : Int) (n t : Nat) :
    lrel σ S w → va = lval σ vaL →
    lrel σ (lstorePostRunD S rl vaL vdL base n t) (storePostRunD w rl va vd base n (σ t)) :=
  fun Hrel Hva => lrelCtrlPost σ _ _ _ _ (lrelStoreFoldD σ rl _ _ t _ S w Hrel)
    (by rw [lvalApp, ← Hva, ← lrelTbank σ S w Hrel])

/-! ### THE TRANSPORT THEOREMS -/

theorem lrelAevPost {D : Type} (σ : Nat → Nat) (ev : Aev D) (S : Lstate) (w : Wstate) :
    sigmaOk σ → lrel σ S w → lrel σ (laevPost ev S) (aevPost σ ev w) := by
  rintro ⟨-, Hinj⟩ Hrel
  obtain ⟨lb, ts, dd⟩ := ev
  cases lb with
  | LLoad aq lat base tvs asrc =>
    exact lrelLoadPostRunD σ S w aq _ _ base _ Hinj Hrel (lrelSrcsView σ S w asrc Hrel)
  | LStore rl base data asrc vsrc =>
    cases ts
    · exact Hrel
    · exact lrelStorePostRunD σ S w rl _ _ _ _ base _ _ Hrel (lrelSrcsView σ S w asrc Hrel)
  | LRmw aq rl base tvs data asrc vsrc =>
    cases ts
    · exact Hrel
    · exact lrelStorePostRunD σ _ _ rl _ _ _ _ base _ _
        (lrelLoadPostRunD σ S w aq _ _ base _ Hinj Hrel (lrelSrcsView σ S w asrc Hrel))
        (lrelSrcsView σ S w asrc Hrel)
  | LFence pr pw sr sw => exact lrelFencePost σ S w pr pw sr sw Hrel
  | LRegW rd srcs => exact lrelRegwPost σ S w rd _ _ Hrel (lrelSrcsView σ S w srcs Hrel)
  | LCtrl srcs => exact lrelCtrlPost σ S w _ _ Hrel (lrelSrcsView σ S w srcs Hrel)
  | LInstr => exact lrelInstrPost σ S w Hrel
  | LExLoad aq base tvs asrc =>
    exact lrelLexloadPostRunD σ S w aq _ _ base _ Hinj Hrel (lrelSrcsView σ S w asrc Hrel)
  | LExStore rl base data asrc vsrc =>
    cases ts
    · exact Hrel
    · exact lrelStorePostRunD σ S w rl _ _ _ _ base _ _ Hrel (lrelSrcsView σ S w asrc Hrel)
  | _ => exact Hrel

theorem lrelAevsPost {D : Type} (σ : Nat → Nat) (evs : List (Aev D)) (S : Lstate) (w : Wstate) :
    sigmaOk σ → lrel σ S w → lrel σ (laevsPost evs S) (aevsPost σ evs w) := by
  intro Hσ
  induction evs generalizing S w with
  | nil => intro Hrel; exact Hrel
  | cons ev evs IH => intro Hrel; exact IH _ _ (lrelAevPost σ ev S w Hσ Hrel)

/-- The two instances the simulation reads off: the behavior's own `Wstate`
fold (σ = `id`) and the promise-free run's (σ = π). -/
theorem lrelAevsPostInit {D : Type} (σ : Nat → Nat) (evs : List (Aev D)) :
    sigmaOk σ → lrel σ (laevsPost evs linit) (aevsPost σ evs wsInit) :=
  fun Hσ => lrelAevsPost σ evs _ _ Hσ (lrelInit σ)

theorem lrelAevsPostId {D : Type} (evs : List (Aev D)) :
    lrel id (laevsPost evs linit) (aevsPost id evs wsInit) :=
  lrelAevsPostInit id evs sigmaOkId

/-! ## E. Leaf provenance: every leaf comes from an event -/

/-- `t` occurs in `ev`: either as a timestamp the label reads, or as the
timestamp the event fulfils. -/
def aevTsOccurs {D : Type} (ev : Aev D) (t : Nat) : Prop :=
  (∃ a, (a, t) ∈ lbReads ev.aeLb) ∨ ev.aeTs = some t

def evTsOccurs {D : Type} (evs : List (Aev D)) (t : Nat) : Prop :=
  ∃ ev, ev ∈ evs ∧ aevTsOccurs ev t

theorem evTsOccursCons {D : Type} (ev : Aev D) (evs : List (Aev D)) (t : Nat) :
    aevTsOccurs ev t ∨ evTsOccurs evs t → evTsOccurs (ev :: evs) t := by
  rintro (H | ⟨e, He, H⟩)
  · exact ⟨ev, by simp, H⟩
  · exact ⟨e, by simp [He], H⟩

/-- `t` is a leaf of `S`: it occurs in some component list, some `coh`
entry, or some forward-bank entry (as the raw store timestamp or in the
banked view). -/
def lstateLeaf (S : Lstate) (t : Nat) : Prop :=
  t ∈ S.lVrOld ∨ t ∈ S.lVwOld ∨ t ∈ S.lVrNew ∨ t ∈ S.lVwNew ∨ t ∈ S.lVRel ∨
  (∃ a L, get? S.lCoh a = some L ∧ t ∈ L) ∨
  (∃ a tf V, get? S.lFwd a = some (tf, V) ∧ (t = tf ∨ t ∈ V)) ∨
  (∃ r L, get? S.lRegv r = some L ∧ t ∈ L) ∨
  t ∈ S.lVcap ∨ t ∈ S.lLdv ∨ t ∈ S.lTbank

/-! The introduction forms of `lstateLeaf` (Lean-only, deviation 6). -/

theorem leafVrOld {S : Lstate} {t : Nat} (h : t ∈ S.lVrOld) : lstateLeaf S t := Or.inl h
theorem leafVwOld {S : Lstate} {t : Nat} (h : t ∈ S.lVwOld) : lstateLeaf S t :=
  Or.inr (Or.inl h)
theorem leafVrNew {S : Lstate} {t : Nat} (h : t ∈ S.lVrNew) : lstateLeaf S t :=
  Or.inr (Or.inr (Or.inl h))
theorem leafVwNew {S : Lstate} {t : Nat} (h : t ∈ S.lVwNew) : lstateLeaf S t :=
  Or.inr (Or.inr (Or.inr (Or.inl h)))
theorem leafVRel {S : Lstate} {t : Nat} (h : t ∈ S.lVRel) : lstateLeaf S t :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
theorem leafCoh {S : Lstate} {t : Nat} {a : Int} {L : List Nat} (hL : get? S.lCoh a = some L)
    (h : t ∈ L) : lstateLeaf S t :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a, L, hL, h⟩)))))
theorem leafFwd {S : Lstate} {t : Nat} {a : Int} {tf : Nat} {V : List Nat}
    (hL : get? S.lFwd a = some (tf, V)) (h : t = tf ∨ t ∈ V) : lstateLeaf S t :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a, tf, V, hL, h⟩))))))
theorem leafRegv {S : Lstate} {t : Nat} {r : Nat} {L : List Nat} (hL : get? S.lRegv r = some L)
    (h : t ∈ L) : lstateLeaf S t :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨r, L, hL, h⟩)))))))
theorem leafVcap {S : Lstate} {t : Nat} (h : t ∈ S.lVcap) : lstateLeaf S t :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))
theorem leafLdv {S : Lstate} {t : Nat} (h : t ∈ S.lLdv) : lstateLeaf S t :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))
theorem leafTbank {S : Lstate} {t : Nat} (h : t ∈ S.lTbank) : lstateLeaf S t :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))

theorem memIteOr {α : Type} {c : Prop} [Decidable c] {A B : List α} {x : α} :
    x ∈ (if c then A else B) → x ∈ A ∨ x ∈ B := by
  intro h
  by_cases hc : c
  · rw [if_pos hc] at h; exact Or.inl h
  · rw [if_neg hc] at h; exact Or.inr h

/- `leaf_tac` closes `lstateLeaf S u` from a hypothesis on one of `S`'s
components (Rocq: `rewrite /lstate_leaf; naive_solver`). -/
local macro "leaf_tac" : tactic => `(tactic| first
  | exact leafVrOld ‹_› | exact leafVwOld ‹_› | exact leafVrNew ‹_› | exact leafVwNew ‹_›
  | exact leafVRel ‹_› | exact leafCoh ‹_› ‹_› | exact leafFwd ‹_› ‹_›
  | exact leafRegv ‹_› ‹_› | exact leafVcap ‹_› | exact leafLdv ‹_› | exact leafTbank ‹_›)

theorem lcohLeaf (S : Lstate) (a : Int) (t : Nat) : t ∈ lcoh S a → lstateLeaf S t := by
  unfold lcoh
  cases HL : get? S.lCoh a with
  | none => intro h; cases h
  | some L => intro h; exact leafCoh HL h

theorem lregvLeaf (S : Lstate) (r : Nat) (t : Nat) : t ∈ lregv S r → lstateLeaf S t := by
  unfold lregv
  cases HL : get? S.lRegv r with
  | none => intro h; cases h
  | some L => intro h; exact leafRegv HL h

/-- EVERY LEAF OF AN OPERAND VIEW IS ALREADY A LEAF: the dependency
components add no NEW timestamps to the state, which is why `aevTsOccurs` is
unchanged by D2. -/
theorem lsrcsViewLeaf (S : Lstate) (srcs : List Dsrc) (t : Nat) :
    t ∈ lsrcsView S srcs → lstateLeaf S t := by
  induction srcs with
  | nil => intro h; cases h
  | cons x srcs IH =>
    intro h
    rcases List.mem_append.1 h with h | h
    · cases x with
      | DReg r => exact lregvLeaf S r t h
      | DLdRes => exact leafLdv h
    · exact IH h

theorem linitNoLeaf (t : Nat) : ¬ lstateLeaf linit t := by
  rintro (H|H|H|H|H|⟨a, L, HL, H⟩|⟨a, tf, V, HL, H⟩|⟨r, L, HL, H⟩|H|H|H) <;>
    simp [linit, lookupEmpty] at *

theorem lloadVpreLeaf (S : Lstate) (aq : Bool) (t : Nat) :
    t ∈ lloadVpre S aq → lstateLeaf S t := by
  intro h
  rcases List.mem_append.1 h with h | h
  · exact leafVrNew h
  · rcases memIteOr h with h | h
    · exact leafVRel h
    · cases h

theorem lloadVpreDLeaf (S : Lstate) (aq : Bool) (vaddrL : List Nat) (t : Nat) :
    t ∈ lloadVpreD S aq vaddrL → t ∈ vaddrL ∨ lstateLeaf S t := by
  intro h
  rcases List.mem_append.1 h with h | h
  · exact Or.inl h
  · exact Or.inr (lloadVpreLeaf S aq t h)

theorem lfwdViewLeaf (S : Lstate) (aq : Bool) (a : Int) (t u : Nat) :
    u ∈ lfwdView S aq a t → lstateLeaf S u ∨ u = t := by
  unfold lfwdView
  cases aq
  · simp only [Bool.false_eq_true, ↓reduceIte]
    cases HS : get? S.lFwd a with
    | none => intro h; exact Or.inr (List.mem_singleton.1 h)
    | some p =>
      obtain ⟨tf, V⟩ := p
      intro h
      dsimp only at h
      by_cases Ht : t = tf
      · rw [if_pos Ht] at h; exact Or.inl (leafFwd HS (Or.inr h))
      · rw [if_neg Ht] at h; exact Or.inr (List.mem_singleton.1 h)
  · intro h; exact Or.inr (List.mem_singleton.1 h)

theorem lloadPostAtLeaf (S : Lstate) (aq : Bool) (vpreL : List Nat) (a : Int) (t u : Nat) :
    lstateLeaf (lloadPostAt S aq vpreL a t) u → lstateLeaf S u ∨ u ∈ vpreL ∨ u = t := by
  have Hpost : ∀ v, v ∈ vpreL ++ lfwdView S aq a t → lstateLeaf S v ∨ v ∈ vpreL ∨ v = t := by
    intro v hv
    rcases List.mem_append.1 hv with hv | hv
    · exact Or.inr (Or.inl hv)
    · rcases lfwdViewLeaf S aq a t v hv with hl | hl
      · exact Or.inl hl
      · exact Or.inr (Or.inr hl)
  intro H
  simp only [lstateLeaf, lloadPostAt] at H
  rcases H with H|H|H|H|H|⟨a', L, HL, H⟩|⟨a', tf, V, HL, H⟩|⟨r', L, HL, H⟩|H|H|H
  · rcases List.mem_append.1 H with H | H
    · exact Or.inl (leafVrOld H)
    · exact Hpost u H
  · exact Or.inl (leafVwOld H)
  · rcases memIteOr H with H | H
    · rcases List.mem_append.1 H with H | H
      · exact Or.inl (leafVrNew H)
      · exact Hpost u H
    · exact Or.inl (leafVrNew H)
  · rcases memIteOr H with H | H
    · rcases List.mem_append.1 H with H | H
      · exact Or.inl (leafVwNew H)
      · exact Hpost u H
    · exact Or.inl (leafVwNew H)
  · exact Or.inl (leafVRel H)
  · rcases lookupInsertSome.1 HL with ⟨rfl, rfl⟩ | ⟨-, HL⟩
    · rcases List.mem_append.1 H with H | H
      · exact Or.inl (lcohLeaf S _ u H)
      · rcases List.mem_append.1 H with H | H
        · exact Hpost u H
        · exact Or.inr (Or.inr (List.mem_singleton.1 H))
    · exact Or.inl (leafCoh HL H)
  · exact Or.inl (leafFwd HL H)
  · exact Or.inl (leafRegv HL H)
  · exact Or.inl (leafVcap H)
  · rcases List.mem_append.1 H with H | H
    · exact Or.inl (leafLdv H)
    · exact Hpost u H
  · -- W-TV's bank: the OLD bank, or this byte's forwarded view
    rcases List.mem_append.1 H with H | H
    · exact Or.inl (leafTbank H)
    · rcases lfwdViewLeaf S aq a t u H with Hl | Heq
      · exact Or.inl Hl
      · exact Or.inr (Or.inr Heq)

/-- D-7r: a store adds NO leaf beyond its own timestamp. -/
theorem lstorePostDLeaf (S : Lstate) (rl : Bool) (vfL : List Nat) (a : Int) (t u : Nat) :
    lstateLeaf (lstorePostD S rl vfL a t) u → lstateLeaf S u ∨ u = t := by
  intro H
  simp only [lstateLeaf, lstorePostD] at H
  rcases H with H|H|H|H|H|⟨a', L, HL, H⟩|⟨a', tf, V, HL, H⟩|⟨r', L, HL, H⟩|H|H|H
  · exact Or.inl (leafVrOld H)
  · rcases List.mem_append.1 H with H | H
    · exact Or.inl (leafVwOld H)
    · exact Or.inr (List.mem_singleton.1 H)
  · exact Or.inl (leafVrNew H)
  · exact Or.inl (leafVwNew H)
  · rcases memIteOr H with H | H
    · rcases List.mem_append.1 H with H | H
      · exact Or.inl (leafVRel H)
      · exact Or.inr (List.mem_singleton.1 H)
    · exact Or.inl (leafVRel H)
  · rcases lookupInsertSome.1 HL with ⟨rfl, rfl⟩ | ⟨-, HL⟩
    · rcases List.mem_append.1 H with H | H
      · exact Or.inl (lcohLeaf S _ u H)
      · exact Or.inr (List.mem_singleton.1 H)
    · exact Or.inl (leafCoh HL H)
  · rcases lookupInsertSome.1 HL with ⟨rfl, Heq⟩ | ⟨-, HL⟩
    · -- the banked leaf list is EMPTY: the timestamp column is the only leaf
      cases Heq
      rcases H with H | H
      · exact Or.inr H
      · cases H
    · exact Or.inl (leafFwd HL H)
  · exact Or.inl (leafRegv HL H)
  · exact Or.inl (leafVcap H)
  · exact Or.inl (leafLdv H)
  · exact Or.inl (leafTbank H)

theorem lstorePostLeaf (S : Lstate) (rl : Bool) (a : Int) (t u : Nat) :
    lstateLeaf (lstorePost S rl a t) u → lstateLeaf S u ∨ u = t :=
  lstorePostDLeaf S rl [] a t u

/-- The three dependency-only effects add no leaf beyond the operand list
they are handed. -/
theorem lregwPostLeaf (S : Lstate) (rd : Nat) (vL : List Nat) (u : Nat) :
    lstateLeaf (lregwPost S rd vL) u → lstateLeaf S u ∨ u ∈ vL := by
  intro H
  simp only [lstateLeaf, lregwPost] at H
  rcases H with H|H|H|H|H|⟨a', L, HL, H⟩|⟨a', tf, V, HL, H⟩|⟨r', L, HL, H⟩|H|H|H
  case inr.inr.inr.inr.inr.inr.inr.inl =>
    rcases lookupInsertSome.1 HL with ⟨rfl, rfl⟩ | ⟨-, HL⟩
    · exact Or.inr H
    · exact Or.inl (leafRegv HL H)
  all_goals exact Or.inl (by leaf_tac)

theorem lctrlPostLeaf (S : Lstate) (vL : List Nat) (u : Nat) :
    lstateLeaf (lctrlPost S vL) u → lstateLeaf S u ∨ u ∈ vL := by
  intro H
  simp only [lstateLeaf, lctrlPost] at H
  rcases H with H|H|H|H|H|⟨a', L, HL, H⟩|⟨a', tf, V, HL, H⟩|⟨r', L, HL, H⟩|H|H|H
  case inr.inr.inr.inr.inr.inr.inr.inr.inl =>
    rcases List.mem_append.1 H with H | H
    · exact Or.inr H
    · exact Or.inl (leafVcap H)
  all_goals exact Or.inl (by leaf_tac)

theorem linstrPostLeaf (S : Lstate) (u : Nat) :
    lstateLeaf (linstrPost S) u → lstateLeaf S u := by
  intro H
  simp only [lstateLeaf, linstrPost] at H
  rcases H with H|H|H|H|H|⟨a', L, HL, H⟩|⟨a', tf, V, HL, H⟩|⟨r', L, HL, H⟩|H|H|H
  case inr.inr.inr.inr.inr.inr.inr.inr.inr.inl => cases H
  case inr.inr.inr.inr.inr.inr.inr.inr.inr.inr => cases H
  all_goals leaf_tac

theorem lfencePostLeaf (S : Lstate) (pr pw sr sw : Bool) (u : Nat) :
    lstateLeaf (lfencePost S pr pw sr sw) u → lstateLeaf S u := by
  have Hv1 : ∀ v, v ∈ (if pr then S.lVrOld else []) ++ (if pw then S.lVwOld else []) →
      lstateLeaf S v := by
    intro v hv
    rcases List.mem_append.1 hv with hv | hv
    · rcases memIteOr hv with hv | hv
      · exact leafVrOld hv
      · cases hv
    · rcases memIteOr hv with hv | hv
      · exact leafVwOld hv
      · cases hv
  intro H
  simp only [lstateLeaf, lfencePost] at H
  rcases H with H|H|H|H|H|⟨a', L, HL, H⟩|⟨a', tf, V, HL, H⟩|⟨r', L, HL, H⟩|H|H|H
  case inr.inr.inl =>
    rcases memIteOr H with H | H
    · rcases List.mem_append.1 H with H | H
      · exact leafVrNew H
      · exact Hv1 u H
    · exact leafVrNew H
  case inr.inr.inr.inl =>
    rcases memIteOr H with H | H
    · rcases List.mem_append.1 H with H | H
      · exact leafVwNew H
      · exact Hv1 u H
    · exact leafVwNew H
  all_goals leaf_tac

theorem lloadFoldLeaf (aq : Bool) (vpreL : List Nat) (ats : List (Int × Nat)) :
    ∀ S u,
      lstateLeaf (ats.foldl (fun S' at_ => lloadPostAt S' aq vpreL at_.1 at_.2) S) u →
      lstateLeaf S u ∨ u ∈ vpreL ∨ ∃ p, p ∈ ats ∧ u = p.2 := by
  induction ats with
  | nil => intro S u Hu; exact Or.inl Hu
  | cons p ats IH =>
    intro S u Hu
    rcases IH _ u Hu with Hu | Hu | ⟨q, Hq, rfl⟩
    · rcases lloadPostAtLeaf S aq vpreL p.1 p.2 u Hu with Hu | Hu | rfl
      · exact Or.inl Hu
      · exact Or.inr (Or.inl Hu)
      · exact Or.inr (Or.inr ⟨p, by simp, rfl⟩)
    · exact Or.inr (Or.inl Hu)
    · exact Or.inr (Or.inr ⟨q, by simp [Hq], rfl⟩)

theorem lloadPostBytesLeaf (S : Lstate) (aq : Bool) (ats : List (Int × Nat)) (u : Nat) :
    lstateLeaf (lloadPostBytes S aq ats) u → lstateLeaf S u ∨ ∃ p, p ∈ ats ∧ u = p.2 := by
  intro Hu
  rcases lloadFoldLeaf aq _ ats S u Hu with Hu | Hu | Hu
  · exact Or.inl Hu
  · exact Or.inl (lloadVpreLeaf S aq u Hu)
  · exact Or.inr Hu

theorem lloadPostBytesDLeaf (S : Lstate) (aq : Bool) (vaddrL : List Nat)
    (ats : List (Int × Nat)) (u : Nat) :
    lstateLeaf (lloadPostBytesD S aq vaddrL ats) u →
    lstateLeaf S u ∨ u ∈ vaddrL ∨ ∃ p, p ∈ ats ∧ u = p.2 := by
  intro Hu
  rcases lloadFoldLeaf aq _ ats S u Hu with Hu | Hu | Hu
  · exact Or.inl Hu
  · rcases lloadVpreDLeaf S aq vaddrL u Hu with Hu | Hu
    · exact Or.inr (Or.inl Hu)
    · exact Or.inl Hu
  · exact Or.inr (Or.inr Hu)

theorem lstoreFoldLeaf (rl : Bool) (t : Nat) (as_ : List Int) :
    ∀ S u, lstateLeaf (as_.foldl (fun S' a => lstorePost S' rl a t) S) u →
      lstateLeaf S u ∨ u = t := by
  induction as_ with
  | nil => intro S u Hu; exact Or.inl Hu
  | cons a as_ IH =>
    intro S u Hu
    rcases IH _ u Hu with Hu | Heq
    · exact lstorePostLeaf S rl a t u Hu
    · exact Or.inr Heq

theorem lstoreFoldDLeaf (rl : Bool) (vfL : List Nat) (t : Nat) (as_ : List Int) :
    ∀ S u, lstateLeaf (as_.foldl (fun S' a => lstorePostD S' rl vfL a t) S) u →
      lstateLeaf S u ∨ u = t := by
  induction as_ with
  | nil => intro S u Hu; exact Or.inl Hu
  | cons a as_ IH =>
    intro S u Hu
    rcases IH _ u Hu with Hu | Heq
    · exact lstorePostDLeaf S rl vfL a t u Hu
    · exact Or.inr Heq

theorem lstorePostRunLeaf (S : Lstate) (rl : Bool) (base : Int) (n t u : Nat) :
    lstateLeaf (lstorePostRun S rl base n t) u → lstateLeaf S u ∨ u = t := by
  intro Hu
  rcases lctrlPostLeaf _ _ u Hu with Hu | Hu
  · exact lstoreFoldLeaf rl t _ S u Hu
  · exact Or.inl (leafTbank Hu)

theorem lstorePostRunDLeaf (S : Lstate) (rl : Bool) (vaL vdL : List Nat) (base : Int)
    (n t u : Nat) :
    lstateLeaf (lstorePostRunD S rl vaL vdL base n t) u →
    lstateLeaf S u ∨ u ∈ vaL ∨ u ∈ vdL ∨ u = t := by
  intro Hu
  rcases lctrlPostLeaf _ _ u Hu with Hu | Hu
  · rcases lstoreFoldDLeaf rl _ t _ S u Hu with Hu | Heq
    · exact Or.inl Hu
    · exact Or.inr (Or.inr (Or.inr Heq))
  · rcases List.mem_append.1 Hu with Hu | Hu
    · exact Or.inr (Or.inl Hu)
    · exact Or.inl (leafTbank Hu)

/-- The contiguous-run access list only ever carries timestamps that are IN
the run's timestamp list. -/
theorem runAtsTs (base : Int) (ts : List Nat) (p : Int × Nat) :
    p ∈ List.zipWith (fun (j : Nat) (t : Nat) => (base + (j : Int), t))
      (List.range' 0 ts.length) ts →
    ∃ j : Nat, ts[j]? = some p.2 := by
  intro Hp
  obtain ⟨i, x, y, Hpe, -, Hy⟩ := elem_of_lookup_zip_with_1 Hp
  subst Hpe
  exact ⟨i, Hy⟩

theorem lloadPostRunLeaf (S : Lstate) (aq : Bool) (base : Int) (ts : List Nat) (u : Nat) :
    lstateLeaf (lloadPostRun S aq base ts) u → lstateLeaf S u ∨ ∃ j : Nat, ts[j]? = some u := by
  intro Hu
  rcases lctrlPostLeaf _ _ u Hu with Hu | Hu
  · rcases lloadPostBytesLeaf S aq _ u Hu with Hu | ⟨p, Hp, rfl⟩
    · exact Or.inl Hu
    · exact Or.inr (runAtsTs base ts p Hp)
  · exact Or.inl (leafTbank Hu)

theorem lloadPostRunDLeaf (S : Lstate) (aq : Bool) (vaddrL : List Nat) (base : Int)
    (ts : List Nat) (u : Nat) :
    lstateLeaf (lloadPostRunD S aq vaddrL base ts) u →
    lstateLeaf S u ∨ u ∈ vaddrL ∨ ∃ j : Nat, ts[j]? = some u := by
  intro Hu
  rcases lctrlPostLeaf _ _ u Hu with Hu | Hu
  · rcases lloadPostBytesDLeaf S aq vaddrL _ u Hu with Hu | Hu | ⟨p, Hp, rfl⟩
    · exact Or.inl Hu
    · exact Or.inr (Or.inl Hu)
    · exact Or.inr (Or.inr (runAtsTs base ts p Hp))
  · rcases List.mem_append.1 Hu with Hu | Hu
    · exact Or.inr (Or.inl Hu)
    · exact Or.inl (leafTbank Hu)

/-- D-2r: the SAME three cases for the exclusive read (the address leaves
still reach `lVcap`, they just no longer reach the fold). -/
theorem lexloadPostRunDLeaf (S : Lstate) (aq : Bool) (vaddrL : List Nat) (base : Int)
    (ts : List Nat) (u : Nat) :
    lstateLeaf (lexloadPostRunD S aq vaddrL base ts) u →
    lstateLeaf S u ∨ u ∈ vaddrL ∨ ∃ j : Nat, ts[j]? = some u := by
  intro Hu
  rcases lctrlPostLeaf _ _ u Hu with Hu | Hu
  · rcases lloadPostBytesLeaf S aq _ u Hu with Hu | ⟨p, Hp, rfl⟩
    · exact Or.inl Hu
    · exact Or.inr (Or.inr (runAtsTs base ts p Hp))
  · rcases List.mem_append.1 Hu with Hu | Hu
    · exact Or.inr (Or.inl Hu)
    · exact Or.inl (leafTbank Hu)

/-- A timestamp read by byte `j` of a load/rmw label IS one of the label's
reads. -/
theorem tvsFstReads (base : Int) (tvs : List (Nat × BitVec 8)) (j u : Nat) :
    (tvs.map Prod.fst)[j]? = some u → ∃ a, (a, u) ∈ tvsReads base tvs := by
  intro h
  rw [List.getElem?_map] at h
  cases Hj : tvs[j]? with
  | none => rw [Hj] at h; cases h
  | some p =>
    rw [Hj] at h
    obtain ⟨t, v⟩ := p
    obtain rfl : t = u := Option.some.inj h
    exact ⟨base + (j : Int), (memTvsReads base tvs _ _).2 ⟨j, v, Hj, rfl⟩⟩

theorem laevPostLeaf {D : Type} (ev : Aev D) (S : Lstate) (u : Nat) :
    lstateLeaf (laevPost ev S) u → lstateLeaf S u ∨ aevTsOccurs ev u := by
  obtain ⟨lb, ts, dd⟩ := ev
  intro Hu
  cases lb with
  | LLoad aq lat base tvs asrc =>
    rcases lloadPostRunDLeaf S aq _ base _ u Hu with Hu | Hu | ⟨j, Hj⟩
    · exact Or.inl Hu
    · exact Or.inl (lsrcsViewLeaf S asrc u Hu)
    · exact Or.inr (Or.inl (tvsFstReads base tvs j u Hj))
  | LStore rl base data asrc vsrc =>
    cases ts with
    | none => exact Or.inl Hu
    | some t =>
      rcases lstorePostRunDLeaf S rl _ _ base _ t u Hu with Hu | Hu | Hu | rfl
      · exact Or.inl Hu
      · exact Or.inl (lsrcsViewLeaf S asrc u Hu)
      · exact Or.inl (lsrcsViewLeaf S vsrc u Hu)
      · exact Or.inr (Or.inr rfl)
  | LRmw aq rl base tvs data asrc vsrc =>
    cases ts with
    | none => exact Or.inl Hu
    | some t =>
      rcases lstorePostRunDLeaf _ rl _ _ base _ t u Hu with Hu | Hu | Hu | rfl
      · rcases lloadPostRunDLeaf S aq _ base _ u Hu with Hu | Hu | ⟨j, Hj⟩
        · exact Or.inl Hu
        · exact Or.inl (lsrcsViewLeaf S asrc u Hu)
        · exact Or.inr (Or.inl (tvsFstReads base tvs j u Hj))
      · exact Or.inl (lsrcsViewLeaf S asrc u Hu)
      · exact Or.inl (lsrcsViewLeaf S vsrc u Hu)
      · exact Or.inr (Or.inr rfl)
  | LFence pr pw sr sw => exact Or.inl (lfencePostLeaf S pr pw sr sw u Hu)
  | LRegW rd srcs =>
    rcases lregwPostLeaf S rd _ u Hu with Hu | Hu
    · exact Or.inl Hu
    · exact Or.inl (lsrcsViewLeaf S srcs u Hu)
  | LCtrl srcs =>
    rcases lctrlPostLeaf S _ u Hu with Hu | Hu
    · exact Or.inl Hu
    · exact Or.inl (lsrcsViewLeaf S srcs u Hu)
  | LInstr => exact Or.inl (linstrPostLeaf S u Hu)
  -- THE RMW SPLIT (S2): `LLoad`'s / `LStore`'s arm verbatim
  | LExLoad aq base tvs asrc =>
    rcases lexloadPostRunDLeaf S aq _ base _ u Hu with Hu | Hu | ⟨j, Hj⟩
    · exact Or.inl Hu
    · exact Or.inl (lsrcsViewLeaf S asrc u Hu)
    · exact Or.inr (Or.inl (tvsFstReads base tvs j u Hj))
  | LExStore rl base data asrc vsrc =>
    cases ts with
    | none => exact Or.inl Hu
    | some t =>
      rcases lstorePostRunDLeaf S rl _ _ base _ t u Hu with Hu | Hu | Hu | rfl
      · exact Or.inl Hu
      · exact Or.inl (lsrcsViewLeaf S asrc u Hu)
      · exact Or.inl (lsrcsViewLeaf S vsrc u Hu)
      · exact Or.inr (Or.inr rfl)
  | _ => exact Or.inl Hu

theorem laevsPostLeaf {D : Type} (evs : List (Aev D)) :
    ∀ S u, lstateLeaf (laevsPost evs S) u → lstateLeaf S u ∨ evTsOccurs evs u := by
  induction evs with
  | nil => intro S u Hu; exact Or.inl Hu
  | cons ev evs IH =>
    intro S u Hu
    rcases IH _ u Hu with Hu | Hu
    · rcases laevPostLeaf ev S u Hu with Hu | Hu
      · exact Or.inl Hu
      · exact Or.inr (evTsOccursCons ev evs u (Or.inl Hu))
    · exact Or.inr (evTsOccursCons ev evs u (Or.inr Hu))

/-- THE PROVENANCE BOUND: every leaf of the whole fold from `linit` is a
timestamp some event of the trace read or fulfilled. -/
theorem laevsLeavesOccur {D : Type} (evs : List (Aev D)) (t : Nat) :
    lstateLeaf (laevsPost evs linit) t → evTsOccurs evs t := by
  intro Ht
  rcases laevsPostLeaf evs linit t Ht with Ht | Ht
  · exact absurd Ht (linitNoLeaf t)
  · exact Ht

/-! ## F. What the consumer reads off -/

/-- The READ FLOOR of an access, `max (loadVpre, coh a)`, as a leaf set (the
`F` of the W2b design's E-edges). -/
def lfloor (S : Lstate) (aq : Bool) (a : Int) : List Nat :=
  lloadVpre S aq ++ lcoh S a

theorem lrelFloor (σ : Nat → Nat) (S : Lstate) (w : Wstate) (aq : Bool) (a : Int) :
    lrel σ S w → max (loadVpre w aq) (coh w a) = lval σ (lfloor S aq a) := by
  intro Hrel
  rw [lfloor, lvalApp, ← lrelLoadVpre σ S w aq Hrel, ← Hrel.1 a]

/-- THE D2 FLOOR: the read floor of a DEPENDENCY-CARRYING load.  Its leaf
list is the operand leaves in front of the old floor's, and `lsrcsViewLeaf`
says those are leaves of the SAME state. -/
theorem lrelFloorD (σ : Nat → Nat) (S : Lstate) (w : Wstate) (aq : Bool) (a : Int)
    (asrc : List Dsrc) :
    lrel σ S w →
    max (loadVpreD w aq (srcsView w asrc)) (coh w a) = lval σ (lsrcsView S asrc ++ lfloor S aq a) := by
  intro Hrel
  rw [lvalApp, ← lrelFloor σ S w aq a Hrel, ← lrelSrcsView σ S w asrc Hrel, loadVpreD]
  omega

/-! ## What W2b inherits

- `astepsWsFold`: a wf trace's `k`-th agent record carries exactly
  `aevsPost id (evs.take k)` of the initial `Wstate`.
- `lrelAevsPost` (+ `lrelAevsPostInit`): the SAME leaf state
  `laevsPost evs linit` valuates, under ANY `sigmaOk` σ, to
  `aevsPost σ evs wsInit`; at σ = `id` and σ = π these are the behavior's and
  the promise-free run's views, two valuations of ONE leaf state.
- `lrelFloor` + `lfloor`: the read floor is `lval σ` of a leaf list
  computable from the trace; with `lvalLeIff` / `lvalLt` / `lvalGe` a floor
  bound is exactly a pointwise bound on σ of the leaves.
- `laevsLeavesOccur`: every leaf is a timestamp SOME event of the trace read
  or fulfilled, so an E-edge's source is always a graph node. -/

end Weak
