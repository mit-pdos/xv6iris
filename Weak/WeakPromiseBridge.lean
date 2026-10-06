/-
Weak: **the erasure bridge** (M6 W1, last item; D-M6-7).

Rocq: `iris/WeakPromiseBridge.v` @ xxvzwolszwmp (1cc222280).

The Rocq header, in substance: `WeakPromise` is the FULL promising machine
(promise sets, the `lat` load kind, PARM-style rmw = `readOk` + `exclOk`);
`WeakAxiomatic` is the canonical PROMISE-FREE labelled LTS (`Mstate`/`mstep`,
executions as (state list, step list) pairs).  D-M6-7 says the two meet by
PROJECTION, and this file is that projection: every promise-free run of
`WeakPromise` projects to an `execWf` execution of `WeakAxiomatic` with the
same image, the same log and the same per-agent `Wstate`s.  The pieces:

(A) `wpPfStep` — the promise-free FRAGMENT of the full machine, the store and
    the rmw FUSED (promise at the fresh top, fulfil immediately); a pf step is
    one or two `wpstep`s (`wpPfStepRtcWpstep`) and keeps every promise set
    empty, hence `wpPfBehavior`.  The class of an appended message is PINNED
    by the abstract class function `pcls` read at the fulfilling agent's
    pre-step program state and `Wstate` (G6a; the Rocq section comment on
    `pcls` records why the full machine keeps its free binder).
(B) `projLbl` / `cfgMatch` — label and state projections; silent and
    dependency-only steps STUTTER; `lat` pinning and the dependency view are
    dropped soundly (`readOkDRdOk`).  `wsEqr` / `cfgMatchd` / `cfgEqr` are
    the T1-D weakening (per-agent `Wstate` equality on the nine components
    any side condition reads, silent about `wRegv`/`wVcap`/`wLdv`/`wTbank`/
    `wRes`).
(C) `pfRmwLatest` — THE DOVETAIL: `readable` + `exclOk` + the invariant
    `ownCoh` give `rmwLatest`.
(D) `wpPfBridge` — the theorem.
(E) `execWfPfRun` — the reverse direction under `progFree` and
    `execClsOk`.

DEPENDENCY-FREE like its inputs: `WeakMem`, `WeakPromise`, `WeakPromiseFact`,
`WeakAxiomatic`.  As in Rocq, the two label alphabets share constructor names;
here they are kept apart by namespace (`Wlabel.LLoad` vs `Lbl.LLoad`, written
`.LLoad` where the expected type fixes it).

**Deviations from Rocq.**

1. NAMES: as `Weak/WeakMem.lean` deviation 1.  The Rocq `Reflexive` /
   `Symmetric` / `Transitive` instances of `ws_eqr` are the theorems
   `wsEqrRefl` / `wsEqrSym` / `wsEqrTrans` plus a `Trans` instance.
   `wp_pf_step` keeps a lower-camel name (`wpPfStep`, a Prop-valued
   inductive, like `wpstep`); its arms are `wpPfStep.PFSilent` …
   `wpPfStep.PFExStore`.
2. VOCABULARY: as `WeakPromise` deviation 2; `zip` ↦ `List.zip`,
   `fst_zip` ↦ `List.map_fst_zip`, `pa_st <$> pc_ags c` ↦
   `c.pcAgs.map Wpagent.paSt`, `tvs.*2` ↦ `tvs.map Prod.snd`.
3. The section variables `pstep` and `pcls` are explicit arguments of every
   declaration that uses them, in Rocq's order (`Global Arguments`).
4. CONVERSIONS: `read_ok_d … 0`, `load_post_run_d … 0` and
   `store_post_run_d … 0 0` collapse to the plain forms by Rocq conversion
   (`Nat.max 0 x ≡ x`) but not in Lean; the proofs rewrite with
   `loadVpreD0` / `loadPostRunD0` / `storePostRunD0` (`WeakMem` deviation 3).
   Statements unchanged.
5. PROOFS: `wp_pf_run_rtc_wpstep` goes by tail induction on `rtc` (Rocq: head
   induction); `bridge_run` by `rtc_ind_l`.  Statements unchanged.
6. O2 — THE INSTRUCTION FETCH (Lean-only label `LIFetch`, `Weak/WeakPromise.lean`
   deviation 8; owner decision (B), 2026-10-06).  A fetch cannot be replayed as
   an axiomatic load unconditionally: `MStepLoad` needs `rdOk` (readability at
   `loadVpre`), which `ifetchOk` does not imply (a stale pre-`fence.i` fetch), and
   `MStepLoad`'s post-state `loadPostRun` (raises `coh`/`wVrOld`/`wLdv`/`wVcap`,
   clears `wRes`) differs from the fetch's IDENTITY post-state.  Changes:
   - `wpPfStep` gains the arm `PFIFetch` (the twin of `wpstep.WPIFetch`:
     `ifetchOk img log 0 base tvs`, state/log/promises unchanged);
     `wpPfStepRtcWpstep` and `ownCohStep` gain the matching arm.
   - `projLbl (LIFetch base tvs) = some (LLoad false base tvs.*1 tvs.*2)`: a fetch
     projects to a PLAIN (`aq = false`) axiomatic load.
   - THE EXTRA PREMISES, per step: `pfFetchLoadOk c i l` (vacuous unless `l` is
     `LIFetch base tvs`; then, for the agent's `ws`):
     (i)  every fetched byte `(t, v)` at `base + j` is `readable … ws (loadVpre ws
          false) (base + j) t` — exactly `MStepLoad`'s `rdOk` minus the value
          conjunct, which `ifetchOk` already gives;
     (ii) `wsEqr (loadPostRun ws false base tvs.*1) ws` — the load's update is
          inert on the nine compared components (field form:
          `wsEqrLoadPostRunSelf`: for every byte, `vpost ≤ wVrOld` and
          `max vpost t ≤ coh a`, `vpost = max (loadVpre ws false) (fwdView ws
          false a t)`).
     Run level: `pfRunFetchOk c c'` (every step of a pf run `c →* c'`
     satisfies `pfFetchLoadOk`), discharged for fetch-free programs by
     `pfRunFetchOkNoFetch` (`pstepNoFetch`).  Non-vacuity: `pfFetchLoadOkInit`
     (a fresh agent's image-byte fetch), `wsEqrLoadPostRunInit`.
   - THE MATCH IS WEAKENED, `cfgMatch` ↦ `cfgMatchd` (the Rocq T1-D relation,
     per-agent `wsEqr`; image and log still equal), in `wpPfStepMstep`,
     `bridgeStep`, `bridgeRun`, `wpPfBridge` (premise and conclusion).  WHY
     (ii) is not stated as Wstate EQUALITY with `cfgMatch` kept: `loadPostAt`
     inserts a `wCoh` entry unconditionally, so `loadPostRun ws false base ts =
     ws` is FALSE whenever `wCoh` lacks the fetched addresses — e.g. every fetch
     from `wsInit` (`wCoh = ∅`) — making the equality form vacuous in practice;
     and it would also demand `wRes = none`, `wLdv`/`wVcap` already raised.
     `wsEqr` ignores exactly `wRegv`/`wVcap`/`wLdv`/`wTbank`/`wRes`, which the
     dependency-free, fused fragment never reads, and compares `coh`
     pointwise; `coh` and `wVrOld` CANNOT be ignored (every later `rdOk`
     reads them), so (ii) constrains exactly those.  (i) and (ii) are then the
     smallest sound premises: (i) is `MStepLoad`'s own side condition, (ii) is
     necessary and sufficient for the `cfgMatchd` step.
   - `wpPfBridgeLog`: same conclusion; gains the `pfRunFetchOk` premise.  The
     reverse direction (E) is unchanged (`unprojLbl` never yields `LIFetch`).
   - Lean-only helpers: `wsEqrRdOk`, `wsEqrLoadPostAtSelf`,
     `wsEqrLoadFoldSelf`, `wsEqrLoadPostRunSelf`, `wsEqrLoadPostRunInit`,
     `pfFetchLoadOk`, `pfFetchLoadOkInit`, `pfRunFetchOk`, `pstepNoFetch`,
     `pfRunFetchOkNoFetch`.

**Rocq → Lean name map.**  `ws_eqr` ↦ `wsEqr`; `ws_eqr_{coh,vrOld,vwOld,
vrNew,vwNew,vRel,fwd,pub,relp}` ↦ `wsEqr{Coh,VrOld,VwOld,VrNew,VwNew,VRel,Fwd,
Pub,Relp}`; `ws_depmove_ws_eqr` ↦ `wsDepmoveWsEqr`; `ws_eqr_{regw_post,
ctrl_post,instr_post,res_set,ctrl_cong,res_set_cong,load_post_at,store_post,
fence_post,load_fold,load_post_bytes,store_fold,store_post_bytes,
load_post_run,store_post_run_d,exload_post_run_d,readable,read_ok}` ↦
`wsEqr{RegwPost,CtrlPost,InstrPost,ResSet,CtrlCong,ResSetCong,LoadPostAt,
StorePost,FencePost,LoadFold,LoadPostBytes,StoreFold,StorePostBytes,
LoadPostRun,StorePostRunD,ExloadPostRunD,Readable,ReadOk}`; `pcls_eqr` ↦
`pclsEqr`; `wp_pf_step` ↦ `wpPfStep` (arms `PFSilent` … `PFExStore` kept);
`wp_pf_run` ↦ `wpPfRun`; `wp_pf_step_rtc_wpstep` ↦ `wpPfStepRtcWpstep`;
`no_promises_upd` ↦ `noPromisesUpd`; `wp_pf_step_no_promises` ↦
`wpPfStepNoPromises`; `wp_pf_run_rtc_wpstep` ↦ `wpPfRunRtcWpstep`;
`wp_pf_behavior` ↦ `wpPfBehavior`; `proj_lbl` ↦ `projLbl`; `cfg_match` ↦
`cfgMatch`; `cfg_matchd` ↦ `cfgMatchd`; `cfg_match_cfg_matchd` ↦
`cfgMatchCfgMatchd`; `cfg_matchd_{img,log,ws,upd_gen}` ↦
`cfgMatchd{Img,Log,Ws,UpdGen}`; `cfg_eqr` ↦ `cfgEqr`; `cfg_eqr_{refl,trans,
matchd}` ↦ `cfgEqr{Refl,Trans,Matchd}`; `proj_ws` ↦ `projWs`; `proj_st` ↦
`projSt`; `cfg_match_proj` ↦ `cfgMatchProj`; `cfg_match_log` ↦
`cfgMatchLog`; `cfg_match_upd_gen` ↦ `cfgMatchUpdGen`; `read_ok_d_rd_ok` ↦
`readOkDRdOk`; `read_ok_rd_ok` ↦ `readOkRdOk`; `own_coh` ↦ `ownCoh`;
`own_coh_{init,upd,append,step,run}` ↦ `ownCoh{Init,Upd,Append,Step,Run}`;
`pf_rmw_latest` ↦ `pfRmwLatest`; `wp_pf_step_mstep` ↦ `wpPfStepMstep`;
`bridge_step` ↦ `bridgeStep`; `pstep_depfree` ↦ `pstepDepfree`;
`wp_pf_step_lb_depfree` ↦ `wpPfStepLbDepfree`; `pstep_fused` ↦
`pstepFused`; `wp_pf_step_lb_fused` ↦ `wpPfStepLbFused`; `bridge_run` ↦
`bridgeRun`; `wp_pf_bridge` ↦ `wpPfBridge`; `wp_pf_bridge_log` ↦
`wpPfBridgeLog`; `prog_free` ↦ `progFree`; `unproj_lbl` ↦ `unprojLbl`;
`mstep_cls_ok` ↦ `mstepClsOk`; `exec_cls_ok` ↦ `execClsOk`;
`rd_ok_read_ok` ↦ `rdOkReadOk`; `rmw_latest_excl_ok` ↦ `rmwLatestExclOk`;
`wp_pf_step_ags_length` ↦ `wpPfStepAgsLength`; `mstep_wp_pf_step` ↦
`mstepWpPfStep`; `exec_prefix_pf_run` ↦ `execPrefixPfRun`;
`exec_wf_pf_run` ↦ `execWfPfRun`.

**Not ported:** nothing — every Rocq definition and lemma has a Lean twin.

**Statements checked** (by hand, against Rocq): all of them; the changed ones
are listed under deviation 6 (`wpPfStep` (+ arm), `projLbl` (+ arm),
`wpPfStepMstep`, `bridgeStep`, `bridgeRun`, `wpPfBridge`, `wpPfBridgeLog`).
-/
import Weak.WeakAxiomatic
import Weak.WeakPromiseFact

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std

/-! ## `wsEqr` — THE T1-D COMPLETENESS RELATION ON `Wstate`s

EQUAL on every component any `WeakPromise` side condition or any `mstep`
post-state reads (`coh` pointwise, `wVrOld`, `wVwOld`, `wVrNew`, `wVwNew`,
`wVRel`, `wFwd`, `wPub`, `wRelp`), SILENT about the five the dependency
machinery owns (`wRegv`, `wVcap`, `wLdv`, `wTbank`, `wRes`).  See the Rocq
comment for why the five are safe to drop in the promise-free fragment and why
the nine must stay equal. -/
def wsEqr (w1 w2 : Wstate) : Prop :=
  (∀ a, coh w1 a = coh w2 a) ∧
  w1.wVrOld = w2.wVrOld ∧ w1.wVwOld = w2.wVwOld ∧
  w1.wVrNew = w2.wVrNew ∧ w1.wVwNew = w2.wVwNew ∧
  w1.wVRel = w2.wVRel ∧ w1.wFwd = w2.wFwd ∧
  w1.wPub = w2.wPub ∧ w1.wRelp = w2.wRelp

theorem wsEqrRefl (w : Wstate) : wsEqr w w :=
  ⟨fun _ => rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem wsEqrSym {w1 w2 : Wstate} : wsEqr w1 w2 → wsEqr w2 w1 := by
  rintro ⟨hc, h1, h2, h3, h4, h5, h6, h7, h8⟩
  exact ⟨fun a => (hc a).symm, h1.symm, h2.symm, h3.symm, h4.symm, h5.symm, h6.symm, h7.symm,
    h8.symm⟩

theorem wsEqrTrans {w1 w2 w3 : Wstate} : wsEqr w1 w2 → wsEqr w2 w3 → wsEqr w1 w3 := by
  rintro ⟨hc, h1, h2, h3, h4, h5, h6, h7, h8⟩ ⟨gc, g1, g2, g3, g4, g5, g6, g7, g8⟩
  exact ⟨fun a => (hc a).trans (gc a), h1.trans g1, h2.trans g2, h3.trans g3, h4.trans g4,
    h5.trans g5, h6.trans g6, h7.trans g7, h8.trans g8⟩

instance : Trans wsEqr wsEqr wsEqr := ⟨wsEqrTrans⟩

/-! The projections. -/
theorem wsEqrCoh (w1 w2 : Wstate) (a : Int) : wsEqr w1 w2 → coh w1 a = coh w2 a :=
  fun h => h.1 a
theorem wsEqrVrOld (w1 w2 : Wstate) : wsEqr w1 w2 → w1.wVrOld = w2.wVrOld := fun h => h.2.1
theorem wsEqrVwOld (w1 w2 : Wstate) : wsEqr w1 w2 → w1.wVwOld = w2.wVwOld := fun h => h.2.2.1
theorem wsEqrVrNew (w1 w2 : Wstate) : wsEqr w1 w2 → w1.wVrNew = w2.wVrNew :=
  fun h => h.2.2.2.1
theorem wsEqrVwNew (w1 w2 : Wstate) : wsEqr w1 w2 → w1.wVwNew = w2.wVwNew :=
  fun h => h.2.2.2.2.1
theorem wsEqrVRel (w1 w2 : Wstate) : wsEqr w1 w2 → w1.wVRel = w2.wVRel :=
  fun h => h.2.2.2.2.2.1
theorem wsEqrFwd (w1 w2 : Wstate) : wsEqr w1 w2 → w1.wFwd = w2.wFwd :=
  fun h => h.2.2.2.2.2.2.1
theorem wsEqrPub (w1 w2 : Wstate) : wsEqr w1 w2 → w1.wPub = w2.wPub :=
  fun h => h.2.2.2.2.2.2.2.1
theorem wsEqrRelp (w1 w2 : Wstate) : wsEqr w1 w2 → w1.wRelp = w2.wRelp :=
  fun h => h.2.2.2.2.2.2.2.2

/-- `wsDepmove` IS `wsEqr` plus a `wVcap` bound, so every dependency-only
effect is `wsEqr`-inert for free. -/
theorem wsDepmoveWsEqr (w1 w2 : Wstate) : wsDepmove w1 w2 → wsEqr w1 w2 := by
  rintro ⟨hc, h1, h2, h3, h4, h5, h6, h7, h8, _⟩
  exact ⟨fun a => by simp only [coh, hc], h1.symm, h2.symm, h3.symm, h4.symm, h5.symm, h6.symm,
    h7.symm, h8.symm⟩

theorem wsEqrRegwPost (ws : Wstate) (rd v : Nat) : wsEqr ws (regwPost ws rd v) :=
  wsDepmoveWsEqr _ _ (regwPostDepmove ws rd v)
theorem wsEqrCtrlPost (ws : Wstate) (v : Nat) : wsEqr ws (ctrlPost ws v) :=
  wsDepmoveWsEqr _ _ (ctrlPostDepmove ws v)
theorem wsEqrInstrPost (ws : Wstate) : wsEqr ws (instrPost ws) :=
  wsDepmoveWsEqr _ _ (instrPostDepmove ws)
theorem wsEqrResSet (ws : Wstate) (r : Option Wresv) : wsEqr ws (wsResSet ws r) :=
  ⟨fun _ => rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- ... hence the two wrappers every run-level access ends in are congruences
AT UNRELATED ARGUMENTS. -/
theorem wsEqrCtrlCong (w1 w2 : Wstate) (v1 v2 : Nat) :
    wsEqr w1 w2 → wsEqr (ctrlPost w1 v1) (ctrlPost w2 v2) := fun he =>
  wsEqrTrans (wsEqrSym (wsEqrCtrlPost w1 v1)) (wsEqrTrans he (wsEqrCtrlPost w2 v2))

theorem wsEqrResSetCong (w1 w2 : Wstate) (r1 r2 : Option Wresv) :
    wsEqr w1 w2 → wsEqr (wsResSet w1 r1) (wsResSet w2 r2) := fun he =>
  wsEqrTrans (wsEqrSym (wsEqrResSet w1 r1)) (wsEqrTrans he (wsEqrResSet w2 r2))

/-! ### The per-byte updates are congruences -/

theorem wsEqrLoadPostAt (w1 w2 : Wstate) (aq : Bool) (vpre : Nat) (a : Int) (t : Nat) :
    wsEqr w1 w2 → wsEqr (loadPostAt w1 aq vpre a t) (loadPostAt w2 aq vpre a t) := by
  rintro ⟨hc, h1, h2, h3, h4, h5, h6, h7, h8⟩
  have hfv : fwdView w1 aq a t = fwdView w2 aq a t := by simp only [fwdView, h6]
  refine ⟨fun b => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · by_cases hb : b = a
    · subst hb; rw [cohLoadPostAtEq, cohLoadPostAtEq, hc b, hfv]
    · rw [cohLoadPostAtNe _ _ _ _ _ _ hb, cohLoadPostAtNe _ _ _ _ _ _ hb]; exact hc b
  all_goals simp only [loadPostAt, h1, h2, h3, h4, h5, h6, h7, h8, hfv]

theorem wsEqrStorePost (w1 w2 : Wstate) (rl : Bool) (a : Int) (t : Nat) :
    wsEqr w1 w2 → wsEqr (storePost w1 rl a t) (storePost w2 rl a t) := by
  rintro ⟨hc, h1, h2, h3, h4, h5, h6, h7, h8⟩
  refine ⟨fun b => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · by_cases hb : b = a
    · subst hb; rw [cohStorePostEq, cohStorePostEq, hc b]
    · rw [cohStorePostNe _ _ _ _ _ hb, cohStorePostNe _ _ _ _ _ hb]; exact hc b
  all_goals simp only [storePost, h1, h2, h3, h4, h5, h6, h7, h8]

theorem wsEqrFencePost (w1 w2 : Wstate) (pr pw sr sw : Bool) :
    wsEqr w1 w2 → wsEqr (fencePost w1 pr pw sr sw) (fencePost w2 pr pw sr sw) := by
  rintro ⟨hc, h1, h2, h3, h4, h5, h6, h7, h8⟩
  refine ⟨fun b => hc b, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [fencePost, h1, h2, h3, h4, h5, h6, h7, h8]

/-! ### ... hence so are the byte folds and the run-level wrappers -/

theorem wsEqrLoadFold (aq : Bool) (vpre : Nat) (ats : List (Int × Nat)) (w1 w2 : Wstate) :
    wsEqr w1 w2 →
    wsEqr (ats.foldl (fun w at_ => loadPostAt w aq vpre at_.1 at_.2) w1)
          (ats.foldl (fun w at_ => loadPostAt w aq vpre at_.1 at_.2) w2) := by
  induction ats generalizing w1 w2 with
  | nil => exact id
  | cons x ats ih => intro he; exact ih _ _ (wsEqrLoadPostAt _ _ _ _ _ _ he)

theorem wsEqrLoadPostBytes (w1 w2 : Wstate) (aq : Bool) (ats : List (Int × Nat)) :
    wsEqr w1 w2 → wsEqr (loadPostBytes w1 aq ats) (loadPostBytes w2 aq ats) := by
  intro he
  have hv : loadVpre w1 aq = loadVpre w2 aq := by
    simp only [loadVpre, wsEqrVrNew _ _ he, wsEqrVRel _ _ he]
  unfold loadPostBytes
  rw [hv]
  exact wsEqrLoadFold _ _ _ _ _ he

theorem wsEqrStoreFold (rl : Bool) (t : Nat) (as_ : List Int) (w1 w2 : Wstate) :
    wsEqr w1 w2 →
    wsEqr (as_.foldl (fun w a => storePost w rl a t) w1)
          (as_.foldl (fun w a => storePost w rl a t) w2) := by
  induction as_ generalizing w1 w2 with
  | nil => exact id
  | cons x as_ ih => intro he; exact ih _ _ (wsEqrStorePost _ _ _ _ _ he)

theorem wsEqrStorePostBytes (w1 w2 : Wstate) (rl : Bool) (as_ : List Int) (t : Nat) :
    wsEqr w1 w2 → wsEqr (storePostBytes w1 rl as_ t) (storePostBytes w2 rl as_ t) :=
  fun he => wsEqrStoreFold rl t as_ w1 w2 he

/-- THE THREE RUN-LEVEL SHAPES THE REALIZATION USES: the AXIOMATIC
(dependency-free) post-state on the left, the MACHINE one on the right, at
ARBITRARY operand views.  There is deliberately no such lemma for the FUSED
`LRmw` (see the Rocq comment: D-2r's recorded residue). -/
theorem wsEqrLoadPostRun (w1 w2 : Wstate) (aq : Bool) (base : Int) (ts : List Nat) :
    wsEqr w1 w2 → wsEqr (loadPostRun w1 aq base ts) (loadPostRun w2 aq base ts) := by
  intro he
  unfold loadPostRun
  exact wsEqrCtrlCong _ _ _ _ (wsEqrLoadPostBytes _ _ _ _ he)

theorem wsEqrStorePostRunD (w1 w2 : Wstate) (rl : Bool) (vaddr vdata : Nat) (base : Int)
    (n t : Nat) :
    wsEqr w1 w2 →
    wsEqr (storePostRun w1 rl base n t) (storePostRunD w2 rl vaddr vdata base n t) := by
  intro he
  unfold storePostRun storePostRunD
  rw [storePostBytesDVf]
  exact wsEqrCtrlCong _ _ _ _ (wsEqrStorePostBytes _ _ _ _ _ he)

theorem wsEqrExloadPostRunD (w1 w2 : Wstate) (aq : Bool) (vaddr : Nat) (base : Int)
    (ts : List Nat) :
    wsEqr w1 w2 → wsEqr (loadPostRun w1 aq base ts) (exloadPostRunD w2 aq vaddr base ts) := by
  intro he
  unfold exloadPostRunD
  refine wsEqrTrans ?_ (wsEqrResSet _ _)
  unfold loadPostRun
  exact wsEqrCtrlCong _ _ _ _ (wsEqrLoadPostBytes _ _ _ _ he)

/-! ### ADMISSIBILITY TRANSFERS -/

theorem wsEqrReadable (img : Image) (log : List Wmsg) (w1 w2 : Wstate) (vpre : Nat) (a : Int)
    (t : Nat) : wsEqr w1 w2 → readable img log w1 vpre a t → readable img log w2 vpre a t := by
  rintro he ⟨hs, hn⟩
  exact ⟨hs, by rw [← wsEqrCoh _ _ a he]; exact hn⟩

theorem wsEqrReadOk (img : Image) (log : List Wmsg) (w1 w2 : Wstate) (aq lat : Bool) (base : Int)
    (tvs : List (Nat × BitVec 8)) :
    wsEqr w1 w2 → readOk img log w1 aq lat base tvs → readOk img log w2 aq lat base tvs := by
  intro he hr j t v hj
  obtain ⟨h1, h2, h3⟩ := hr j t v hj
  have hv : loadVpreD w1 aq 0 = loadVpreD w2 aq 0 := by
    simp only [loadVpreD, loadVpre, wsEqrVrNew _ _ he, wsEqrVRel _ _ he]
  refine ⟨h1, ?_, h3⟩
  rw [← hv]
  exact wsEqrReadable _ _ _ _ _ _ _ he h2

/-- (Lean-only) The axiomatic read check transfers along `wsEqr` too. -/
theorem wsEqrRdOk (img : Image) (log : List Wmsg) (w1 w2 : Wstate) (aq : Bool) (base : Int)
    (ts : List Nat) (vs : List (BitVec 8)) :
    wsEqr w1 w2 → rdOk img log w1 aq base ts vs → rdOk img log w2 aq base ts vs := by
  rintro he ⟨hl, hall⟩
  refine ⟨hl, fun j t v ht hv => ?_⟩
  obtain ⟨h1, h2⟩ := hall j t v ht hv
  have hvp : loadVpre w1 aq = loadVpre w2 aq := by
    simp only [loadVpre, wsEqrVrNew _ _ he, wsEqrVRel _ _ he]
  exact ⟨h1, by rw [← hvp]; exact wsEqrReadable _ _ _ _ _ _ _ he h2⟩

/-! ### (Lean-only, O2) When a fetch-as-load is `wsEqr`-harmless

A plain (`aq = false`) load at `(a, t)` with pre-view `vpre` moves, among the
components `wsEqr` compares, only `coh` at `a` (to `max (coh a) (max vpost t)`)
and `wVrOld` (to `max wVrOld vpost`), `vpost = max vpre (fwdView ws false a t)`.
So it is `wsEqr`-inert exactly when both are already at or above. -/

theorem wsEqrLoadPostAtSelf (ws : Wstate) (vpre : Nat) (a : Int) (t : Nat) :
    max vpre (fwdView ws false a t) ≤ ws.wVrOld →
    max (max vpre (fwdView ws false a t)) t ≤ coh ws a →
    wsEqr (loadPostAt ws false vpre a t) ws := by
  intro h1 h2
  refine ⟨fun b => ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · by_cases hb : b = a
    · subst hb; rw [cohLoadPostAtEq]; omega
    · exact cohLoadPostAtNe _ _ _ _ _ _ hb
  · show max ws.wVrOld (max vpre (fwdView ws false a t)) = ws.wVrOld
    omega

theorem wsEqrLoadFoldSelf (vpre : Nat) (ats : List (Int × Nat)) :
    ∀ ws : Wstate,
    (∀ p ∈ ats, max vpre (fwdView ws false p.1 p.2) ≤ ws.wVrOld ∧
      max (max vpre (fwdView ws false p.1 p.2)) p.2 ≤ coh ws p.1) →
    wsEqr (ats.foldl (fun w at_ => loadPostAt w false vpre at_.1 at_.2) ws) ws := by
  induction ats with
  | nil => intro ws _; exact wsEqrRefl ws
  | cons x ats ih =>
    intro ws h
    obtain ⟨hx1, hx2⟩ := h x List.mem_cons_self
    have he1 := wsEqrLoadPostAtSelf ws vpre x.1 x.2 hx1 hx2
    refine wsEqrTrans (ih _ (fun p hp => ?_)) he1
    have hfv : fwdView (loadPostAt ws false vpre x.1 x.2) false p.1 p.2 = fwdView ws false p.1 p.2 :=
      rfl
    obtain ⟨hp1, hp2⟩ := h p (List.mem_cons_of_mem _ hp)
    rw [hfv, wsEqrVrOld _ _ he1, wsEqrCoh _ _ _ he1]
    exact ⟨hp1, hp2⟩

/-- The run-level form: the harmlessness premise of the fetch projection, in
field terms. -/
theorem wsEqrLoadPostRunSelf (ws : Wstate) (base : Int) (ts : List Nat) :
    (∀ p ∈ loadRunAts base ts, max (loadVpre ws false) (fwdView ws false p.1 p.2) ≤ ws.wVrOld ∧
      max (max (loadVpre ws false) (fwdView ws false p.1 p.2)) p.2 ≤ coh ws p.1) →
    wsEqr (loadPostRun ws false base ts) ws := by
  intro h
  unfold loadPostRun loadPostBytes
  exact wsEqrTrans (wsEqrSym (wsEqrCtrlPost _ _)) (wsEqrLoadFoldSelf _ _ ws h)

/-- NON-VACUITY: a fresh agent's one-byte fetch of timestamp 0 is harmless. -/
theorem wsEqrLoadPostRunInit (base : Int) : wsEqr (loadPostRun wsInit false base [0]) wsInit := by
  apply wsEqrLoadPostRunSelf
  intro p hp
  have hp' : p = (base + ((0 : Nat) : Int), 0) := by
    simpa [loadRunAts] using hp
  subst hp'
  rw [fwdViewEmpty _ _ _ _ rfl, cohInit]
  simp [loadVpre, wsInit]

/-- THE CLASS FUNCTION'S T1-D OBLIGATION: a class function may not read a
component `wsEqr` leaves unrelated (an INSTANCE-DISCHARGED OBLIGATION). -/
def pclsEqr {P : Type} (clsf : P → Wlabel → Wstate → WmClass) : Prop :=
  ∀ p l w1 w2, wsEqr w1 w2 → clsf p l w1 = clsf p l w2

/-! ## The bridge -/

section bridge

variable {P D : Type}
variable (pstep : P → D → Wlabel → P → D → Prop)

-- THE MESSAGE CLASS, PINNED AT FULFIL TIME (G6a): `pcls p l ws` is the class
-- the machine stamps on the message a store/rmw labelled `l` appends, read at
-- the FULFILLING agent's own pre-step program state `p` and `Wstate` `ws`.
-- See the Rocq section comment for why the program state is an argument, why
-- the pinning is at fulfil and not at promise, why hardware containment is
-- preserved, and why only the promise-free fragment is pinned.
variable (pcls : P → Wlabel → Wstate → WmClass)

/-! ### (A) The promise-free fragment -/

/-- Five arms mirroring `mstep`'s four plus the silent step; the store and rmw
arms are FUSED (the message is appended at the fresh top `log.length + 1` and
consumed in the same step); the twins `PFDev`, the three dependency-only arms
(D2) and the two halves of the RMW split (S2). -/
inductive wpPfStep (i : Nat) : Wlabel → Wpcfg P D → Wpcfg P D → Prop
  | PFSilent (cfg : Wpcfg P D) (ag : Wpagent P) (st' : P) (d' : D) :
      cfg.pcAgs[i]? = some ag →
      pstep ag.paSt cfg.pcDev .LSilent st' d' →
      wpPfStep i .LSilent cfg
        ⟨cfg.pcImg, cfg.pcLog, d', cfg.pcAgs.set i ⟨st', ag.paWs, ag.paProm⟩⟩
  | PFLoad (cfg : Wpcfg P D) (ag : Wpagent P) (aq lat : Bool) (base : Int)
      (tvs : List (Nat × BitVec 8)) (asrc : List Dsrc) (st' : P) (d' : D) :
      cfg.pcAgs[i]? = some ag →
      pstep ag.paSt cfg.pcDev (.LLoad aq lat base tvs asrc) st' d' →
      readOkD cfg.pcImg cfg.pcLog ag.paWs aq lat base tvs (srcsView ag.paWs asrc) →
      wpPfStep i (.LLoad aq lat base tvs asrc) cfg
        ⟨cfg.pcImg, cfg.pcLog, d',
         cfg.pcAgs.set i ⟨st',
           loadPostRunD ag.paWs aq (srcsView ag.paWs asrc) base (tvs.map Prod.fst),
           ag.paProm⟩⟩
  | PFStore (cfg : Wpcfg P D) (ag : Wpagent P) (rl : Bool) (base : Int)
      (data : List (BitVec 8)) (asrc vsrc : List Dsrc) (k : WmClass) (st' : P) (d' : D) :
      cfg.pcAgs[i]? = some ag →
      pstep ag.paSt cfg.pcDev (.LStore rl base data asrc vsrc) st' d' →
      data ≠ [] →
      k = pcls ag.paSt (.LStore rl base data asrc vsrc) ag.paWs →
      wpPfStep i (.LStore rl base data asrc vsrc) cfg
        ⟨cfg.pcImg, cfg.pcLog ++ [⟨base, data, some i, k⟩], d',
         cfg.pcAgs.set i ⟨st',
           storePostRunD ag.paWs rl (srcsView ag.paWs asrc) (srcsView ag.paWs vsrc)
             base data.length (cfg.pcLog.length + 1),
           ag.paProm⟩⟩
  | PFRmw (cfg : Wpcfg P D) (ag : Wpagent P) (aq rl : Bool) (base : Int)
      (tvs : List (Nat × BitVec 8)) (data : List (BitVec 8)) (asrc vsrc : List Dsrc)
      (k : WmClass) (st' : P) (d' : D) :
      cfg.pcAgs[i]? = some ag →
      pstep ag.paSt cfg.pcDev (.LRmw aq rl base tvs data asrc vsrc) st' d' →
      data ≠ [] →
      tvs.length = data.length →
      -- D-2r: the 0 floor, mirroring `wpstep.WPRmw`.
      readOk cfg.pcImg cfg.pcLog ag.paWs aq false base tvs →
      exclOk cfg.pcLog i base tvs (cfg.pcLog.length + 1) →
      k = pcls ag.paSt (.LRmw aq rl base tvs data asrc vsrc) ag.paWs →
      wpPfStep i (.LRmw aq rl base tvs data asrc vsrc) cfg
        ⟨cfg.pcImg, cfg.pcLog ++ [⟨base, data, some i, k⟩], d',
         cfg.pcAgs.set i ⟨st',
           storePostRunD
             (loadPostRunD ag.paWs aq (srcsView ag.paWs asrc) base (tvs.map Prod.fst))
             rl (srcsView ag.paWs asrc) (srcsView ag.paWs vsrc)
             base data.length (cfg.pcLog.length + 1),
           ag.paProm⟩⟩
  | PFFence (cfg : Wpcfg P D) (ag : Wpagent P) (pr pw sr sw : Bool) (st' : P) (d' : D) :
      cfg.pcAgs[i]? = some ag →
      pstep ag.paSt cfg.pcDev (.LFence pr pw sr sw) st' d' →
      wpPfStep i (.LFence pr pw sr sw) cfg
        ⟨cfg.pcImg, cfg.pcLog, d',
         cfg.pcAgs.set i ⟨st', fencePost ag.paWs pr pw sr sw, ag.paProm⟩⟩
  | PFDev (cfg : Wpcfg P D) (ag : Wpagent P) (st' : P) (d' : D) :
      cfg.pcAgs[i]? = some ag →
      pstep ag.paSt cfg.pcDev .LDev st' d' →
      wpPfStep i .LDev cfg
        ⟨cfg.pcImg, cfg.pcLog, d', cfg.pcAgs.set i ⟨st', ag.paWs, ag.paProm⟩⟩
  | PFRegW (cfg : Wpcfg P D) (ag : Wpagent P) (rd : Nat) (srcs : List Dsrc) (st' : P) (d' : D) :
      cfg.pcAgs[i]? = some ag →
      pstep ag.paSt cfg.pcDev (.LRegW rd srcs) st' d' →
      wpPfStep i (.LRegW rd srcs) cfg
        ⟨cfg.pcImg, cfg.pcLog, d',
         cfg.pcAgs.set i ⟨st', regwPost ag.paWs rd (srcsView ag.paWs srcs), ag.paProm⟩⟩
  | PFCtrl (cfg : Wpcfg P D) (ag : Wpagent P) (srcs : List Dsrc) (st' : P) (d' : D) :
      cfg.pcAgs[i]? = some ag →
      pstep ag.paSt cfg.pcDev (.LCtrl srcs) st' d' →
      wpPfStep i (.LCtrl srcs) cfg
        ⟨cfg.pcImg, cfg.pcLog, d',
         cfg.pcAgs.set i ⟨st', ctrlPost ag.paWs (srcsView ag.paWs srcs), ag.paProm⟩⟩
  | PFInstr (cfg : Wpcfg P D) (ag : Wpagent P) (st' : P) (d' : D) :
      cfg.pcAgs[i]? = some ag →
      pstep ag.paSt cfg.pcDev .LInstr st' d' →
      wpPfStep i .LInstr cfg
        ⟨cfg.pcImg, cfg.pcLog, d', cfg.pcAgs.set i ⟨st', instrPost ag.paWs, ag.paProm⟩⟩
  | PFExLoad (cfg : Wpcfg P D) (ag : Wpagent P) (aq : Bool) (base : Int)
      (tvs : List (Nat × BitVec 8)) (asrc : List Dsrc) (st' : P) (d' : D) :
      cfg.pcAgs[i]? = some ag →
      pstep ag.paSt cfg.pcDev (.LExLoad aq base tvs asrc) st' d' →
      -- D-2r: the 0 floor, mirroring `wpstep.WPExLoad`.
      readOk cfg.pcImg cfg.pcLog ag.paWs aq false base tvs →
      wpPfStep i (.LExLoad aq base tvs asrc) cfg
        ⟨cfg.pcImg, cfg.pcLog, d',
         cfg.pcAgs.set i ⟨st',
           exloadPostRunD ag.paWs aq (srcsView ag.paWs asrc) base (tvs.map Prod.fst),
           ag.paProm⟩⟩
  | PFExStore (cfg : Wpcfg P D) (ag : Wpagent P) (rl : Bool) (base : Int)
      (data : List (BitVec 8)) (asrc vsrc : List Dsrc) (k : WmClass) (R : Wresv) (st' : P)
      (d' : D) :
      cfg.pcAgs[i]? = some ag →
      pstep ag.paSt cfg.pcDev (.LExStore rl base data asrc vsrc) st' d' →
      data ≠ [] →
      ag.paWs.wRes = some R →
      R.rvBase = base →
      R.rvTs.length = data.length →
      exclOkTs cfg.pcLog i base R.rvTs (cfg.pcLog.length + 1) →
      k = pcls ag.paSt (.LExStore rl base data asrc vsrc) ag.paWs →
      wpPfStep i (.LExStore rl base data asrc vsrc) cfg
        ⟨cfg.pcImg, cfg.pcLog ++ [⟨base, data, some i, k⟩], d',
         cfg.pcAgs.set i ⟨st',
           storePostRunD ag.paWs rl (srcsView ag.paWs asrc) (srcsView ag.paWs vsrc)
             base data.length (cfg.pcLog.length + 1),
           ag.paProm⟩⟩
  /-- O2 (Lean-only, deviation 6): the twin of `wpstep.WPIFetch` — an i-cache read at
  instruction view 0, state and log unchanged. -/
  | PFIFetch (cfg : Wpcfg P D) (ag : Wpagent P) (base : Int) (tvs : List (Nat × BitVec 8))
      (st' : P) (d' : D) :
      cfg.pcAgs[i]? = some ag →
      pstep ag.paSt cfg.pcDev (.LIFetch base tvs) st' d' →
      ifetchOk cfg.pcImg cfg.pcLog 0 base tvs →
      wpPfStep i (.LIFetch base tvs) cfg
        ⟨cfg.pcImg, cfg.pcLog, d', cfg.pcAgs.set i ⟨st', ag.paWs, ag.paProm⟩⟩

def wpPfRun (c c' : Wpcfg P D) : Prop := ∃ i l, wpPfStep pstep pcls i l c c'

/-! ### A pf step is one or two `wpstep`s -/

theorem wpPfStepRtcWpstep (i : Nat) (l : Wlabel) (c c' : Wpcfg P D) :
    cfgWf c → noPromises c → wpPfStep pstep pcls i l c c' → rtc (wpstep pstep) c c' := by
  intro hwf hnp hstep
  cases hstep with
  | PFSilent c ag st' d' hlk hps => exact rtc_once (wpstep.WPSilent c i ag st' d' hlk hps)
  | PFLoad c ag aq lat base tvs asrc st' d' hlk hps hr =>
    exact rtc_once (wpstep.WPLoad c i ag aq lat base tvs asrc st' d' hlk hps hr)
  | PFStore c ag rl base data asrc vsrc k st' d' hlk hps hnn _ =>
    exact wpstepStoreNow pstep c i ag rl base data asrc vsrc k st' d' hlk hps hnn
      (hwf i ag hlk).1 (by rw [hnp i ag hlk]; set_solver)
  | PFRmw c ag aq rl base tvs data asrc vsrc k st' d' hlk hps hnn hlen hr he _ =>
    exact wpstepRmwNow pstep c i ag aq rl base tvs data asrc vsrc k st' d' hlk hps hnn hlen
      (hwf i ag hlk).1 (by rw [hnp i ag hlk]; set_solver) hr he
  | PFFence c ag pr pw sr sw st' d' hlk hps =>
    exact rtc_once (wpstep.WPFence c i ag pr pw sr sw st' d' hlk hps)
  | PFDev c ag st' d' hlk hps => exact rtc_once (wpstep.WPDev c i ag st' d' hlk hps)
  | PFRegW c ag rd srcs st' d' hlk hps => exact rtc_once (wpstep.WPRegW c i ag rd srcs st' d' hlk hps)
  | PFCtrl c ag srcs st' d' hlk hps => exact rtc_once (wpstep.WPCtrl c i ag srcs st' d' hlk hps)
  | PFInstr c ag st' d' hlk hps => exact rtc_once (wpstep.WPInstr c i ag st' d' hlk hps)
  | PFExLoad c ag aq base tvs asrc st' d' hlk hps hr =>
    exact rtc_once (wpstep.WPExLoad c i ag aq base tvs asrc st' d' hlk hps hr)
  | PFExStore c ag rl base data asrc vsrc k R st' d' hlk hps hnn hres hrb hrlen he _ =>
    exact wpstepExstoreNow pstep c i ag rl base data asrc vsrc k R st' d' hlk hps hnn
      (hwf i ag hlk).1 (by rw [hnp i ag hlk]; set_solver) hres hrb hrlen he
  | PFIFetch c ag base tvs st' d' hlk hps hif =>
    exact rtc_once (wpstep.WPIFetch c i ag base tvs st' d' hlk hps hif)

theorem noPromisesUpd (c : Wpcfg P D) (i : Nat) (ag : Wpagent P) (st' : P) (w : Wstate)
    (lg : List Wmsg) (dv : D) :
    noPromises c → c.pcAgs[i]? = some ag →
    noPromises (⟨c.pcImg, lg, dv, c.pcAgs.set i ⟨st', w, ag.paProm⟩⟩ : Wpcfg P D) := by
  intro hnp hlk j agj hj
  rcases lookupSetCases hj with ⟨rfl, rfl⟩ | ⟨_, hj⟩
  · exact hnp _ ag hlk
  · exact hnp j agj hj

theorem wpPfStepNoPromises (i : Nat) (l : Wlabel) (c c' : Wpcfg P D) :
    noPromises c → wpPfStep pstep pcls i l c c' → noPromises c' := by
  intro hnp hstep
  cases hstep <;> (refine noPromisesUpd _ _ _ _ _ _ _ hnp ?_; assumption)

theorem wpPfRunRtcWpstep (c c' : Wpcfg P D) :
    cfgWf c → noPromises c → rtc (wpPfRun pstep pcls) c c' →
    rtc (wpstep pstep) c c' ∧ cfgWf c' ∧ noPromises c' := by
  intro hwf hnp hrun
  induction hrun with
  | refl => exact ⟨rtc_refl _, hwf, hnp⟩
  | tail _ hs ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    obtain ⟨i, l, hs⟩ := hs
    have hyz := wpPfStepRtcWpstep pstep pcls i l _ _ h2 h3 hs
    exact ⟨rtc_transitive h1 hyz, cfgWfReach pstep _ _ h2 hyz,
      wpPfStepNoPromises pstep pcls i l _ _ h3 hs⟩

/-- SANITY: a pf run from an initial configuration is a `wpBehavior` of the
FULL machine. -/
theorem wpPfBehavior (img : Image) (d0 : D) (ps : List P) (c : Wpcfg P D) :
    rtc (wpPfRun pstep pcls) (wpInit img d0 ps) c → wpBehavior pstep img d0 ps c := by
  intro hrun
  have hnp : noPromises (wpInit img d0 ps : Wpcfg P D) := by
    intro i ag hlk
    simp only [wpInit, List.getElem?_map] at hlk
    cases hp : ps[i]? with
    | none => rw [hp] at hlk; cases hlk
    | some p => rw [hp] at hlk; injection hlk with hlk; subst hlk; rfl
  obtain ⟨h1, _, h3⟩ := wpPfRunRtcWpstep pstep pcls _ _ (cfgWfInit img d0 ps) hnp hrun
  exact ⟨h1, h3⟩

/-! ### (B) The projections -/

/-- `LSilent`, `LDev` and the dependency-only labels have no image (the
axiomatic execution skips them); `k` is the class the pf step's append
stamped; the split labels project to the axiomatic PLAIN load / store. -/
def projLbl (k : WmClass) (l : Wlabel) : Option Lbl :=
  match l with
  | .LSilent => none
  | .LLoad aq _ base tvs _ => some (.LLoad aq base (tvs.map Prod.fst) (tvs.map Prod.snd))
  | .LStore rl base data _ _ => some (.LStore rl base data k)
  | .LRmw aq rl base tvs data _ _ =>
      some (.LRmw aq rl base (tvs.map Prod.fst) (tvs.map Prod.snd) data k)
  | .LFence pr pw sr sw => some (.LFence pr pw sr sw)
  | .LDev => none
  | .LRegW _ _ => none
  | .LCtrl _ => none
  | .LInstr => none
  | .LExLoad aq base tvs _ => some (.LLoad aq base (tvs.map Prod.fst) (tvs.map Prod.snd))
  | .LExStore rl base data _ _ => some (.LStore rl base data k)
  | .LIFetch base tvs => some (.LLoad false base (tvs.map Prod.fst) (tvs.map Prod.snd))

/-- The state projection, RELATIONALLY: same image, same log, and the
`Mstate`'s view function agrees with the agent list where it is defined. -/
def cfgMatch (c : Wpcfg P D) (σ : Mstate) : Prop :=
  σ.msImg = c.pcImg ∧ σ.msLog = c.pcLog ∧
  ∀ i ag, c.pcAgs[i]? = some ag → σ.msWs i = ag.paWs

/-- THE T1-D WEAKENING OF `cfgMatch`: per-agent `wsEqr` instead of equality. -/
def cfgMatchd (c : Wpcfg P D) (σ : Mstate) : Prop :=
  σ.msImg = c.pcImg ∧ σ.msLog = c.pcLog ∧
  ∀ i ag, c.pcAgs[i]? = some ag → wsEqr (σ.msWs i) ag.paWs

theorem cfgMatchCfgMatchd (c : Wpcfg P D) (σ : Mstate) : cfgMatch c σ → cfgMatchd c σ := by
  rintro ⟨h1, h2, hf⟩
  exact ⟨h1, h2, fun i ag hlk => by rw [hf i ag hlk]; exact wsEqrRefl _⟩

theorem cfgMatchdImg (c : Wpcfg P D) (σ : Mstate) : cfgMatchd c σ → σ.msImg = c.pcImg :=
  fun h => h.1

theorem cfgMatchdLog (c : Wpcfg P D) (σ : Mstate) : cfgMatchd c σ → σ.msLog = c.pcLog :=
  fun h => h.2.1

theorem cfgMatchdWs (c : Wpcfg P D) (σ : Mstate) (i : Nat) (ag : Wpagent P) :
    cfgMatchd c σ → c.pcAgs[i]? = some ag → wsEqr (σ.msWs i) ag.paWs :=
  fun h => h.2.2 i ag

/-- `cfgMatchUpdGen`'s analogue. -/
theorem cfgMatchdUpdGen (img : Image) (lg : List Wmsg) (dv : D) (ags : List (Wpagent P))
    (i : Nat) (ag : Wpagent P) (st' : P) (w : Wstate) (pr : GSet Nat) (f g : Nat → Wstate) :
    (∀ j agj, ags[j]? = some agj → wsEqr (f j) agj.paWs) →
    ags[i]? = some ag →
    wsEqr (g i) w →
    (∀ j, j ≠ i → g j = f j) →
    cfgMatchd (⟨img, lg, dv, ags.set i ⟨st', w, pr⟩⟩ : Wpcfg P D) ⟨img, lg, g⟩ := by
  intro hf _ hgi hgne
  refine ⟨rfl, rfl, fun j agj hj => ?_⟩
  rcases lookupSetCases hj with ⟨rfl, rfl⟩ | ⟨hne, hj⟩
  · exact hgi
  · show wsEqr (g j) agj.paWs
    rw [hgne j hne]; exact hf j agj hj

/-- THE CONFIGURATION-SIDE MOVE THE ADMINISTRATIVE STAR MAKES. -/
def cfgEqr (c c' : Wpcfg P D) : Prop :=
  c'.pcImg = c.pcImg ∧ c'.pcLog = c.pcLog ∧
  ∀ (j : Nat) (agj' : Wpagent P), c'.pcAgs[j]? = some agj' →
    ∃ agj : Wpagent P, c.pcAgs[j]? = some agj ∧ wsEqr agj.paWs agj'.paWs

theorem cfgEqrRefl (c : Wpcfg P D) : cfgEqr c c :=
  ⟨rfl, rfl, fun _ agj' hj => ⟨agj', hj, wsEqrRefl _⟩⟩

theorem cfgEqrTrans (c1 c2 c3 : Wpcfg P D) : cfgEqr c1 c2 → cfgEqr c2 c3 → cfgEqr c1 c3 := by
  rintro ⟨hi, hl, ha⟩ ⟨hi', hl', ha'⟩
  refine ⟨hi'.trans hi, hl'.trans hl, fun j agj3 hj => ?_⟩
  obtain ⟨agj2, hj2, he2⟩ := ha' j agj3 hj
  obtain ⟨agj1, hj1, he1⟩ := ha j agj2 hj2
  exact ⟨agj1, hj1, wsEqrTrans he1 he2⟩

theorem cfgEqrMatchd (c c' : Wpcfg P D) (σ : Mstate) :
    cfgEqr c c' → cfgMatchd c σ → cfgMatchd c' σ := by
  rintro ⟨hi, hl, ha⟩ ⟨hmi, hml, hmw⟩
  refine ⟨hmi.trans hi.symm, hml.trans hl.symm, fun j agj' hj => ?_⟩
  obtain ⟨agj, hj0, he⟩ := ha j agj' hj
  exact wsEqrTrans (hmw j agj hj0) he

/-- The functional projection, for consumers who want one: it matches. -/
def projWs (c : Wpcfg P D) : Nat → Wstate :=
  fun i => match c.pcAgs[i]? with
    | some ag => ag.paWs
    | none => wsInit

def projSt (c : Wpcfg P D) : Mstate := ⟨c.pcImg, c.pcLog, projWs c⟩

theorem cfgMatchProj (c : Wpcfg P D) : cfgMatch c (projSt c) :=
  ⟨rfl, rfl, fun i ag hlk => by simp only [projSt, projWs, hlk]⟩

theorem cfgMatchLog (c : Wpcfg P D) (σ : Mstate) : cfgMatch c σ → σ.msLog = c.pcLog :=
  fun h => h.2.1

theorem cfgMatchUpdGen (img : Image) (lg : List Wmsg) (dv : D) (ags : List (Wpagent P))
    (i : Nat) (ag : Wpagent P) (st' : P) (w : Wstate) (pr : GSet Nat) (f g : Nat → Wstate) :
    (∀ j agj, ags[j]? = some agj → f j = agj.paWs) →
    ags[i]? = some ag →
    g i = w →
    (∀ j, j ≠ i → g j = f j) →
    cfgMatch (⟨img, lg, dv, ags.set i ⟨st', w, pr⟩⟩ : Wpcfg P D) ⟨img, lg, g⟩ := by
  intro hf _ hgi hgne
  refine ⟨rfl, rfl, fun j agj hj => ?_⟩
  rcases lookupSetCases hj with ⟨rfl, rfl⟩ | ⟨hne, hj⟩
  · exact hgi
  · show g j = agj.paWs
    rw [hgne j hne]; exact hf j agj hj

/-- THE DEPENDENCY VIEW (and the `lat` pinning) IS DROPPED HERE, SOUNDLY:
`readable` is ANTI-monotone in the pre-view. -/
theorem readOkDRdOk (img : Image) (log : List Wmsg) (ws : Wstate) (aq lat : Bool) (base : Int)
    (tvs : List (Nat × BitVec 8)) (va : Nat) :
    readOkD img log ws aq lat base tvs va →
    rdOk img log ws aq base (tvs.map Prod.fst) (tvs.map Prod.snd) := by
  intro hr
  refine ⟨by simp, fun j t v ht hv => ?_⟩
  rw [List.getElem?_map] at ht hv
  cases htv : tvs[j]? with
  | none => rw [htv] at ht; cases ht
  | some p =>
    obtain ⟨t', v'⟩ := p
    rw [htv] at ht hv
    injection ht with ht
    injection hv with hv
    subst ht hv
    obtain ⟨h1, h2, _⟩ := hr j t' v' htv
    exact ⟨h1, readableAntiVpre _ _ _ _ _ _ _ (loadVpreLoadVpreD _ _ _) h2⟩

theorem readOkRdOk (img : Image) (log : List Wmsg) (ws : Wstate) (aq lat : Bool) (base : Int)
    (tvs : List (Nat × BitVec 8)) :
    readOk img log ws aq lat base tvs →
    rdOk img log ws aq base (tvs.map Prod.fst) (tvs.map Prod.snd) :=
  readOkDRdOk img log ws aq lat base tvs 0

/-! ### (C) `ownCoh` and the dovetail -/

/-- THE NEW CONFIGURATION INVARIANT: every message in the log is at or below its
OWN author's coherence floor for every byte it writes. -/
def ownCoh (c : Wpcfg P D) : Prop :=
  ∀ (p : Nat) (m : Wmsg) (i : Nat) (ag : Wpagent P) (a : Int),
    c.pcLog[p]? = some m → m.wmTid = some i →
    c.pcAgs[i]? = some ag → (msgByte m a).isSome →
    p + 1 ≤ coh ag.paWs a

theorem ownCohInit (img : Image) (d0 : D) (ps : List P) : ownCoh (wpInit img d0 ps : Wpcfg P D) := by
  intro p m i ag a hm
  simp [wpInit] at hm

/-- The frozen-log arms. -/
theorem ownCohUpd (c : Wpcfg P D) (i : Nat) (ag : Wpagent P) (st' : P) (w : Wstate)
    (pr : GSet Nat) (dv : D) :
    ownCoh c → c.pcAgs[i]? = some ag → wsLe ag.paWs w →
    ownCoh (⟨c.pcImg, c.pcLog, dv, c.pcAgs.set i ⟨st', w, pr⟩⟩ : Wpcfg P D) := by
  intro hoc hlk hle p m j agj a hm htid hj hb
  rcases lookupSetCases hj with ⟨rfl, rfl⟩ | ⟨_, hj⟩
  · exact Nat.le_trans (hoc p m _ ag a hm htid hlk hb) (wsLeCoh _ _ a hle)
  · exact hoc p m j agj a hm htid hj hb

/-- The appending arms. -/
theorem ownCohAppend (c : Wpcfg P D) (i : Nat) (ag : Wpagent P) (st' : P) (w : Wstate)
    (pr : GSet Nat) (base : Int) (data : List (BitVec 8)) (kc : WmClass) (dv : D) :
    ownCoh c → c.pcAgs[i]? = some ag → wsLe ag.paWs w →
    (∀ j : Nat, j < data.length → c.pcLog.length + 1 ≤ coh w (base + (j : Int))) →
    ownCoh (⟨c.pcImg, c.pcLog ++ [⟨base, data, some i, kc⟩], dv,
      c.pcAgs.set i ⟨st', w, pr⟩⟩ : Wpcfg P D) := by
  intro hoc hlk hle hnew p m j agj a hm htid hj hb
  by_cases hlt : p < c.pcLog.length
  · have hm' : c.pcLog[p]? = some m := by rw [← hm]; exact (lookup_app_l hlt).symm
    rcases lookupSetCases hj with ⟨rfl, rfl⟩ | ⟨_, hj⟩
    · exact Nat.le_trans (hoc p m _ ag a hm' htid hlk hb) (wsLeCoh _ _ a hle)
    · exact hoc p m j agj a hm' htid hj hb
  · have hp := lookup_lt_Some hm
    simp only [List.length_append, List.length_singleton] at hp
    have hpe : p = c.pcLog.length := by omega
    subst hpe
    rw [lookup_app_r (Nat.le_refl _), Nat.sub_self] at hm
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hm
    subst hm
    simp only [Option.some.injEq] at htid
    subst htid
    rcases lookupSetCases hj with ⟨_, rfl⟩ | ⟨hne, _⟩
    · obtain ⟨jb, hjb, rfl⟩ := msgByteRange _ _ hb
      exact hnew jb hjb
    · exact absurd rfl hne

theorem ownCohStep (i : Nat) (l : Wlabel) (c c' : Wpcfg P D) :
    ownCoh c → wpPfStep pstep pcls i l c c' → ownCoh c' := by
  intro hoc hstep
  cases hstep with
  | PFSilent c ag st' d' hlk _ => exact ownCohUpd c i ag st' _ _ d' hoc hlk (wsLeRefl _)
  | PFLoad c ag aq lat base tvs asrc st' d' hlk _ _ =>
    exact ownCohUpd c i ag st' _ _ d' hoc hlk (loadPostRunDLe _ _ _ _ _)
  | PFStore c ag rl base data asrc vsrc k st' d' hlk _ _ _ =>
    exact ownCohAppend c i ag st' _ _ base data k d' hoc hlk (storePostRunDLe _ _ _ _ _ _ _)
      (fun j hj => storePostRunDCoh _ _ _ _ _ _ _ j hj)
  | PFRmw c ag aq rl base tvs data asrc vsrc k st' d' hlk _ _ _ _ _ _ =>
    exact ownCohAppend c i ag st' _ _ base data k d' hoc hlk
      (wsLeTrans (loadPostRunDLe _ _ _ _ _) (storePostRunDLe _ _ _ _ _ _ _))
      (fun j hj => storePostRunDCoh _ _ _ _ _ _ _ j hj)
  | PFFence c ag pr pw sr sw st' d' hlk _ =>
    exact ownCohUpd c i ag st' _ _ d' hoc hlk (fencePostLe _ _ _ _ _)
  | PFDev c ag st' d' hlk _ => exact ownCohUpd c i ag st' _ _ d' hoc hlk (wsLeRefl _)
  | PFRegW c ag rd srcs st' d' hlk _ =>
    exact ownCohUpd c i ag st' _ _ d' hoc hlk (regwPostLe _ _ _)
  | PFCtrl c ag srcs st' d' hlk _ =>
    exact ownCohUpd c i ag st' _ _ d' hoc hlk (ctrlPostLe _ _)
  | PFInstr c ag st' d' hlk _ => exact ownCohUpd c i ag st' _ _ d' hoc hlk (instrPostLe _)
  | PFExLoad c ag aq base tvs asrc st' d' hlk _ _ =>
    exact ownCohUpd c i ag st' _ _ d' hoc hlk (exloadPostRunDLe _ _ _ _ _)
  | PFExStore c ag rl base data asrc vsrc k R st' d' hlk _ _ _ _ _ _ _ =>
    exact ownCohAppend c i ag st' _ _ base data k d' hoc hlk (storePostRunDLe _ _ _ _ _ _ _)
      (fun j hj => storePostRunDCoh _ _ _ _ _ _ _ j hj)
  | PFIFetch c ag base tvs st' d' hlk _ _ => exact ownCohUpd c i ag st' _ _ d' hoc hlk (wsLeRefl _)

theorem ownCohRun (c c' : Wpcfg P D) : ownCoh c → rtc (wpPfRun pstep pcls) c c' → ownCoh c' := by
  intro hoc hrun
  induction hrun with
  | refl => exact hoc
  | tail _ hs ih =>
    obtain ⟨i, l, hs⟩ := hs
    exact ownCohStep pstep pcls i l _ _ ih hs

/-- THE DOVETAIL.  `readable` + `exclOk` + `ownCoh` ⊢ `rmwLatest`. -/
theorem pfRmwLatest (c : Wpcfg P D) (i : Nat) (ag : Wpagent P) (aq : Bool) (base : Int)
    (tvs : List (Nat × BitVec 8)) (va : Nat) :
    ownCoh c →
    c.pcAgs[i]? = some ag →
    readOkD c.pcImg c.pcLog ag.paWs aq false base tvs va →
    exclOk c.pcLog i base tvs (c.pcLog.length + 1) →
    rmwLatest c.pcImg c.pcLog base (tvs.map Prod.fst) := by
  intro hoc hlk hr he j t hj
  rw [List.getElem?_map] at hj
  cases htv : tvs[j]? with
  | none => rw [htv] at hj; cases hj
  | some p =>
    obtain ⟨t', v⟩ := p
    rw [htv] at hj
    injection hj with hj
    subst hj
    obtain ⟨_, ⟨hs, hnw⟩, _⟩ := hr j t' v htv
    refine ⟨hs, ?_⟩
    rintro ⟨t2, hlt, hle, m, hm, hbm⟩
    by_cases htid : m.wmTid = some i
    · -- the reader's OWN write: `ownCoh` puts it at or below `coh`
      apply hnw
      have hcoh := hoc (t2 - 1) m i ag (base + (j : Int)) hm htid hlk hbm
      exact ⟨t2, hlt, by omega, m, hm, hbm⟩
    · -- another agent's write: `exclOk` forbids it
      exact he j t' v htv ⟨t2, hlt, by omega, m, hm, hbm, htid⟩

/-! ### (D) The bridge

O2 / owner decision (B) (deviation 6): an i-cache FETCH (`LIFetch`) projects to
the axiomatic PLAIN load `LLoad false base ts vs`, under the per-step premise
`pfFetchLoadOk` — (i) every fetched byte is also READABLE as a plain load at
`loadVpre ws false` (`MStepLoad`'s `rdOk`; `ifetchOk` supplies the values but
not readability: a stale pre-`fence.i` fetch need not be readable), and (ii) the
load's post-state is `wsEqr`-harmless.  Because a fetch leaves the agent's
`Wstate` IDENTICAL while `MStepLoad` applies `loadPostRun`, the forward bridge
now tracks the T1-D weakening `cfgMatchd` (Rocq: `cfgMatch`). -/

/-- THE FETCH PROJECTION PREMISE at one step (Lean-only, deviation 6).  Vacuous
for every label but `LIFetch`. -/
def pfFetchLoadOk (c : Wpcfg P D) (i : Nat) (l : Wlabel) : Prop :=
  match l with
  | .LIFetch base tvs =>
      ∀ ag : Wpagent P, c.pcAgs[i]? = some ag →
        (∀ (j t : Nat) (v : BitVec 8), tvs[j]? = some (t, v) →
          readable c.pcImg c.pcLog ag.paWs (loadVpre ag.paWs false) (base + (j : Int)) t) ∧
        wsEqr (loadPostRun ag.paWs false base (tvs.map Prod.fst)) ag.paWs
  | _ => True

/-- NON-VACUITY of `pfFetchLoadOk`: a fresh agent fetching one image byte. -/
theorem pfFetchLoadOkInit (c : Wpcfg P D) (i : Nat) (base : Int) (v : BitVec 8) :
    (∀ ag, c.pcAgs[i]? = some ag → ag.paWs = wsInit) →
    logByte c.pcImg c.pcLog 0 base = some v →
    pfFetchLoadOk c i (.LIFetch base [(0, v)]) := by
  intro hini hv ag hlk
  rw [hini ag hlk]
  refine ⟨fun j t v' hj => ?_, wsEqrLoadPostRunInit base⟩
  cases j with
  | succ j => simp at hj
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hj
    obtain ⟨rfl, rfl⟩ := hj
    refine ⟨by simp [hv], ?_⟩
    rintro ⟨t', h1, h2, _⟩
    rw [cohInit] at h2
    simp only [loadVpre, wsInit] at h2
    simp at h2
    omega

/-- One pf step projects to one `mstep` (or, for the label-free arms, to
nothing at all).  THE DEPENDENCY-FREE PREMISE (D2, recorded residue) and the
`lbFused` GATE (lifted by A2): see the Rocq comments.  Deviation 6: the
`pfFetchLoadOk` premise, and `cfgMatchd` for `cfgMatch`. -/
theorem wpPfStepMstep (i : Nat) (l : Wlabel) (c c' : Wpcfg P D) (σ : Mstate) :
    lbDepfree l → lbFused l → pfFetchLoadOk c i l → ownCoh c → cfgMatchd c σ →
    wpPfStep pstep pcls i l c c' →
    ∃ k, match projLbl k l with
      | none => cfgMatchd c' σ
      | some lb => ∃ σ', mstep σ i lb σ' ∧ cfgMatchd c' σ' := by
  intro hdf hfu hfe hoc hm hstep
  obtain ⟨img, lg, f⟩ := σ
  obtain ⟨himg, hlg, hf⟩ := hm
  dsimp only at himg hlg hf
  subst himg hlg
  cases hstep with
  | PFSilent c ag st' d' hlk _ =>
    exact ⟨.WCplain,
      cfgMatchdUpdGen _ _ _ _ i ag st' ag.paWs ag.paProm f f hf hlk (hf i ag hlk) (fun _ _ => rfl)⟩
  | PFLoad c ag aq lat base tvs asrc st' d' hlk _ hr =>
    have hasrc : asrc = [] := hdf
    subst hasrc
    refine ⟨.WCplain, ?_⟩
    dsimp only [projLbl]
    refine ⟨_, mstep.MStepLoad aq base (tvs.map Prod.fst) (tvs.map Prod.snd) ?_, ?_⟩
    · dsimp only
      exact wsEqrRdOk _ _ _ _ _ _ _ _ (wsEqrSym (hf i ag hlk)) (readOkDRdOk _ _ _ _ _ _ _ _ hr)
    · dsimp only
      rw [srcsViewNil, loadPostRunD0]
      exact cfgMatchdUpdGen _ _ _ _ i ag st' _ _ f _ hf hlk
        (by rw [updWsEq]; exact wsEqrLoadPostRun _ _ _ _ _ (hf i ag hlk))
        (fun j hne => updWsNe _ _ _ _ hne)
  | PFStore c ag rl base data asrc vsrc k st' d' hlk _ hnn _ =>
    obtain ⟨rfl, rfl⟩ : asrc = [] ∧ vsrc = [] := hdf
    refine ⟨k, ?_⟩
    dsimp only [projLbl]
    refine ⟨_, mstep.MStepStore rl base data k hnn, ?_⟩
    dsimp only
    rw [srcsViewNil]
    exact cfgMatchdUpdGen _ _ _ _ i ag st' _ _ f _ hf hlk
      (by rw [updWsEq]; exact wsEqrStorePostRunD _ _ _ _ _ _ _ _ (hf i ag hlk))
      (fun j hne => updWsNe _ _ _ _ hne)
  | PFRmw c ag aq rl base tvs data asrc vsrc k st' d' hlk _ hnn hlen hr he _ =>
    obtain ⟨rfl, rfl⟩ : asrc = [] ∧ vsrc = [] := hdf
    refine ⟨k, ?_⟩
    dsimp only [projLbl]
    refine ⟨_, mstep.MStepRmw aq rl base (tvs.map Prod.fst) (tvs.map Prod.snd) data k hnn
      (by rw [List.length_map, hlen]) ?_ ?_, ?_⟩
    · dsimp only
      exact wsEqrRdOk _ _ _ _ _ _ _ _ (wsEqrSym (hf i ag hlk)) (readOkRdOk _ _ _ _ _ _ _ hr)
    · -- the dovetail supplies `rmwLatest`
      exact pfRmwLatest c i ag aq base tvs 0 hoc hlk hr he
    · dsimp only
      rw [srcsViewNil, loadPostRunD0]
      exact cfgMatchdUpdGen _ _ _ _ i ag st' _ _ f _ hf hlk
        (by
          rw [updWsEq]
          exact wsEqrStorePostRunD _ _ _ _ _ _ _ _
            (wsEqrLoadPostRun _ _ _ _ _ (hf i ag hlk)))
        (fun j hne => updWsNe _ _ _ _ hne)
  | PFFence c ag pr pw sr sw st' d' hlk _ =>
    refine ⟨.WCplain, ?_⟩
    dsimp only [projLbl]
    refine ⟨_, mstep.MStepFence pr pw sr sw, ?_⟩
    dsimp only
    exact cfgMatchdUpdGen _ _ _ _ i ag st' _ _ f _ hf hlk
      (by rw [updWsEq]; exact wsEqrFencePost _ _ _ _ _ _ (hf i ag hlk))
      (fun j hne => updWsNe _ _ _ _ hne)
  | PFDev c ag st' d' hlk _ =>
    exact ⟨.WCplain,
      cfgMatchdUpdGen _ _ _ _ i ag st' ag.paWs ag.paProm f f hf hlk (hf i ag hlk) (fun _ _ => rfl)⟩
  -- the three dependency-only arms are excluded outright
  | PFRegW => exact (hdf : False).elim
  | PFCtrl => exact (hdf : False).elim
  | PFInstr => exact (hdf : False).elim
  -- the two split arms are excluded by `lbFused`
  | PFExLoad => exact (hfu : False).elim
  | PFExStore => exact (hfu : False).elim
  -- O2 (deviation 6): the fetch, as a plain load, under `pfFetchLoadOk`
  | PFIFetch c ag base tvs st' d' hlk _ hif =>
    obtain ⟨hrd, hharm⟩ := hfe ag hlk
    refine ⟨.WCplain, ?_⟩
    dsimp only [projLbl]
    refine ⟨_, mstep.MStepLoad false base (tvs.map Prod.fst) (tvs.map Prod.snd) ?_, ?_⟩
    · dsimp only
      refine wsEqrRdOk _ _ _ _ _ _ _ _ (wsEqrSym (hf i ag hlk)) ⟨by simp, fun j t v ht hv => ?_⟩
      rw [List.getElem?_map] at ht hv
      cases htv : tvs[j]? with
      | none => rw [htv] at ht; cases ht
      | some p =>
        obtain ⟨t', v'⟩ := p
        rw [htv] at ht hv
        injection ht with ht
        injection hv with hv
        subst ht hv
        exact ⟨(hif j t' v' htv).1, hrd j t' v' htv⟩
    · dsimp only
      exact cfgMatchdUpdGen _ _ _ _ i ag st' _ _ f _ hf hlk
        (by rw [updWsEq]; exact wsEqrTrans (wsEqrLoadPostRun _ _ _ _ _ (hf i ag hlk)) hharm)
        (fun j hne => updWsNe _ _ _ _ hne)

/-- Extending the execution by one pf step (deviation 6: `pfFetchLoadOk`,
`cfgMatchd`). -/
theorem bridgeStep (E : Exec) (i : Nat) (l : Wlabel) (c c' : Wpcfg P D) :
    lbDepfree l → lbFused l → pfFetchLoadOk c i l →
    execWf E → cfgMatchd c (stt E E.exTr.length) →
    ownCoh c → wpPfStep pstep pcls i l c c' →
    ∃ E', execWf E' ∧ exImg E' = exImg E ∧ cfgMatchd c' (stt E' E'.exTr.length) := by
  intro hdf hfu hfe hE hm hoc hstep
  obtain ⟨k, hpr⟩ := wpPfStepMstep pstep pcls i l c c' _ hdf hfu hfe hoc hm hstep
  revert hpr
  cases projLbl k l with
  | some lb =>
    rintro ⟨σ', hms, hm'⟩
    have hlen := hE.1
    refine ⟨⟨E.exSt ++ [σ'], E.exTr ++ [⟨i, lb⟩]⟩, execSnoc E ⟨i, lb⟩ σ' hE hms, ?_, ?_⟩
    · simp only [exImg, eimg, stt]
      rw [lookup_app_l (by omega)]
    · simp only [stt, List.length_append, List.length_singleton]
      rw [lookup_app_r (by omega)]
      have h0 : E.exTr.length + 1 - E.exSt.length = 0 := by omega
      rw [h0]
      exact hm'
  | none => intro hm'; exact ⟨E, hE, rfl, hm'⟩

/-- The run-level dependency-free premise: the program LTS emits only
operand-free labels. -/
def pstepDepfree : Prop := ∀ p d l p' d', pstep p d l p' d' → lbDepfree l

theorem wpPfStepLbDepfree (i : Nat) (l : Wlabel) (c c' : Wpcfg P D) :
    pstepDepfree pstep → wpPfStep pstep pcls i l c c' → lbDepfree l := by
  intro hdf hs
  cases hs <;> (apply hdf; assumption)

/-- LIFTED BY A2: the run-level twin of `lbFused`. -/
def pstepFused : Prop := ∀ p d l p' d', pstep p d l p' d' → lbFused l

theorem wpPfStepLbFused (i : Nat) (l : Wlabel) (c c' : Wpcfg P D) :
    pstepFused pstep → wpPfStep pstep pcls i l c c' → lbFused l := by
  intro hfu hs
  cases hs <;> (apply hfu; assumption)

/-- THE RUN-LEVEL FETCH PREMISE (Lean-only, deviation 6): every pf step on a run
from `c` to `c'` satisfies `pfFetchLoadOk` (i.e. every FETCH on it is readable
as a plain load and `wsEqr`-harmless as one). -/
def pfRunFetchOk (c c' : Wpcfg P D) : Prop :=
  ∀ (x y : Wpcfg P D) (i : Nat) (l : Wlabel),
    rtc (wpPfRun pstep pcls) c x → wpPfStep pstep pcls i l x y → rtc (wpPfRun pstep pcls) y c' →
    pfFetchLoadOk x i l

/-- The program-level discharge: a program LTS that never fetches. -/
def pstepNoFetch : Prop :=
  ∀ p d l p' d', pstep p d l p' d' → ∀ base tvs, l ≠ .LIFetch base tvs

theorem pfRunFetchOkNoFetch (c c' : Wpcfg P D) :
    pstepNoFetch pstep → pfRunFetchOk pstep pcls c c' := by
  intro hnf x y i l _ hs _
  cases hs with
  | PFIFetch _ ag base tvs _ _ _ hps _ => exact absurd rfl (hnf _ _ _ _ _ hps base tvs)
  | PFSilent => trivial
  | PFLoad => trivial
  | PFStore => trivial
  | PFRmw => trivial
  | PFFence => trivial
  | PFDev => trivial
  | PFRegW => trivial
  | PFCtrl => trivial
  | PFInstr => trivial
  | PFExLoad => trivial
  | PFExStore => trivial

theorem bridgeRun (c c' : Wpcfg P D) :
    pstepDepfree pstep → pstepFused pstep → pfRunFetchOk pstep pcls c c' →
    rtc (wpPfRun pstep pcls) c c' → ownCoh c →
    ∀ E, execWf E → cfgMatchd c (stt E E.exTr.length) →
    ∃ E', execWf E' ∧ exImg E' = exImg E ∧ cfgMatchd c' (stt E' E'.exTr.length) := by
  intro hpdf hpfu hfo0 hrun
  refine rtc_ind_l (fun x => pfRunFetchOk pstep pcls x c' → ownCoh x → ∀ E, execWf E →
      cfgMatchd x (stt E E.exTr.length) →
      ∃ E', execWf E' ∧ exImg E' = exImg E ∧ cfgMatchd c' (stt E' E'.exTr.length)) c' ?_ ?_ c hrun
      hfo0
  · intro _ _ E hE hm; exact ⟨E, hE, rfl, hm⟩
  · rintro x y ⟨i, l, hs⟩ hyc ih hfo hoc E hE hm
    have hfx : pfFetchLoadOk x i l := hfo x y i l (rtc_refl _) hs hyc
    have hfy : pfRunFetchOk pstep pcls y c' := fun x' y' i' l' h1 h2 h3 =>
      hfo x' y' i' l' (rtc_l ⟨i, l, hs⟩ h1) h2 h3
    obtain ⟨E1, hE1, himg1, hm1⟩ := bridgeStep pstep pcls E i l x y
      (wpPfStepLbDepfree pstep pcls i l x y hpdf hs)
      (wpPfStepLbFused pstep pcls i l x y hpfu hs) hfx hE hm hoc hs
    obtain ⟨E2, hE2, himg2, hm2⟩ := ih hfy (ownCohStep pstep pcls i l x y hoc hs) E1 hE1 hm1
    exact ⟨E2, hE2, himg2.trans himg1, hm2⟩

/-- THE BRIDGE THEOREM (D-M6-7's W1 obligation).  Deviation 6: the run-level
fetch premise `pfRunFetchOk`, and the conclusion is `cfgMatchd` (per-agent
`wsEqr`; image and log still EQUAL). -/
theorem wpPfBridge (img : Image) (d0 : D) (ps : List P) (c : Wpcfg P D) :
    pstepDepfree pstep → pstepFused pstep → pfRunFetchOk pstep pcls (wpInit img d0 ps) c →
    rtc (wpPfRun pstep pcls) (wpInit img d0 ps) c →
    ∃ E, execWf E ∧ exImg E = img ∧ cfgMatchd c (stt E E.exTr.length) := by
  intro hpdf hpfu hfo hrun
  let σ0 : Mstate := ⟨img, [], fun _ => wsInit⟩
  have hE : execWf ⟨[σ0], []⟩ := execNil σ0 rfl (fun _ => rfl)
  have hm0 : cfgMatch (wpInit img d0 ps) (stt ⟨[σ0], []⟩ 0) := by
    refine ⟨rfl, rfl, fun i ag hlk => ?_⟩
    simp only [wpInit, List.getElem?_map] at hlk
    cases hp : ps[i]? with
    | none => rw [hp] at hlk; cases hlk
    | some p => rw [hp] at hlk; injection hlk with hlk; subst hlk; rfl
  obtain ⟨E, hE', himg, hm⟩ :=
    bridgeRun pstep pcls _ _ hpdf hpfu hfo hrun (ownCohInit img d0 ps) ⟨[σ0], []⟩ hE
      (cfgMatchCfgMatchd _ _ hm0)
  exact ⟨E, hE', himg, hm⟩

theorem wpPfBridgeLog (img : Image) (d0 : D) (ps : List P) (c : Wpcfg P D) :
    pstepDepfree pstep → pstepFused pstep → pfRunFetchOk pstep pcls (wpInit img d0 ps) c →
    rtc (wpPfRun pstep pcls) (wpInit img d0 ps) c →
    ∃ E, execWf E ∧ exImg E = img ∧ exLog E = c.pcLog := by
  intro hpdf hpfu hfo hrun
  obtain ⟨E, h1, h2, hm⟩ := wpPfBridge pstep pcls img d0 ps c hpdf hpfu hfo hrun
  exact ⟨E, h1, h2, cfgMatchdLog _ _ hm⟩

/-! ### (E) The reverse direction: "programs are free" (and FABRIC-BLIND) -/

def progFree : Prop := ∀ p d l p', pstep p d l p' d

def unprojLbl (lb : Lbl) : Wlabel :=
  match lb with
  | .LLoad aq base ts vs => .LLoad aq false base (ts.zip vs) []
  | .LStore rl base vs _ => .LStore rl base vs [] []
  | .LFence pr pw sr sw => .LFence pr pw sr sw
  | .LRmw aq rl base ts rvs wvs _ => .LRmw aq rl base (ts.zip rvs) wvs [] []

/-- THE REVERSE BRIDGE'S ONE NEW PREMISE (G6a): the labelled classes are the
ones `pcls` would have written. -/
def mstepClsOk (p : P) (σ : Mstate) (i : Nat) (lb : Lbl) : Prop :=
  match lb with
  | .LStore _ _ _ k => k = pcls p (unprojLbl lb) (σ.msWs i)
  | .LRmw _ _ _ _ _ _ k => k = pcls p (unprojLbl lb) (σ.msWs i)
  | _ => True

/-- Indexed by the INITIAL programs `ps`: under `progFree` the acting agent's
program state never moves. -/
def execClsOk (ps : List P) (E : Exec) : Prop :=
  ∀ (n : Nat) (s : Estep) (p : P), E.exTr[n]? = some s → ps[s.esAg]? = some p →
    mstepClsOk pcls p (stt E n) s.esAg s.esLb

theorem rdOkReadOk (img : Image) (log : List Wmsg) (ws : Wstate) (aq : Bool) (base : Int)
    (ts : List Nat) (vs : List (BitVec 8)) :
    rdOk img log ws aq base ts vs → readOk img log ws aq false base (ts.zip vs) := by
  rintro ⟨_, hall⟩ j t v hj
  obtain ⟨ht, hv⟩ := List.getElem?_zip_eq_some.1 hj
  obtain ⟨h1, h2⟩ := hall j t v ht hv
  exact ⟨h1, by rw [loadVpreD0]; exact h2, fun h => by cases h⟩

theorem rmwLatestExclOk (img : Image) (log : List Wmsg) (i : Nat) (base : Int) (ts : List Nat)
    (vs : List (BitVec 8)) :
    rmwLatest img log base ts → exclOk log i base (ts.zip vs) (log.length + 1) := by
  intro hlat j t v hj hw
  obtain ⟨ht, _⟩ := List.getElem?_zip_eq_some.1 hj
  obtain ⟨_, hnw⟩ := hlat j t ht
  apply hnw
  exact writesInMono log _ t (log.length + 1 - 1) t log.length (Nat.le_refl _) (by omega)
    (writesInByWritesIn _ _ _ _ _ hw)

theorem wpPfStepAgsLength (i : Nat) (l : Wlabel) (c c' : Wpcfg P D) :
    wpPfStep pstep pcls i l c c' → c'.pcAgs.length = c.pcAgs.length := by
  intro h
  cases h <;> simp

/-- The conclusion also records that the step left every agent's PROGRAM state
alone. -/
theorem mstepWpPfStep (σ σ' : Mstate) (i : Nat) (lb : Lbl) (c : Wpcfg P D) :
    progFree pstep → cfgMatch c σ → i < c.pcAgs.length →
    (∀ ag, c.pcAgs[i]? = some ag → mstepClsOk pcls ag.paSt σ i lb) →
    mstep σ i lb σ' →
    ∃ c', wpPfStep pstep pcls i (unprojLbl lb) c c' ∧ cfgMatch c' σ' ∧
      c'.pcAgs.map Wpagent.paSt = c.pcAgs.map Wpagent.paSt := by
  intro hpf hm hi hck0 hms
  obtain ⟨ag, hlk⟩ := someOfIsSome (lookup_lt_is_Some_2 hi)
  have hck := hck0 ag hlk
  clear hck0
  obtain ⟨img, lg, f⟩ := σ
  obtain ⟨himg, hlg, hf⟩ := hm
  dsimp only at himg hlg hf
  subst himg hlg
  -- the `cfgMatch` obligation is the same three lines in every arm
  have hmatch : ∀ (st' : P) (w : Wstate) (pr : GSet Nat) (lg' : List Wmsg),
      cfgMatch (⟨c.pcImg, lg', c.pcDev, c.pcAgs.set i ⟨st', w, pr⟩⟩ : Wpcfg P D)
        ⟨c.pcImg, lg', updWs f i w⟩ := fun st' w pr lg' =>
    cfgMatchUpdGen _ _ _ _ i ag st' w pr f _ hf hlk (updWsEq _ _ _)
      (fun j hne => updWsNe _ _ _ _ hne)
  -- every arm re-uses `ag.paSt`, so the program-state projection is untouched
  have hlt := lookup_lt_Some hlk
  have hst : ∀ (w : Wstate) (pr : GSet Nat),
      (c.pcAgs.set i ⟨ag.paSt, w, pr⟩).map Wpagent.paSt = c.pcAgs.map Wpagent.paSt := by
    intro w pr
    apply List.ext_getElem?
    intro j
    rw [List.getElem?_map, List.getElem?_map]
    by_cases hj : i = j
    · subst hj; rw [list_lookup_insert hlt, hlk] <;> rfl
    · rw [list_lookup_insert_ne hj]
  cases hms with
  | MStepLoad aq base ts vs hrd =>
    dsimp only at hrd
    have hl1 := hrd.1
    refine ⟨_, wpPfStep.PFLoad c ag aq false base (ts.zip vs) [] ag.paSt c.pcDev hlk
      (hpf _ _ _ _) ?_, ?_, hst _ _⟩
    · rw [srcsViewNil, readOkD0, ← hf i ag hlk]
      exact rdOkReadOk _ _ _ _ _ _ _ hrd
    · dsimp only
      rw [srcsViewNil, loadPostRunD0, List.map_fst_zip (by omega), hf i ag hlk]
      exact hmatch _ _ _ _
  | MStepStore rl base vs kc hnn =>
    refine ⟨_, wpPfStep.PFStore c ag rl base vs [] [] kc ag.paSt c.pcDev hlk (hpf _ _ _ _) hnn
      ?_, ?_, hst _ _⟩
    · rw [← hf i ag hlk]; exact hck
    · dsimp only
      rw [srcsViewNil, storePostRunD0, hf i ag hlk]
      exact hmatch _ _ _ _
  | MStepFence pr pw sr sw =>
    refine ⟨_, wpPfStep.PFFence c ag pr pw sr sw ag.paSt c.pcDev hlk (hpf _ _ _ _), ?_, hst _ _⟩
    dsimp only
    rw [hf i ag hlk]
    exact hmatch _ _ _ _
  | MStepRmw aq rl base ts rvs wvs kc hnn hlen hrd hlat =>
    dsimp only at hrd hlat
    have hl1 := hrd.1
    refine ⟨_, wpPfStep.PFRmw c ag aq rl base (ts.zip rvs) wvs [] [] kc ag.paSt c.pcDev hlk
      (hpf _ _ _ _) hnn ?_ ?_ ?_ ?_, ?_, hst _ _⟩
    · simp only [List.length_zip]; omega
    · -- D-2r: the read half is at the plain floor
      rw [← hf i ag hlk]; exact rdOkReadOk _ _ _ _ _ _ _ hrd
    · exact rmwLatestExclOk c.pcImg _ i base ts rvs hlat
    · rw [← hf i ag hlk]; exact hck
    · dsimp only
      rw [srcsViewNil, loadPostRunD0, storePostRunD0, List.map_fst_zip (by omega), hf i ag hlk]
      exact hmatch _ _ _ _

theorem execPrefixPfRun (ps : List P) (d0 : D) (E : Exec) (n : Nat) :
    progFree pstep → execWf E → execClsOk pcls ps E →
    (∀ (k : Nat) (s : Estep), E.exTr[k]? = some s → s.esAg < ps.length) →
    n ≤ E.exTr.length →
    ∃ c, rtc (wpPfRun pstep pcls) (wpInit (exImg E) d0 ps) c ∧
      c.pcAgs.length = ps.length ∧ c.pcAgs.map Wpagent.paSt = ps ∧
      cfgMatch c (stt E n) := by
  intro hpf hE hck hag
  induction n with
  | zero =>
    intro _
    refine ⟨wpInit (exImg E) d0 ps, rtc_refl _, by simp [wpInit],
      by simp [wpInit, List.map_map, Function.comp_def], rfl, execLogInit E hE, ?_⟩
    intro i ag hlk
    simp only [wpInit, List.getElem?_map] at hlk
    cases hp : ps[i]? with
    | none => rw [hp] at hlk; cases hlk
    | some p =>
      rw [hp] at hlk; injection hlk with hlk; subst hlk
      exact execWsInit E i hE
  | succ n ih =>
    intro hn
    obtain ⟨c, hrun, hlen, hst, hm⟩ := ih (by omega)
    obtain ⟨s, hs⟩ := someOfIsSome (execTrLookup E n (by omega))
    have hms := execStepAt E n s hE hs
    obtain ⟨c', hstep, hm', hst'⟩ := mstepWpPfStep pstep pcls (stt E n) (stt E (n + 1)) s.esAg
      s.esLb c hpf hm (by rw [hlen]; exact hag n s hs)
      (fun ag hlk => hck n s ag.paSt hs (by rw [← hst, List.getElem?_map, hlk] <;> rfl)) hms
    exact ⟨c', rtc_r hrun ⟨s.esAg, unprojLbl s.esLb, hstep⟩,
      by rw [wpPfStepAgsLength pstep pcls _ _ _ _ hstep, hlen], by rw [hst', hst], hm'⟩

/-- THE REVERSE BRIDGE.  With a program LTS that admits everything, every
`execWf` execution over agents `0 .. ps.length - 1` is the projection of a
promise-free run of the full machine. -/
theorem execWfPfRun (ps : List P) (d0 : D) (E : Exec) :
    progFree pstep → execWf E → execClsOk pcls ps E →
    (∀ (k : Nat) (s : Estep), E.exTr[k]? = some s → s.esAg < ps.length) →
    ∃ c, rtc (wpPfRun pstep pcls) (wpInit (exImg E) d0 ps) c ∧
      cfgMatch c (stt E E.exTr.length) := by
  intro hpf hE hck hag
  obtain ⟨c, h1, _, _, h4⟩ :=
    execPrefixPfRun pstep pcls ps d0 E E.exTr.length hpf hE hck hag (Nat.le_refl _)
  exact ⟨c, h1, h4⟩

end bridge

end Weak
