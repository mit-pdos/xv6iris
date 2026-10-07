/-
Weak: **the re-fusion simulation** (T2 carrier, A2 stage 2).

Rocq: `iris/WeakRefuse.v` @ xxvzwolszwmp.

The Rocq header, in substance (design: `claude-notes/design/weak-memory-srvwmo.md`, "THE T2
CARRIER PIPELINE (A2)", stage 2; stage 1 is `WeakErase`, stage 3 the projection
`wpPfBridgeLog`):

THE PROBLEM.  Stage 1 leaves ONE gate, `pstepFused`: the RMW split makes the event instance emit
`LExLoad`/`LExStore`, while the axiomatic alphabet is FUSED (`LRmw` is one event).

THE MOVE.  Simulate the split run by a run of the SAME program over the FUSED alphabet: an
`LExLoad` step becomes an `LSilent` step (`RFDrop`; the read moves to the write's position) and its
`LExStore` becomes ONE `PFRmw` step (`RFFuse`) whose read half RE-READS the reservation's
timestamps, with the values the exclusive read saw.  Log, image, fabric and program states are
preserved step for step.  A DANGLING exclusive read is the case where no `RFFuse` follows the
`RFDrop` (Rocq §0: every exclusive read becomes `LSilent`, the one uniform choice needing no
lookahead; a dangling read loses its axiomatic event, nothing is invented, the log is identical).

NO PAIRING PREMISE (A2-s3).  The agent's own plain loads and real fences CLEAR `wRes`, so the
pending-pair invariant (the last conjunct of `rfAg`) is guarded by `wRes = some R` ALONE: it is
established at the exload arm from the label's own data, carried verbatim across `Wstate`-inert
steps (the zero-byte load included: `loadPostRunDNil` + `rfWsCtrl`), killed by the guard at every
dirty label, and consumed at the exstore arm, whose machine premise IS the guard.

THE STATE RELATION.  `rfWs wF wS = erWs wF (wsResSet wS none)`: stage 1's ≤-relation against the
split state WITH ITS RESERVATION FORGOTTEN (the fused side never takes a `PFExLoad`, so its `wRes`
stays `none`, and `erWs`'s `resRel` would be false of the pair).  §1's commutation lemmas are the
price, and they are conversions.

**Deviations from Rocq.**

1. NAMES: lowerCamelCase as `Weak/WeakMem.lean` deviation 1.  The Rocq `Reflexive` instance
   `rf_ws_refl` is the theorem `rfWsRefl`.  Three names are DUPLICATED Rocq names (also in
   `WeakMem`, whose Lean twins are field equations), hence file-qualified:
   `WeakRefuse.loadPostRunDRes`, `WeakRefuse.fencePostRes`, `WeakRefuse.storePostRunDRes`.
2. The section variables `pstep` and `pcls` are explicit arguments of every declaration that uses
   them, in Rocq's order (`Global Arguments`); `refusePstep`'s constructors take them implicitly.
3. CONVERSIONS (`WeakMem` deviation 3): `loadPostRunDNil`, `exloadPostRunDResN` and the run-level
   `ws_res_set` commutations are proved by rewriting (`Nat.zero_max`, `loadPostRunD0`,
   `exloadPostRunD0`, the fold inductions) where Rocq closes by `done`.  `loadPostRunDResNone` /
   `storePostRunDResNone` go through `WeakMem`'s field equations.  Statements unchanged.
4. O2 — THE INSTRUCTION FETCH (Lean-only label `LIFetch`, `Weak/WeakPromise.lean` deviation 8;
   `WeakErase` deviation 6):
   - `refuseStep` gains the `PFIFetch` arm (kept by `RFKeep`: a fetch is `lbFused`; log-only side
     condition, identity post-state, the pending invariant carried verbatim).
   - STAGE C (owner ruling Q-C3, `notes/weak-port-o2-stageC.md`): the bridge treats a fetch as a
     stutter (`WeakPromiseBridge` deviation 6), so `refuseBridgeLog` and `t2Bridge` have Rocq's
     statements (Stage B's `pstepNoFetch` premise, `refusePstepNoFetch`, `refuseBridgeLogFetch`
     and `t2BridgeFetch` are deleted).

**Rocq → Lean name map.**  `ws_res_set_idem` ↦ `wsResSetIdem`; `ctrl_post_res_set` ↦
`ctrlPostResSet`; `load_post_at_res` ↦ `loadPostAtRes`; `load_post_at_res_None` ↦
`loadPostAtResNone`; `fence_post_res_None` ↦ `fencePostResNone`; `store_post_d_res` ↦
`storePostDRes`; `fence_post_res` ↦ `WeakRefuse.fencePostRes`; `load_post_fold_res` ↦
`loadPostFoldRes`; `load_post_run_d_res` ↦ `WeakRefuse.loadPostRunDRes`;
`load_post_fold_res_None` ↦ `loadPostFoldResNone`; `load_post_run_d_res_None` ↦
`loadPostRunDResNone`; `store_post_fold_res_None` ↦ `storePostFoldResNone`;
`load_post_run_d_nil` ↦ `loadPostRunDNil`; `store_post_run_d_res_None` ↦ `storePostRunDResNone`;
`store_post_fold_res` ↦ `storePostFoldRes`; `store_post_run_d_res` ↦
`WeakRefuse.storePostRunDRes`; `exload_post_run_d_resN` ↦ `exloadPostRunDResN`; `rf_ws` ↦ `rfWs`;
`rf_ws_{ws_le_nc,relp,fwd,ctrl,refl,load_r,exload_r,load,load_exload,store,fence}` ↦
`rfWs{WsLeNc,Relp,Fwd,Ctrl,Refl,LoadR,ExloadR,Load,LoadExload,Store,Fence}`; `read_ok_d_rf` ↦
`readOkDRf`; `excl_ok_of_excl_ok_ts` ↦ `exclOkOfExclOkTs`; `pcls_fusable` ↦ `pclsFusable`;
`refuse_pstep` ↦ `refusePstep` (arms `RFKeep`/`RFDrop`/`RFFuse`); `refuse_pstep_{fused,depfree,
lat_free}` ↦ `refusePstep{Fused,Depfree,LatFree}`; `rf_pend` ↦ `rfPend`; `rf_ag` ↦ `rfAg`;
`rf_cfg` ↦ `rfCfg`; `rf_cfg_{log,init,upd}` ↦ `rfCfg{Log,Init,Upd}`; `rf_ag_app` ↦ `rfAgApp`;
`refuse_step` ↦ `refuseStep`; `refuse_run_step` ↦ `refuseRunStep`; `refuse_rtc` ↦ `refuseRtc`;
`refuse_run` ↦ `refuseRun`; `refuse_bridge_log` ↦ `refuseBridgeLog`; `pcls_fusable_erase` ↦
`pclsFusableErase`; `t2_bridge` ↦ `t2Bridge`.

**Not ported:** nothing — every Rocq definition and lemma has a Lean twin.
-/
import Weak.WeakErase

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std Wlabel

/-! ## 1. `wsResSet` commutes with every step function the fused side runs -/

theorem wsResSetIdem (ws : Wstate) (r1 r2 : Option Wresv) :
    wsResSet (wsResSet ws r1) r2 = wsResSet ws r2 := rfl

/-- The `wsResSet` COMMUTATION (not the field equation `ctrlPostRes`). -/
theorem ctrlPostResSet (ws : Wstate) (r : Option Wresv) (v : Nat) :
    ctrlPost (wsResSet ws r) v = wsResSet (ctrlPost ws v) r := rfl

/-- A2-s3: loads and fences CLEAR the reservation, so their commutations hold at `none`. -/
theorem loadPostAtRes (ws : Wstate) (r : Option Wresv) (aq : Bool) (vpre : Nat) (a : Int)
    (t : Nat) :
    loadPostAt (wsResSet ws r) aq vpre a t = wsResSet (loadPostAt ws aq vpre a t) none := rfl

theorem loadPostAtResNone (ws : Wstate) (aq : Bool) (vpre : Nat) (a : Int) (t : Nat) :
    (loadPostAt ws aq vpre a t).wRes = none := rfl

theorem fencePostResNone (ws : Wstate) (pr pw sr sw : Bool) :
    (pr || pw || sr || sw) = true → (fencePost ws pr pw sr sw).wRes = none := by
  intro h
  rw [fencePostRes, h]
  rfl

theorem storePostDRes (ws : Wstate) (rl : Bool) (vf : Nat) (a : Int) (t : Nat) :
    storePostD (wsResSet ws none) rl vf a t = wsResSet (storePostD ws rl vf a t) none := rfl

theorem WeakRefuse.fencePostRes (ws : Wstate) (pr pw sr sw : Bool) :
    fencePost (wsResSet ws none) pr pw sr sw = wsResSet (fencePost ws pr pw sr sw) none := by
  cases pr <;> cases pw <;> cases sr <;> cases sw <;> rfl

theorem loadPostFoldRes (aq : Bool) (vpre : Nat) (ats : List (Int × Nat)) (ws : Wstate) :
    ats.foldl (fun w at_ => loadPostAt w aq vpre at_.1 at_.2) (wsResSet ws none)
    = wsResSet (ats.foldl (fun w at_ => loadPostAt w aq vpre at_.1 at_.2) ws) none := by
  induction ats generalizing ws with
  | nil => rfl
  | cons x l ih =>
    show List.foldl _ (loadPostAt (wsResSet ws none) aq vpre x.1 x.2) l = _
    rw [loadPostAtRes]
    exact ih _

theorem WeakRefuse.loadPostRunDRes (ws : Wstate) (aq : Bool) (vaddr : Nat) (base : Int)
    (ts : List Nat) :
    loadPostRunD (wsResSet ws none) aq vaddr base ts
    = wsResSet (loadPostRunD ws aq vaddr base ts) none := by
  unfold loadPostRunD loadPostBytesD
  rw [loadPostFoldRes]
  rfl

/-- ... and the CLEAR itself, at the fold level, on any non-empty access. -/
theorem loadPostFoldResNone (aq : Bool) (vpre : Nat) (ats : List (Int × Nat)) (ws : Wstate) :
    ats ≠ [] → (ats.foldl (fun w at_ => loadPostAt w aq vpre at_.1 at_.2) ws).wRes = none := by
  induction ats generalizing ws with
  | nil => intro h; exact absurd rfl h
  | cons x l ih =>
    intro _
    cases l with
    | nil => rfl
    | cons y l' => exact ih _ (List.cons_ne_nil _ _)

theorem loadPostRunDResNone (ws : Wstate) (aq : Bool) (vaddr : Nat) (base : Int)
    (ts : List Nat) : ts ≠ [] → (loadPostRunD ws aq vaddr base ts).wRes = none := by
  intro hne
  rw [Weak.loadPostRunDRes]
  cases ts with
  | nil => exact absurd rfl hne
  | cons _ _ => rfl

theorem storePostFoldResNone (rl : Bool) (vf t : Nat) (as_ : List Int) (ws : Wstate) :
    as_ ≠ [] → (as_.foldl (fun w a => storePostD w rl vf a t) ws).wRes = none := by
  induction as_ generalizing ws with
  | nil => intro h; exact absurd rfl h
  | cons x l ih =>
    intro _
    cases l with
    | nil => rfl
    | cons y l' => exact ih _ (List.cons_ne_nil _ _)

/-- The ZERO-BYTE load moves nothing but the CONTROL VIEW. -/
theorem loadPostRunDNil (ws : Wstate) (aq : Bool) (base : Int) :
    loadPostRunD ws aq 0 base [] = ctrlPost ws ws.wTbank := by
  show ctrlPost ws (max 0 ws.wTbank) = _
  rw [Nat.zero_max]

theorem storePostRunDResNone (ws : Wstate) (rl : Bool) (vaddr vdata : Nat) (base : Int)
    (n t : Nat) : n ≠ 0 → (storePostRunD ws rl vaddr vdata base n t).wRes = none := by
  intro hne
  rw [Weak.storePostRunDRes]
  cases n with
  | zero => exact absurd rfl hne
  | succ _ => rfl

theorem storePostFoldRes (rl : Bool) (vf t : Nat) (as_ : List Int) (ws : Wstate) :
    as_.foldl (fun w a => storePostD w rl vf a t) (wsResSet ws none)
    = wsResSet (as_.foldl (fun w a => storePostD w rl vf a t) ws) none := by
  induction as_ generalizing ws with
  | nil => rfl
  | cons x l ih =>
    show List.foldl _ (storePostD (wsResSet ws none) rl vf x t) l = _
    rw [storePostDRes]
    exact ih _

theorem WeakRefuse.storePostRunDRes (ws : Wstate) (rl : Bool) (vaddr vdata : Nat) (base : Int)
    (n t : Nat) :
    storePostRunD (wsResSet ws none) rl vaddr vdata base n t
    = wsResSet (storePostRunD ws rl vaddr vdata base n t) none := by
  unfold storePostRunD storePostBytesD
  rw [storePostFoldRes]
  rfl

/-- D-2r: forgetting the reservation leaves the plain load run under ONE `ctrlPost`. -/
theorem exloadPostRunDResN (ws : Wstate) (aq : Bool) (vaddr : Nat) (base : Int)
    (ts : List Nat) :
    wsResSet (exloadPostRunD ws aq vaddr base ts) none
    = ctrlPost (wsResSet (loadPostRunD ws aq 0 base ts) none) vaddr := by
  rw [exloadPostRunDCtrl, exloadPostRunD0, loadPostRunD0]
  rfl

/-! ## 2. `rfWs`: stage 1's ≤-relation, with the reservation forgotten -/

def rfWs (wF wS : Wstate) : Prop := erWs wF (wsResSet wS none)

theorem rfWsWsLeNc (wF wS : Wstate) : rfWs wF wS → wsLeNc wF wS :=
  fun h => erWsWsLeNc wF (wsResSet wS none) h

theorem rfWsRelp (wF wS : Wstate) : rfWs wF wS → wF.wRelp = wS.wRelp :=
  fun h => erWsRelp wF (wsResSet wS none) h

theorem rfWsFwd (wF wS : Wstate) : rfWs wF wS → WeakErase.fwdLe wF wS :=
  fun h => erWsFwd wF (wsResSet wS none) h

/-- A control raise on EITHER side is invisible to `rfWs`. -/
theorem rfWsCtrl (wF wS : Wstate) (vF vS : Nat) :
    rfWs wF wS → rfWs (ctrlPost wF vF) (ctrlPost wS vS) := by
  intro h
  have heq : wsResSet (ctrlPost wS vS) none = ctrlPost (wsResSet wS none) vS := rfl
  unfold rfWs
  rw [heq]
  exact ctrlPostEr _ _ _ _ h

theorem rfWsRefl (w : Wstate) : rfWs w w :=
  ⟨wsLeNcRefl w, rfl, fwdLeRefl w, fun R h => by cases h⟩

/-- The ONE-SIDED step: the split side takes a read the fused side does not. -/
theorem rfWsLoadR (wF wS : Wstate) (aq : Bool) (vaddr : Nat) (base : Int) (ts : List Nat) :
    rfWs wF wS → rfWs wF (loadPostRunD wS aq vaddr base ts) := by
  intro h
  have hf := loadPostRunDFwd wS aq vaddr base ts
  refine erWsTrans h ⟨wsLeWsLeNc _ _ (loadPostRunDLe wS aq vaddr base ts),
    (loadPostRunDRelp wS aq vaddr base ts).symm,
    fun aq' a t => Nat.le_of_eq (by simp only [fwdView, wsResSetFwd, hf]),
    fun R hR => by cases hR⟩

theorem rfWsExloadR (wF wS : Wstate) (aq : Bool) (vaddr : Nat) (base : Int) (ts : List Nat) :
    rfWs wF wS → rfWs wF (exloadPostRunD wS aq vaddr base ts) := by
  intro h
  unfold rfWs
  rw [exloadPostRunDResN]
  exact erWsCtrlR _ _ _ (rfWsLoadR wF wS aq 0 base ts h)

/-- The two-sided steps: the fused side always runs at operand view `0`. -/
theorem rfWsLoad (wF wS : Wstate) (aq : Bool) (vaddr : Nat) (base : Int) (ts : List Nat) :
    rfWs wF wS → rfWs (loadPostRunD wF aq 0 base ts) (loadPostRunD wS aq vaddr base ts) := by
  intro h
  unfold rfWs
  rw [← WeakRefuse.loadPostRunDRes]
  exact loadPostRunDEr0 _ _ _ _ _ _ h

theorem rfWsLoadExload (wF wS : Wstate) (aq : Bool) (vaddr : Nat) (base : Int)
    (ts : List Nat) :
    rfWs wF wS → rfWs (loadPostRunD wF aq 0 base ts) (exloadPostRunD wS aq vaddr base ts) := by
  intro h
  unfold rfWs
  rw [exloadPostRunDResN]
  apply erWsCtrlR
  rw [← WeakRefuse.loadPostRunDRes]
  exact loadPostRunDEr0 _ _ _ _ _ _ h

theorem rfWsStore (wF wS : Wstate) (rl : Bool) (vaddr vdata : Nat) (base : Int) (n t : Nat) :
    rfWs wF wS →
    rfWs (storePostRunD wF rl 0 0 base n t) (storePostRunD wS rl vaddr vdata base n t) := by
  intro h
  unfold rfWs
  rw [← WeakRefuse.storePostRunDRes]
  exact storePostRunDEr0 _ _ _ _ _ _ _ _ h

theorem rfWsFence (wF wS : Wstate) (pr pw sr sw : Bool) :
    rfWs wF wS → rfWs (fencePost wF pr pw sr sw) (fencePost wS pr pw sr sw) := by
  intro h
  unfold rfWs
  rw [← WeakRefuse.fencePostRes]
  exact fencePostEr _ _ _ _ _ _ h

/-- Readability is ANTI-monotone: the fused agent's LOWER floors admit every timestamp the
split agent could read. -/
theorem readOkDRf (img : Image) (log : List Wmsg) (wF wS : Wstate) (aq lat : Bool) (base : Int)
    (tvs : List (Nat × BitVec 8)) (va : Nat) :
    rfWs wF wS → readOkD img log wS aq lat base tvs va →
    readOkD img log wF aq lat base tvs 0 :=
  fun h hr => readOkDEr0 img log wF (wsResSet wS none) aq lat base tvs va h hr

/-- The converse of `exclOkTsOfExclOk`. -/
theorem exclOkOfExclOkTs (log : List Wmsg) (i : Nat) (base : Int) (tvs : List (Nat × BitVec 8))
    (ts : Nat) : exclOkTs log i base (tvs.map Prod.fst) ts → exclOk log i base tvs ts := by
  intro he j t v hj
  exact he j t (by simp [List.getElem?_map, hj])

/-! ## 3–4. The pairing discipline is the machine's; the fused program LTS -/

section refuse

variable {P D : Type}
variable (pstep : P → D → Wlabel → P → D → Prop)
variable (pcls : P → Wlabel → Wstate → WmClass)

/-- THE MESSAGE-CLASS PREMISE (stage 2's twin of `pclsErasable`), QUANTIFIED OVER A STEP: the
class at the rebuilt `LRmw` is the class at the `LExStore`, at a lower `Wstate` with equal
`wRelp`. -/
def pclsFusable : Prop :=
  ∀ (p : P) (d : D) (rl : Bool) (base : Int) (data : List (BitVec 8)) (asrc vsrc : List Dsrc)
    (p' : P) (d' : D) (aq : Bool) (tvs : List (Nat × BitVec 8)) (wF wS : Wstate),
    pstep p d (.LExStore rl base data asrc vsrc) p' d' →
    wF.wRelp = wS.wRelp →
    pcls p (.LRmw aq rl base tvs data [] []) wF = pcls p (.LExStore rl base data asrc vsrc) wS

/-- THE FUSED PROGRAM LTS: same program states, same fabric, same steps; only the two split
labels change. -/
inductive refusePstep (p : P) (d : D) : Wlabel → P → D → Prop
  | RFKeep (l : Wlabel) (p' : P) (d' : D) :
      lbFused l → pstep p d l p' d' → refusePstep p d l p' d'
  | RFDrop (aq : Bool) (base : Int) (tvs : List (Nat × BitVec 8)) (asrc : List Dsrc) (p' : P)
      (d' : D) :
      pstep p d (.LExLoad aq base tvs asrc) p' d' → refusePstep p d .LSilent p' d'
  | RFFuse (aq rl : Bool) (base : Int) (tvs : List (Nat × BitVec 8)) (data : List (BitVec 8))
      (asrc vsrc : List Dsrc) (p' : P) (d' : D) :
      pstep p d (.LExStore rl base data asrc vsrc) p' d' →
      refusePstep p d (.LRmw aq rl base tvs data [] []) p' d'

/-- THE GATE, DISCHARGED BY CONSTRUCTION — stage 2's whole content. -/
theorem refusePstepFused : pstepFused (refusePstep pstep) := by
  intro p d l p' d' h
  cases h with
  | RFKeep l p' d' hl _ => exact hl
  | RFDrop => trivial
  | RFFuse => trivial

theorem refusePstepDepfree : pstepDepfree pstep → pstepDepfree (refusePstep pstep) := by
  intro hdf p d l p' d' h
  cases h with
  | RFKeep l p' d' _ hs => exact hdf _ _ _ _ _ hs
  | RFDrop => trivial
  | RFFuse => exact ⟨rfl, rfl⟩

theorem refusePstepLatFree :
    (∀ p d l p' d', pstep p d l p' d' → latFree l) →
    ∀ p d l p' d', refusePstep pstep p d l p' d' → latFree l := by
  intro hlf p d l p' d' h
  cases h with
  | RFKeep l p' d' _ hs => exact hlf _ _ _ _ _ hs
  | RFDrop => trivial
  | RFFuse => trivial

/-! ## 5. The configuration relation -/

/-- THE PENDING PAIR, R-keyed and ∃-shaped. -/
def rfPend (img : Image) (log : List Wmsg) (wF wS : Wstate) (R : Wresv) : Prop :=
  ∃ (aq : Bool) (tvs : List (Nat × BitVec 8)),
    R.rvTs = tvs.map Prod.fst ∧
    readOkD img log wF aq false R.rvBase tvs 0 ∧
    rfWs (loadPostRunD wF aq 0 R.rvBase (tvs.map Prod.fst)) wS

def rfAg (img : Image) (log : List Wmsg) (agF agS : Wpagent P) : Prop :=
  agF.paSt = agS.paSt ∧ agF.paProm = agS.paProm ∧
  rfWs agF.paWs agS.paWs ∧
  ∀ R : Wresv, agS.paWs.wRes = some R → rfPend img log agF.paWs agS.paWs R

def rfCfg (cF cS : Wpcfg P D) : Prop :=
  cF.pcImg = cS.pcImg ∧ cF.pcLog = cS.pcLog ∧ cF.pcDev = cS.pcDev ∧
  cF.pcAgs.length = cS.pcAgs.length ∧
  ∀ (i : Nat) (agS : Wpagent P), cS.pcAgs[i]? = some agS →
    ∃ agF, cF.pcAgs[i]? = some agF ∧ rfAg cF.pcImg cF.pcLog agF agS

theorem rfCfgLog (cF cS : Wpcfg P D) : rfCfg cF cS → cF.pcLog = cS.pcLog := fun h => h.2.1

/-- THE INITIAL CONFIGURATION needs no premise: an agent at `wsInit` holds no reservation. -/
theorem rfCfgInit (img : Image) (d0 : D) (ps : List P) :
    rfCfg (wpInit img d0 ps : Wpcfg P D) (wpInit img d0 ps) := by
  refine ⟨rfl, rfl, rfl, rfl, fun i agS hlk => ⟨agS, hlk, rfl, rfl, rfWsRefl _, fun R hR => ?_⟩⟩
  simp only [wpInit, List.getElem?_map] at hlk
  cases hp : ps[i]? with
  | none => rw [hp] at hlk; cases hlk
  | some p => rw [hp] at hlk; injection hlk with hlk; subst hlk; cases hR

/-- The pending read side condition survives an append. -/
theorem rfAgApp (img : Image) (lg lg' ext : List Wmsg) (agF agS : Wpagent P) :
    lg' = lg ++ ext → wsBounded agF.paWs lg.length →
    rfAg img lg agF agS → rfAg img lg' agF agS := by
  rintro rfl hb ⟨hst, hpr, hws, hpd⟩
  refine ⟨hst, hpr, hws, fun R hR => ?_⟩
  obtain ⟨aq, tvs, hrts, hr, hal⟩ := hpd R hR
  exact ⟨aq, tvs, hrts, readOkDApp img lg ext agF.paWs aq R.rvBase tvs 0 hb (Nat.zero_le _) hr,
    hal⟩

/-- The one configuration-update lemma every arm uses. -/
theorem rfCfgUpd (img : Image) (lg lg' ext : List Wmsg) (dv : D)
    (agsF agsS : List (Wpagent P)) (i : Nat) (agF agS : Wpagent P) (st' : P) (wF wS : Wstate)
    (pr : GSet Nat) :
    lg' = lg ++ ext →
    agsF.length = agsS.length →
    (∀ (j : Nat) (agj : Wpagent P), agsS[j]? = some agj →
      ∃ agFj, agsF[j]? = some agFj ∧ rfAg img lg agFj agj ∧
        wsBounded agFj.paWs lg.length) →
    agsS[i]? = some agS → agsF[i]? = some agF →
    rfWs wF wS →
    (∀ R : Wresv, wS.wRes = some R → rfPend img lg' wF wS R) →
    rfCfg (⟨img, lg', dv, agsF.set i ⟨st', wF, pr⟩⟩ : Wpcfg P D)
      ⟨img, lg', dv, agsS.set i ⟨st', wS, pr⟩⟩ := by
  intro hext hlen hags _ hie hws hpd
  obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.mp hie
  refine ⟨rfl, rfl, rfl, by simp only [List.length_set, hlen], fun j agj hj => ?_⟩
  rcases lookupSetCases hj with ⟨rfl, rfl⟩ | ⟨hne, hj⟩
  · refine ⟨⟨st', wF, pr⟩, ?_, rfl, rfl, hws, hpd⟩
    rw [List.getElem?_set]
    simp [hlt]
  · obtain ⟨agFj, hlk, hrel, hb⟩ := hags j agj hj
    refine ⟨agFj, ?_, rfAgApp img lg lg' ext agFj agj hext hb hrel⟩
    rw [List.getElem?_set]
    simp only [Ne.symm hne, ↓reduceIte]
    exact hlk

/-! ## 6. THE STEP SIMULATION -/

theorem refuseStep (i : Nat) (l : Wlabel) (cS cS' cF : Wpcfg P D) :
    pclsErasable pcls → pclsFusable pstep pcls → pstepDepfree pstep →
    cfgWf cF → rfCfg cF cS → wpPfStep pstep pcls i l cS cS' →
    ∃ lF cF', wpPfStep (refusePstep pstep) pcls i lF cF cF' ∧ rfCfg cF' cS' := by
  intro hcls hfus hdf hwf hm hstep
  obtain ⟨himg, hlog, hdev, hlen, hags⟩ := hm
  -- the per-agent package every arm feeds to `rfCfgUpd`, read at the SPLIT side's image and log
  have hags' : ∀ (j : Nat) (agj : Wpagent P), cS.pcAgs[j]? = some agj →
      ∃ agFj, cF.pcAgs[j]? = some agFj ∧ rfAg cS.pcImg cS.pcLog agFj agj ∧
        wsBounded agFj.paWs cS.pcLog.length := by
    intro j agj hj
    obtain ⟨agFj, hlk, hrel⟩ := hags j agj hj
    rw [himg, hlog] at hrel
    exact ⟨agFj, hlk, hrel, by rw [← hlog]; exact (hwf j agFj hlk).1⟩
  clear hags
  cases hstep with
  | PFSilent cfg ag st' d' hlk hps =>
    -- both wstates frozen: the invariant carries verbatim
    obtain ⟨agF, hlke, ⟨hst, hpr, hws, hpd⟩, _⟩ := hags' i ag hlk
    refine ⟨.LSilent, _, wpPfStep.PFSilent cF agF st' d' hlke
      (by rw [hst, hdev]; exact refusePstep.RFKeep _ _ _ trivial hps), ?_⟩
    rw [himg, hlog, hpr]
    exact rfCfgUpd _ _ _ [] _ _ _ _ _ _ _ _ _ _ (List.append_nil _).symm hlen hags' hlk hlke
      hws hpd
  | PFLoad cfg ag aq lat base tvs asrc st' d' hlk hps hr =>
    -- the machine CLEARS the reservation unless the load is zero-byte
    obtain ⟨agF, hlke, ⟨hst, hpr, hws, hpd⟩, _⟩ := hags' i ag hlk
    have hd : asrc = [] := hdf _ _ _ _ _ hps
    subst hd
    refine ⟨.LLoad aq lat base tvs [], _, wpPfStep.PFLoad cF agF aq lat base tvs [] st' d' hlke
      (by rw [hst, hdev]; exact refusePstep.RFKeep _ _ _ trivial hps)
      (by rw [himg, hlog]; exact readOkDRf _ _ _ _ _ _ _ _ _ hws hr), ?_⟩
    rw [himg, hlog, hpr]
    refine rfCfgUpd _ _ _ [] _ _ _ _ _ _ _ _ _ _ (List.append_nil _).symm hlen hags' hlk hlke
      (rfWsLoad _ _ _ _ _ _ hws) ?_
    simp only [srcsView, List.foldr_nil]
    intro R hR
    cases tvs with
    | nil =>
      simp only [List.map_nil, loadPostRunDNil, ctrlPostRes] at hR ⊢
      obtain ⟨aq0, tvs0, hts0, hrok, hrf⟩ := hpd R hR
      refine ⟨aq0, tvs0, hts0, hrok, ?_⟩
      rw [loadPostRunDCtrl]
      exact rfWsCtrl _ _ _ _ hrf
    | cons tv tvs0 =>
      have hne : (tv :: tvs0).map Prod.fst ≠ [] := by simp
      rw [loadPostRunDResNone _ _ _ _ _ hne] at hR
      cases hR
  | PFStore cfg ag rl base data asrc vsrc k st' d' hlk hps hnn hk =>
    -- the store clears the reservation
    obtain ⟨agF, hlke, ⟨hst, hpr, hws, hpd⟩, _⟩ := hags' i ag hlk
    obtain ⟨rfl, rfl⟩ : asrc = [] ∧ vsrc = [] := hdf _ _ _ _ _ hps
    have hkk : k = pcls agF.paSt (.LStore rl base data [] []) agF.paWs := by
      rw [hst, hk]
      exact (hcls ag.paSt (.LStore rl base data [] []) _ _ (rfWsRelp _ _ hws)).symm
    refine ⟨.LStore rl base data [] [], _, wpPfStep.PFStore cF agF rl base data [] [] k st' d'
      hlke (by rw [hst, hdev]; exact refusePstep.RFKeep _ _ _ trivial hps) hnn hkk, ?_⟩
    rw [himg, hlog, hpr]
    refine rfCfgUpd _ _ _ [⟨base, data, some i, k⟩] _ _ _ _ _ _ _ _ _ _ rfl hlen hags' hlk hlke
      (rfWsStore _ _ _ _ _ _ _ _ hws) ?_
    intro R hR
    have hne : data.length ≠ 0 := by
      intro h; apply hnn
      cases data with
      | nil => rfl
      | cons _ _ => simp at h
    rw [storePostRunDResNone _ _ _ _ _ _ _ hne] at hR
    cases hR
  | PFRmw cfg ag aq rl base tvs data asrc vsrc k st' d' hlk hps hnn hlen' hr he hk =>
    -- already fused; its store half clears the reservation
    obtain ⟨agF, hlke, ⟨hst, hpr, hws, hpd⟩, _⟩ := hags' i ag hlk
    obtain ⟨rfl, rfl⟩ : asrc = [] ∧ vsrc = [] := hdf _ _ _ _ _ hps
    have hkk : k = pcls agF.paSt (.LRmw aq rl base tvs data [] []) agF.paWs := by
      rw [hst, hk]
      exact (hcls ag.paSt (.LRmw aq rl base tvs data [] []) _ _ (rfWsRelp _ _ hws)).symm
    refine ⟨.LRmw aq rl base tvs data [] [], _, wpPfStep.PFRmw cF agF aq rl base tvs data [] []
      k st' d' hlke (by rw [hst, hdev]; exact refusePstep.RFKeep _ _ _ trivial hps) hnn hlen'
      (by rw [himg, hlog]; exact readOkDRf _ _ _ _ _ _ _ _ _ hws hr)
      (by rw [hlog]; exact he) hkk, ?_⟩
    rw [himg, hlog, hpr]
    refine rfCfgUpd _ _ _ [⟨base, data, some i, k⟩] _ _ _ _ _ _ _ _ _ _ rfl hlen hags' hlk hlke
      (rfWsStore _ _ _ _ _ _ _ _ (rfWsLoad _ _ _ _ _ _ hws)) ?_
    intro R hR
    have hne : data.length ≠ 0 := by
      intro h; apply hnn
      cases data with
      | nil => rfl
      | cons _ _ => simp at h
    rw [storePostRunDResNone _ _ _ _ _ _ _ hne] at hR
    cases hR
  | PFFence cfg ag pr pw sr sw st' d' hlk hps =>
    -- a real fence clears the reservation; the all-false fence is the identity
    obtain ⟨agF, hlke, ⟨hst, hpr, hws, hpd⟩, _⟩ := hags' i ag hlk
    refine ⟨.LFence pr pw sr sw, _, wpPfStep.PFFence cF agF pr pw sr sw st' d' hlke
      (by rw [hst, hdev]; exact refusePstep.RFKeep _ _ _ trivial hps), ?_⟩
    rw [himg, hlog, hpr]
    refine rfCfgUpd _ _ _ [] _ _ _ _ _ _ _ _ _ _ (List.append_nil _).symm hlen hags' hlk hlke
      (rfWsFence _ _ _ _ _ _ hws) ?_
    intro R hR
    by_cases hb : (pr || pw || sr || sw) = true
    · rw [fencePostResNone _ _ _ _ _ hb] at hR
      cases hR
    · have h4 : pr = false ∧ pw = false ∧ sr = false ∧ sw = false := by
        cases pr <;> cases pw <;> cases sr <;> cases sw <;> simp_all
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h4
      rw [fencePostId] at hR
      rw [fencePostId, fencePostId]
      exact hpd R hR
  | PFDev cfg ag st' d' hlk hps =>
    obtain ⟨agF, hlke, ⟨hst, hpr, hws, hpd⟩, _⟩ := hags' i ag hlk
    refine ⟨.LDev, _, wpPfStep.PFDev cF agF st' d' hlke
      (by rw [hst, hdev]; exact refusePstep.RFKeep _ _ _ trivial hps), ?_⟩
    rw [himg, hlog, hpr]
    exact rfCfgUpd _ _ _ [] _ _ _ _ _ _ _ _ _ _ (List.append_nil _).symm hlen hags' hlk hlke
      hws hpd
  | PFRegW cfg ag rd srcs st' d' hlk hps => exact False.elim (hdf _ _ _ _ _ hps)
  | PFCtrl cfg ag srcs st' d' hlk hps => exact False.elim (hdf _ _ _ _ _ hps)
  | PFInstr cfg ag st' d' hlk hps => exact False.elim (hdf _ _ _ _ _ hps)
  | PFExLoad cfg ag aq base tvs asrc st' d' hlk hps hr =>
    -- `LExLoad ↦ LSilent`: the pair OPENS; the invariant is established from the label's data
    obtain ⟨agF, hlke, ⟨hst, hpr, hws, _⟩, _⟩ := hags' i ag hlk
    have hd : asrc = [] := hdf _ _ _ _ _ hps
    subst hd
    refine ⟨.LSilent, _, wpPfStep.PFSilent cF agF st' d' hlke
      (by rw [hst, hdev]; exact refusePstep.RFDrop _ _ _ _ _ _ hps), ?_⟩
    rw [himg, hlog, hpr]
    refine rfCfgUpd _ _ _ [] _ _ _ _ _ _ _ _ _ _ (List.append_nil _).symm hlen hags' hlk hlke
      (rfWsExloadR _ _ _ _ _ _ hws) ?_
    intro R hR
    rw [exloadPostRunDRes] at hR
    injection hR with hR
    subst hR
    exact ⟨aq, tvs, rfl, readOkDRf _ _ _ _ _ _ _ _ _ hws hr, rfWsLoadExload _ _ _ _ _ _ hws⟩
  | PFExStore cfg ag rl base data asrc vsrc k R st' d' hlk hps hnn hres hrb hrlen he hk =>
    -- `LExStore ↦ LRmw`: the pair CLOSES; the machine's `wRes` premise IS the guard
    obtain ⟨agF, hlke, ⟨hst, hpr, hws, hpd⟩, _⟩ := hags' i ag hlk
    obtain ⟨rfl, rfl⟩ : asrc = [] ∧ vsrc = [] := hdf _ _ _ _ _ hps
    obtain ⟨aq, tvs, hrts, hrok, hal⟩ := hpd R hres
    rw [hrb] at hrok hal
    have hkk : k = pcls agF.paSt (.LRmw aq rl base tvs data [] []) agF.paWs := by
      rw [hst, hk]
      exact (hfus _ _ _ _ _ _ _ _ _ aq tvs _ _ hps (rfWsRelp _ _ hws)).symm
    refine ⟨.LRmw aq rl base tvs data [] [], _, wpPfStep.PFRmw cF agF aq rl base tvs data [] []
      k st' d' hlke (by rw [hst, hdev]; exact refusePstep.RFFuse _ _ _ _ _ _ _ _ _ hps) hnn
      (by rw [← hrlen, hrts, List.length_map])
      (by rw [himg, hlog]; exact hrok)
      (by rw [hlog]; rw [hrts] at he; exact exclOkOfExclOkTs _ _ _ _ _ he) hkk, ?_⟩
    rw [himg, hlog, hpr]
    refine rfCfgUpd _ _ _ [⟨base, data, some i, k⟩] _ _ _ _ _ _ _ _ _ _ rfl hlen hags' hlk hlke
      (rfWsStore _ _ _ _ _ _ _ _ hal) ?_
    intro R0 hR0
    have hne : data.length ≠ 0 := by
      intro h; apply hnn
      cases data with
      | nil => rfl
      | cons _ _ => simp at h
    rw [storePostRunDResNone _ _ _ _ _ _ _ hne] at hR0
    cases hR0
  | PFIFetch cfg ag base tvs st' d' hlk hps hif =>
    -- O2 (deviation 4): log-only side condition, identity post-state
    obtain ⟨agF, hlke, ⟨hst, hpr, hws, hpd⟩, _⟩ := hags' i ag hlk
    refine ⟨.LIFetch base tvs, _, wpPfStep.PFIFetch cF agF base tvs st' d' hlke
      (by rw [hst, hdev]; exact refusePstep.RFKeep _ _ _ trivial hps)
      (by rw [himg, hlog]; exact hif), ?_⟩
    rw [himg, hlog, hpr]
    exact rfCfgUpd _ _ _ [] _ _ _ _ _ _ _ _ _ _ (List.append_nil _).symm hlen hags' hlk hlke
      hws hpd

/-! ## 7. The run level and the endpoint -/

theorem refuseRunStep (cF cS cS' : Wpcfg P D) :
    pclsErasable pcls → pclsFusable pstep pcls → pstepDepfree pstep →
    cfgWf cF → noPromises cF → rfCfg cF cS →
    wpPfRun pstep pcls cS cS' →
    ∃ cF', wpPfRun (refusePstep pstep) pcls cF cF' ∧ rfCfg cF' cS' ∧
      cfgWf cF' ∧ noPromises cF' := by
  rintro hcls hfus hdf hwf hnp hm ⟨i, l, hs⟩
  obtain ⟨lF, cF', hse, hm'⟩ := refuseStep pstep pcls i l cS cS' cF hcls hfus hdf hwf hm hs
  have hrun : wpPfRun (refusePstep pstep) pcls cF cF' := ⟨i, lF, hse⟩
  obtain ⟨_, hwf', hnp'⟩ :=
    wpPfRunRtcWpstep (refusePstep pstep) pcls cF cF' hwf hnp (rtc_once hrun)
  exact ⟨cF', hrun, hm', hwf', hnp'⟩

theorem refuseRtc (cF cS cS' : Wpcfg P D) :
    pclsErasable pcls → pclsFusable pstep pcls → pstepDepfree pstep →
    cfgWf cF → noPromises cF → rfCfg cF cS →
    rtc (wpPfRun pstep pcls) cS cS' →
    ∃ cF', rtc (wpPfRun (refusePstep pstep) pcls) cF cF' ∧ rfCfg cF' cS' := by
  intro hcls hfus hdf hwf hnp hm hrun
  refine rtc_ind_l (fun x => ∀ cF, cfgWf cF → noPromises cF → rfCfg cF x →
      ∃ cF', rtc (wpPfRun (refusePstep pstep) pcls) cF cF' ∧ rfCfg cF' cS') cS'
    (fun cF _ _ hm => ⟨cF, rtc_refl _, hm⟩) ?_ cS hrun cF hwf hnp hm
  intro x y hxy _ ih cF hwf hnp hm
  obtain ⟨cF1, hs1, hm1, hwf1, hnp1⟩ :=
    refuseRunStep pstep pcls cF x y hcls hfus hdf hwf hnp hm hxy
  obtain ⟨cF2, hs2, hm2⟩ := ih cF1 hwf1 hnp1 hm1
  exact ⟨cF2, rtc_l hs1 hs2, hm2⟩

/-- THE ENDPOINT (stage 2's deliverable): every DEPENDENCY-FREE pf run is matched, step for
step, by a pf run of the SAME program over the FUSED alphabet, with the same image, THE SAME
LOG, the same fabric and the same program states — NO pairing premise. -/
theorem refuseRun (img : Image) (d0 : D) (ps : List P) (c : Wpcfg P D) :
    pclsErasable pcls → pclsFusable pstep pcls → pstepDepfree pstep →
    rtc (wpPfRun pstep pcls) (wpInit img d0 ps) c →
    ∃ cF, rtc (wpPfRun (refusePstep pstep) pcls) (wpInit img d0 ps) cF ∧
      cF.pcImg = c.pcImg ∧ cF.pcLog = c.pcLog ∧ cF.pcDev = c.pcDev ∧
      (∀ (i : Nat) (agS : Wpagent P), c.pcAgs[i]? = some agS →
        ∃ agF, cF.pcAgs[i]? = some agF ∧ agF.paSt = agS.paSt) ∧
      pstepFused (refusePstep pstep) ∧ pstepDepfree (refusePstep pstep) := by
  intro hcls hfus hdf hrun
  have hnp : noPromises (wpInit img d0 ps : Wpcfg P D) := by
    intro i ag hlk
    simp only [wpInit, List.getElem?_map] at hlk
    cases hp : ps[i]? with
    | none => rw [hp] at hlk; cases hlk
    | some p => rw [hp] at hlk; injection hlk with hlk; subst hlk; rfl
  obtain ⟨cF, hrunF, himg, hlog, hdev, _, hags⟩ :=
    refuseRtc pstep pcls _ _ c hcls hfus hdf (cfgWfInit img d0 ps) hnp (rfCfgInit img d0 ps)
      hrun
  refine ⟨cF, hrunF, himg, hlog, hdev, fun i agS hlk => ?_, refusePstepFused pstep,
    refusePstepDepfree pstep hdf⟩
  obtain ⟨agF, hlke, hst, _⟩ := hags i agS hlk
  exact ⟨agF, hlke, hst⟩

/-- STAGE 2's PAYOFF: T2 containment for a DEPENDENCY-FREE run that emits the SPLIT alphabet;
`wpPfBridgeLog`'s `pstepFused` premise is discharged by construction. -/
theorem refuseBridgeLog (img : Image) (d0 : D) (ps : List P) (c : Wpcfg P D) :
    pclsErasable pcls → pclsFusable pstep pcls → pstepDepfree pstep →
    rtc (wpPfRun pstep pcls) (wpInit img d0 ps) c →
    ∃ E, execWf E ∧ exImg E = img ∧ exLog E = c.pcLog := by
  intro hcls hfus hdf hrun
  obtain ⟨cF, hrunF, _, hlog, _⟩ := refuseRun pstep pcls img d0 ps c hcls hfus hdf hrun
  obtain ⟨E, hE, hEimg, hElog⟩ := wpPfBridgeLog (refusePstep pstep) pcls img d0 ps cF
    (refusePstepDepfree pstep hdf) (refusePstepFused pstep) hrunF
  exact ⟨E, hE, hEimg, hElog.trans hlog⟩

end refuse

/-! ## 8. THE COMPOSITION: T2 for the dependency-carrying, split instance -/

section compose

variable {P D : Type}
variable (pstep : P → D → Wlabel → P → D → Prop)
variable (pcls : P → Wlabel → Wstate → WmClass)

/-- The class premise transfers to the erased LTS. -/
theorem pclsFusableErase :
    pclsErasable pcls → pclsFusable pstep pcls → pclsFusable (erasePstep pstep) pcls := by
  intro her hfu p d rl base data asrc vsrc p' d' aq tvs wF wS hst hrelp
  obtain ⟨l0, hl0, hs⟩ := hst
  cases l0 <;> simp only [eraseLbl, reduceCtorEq, Wlabel.LExStore.injEq] at hl0
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hl0
  exact (hfu _ _ _ _ _ _ _ _ _ aq tvs wF wS hs hrelp).trans (her _ _ wS wS rfl).symm

/-- T2 FINAL for the dependency-carrying, split-alphabet instance: no `pstepDepfree`, no
`pstepFused`, NO PAIRING PREMISE. -/
theorem t2Bridge (img : Image) (d0 : D) (ps : List P) (c : Wpcfg P D) :
    pclsErasable pcls → pclsFusable pstep pcls →
    rtc (wpPfRun pstep pcls) (wpInit img d0 ps) c →
    ∃ E, execWf E ∧ exImg E = img ∧ exLog E = c.pcLog := by
  intro hcls hfus hrun
  obtain ⟨ce, hrune, hme⟩ := eraseRtc pstep pcls _ _ c hcls (erCfgInit img d0 ps) hrun
  obtain ⟨E, hE, himg, hlog⟩ := refuseBridgeLog (erasePstep pstep) pcls img d0 ps ce hcls
    (pclsFusableErase pstep pcls hcls hfus) (erasePstepDepfree pstep) hrune
  exact ⟨E, hE, himg, hlog.trans (erCfgLog _ _ hme)⟩

end compose

end Weak
