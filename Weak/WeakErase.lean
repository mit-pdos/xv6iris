/-
Weak: **the erasure simulation** (T2 carrier, A2 stage 1).

Rocq: `iris/WeakErase.v` @ xxvzwolszwmp (1cc222280).

The Rocq header, in substance (design: `claude-notes/design/weak-memory-srvwmo.md`, "THE T2
CARRIER PIPELINE (A2)", stage 1):

THE PROBLEM.  `WeakPromiseBridge`'s axiomatic projection (`wpPfStepMstep` and everything above
it up to `wpPfBridge`) is gated on `lbDepfree`: the axiomatic tier steps with the
DEPENDENCY-FREE `loadPostRun`/`storePostRun`, so a machine step that raises a view through an
operand list has no `mstep` image.  The D2 event instance FAILS that gate (its stores carry real
`asrc`/`vsrc` and it emits `LRegW`/`LCtrl`/`LInstr`), so T2 could not be stated for it.

THE MOVE.  Erase the dependencies from the LABELS and simulate.  `eraseLbl` blanks every operand
list and sends the three dependency-only labels to `LSilent`; `erasePstep` is the program LTS read
through that map.  Every erased label is `lbDepfree` BY CONSTRUCTION, and the simulation says the
erased run exists and has the SAME LOG (and image, program states and fabric).

WHY A ≤-SIMULATION AND NOT AN EQUALITY.  Dropping the operand lists lowers every dependency view
to `0`, and dropping `LInstr` leaves the erased agent's `wLdv`/`wRes`/`wTbank` un-reset (and,
through the un-reset bank, its `wVcap` raised past the instance's).  What IS true is that every
erased view is BELOW its instance counterpart (`erWs`), and every side condition of the pf machine
is ANTI-monotone in the views: `readable`'s no-write window `(t, vpre ⊔ coh a]` shrinks with a lower
floor (`writesInMonoHi`); `readOkD`'s `lat` conjunct, `exclOk` and `exclOkTs` are LOG-ONLY; the pf
fragment has NO `fulfilOk` at all, so `wVcap`/`wVwNew`/`rvView` never appear in a side condition.

THE FOUR COMPONENTS OF `erWs`: `wsLeNc` (the monotone views minus the control view; `wVcap` is
deliberately absent, since W-TV's consumption lets the erased `wVcap` overtake the instance's);
`wRelp` EQUAL (a toggle moved by fence bits and stores, which the erasure preserves; `wPub`'s
monotonicity and the message class need it); `fwdLe` (the forward bank, semantically — since D-7r
both sides bank `(t, 0)`, so this is the reflexive case); `resRel` (ONE-WAY: instance `some R` ⟹
erased `some R'` with the same `rvBase`/`rvTs` and a lower `rvView`, because `LInstr ↦ LSilent`
lets the instance clear `wRes` where the erased side keeps it).

NOT DONE HERE: `lbFused` is stage 2's gate (re-fusion, `WeakRefuse`); stage 3 is the existing
projection.

**Deviations from Rocq.**

1. NAMES: as `Weak/WeakMem.lean` deviation 1 (lowerCamelCase).  The Rocq `Reflexive` /
   `Transitive` instances `fwd_le_refl`, `res_rel_refl`, `er_ws_refl`, `er_ws_trans` are the
   theorems `fwdLeRefl`, `resRelRefl`, `erWsRefl`, `erWsTrans` plus a `Trans` instance.
   `fwd_le` is a DUPLICATED Rocq name (also in `AxViolSubsume`), hence file-qualified:
   `WeakErase.fwdLe`.
2. VOCABULARY: as `WeakPromise` deviation 2 / `WeakPromiseBridge` deviation 2.
3. The section variables `pstep` and `pcls` are explicit arguments of every declaration that uses
   them, in Rocq's order (`WeakPromiseBridge` deviation 3).
4. CONVERSIONS (`WeakMem` deviation 3): `loadVpreD ws aq 0 = loadVpre ws aq` is propositional in
   Lean (`loadVpreD0`); `exloadPostRunDEr` rewrites with it where Rocq unfolds by conversion.
   `srcsView ws [] = 0` stays definitional, so the erased arms still meet their side conditions
   at view `0` by conversion.  Statements unchanged.
5. `exloadPostRunDEr`'s proof follows Lean's `exloadPostRunD` (its byte fold is `loadPostBytes` at
   the plain pre-view, D-2r) directly via `loadPostFoldEr`, instead of going through
   `load_post_run_d_er … 0 0`.  Statement unchanged.
6. O2 — THE INSTRUCTION FETCH (Lean-only label `LIFetch`, `Weak/WeakPromise.lean` deviation 8;
   `WeakPromiseBridge` deviation 6):
   - `eraseLbl (LIFetch base tvs) = LIFetch base tvs` (a fetch carries no operand list, and is
     `lbDepfree`; the erasure is the identity on it, so `eraseLblDepfreeId` stays true).
   - `eraseStep` gains the `PFIFetch` arm: `ifetchOk` reads only the image and the log (both
     equal), and the `Wstate` is unchanged on both sides.
   - STAGE C (owner ruling Q-C3, `notes/weak-port-o2-stageC.md`): the bridge treats a fetch as a
     stutter (`WeakPromiseBridge` deviation 6), so `eraseBridgeLog` has Rocq's statement (Stage
     B's `pstepNoFetch` premise, `erasePstepNoFetch` and `eraseBridgeLogFetch` are deleted).

**Rocq → Lean name map.**  `erase_lbl` ↦ `eraseLbl`; `erase_lbl_{depfree,depfree_id,idem,
lat_free,fused,ldepfree}` ↦ `eraseLbl{Depfree,DepfreeId,Idem,LatFree,Fused,Ldepfree}`; `fwd_le` ↦
`WeakErase.fwdLe`; `fwd_le_refl` ↦ `fwdLeRefl`; `res_rel` ↦ `resRel`; `res_rel_refl` ↦
`resRelRefl`; `er_ws` ↦ `erWs`; `er_ws_{ws_le_nc,relp,fwd,res,refl,trans}` ↦
`erWs{WsLeNc,Relp,Fwd,Res,Refl,Trans}`; `er_ws_load_vpre_d` ↦ `erWsLoadVpreD`; `readable_er` ↦
`readableEr`; `read_ok_d_er` ↦ `readOkDEr`; `load_post_at_er` ↦ `loadPostAtEr`;
`load_post_at_ldv_er` ↦ `loadPostAtLdvEr`; `load_post_fold_er` ↦ `loadPostFoldEr`;
`load_post_fold_ldv_er` ↦ `loadPostFoldLdvEr`; `store_post_d_er` ↦ `storePostDEr`;
`store_post_fold_er` ↦ `storePostFoldEr`; `ctrl_post_er` ↦ `ctrlPostEr`; `fence_post_er` ↦
`fencePostEr`; `instr_post_er` ↦ `instrPostEr`; `er_ws_regw_r` ↦ `erWsRegwR`; `er_ws_ctrl_r` ↦
`erWsCtrlR`; `er_ws_instr_r` ↦ `erWsInstrR`; `load_post_run_d_er` ↦ `loadPostRunDEr`;
`store_post_run_d_er` ↦ `storePostRunDEr`; `ldv_of_er` ↦ `ldvOfEr`; `exload_post_run_d_er` ↦
`exloadPostRunDEr`; `{read_ok_d,load_post_run_d,store_post_run_d,exload_post_run_d}_er0` ↦
`{readOkD,loadPostRunD,storePostRunD,exloadPostRunD}Er0`; `erase_pstep` ↦ `erasePstep`;
`erase_pstep_{intro,depfree,lat_free,fused,gates}` ↦ `erasePstep{Intro,Depfree,LatFree,Fused,
Gates}`; `pcls_erasable` ↦ `pclsErasable`; `er_ag` ↦ `erAg`; `er_cfg` ↦ `erCfg`;
`er_cfg_{log,img,dev,init,upd}` ↦ `erCfg{Log,Img,Dev,Init,Upd}`; `erase_step` ↦ `eraseStep`;
`erase_run_step` ↦ `eraseRunStep`; `erase_rtc` ↦ `eraseRtc`; `erase_run` ↦ `eraseRun`;
`erase_bridge_log` ↦ `eraseBridgeLog`.

**Not ported:** nothing — every Rocq definition and lemma has a Lean twin.

**Statements checked** (by hand, against Rocq): all of them; the changed ones are `eraseLbl`
(+ arm), `eraseStep` (+ arm, same statement), deviation 6.
-/
import Weak.WeakPromiseBridge

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std Wlabel

/-! ## 1. The label erasure -/

/-- Blank every operand list; send the three dependency-only labels to `LSilent`.  Everything
else is kept VERBATIM, which is what makes the log, the message classes and the axiomatic
projection agree on the nose.  (Deviation 6: a fetch is kept as is.  W13 (F-dep) (1): `LDev`'s operand lists
are blanked like every other label's.) -/
def eraseLbl (l : Wlabel) : Wlabel :=
  match l with
  | LSilent => LSilent
  | LLoad aq lat base tvs _ => LLoad aq lat base tvs []
  | LStore rl base data _ _ => LStore rl base data [] []
  | LRmw aq rl base tvs data _ _ => LRmw aq rl base tvs data [] []
  | LFence pr pw sr sw => LFence pr pw sr sw
  | LDev kd ba bs _ _ => LDev kd ba bs [] []
  | LRegW _ _ => LSilent
  | LCtrl _ => LSilent
  | LInstr => LSilent
  | LExLoad aq base tvs _ => LExLoad aq base tvs []
  | LExStore rl base data _ _ => LExStore rl base data [] []
  | LIFetch base tvs => LIFetch base tvs

/-- THE POINT: the gate holds of every erased label BY CONSTRUCTION. -/
theorem eraseLblDepfree (l : Wlabel) : lbDepfree (eraseLbl l) := by
  cases l <;> simp [eraseLbl, lbDepfree]

/-- On the dependency-free fragment the erasure is the identity. -/
theorem eraseLblDepfreeId (l : Wlabel) : lbDepfree l → eraseLbl l = l := by
  intro h
  cases l <;> simp_all [eraseLbl, lbDepfree]

theorem eraseLblIdem (l : Wlabel) : eraseLbl (eraseLbl l) = eraseLbl l :=
  eraseLblDepfreeId _ (eraseLblDepfree l)

/-- The `lat` bit and the fused/split shape are label data the erasure copies. -/
theorem eraseLblLatFree (l : Wlabel) : latFree l → latFree (eraseLbl l) := by
  intro h
  cases l <;> simp_all [eraseLbl, latFree]

theorem eraseLblFused (l : Wlabel) : lbFused l → lbFused (eraseLbl l) := by
  intro h
  cases l <;> simp_all [eraseLbl, lbFused]

theorem eraseLblLdepfree (l : Wlabel) : lbLdepfree (eraseLbl l) := by
  cases l <;> simp [eraseLbl, lbLdepfree]

/-! ## 2. The state relation -/

/-- The forward bank, SEMANTICALLY: what a read of timestamp `t` at byte `a` takes away from the
bank (duplicated Rocq name, file-qualified). -/
def WeakErase.fwdLe (we wi : Wstate) : Prop :=
  ∀ (aq : Bool) (a : Int) (t : Nat), fwdView we aq a t ≤ fwdView wi aq a t

theorem fwdLeRefl (w : Wstate) : WeakErase.fwdLe w w := fun _ _ _ => Nat.le_refl _

/-- The reservation, ONE-WAY: wherever the INSTANCE holds a reservation the erased side holds
one with the same base and timestamp column and a lower banked view. -/
def resRel (we wi : Wstate) : Prop :=
  ∀ Ri : Wresv, wi.wRes = some Ri →
    ∃ Re : Wresv, we.wRes = some Re ∧ Re.rvBase = Ri.rvBase ∧
      Re.rvTs = Ri.rvTs ∧ Re.rvView ≤ Ri.rvView

theorem resRelRefl (w : Wstate) : resRel w w :=
  fun R h => ⟨R, h, rfl, rfl, Nat.le_refl _⟩

/-- THE ERASURE'S STATE RELATION: `we` (the ERASED agent's state) is below `wi` (the
INSTANCE agent's). -/
def erWs (we wi : Wstate) : Prop :=
  wsLeNc we wi ∧ we.wRelp = wi.wRelp ∧ WeakErase.fwdLe we wi ∧ resRel we wi

theorem erWsWsLeNc (we wi : Wstate) : erWs we wi → wsLeNc we wi := fun h => h.1
theorem erWsRelp (we wi : Wstate) : erWs we wi → we.wRelp = wi.wRelp := fun h => h.2.1
theorem erWsFwd (we wi : Wstate) : erWs we wi → WeakErase.fwdLe we wi := fun h => h.2.2.1
theorem erWsRes (we wi : Wstate) : erWs we wi → resRel we wi := fun h => h.2.2.2

theorem erWsRefl (w : Wstate) : erWs w w :=
  ⟨wsLeNcRefl w, rfl, fwdLeRefl w, resRelRefl w⟩

/-- Transitive because each of its four components is. -/
theorem erWsTrans {w1 w2 w3 : Wstate} : erWs w1 w2 → erWs w2 w3 → erWs w1 w3 := by
  rintro ⟨hle1, hrp1, hfw1, hrs1⟩ ⟨hle2, hrp2, hfw2, hrs2⟩
  refine ⟨wsLeNcTrans hle1 hle2, hrp1.trans hrp2,
    fun aq a t => Nat.le_trans (hfw1 aq a t) (hfw2 aq a t), fun R3 hR3 => ?_⟩
  obtain ⟨R2, hR2, hb2, ht2, hv2⟩ := hrs2 R3 hR3
  obtain ⟨R1, hR1, hb1, ht1, hv1⟩ := hrs1 R2 hR2
  exact ⟨R1, hR1, hb1.trans hb2, ht1.trans ht2, Nat.le_trans hv1 hv2⟩

instance : Trans erWs erWs erWs := ⟨erWsTrans⟩

/-- The `loadVpre`/`coh` consequences the read arms consume. -/
theorem erWsLoadVpreD (we wi : Wstate) (aq : Bool) (vae vai : Nat) :
    erWs we wi → vae ≤ vai → loadVpreD we aq vae ≤ loadVpreD wi aq vai := by
  intro her hv
  have h1 := wsLeNcVrNew _ _ (erWsWsLeNc _ _ her)
  have h2 := wsLeNcVRel _ _ (erWsWsLeNc _ _ her)
  cases aq <;> simp only [loadVpreD, loadVpre, Bool.false_eq_true, ↓reduceIte] <;> omega

/-! ### Readability and the read side condition are ANTI-monotone

`readable` forbids a write in the window `(t, vpre ⊔ coh a]`.  Lowering `vpre` or `coh` SHRINKS
the window, so the erased agent can read everything the instance agent can. -/

theorem readableEr (img : Image) (log : List Wmsg) (we wi : Wstate) (vpe vpi : Nat) (a : Int)
    (t : Nat) :
    coh we a ≤ coh wi a → vpe ≤ vpi →
    readable img log wi vpi a t → readable img log we vpe a t := by
  rintro hc hv ⟨hs, hn⟩
  exact ⟨hs, fun hw => hn (writesInMonoHi log a t _ _ (by omega) hw)⟩

theorem readOkDEr (img : Image) (log : List Wmsg) (we wi : Wstate) (aq lat : Bool) (base : Int)
    (tvs : List (Nat × BitVec 8)) (vae vai : Nat) :
    erWs we wi → vae ≤ vai →
    readOkD img log wi aq lat base tvs vai →
    readOkD img log we aq lat base tvs vae := by
  intro her hv hr j t v hj
  obtain ⟨h1, h2, h3⟩ := hr j t v hj
  exact ⟨h1, readableEr img log we wi _ _ _ t
    (wsLeNcCoh _ _ _ (erWsWsLeNc _ _ her)) (erWsLoadVpreD we wi aq vae vai her hv) h2, h3⟩

/-! ### `erWs` is preserved by every step function -/

theorem loadPostAtEr (we wi : Wstate) (aq : Bool) (vpe vpi : Nat) (a : Int) (t : Nat) :
    erWs we wi → vpe ≤ vpi →
    erWs (loadPostAt we aq vpe a t) (loadPostAt wi aq vpi a t) := by
  rintro ⟨⟨hc, h1, h2, h3, h4, h5, h6⟩, hrp, hf, _⟩ hv
  have hfa := hf aq a t
  refine ⟨⟨fun b => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hrp, hf, ?_⟩
  · by_cases hb : b = a
    · subst hb
      rw [cohLoadPostAtEq, cohLoadPostAtEq]
      have := hc b
      omega
    · rw [cohLoadPostAtNe _ _ _ _ _ _ hb, cohLoadPostAtNe _ _ _ _ _ _ hb]; exact hc b
  · simp only [loadPostAt]; omega
  · simp only [loadPostAt]; omega
  · cases aq <;> simp only [loadPostAt, Bool.false_eq_true, ↓reduceIte] <;> omega
  · cases aq <;> simp only [loadPostAt, Bool.false_eq_true, ↓reduceIte] <;> omega
  · simp only [loadPostAt]; omega
  · simp only [loadPostAt]; omega
  · -- A2-s3: both sides CLEAR the reservation here, so `resRel` is vacuous.
    intro Ri hRi
    simp [loadPostAt] at hRi

theorem loadPostAtLdvEr (we wi : Wstate) (aq : Bool) (vpe vpi : Nat) (a : Int) (t : Nat) :
    erWs we wi → vpe ≤ vpi → we.wLdv ≤ wi.wLdv →
    (loadPostAt we aq vpe a t).wLdv ≤ (loadPostAt wi aq vpi a t).wLdv := by
  intro her hv hldv
  have := erWsFwd _ _ her aq a t
  simp only [loadPostAt]
  omega

theorem loadPostFoldEr (aq : Bool) (vpe vpi : Nat) (ats : List (Int × Nat)) (we wi : Wstate) :
    erWs we wi → vpe ≤ vpi →
    erWs (ats.foldl (fun w at_ => loadPostAt w aq vpe at_.1 at_.2) we)
      (ats.foldl (fun w at_ => loadPostAt w aq vpi at_.1 at_.2) wi) := by
  induction ats generalizing we wi with
  | nil => intro h _; exact h
  | cons x l ih => intro h hv; exact ih _ _ (loadPostAtEr _ _ _ _ _ _ _ h hv) hv

theorem loadPostFoldLdvEr (aq : Bool) (vpe vpi : Nat) (ats : List (Int × Nat)) (we wi : Wstate) :
    erWs we wi → vpe ≤ vpi → we.wLdv ≤ wi.wLdv →
    (ats.foldl (fun w at_ => loadPostAt w aq vpe at_.1 at_.2) we).wLdv
      ≤ (ats.foldl (fun w at_ => loadPostAt w aq vpi at_.1 at_.2) wi).wLdv := by
  induction ats generalizing we wi with
  | nil => intro _ _ h; exact h
  | cons x l ih =>
    intro h hv hldv
    exact ih _ _ (loadPostAtEr _ _ _ _ _ _ _ h hv) hv (loadPostAtLdvEr _ _ _ _ _ _ _ h hv hldv)

/-- D-7r: the two sides bank the SAME view column (`0`), so no `vfe ≤ vfi` premise. -/
theorem storePostDEr (we wi : Wstate) (rl : Bool) (vfe vfi : Nat) (a : Int) (t : Nat) :
    erWs we wi → erWs (storePostD we rl vfe a t) (storePostD wi rl vfi a t) := by
  rintro ⟨⟨hc, h1, h2, h3, h4, h5, h6⟩, hrp, hf, _⟩
  rw [storePostDVf, storePostDVf]
  refine ⟨⟨fun b => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, rfl, fun aq' b t' => ?_, ?_⟩
  · by_cases hb : b = a
    · subst hb
      rw [cohStorePostEq, cohStorePostEq]
      have := hc b
      omega
    · rw [cohStorePostNe _ _ _ _ _ hb, cohStorePostNe _ _ _ _ _ hb]; exact hc b
  · simp only [storePost]; omega
  · simp only [storePost]; omega
  · simp only [storePost]; omega
  · simp only [storePost]; omega
  · cases rl <;> simp only [storePost, Bool.false_eq_true, ↓reduceIte] <;> omega
  · simp only [storePost, hrp]
    by_cases hb : (wi.wRelp || rl) = true <;>
      simp only [hb, Bool.false_eq_true, ↓reduceIte] <;> omega
  · cases aq'
    · by_cases hb : b = a
      · subst hb
        exact Nat.le_of_eq (by simp only [fwdView, storePost, lookupInsert, Bool.false_eq_true,
          ↓reduceIte])
      · have e1 : fwdView (storePost we rl a t) false b t' = fwdView we false b t' := by
          simp only [fwdView, storePost, lookupInsertNe (Ne.symm hb)]
        have e2 : fwdView (storePost wi rl a t) false b t' = fwdView wi false b t' := by
          simp only [fwdView, storePost, lookupInsertNe (Ne.symm hb)]
        rw [e1, e2]; exact hf false b t'
    · rw [fwdViewAq, fwdViewAq]; exact Nat.le_refl _
  · intro Ri hRi
    simp [storePost] at hRi

theorem storePostFoldEr (rl : Bool) (vfe vfi t : Nat) (as_ : List Int) (we wi : Wstate) :
    erWs we wi →
    erWs (as_.foldl (fun w a => storePostD w rl vfe a t) we)
      (as_.foldl (fun w a => storePostD w rl vfi a t) wi) := by
  induction as_ generalizing we wi with
  | nil => intro h; exact h
  | cons x l ih => intro h; exact ih _ _ (storePostDEr _ _ _ _ _ _ _ h)

/-- NO relation between the two control views is asked for, or available. -/
theorem ctrlPostEr (we wi : Wstate) (ve vi : Nat) :
    erWs we wi → erWs (ctrlPost we ve) (ctrlPost wi vi) := fun h => h

theorem fencePostEr (we wi : Wstate) (pr pw sr sw : Bool) :
    erWs we wi → erWs (fencePost we pr pw sr sw) (fencePost wi pr pw sr sw) := by
  rintro ⟨⟨hc, h1, h2, h3, h4, h5, h6⟩, hrp, hf, hr⟩
  refine ⟨⟨fun b => hc b, h1, h2, ?_, ?_, h5, h6⟩, ?_, hf, ?_⟩
  · cases sr <;> cases pr <;> cases pw <;>
      simp only [fencePost, Bool.false_eq_true, ↓reduceIte] <;> omega
  · cases sw <;> cases pr <;> cases pw <;>
      simp only [fencePost, Bool.false_eq_true, ↓reduceIte] <;> omega
  · simp only [fencePost, hrp]
  · -- A2-s3: a REAL fence clears the reservation on both sides (vacuous); the all-false fence
    -- preserves it on both.
    intro Ri hRi
    by_cases hb : (pr || pw || sr || sw) = true
    · simp [fencePost, hb] at hRi
    · simp only [fencePost, hb, Bool.false_eq_true, ↓reduceIte] at hRi ⊢
      exact hr Ri hRi

theorem instrPostEr (we wi : Wstate) : erWs we wi → erWs (instrPost we) (instrPost wi) := by
  rintro ⟨hle, hrp, hf, _⟩
  exact ⟨hle, hrp, hf, fun Ri hRi => by simp [instrPost] at hRi⟩

/-! THE THREE ONE-SIDED (divergence) LEMMAS: the erased side takes a `PFSilent` where the
instance takes a dependency-only arm. -/

theorem erWsRegwR (we wi : Wstate) (rd v : Nat) : erWs we wi → erWs we (regwPost wi rd v) :=
  fun h => h

theorem erWsCtrlR (we wi : Wstate) (v : Nat) : erWs we wi → erWs we (ctrlPost wi v) :=
  fun h => h

/-- `LInstr ↦ LSilent` is the ONE place `resRel`'s one-wayness is used. -/
theorem erWsInstrR (we wi : Wstate) : erWs we wi → erWs we (instrPost wi) := by
  rintro ⟨hle, hrp, hf, _⟩
  exact ⟨hle, hrp, hf, fun Ri hRi => by simp [instrPost] at hRi⟩

/-! ### The RUN-level wrappers the machine arms actually apply -/

theorem loadPostRunDEr (we wi : Wstate) (aq : Bool) (vae vai : Nat) (base : Int)
    (ts : List Nat) :
    erWs we wi → vae ≤ vai →
    erWs (loadPostRunD we aq vae base ts) (loadPostRunD wi aq vai base ts) := by
  intro her hv
  unfold loadPostRunD loadPostBytesD
  exact ctrlPostEr _ _ _ _
    (loadPostFoldEr aq _ _ _ we wi her (erWsLoadVpreD we wi aq vae vai her hv))

/-- D-7r: BOTH operand-view premises are gone. -/
theorem storePostRunDEr (we wi : Wstate) (rl : Bool) (vae vai vde vdi : Nat) (base : Int)
    (n t : Nat) :
    erWs we wi →
    erWs (storePostRunD we rl vae vde base n t) (storePostRunD wi rl vai vdi base n t) := by
  intro her
  unfold storePostRunD storePostBytesD
  exact ctrlPostEr _ _ _ _ (storePostFoldEr rl _ _ t _ we wi her)

/-- The reservation's banked view, computed from a ZEROED `wLdv` (`wsLdv0 = instrPost`). -/
theorem ldvOfEr (we wi : Wstate) (aq : Bool) (vae vai : Nat) (base : Int) (ts : List Nat) :
    erWs we wi → vae ≤ vai → ldvOf we aq vae base ts ≤ ldvOf wi aq vai base ts := by
  intro her hv
  have hi := instrPostEr we wi her
  exact loadPostFoldLdvEr aq _ _ (loadRunAts base ts) (instrPost we) (instrPost wi) hi
    (erWsLoadVpreD _ _ aq vae vai hi hv) (Nat.le_refl 0)

/-- D-2r: THE OPERAND-VIEW PREMISE IS GONE — the two sides erase at ARBITRARY address views. -/
theorem exloadPostRunDEr (we wi : Wstate) (aq : Bool) (vae vai : Nat) (base : Int)
    (ts : List Nat) :
    erWs we wi →
    erWs (exloadPostRunD we aq vae base ts) (exloadPostRunD wi aq vai base ts) := by
  intro her
  have hv : loadVpre we aq ≤ loadVpre wi aq := by
    have := erWsLoadVpreD we wi aq 0 0 her (Nat.le_refl 0)
    rwa [loadVpreD0, loadVpreD0] at this
  obtain ⟨hle, hrp, hf, _⟩ := loadPostFoldEr aq _ _
    (List.zipWith (fun (j : Nat) t => (base + (j : Int), t)) (List.range' 0 ts.length) ts)
    we wi her hv
  refine ⟨hle, hrp, hf, fun Ri hRi => ?_⟩
  rw [exloadPostRunDRes, Option.some.injEq] at hRi
  subst hRi
  exact ⟨⟨base, ts, ldvOf we aq 0 base ts⟩, exloadPostRunDRes we aq vae base ts, rfl, rfl,
    ldvOfEr we wi aq 0 0 base ts her (Nat.le_refl 0)⟩

/-! ### The AT-ZERO instances the machine arms actually meet -/

theorem readOkDEr0 (img : Image) (log : List Wmsg) (we wi : Wstate) (aq lat : Bool) (base : Int)
    (tvs : List (Nat × BitVec 8)) (vai : Nat) :
    erWs we wi → readOkD img log wi aq lat base tvs vai →
    readOkD img log we aq lat base tvs 0 :=
  fun her hr => readOkDEr img log we wi aq lat base tvs 0 vai her (Nat.zero_le _) hr

theorem loadPostRunDEr0 (we wi : Wstate) (aq : Bool) (vai : Nat) (base : Int) (ts : List Nat) :
    erWs we wi → erWs (loadPostRunD we aq 0 base ts) (loadPostRunD wi aq vai base ts) :=
  fun her => loadPostRunDEr we wi aq 0 vai base ts her (Nat.zero_le _)

theorem storePostRunDEr0 (we wi : Wstate) (rl : Bool) (vai vdi : Nat) (base : Int) (n t : Nat) :
    erWs we wi →
    erWs (storePostRunD we rl 0 0 base n t) (storePostRunD wi rl vai vdi base n t) :=
  fun her => storePostRunDEr we wi rl 0 vai 0 vdi base n t her

theorem exloadPostRunDEr0 (we wi : Wstate) (aq : Bool) (vai : Nat) (base : Int)
    (ts : List Nat) :
    erWs we wi → erWs (exloadPostRunD we aq 0 base ts) (exloadPostRunD wi aq vai base ts) :=
  fun her => exloadPostRunDEr we wi aq 0 vai base ts her

/-! ## 3. The erased machine and the configuration relation -/

section erase

variable {P D : Type}
variable (pstep : P → D → Wlabel → P → D → Prop)
variable (pcls : P → Wlabel → Wstate → WmClass)

/-- THE ERASED PROGRAM LTS: the original label carried existentially, over the SAME program
states. -/
def erasePstep (p : P) (d : D) (l : Wlabel) (p' : P) (d' : D) : Prop :=
  ∃ l0, l = eraseLbl l0 ∧ pstep p d l0 p' d'

theorem erasePstepIntro (p : P) (d : D) (l : Wlabel) (p' : P) (d' : D) :
    pstep p d l p' d' → erasePstep pstep p d (eraseLbl l) p' d' :=
  fun h => ⟨l, rfl, h⟩

/-- THE GATE, DISCHARGED BY CONSTRUCTION — the whole point of stage 1. -/
theorem erasePstepDepfree : pstepDepfree (erasePstep pstep) := by
  rintro p d l p' d' ⟨l0, rfl, _⟩
  exact eraseLblDepfree l0

/-- The other two alphabet premises are INHERITED (not discharged). -/
theorem erasePstepLatFree :
    (∀ p d l p' d', pstep p d l p' d' → latFree l) →
    ∀ p d l p' d', erasePstep pstep p d l p' d' → latFree l := by
  rintro h p d l p' d' ⟨l0, rfl, hs⟩
  exact eraseLblLatFree _ (h p d l0 p' d' hs)

theorem erasePstepFused : pstepFused pstep → pstepFused (erasePstep pstep) := by
  rintro h p d l p' d' ⟨l0, rfl, hs⟩
  exact eraseLblFused _ (h p d l0 p' d' hs)

/-- THE THREE ALPHABET GATES IN ONE PLACE. -/
theorem erasePstepGates :
    (∀ p d l p' d', pstep p d l p' d' → latFree l) → pstepFused pstep →
    pstepDepfree (erasePstep pstep) ∧ pstepFused (erasePstep pstep) ∧
    (∀ p d l p' d', erasePstep pstep p d l p' d' → latFree l) :=
  fun hlf hfu =>
    ⟨erasePstepDepfree pstep, erasePstepFused pstep hfu, erasePstepLatFree pstep hlf⟩

/-- THE MESSAGE-CLASS PREMISE: the class does not read the operand lists and reads the state only
through `wRelp` (what `WeakEvInst.pcls_ev` does). -/
def pclsErasable : Prop :=
  ∀ (p : P) (l : Wlabel) (we wi : Wstate), we.wRelp = wi.wRelp →
    pcls p (eraseLbl l) we = pcls p l wi

/-! ### The configuration relation -/

def erAg (age agi : Wpagent P) : Prop :=
  age.paSt = agi.paSt ∧ age.paProm = agi.paProm ∧ erWs age.paWs agi.paWs

/-- `erCfg ce c` — "`ce` (the ERASED configuration) simulates `c`": image, LOG and fabric equal;
per agent, the same program state and promise set, and `erWs`. -/
def erCfg (ce c : Wpcfg P D) : Prop :=
  ce.pcImg = c.pcImg ∧ ce.pcLog = c.pcLog ∧ ce.pcDev = c.pcDev ∧
  ce.pcAgs.length = c.pcAgs.length ∧
  ∀ (i : Nat) (agi : Wpagent P), c.pcAgs[i]? = some agi →
    ∃ age, ce.pcAgs[i]? = some age ∧ erAg age agi

theorem erCfgLog (ce c : Wpcfg P D) : erCfg ce c → ce.pcLog = c.pcLog := fun h => h.2.1

theorem erCfgImg (ce c : Wpcfg P D) : erCfg ce c → ce.pcImg = c.pcImg := fun h => h.1

theorem erCfgDev (ce c : Wpcfg P D) : erCfg ce c → ce.pcDev = c.pcDev := fun h => h.2.2.1

theorem erCfgInit (img : Image) (d0 : D) (ps : List P) :
    erCfg (wpInit img d0 ps : Wpcfg P D) (wpInit img d0 ps) :=
  ⟨rfl, rfl, rfl, rfl, fun _ agi h => ⟨agi, h, rfl, rfl, erWsRefl _⟩⟩

/-- The one configuration-update lemma every arm of the simulation uses. -/
theorem erCfgUpd (imge img : Image) (lge lg : List Wmsg) (dv : D)
    (agse ags : List (Wpagent P)) (i : Nat) (age agi : Wpagent P) (st' : P) (wse wsi : Wstate)
    (pr : GSet Nat) :
    imge = img → lge = lg →
    agse.length = ags.length →
    (∀ (j : Nat) (agj : Wpagent P), ags[j]? = some agj →
      ∃ agej, agse[j]? = some agej ∧ erAg agej agj) →
    ags[i]? = some agi → agse[i]? = some age →
    erWs wse wsi →
    erCfg (⟨imge, lge, dv, agse.set i ⟨st', wse, pr⟩⟩ : Wpcfg P D)
      ⟨img, lg, dv, ags.set i ⟨st', wsi, pr⟩⟩ := by
  rintro rfl rfl hlen hags _ hie her
  obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.mp hie
  refine ⟨rfl, rfl, rfl, by simp only [List.length_set, hlen], fun j agj hj => ?_⟩
  rcases lookupSetCases hj with ⟨rfl, rfl⟩ | ⟨hne, hj⟩
  · refine ⟨⟨st', wse, pr⟩, ?_, rfl, rfl, her⟩
    rw [List.getElem?_set]
    simp [hlt]
  · obtain ⟨agej, hlk, hrel⟩ := hags j agj hj
    refine ⟨agej, ?_, hrel⟩
    rw [List.getElem?_set]
    simp only [Ne.symm hne, ↓reduceIte]
    exact hlk

/-! ## 4. THE STEP SIMULATION

Every instance step erases: the read arms weaken by `readOkDEr`, the write arms carry NO fulfil
check on the pf fragment, `exclOk`/`exclOkTs` are log-only (and the reservation's timestamp
column is equal), and the class is pinned by `pclsErasable`. -/

theorem eraseStep (i : Nat) (l : Wlabel) (c c' ce : Wpcfg P D) :
    pclsErasable pcls →
    erCfg ce c → wpPfStep pstep pcls i l c c' →
    ∃ ce', wpPfStep (erasePstep pstep) pcls i (eraseLbl l) ce ce' ∧ erCfg ce' c' := by
  intro hcls hm hstep
  obtain ⟨himg, hlog, hdev, hlen, hags⟩ := hm
  cases hstep with
  | PFSilent cfg ag st' d' hlk hps =>
    obtain ⟨age, hlke, hst, hpr, hws⟩ := hags i ag hlk
    refine ⟨_, wpPfStep.PFSilent ce age st' d' hlke ⟨.LSilent, rfl, by rw [hst, hdev]; exact hps⟩,
      ?_⟩
    rw [hpr]
    exact erCfgUpd _ _ _ _ _ _ _ _ _ _ _ _ _ _ himg hlog hlen hags hlk hlke hws
  | PFLoad cfg ag aq lat base tvs asrc st' d' hlk hps hr =>
    obtain ⟨age, hlke, hst, hpr, hws⟩ := hags i ag hlk
    refine ⟨_, wpPfStep.PFLoad ce age aq lat base tvs [] st' d' hlke
      ⟨.LLoad aq lat base tvs asrc, rfl, by rw [hst, hdev]; exact hps⟩
      (by rw [himg, hlog]; exact readOkDEr0 _ _ _ _ _ _ _ _ _ hws hr), ?_⟩
    rw [hpr]
    exact erCfgUpd _ _ _ _ _ _ _ _ _ _ _ _ _ _ himg hlog hlen hags hlk hlke
      (loadPostRunDEr0 _ _ _ _ _ _ hws)
  | PFStore cfg ag rl base data asrc vsrc k st' d' hlk hps hnn hk =>
    -- the class is pinned by `pclsErasable`
    obtain ⟨age, hlke, hst, hpr, hws⟩ := hags i ag hlk
    have hkk : k = pcls age.paSt (.LStore rl base data [] []) age.paWs := by
      rw [hst, hk]
      exact (hcls ag.paSt (.LStore rl base data asrc vsrc) _ _ (erWsRelp _ _ hws)).symm
    refine ⟨_, wpPfStep.PFStore ce age rl base data [] [] k st' d' hlke
      ⟨.LStore rl base data asrc vsrc, rfl, by rw [hst, hdev]; exact hps⟩ hnn hkk, ?_⟩
    rw [hpr, hlog]
    exact erCfgUpd _ _ _ _ _ _ _ _ _ _ _ _ _ _ himg rfl hlen hags hlk hlke
      (storePostRunDEr0 _ _ _ _ _ _ _ _ hws)
  | PFRmw cfg ag aq rl base tvs data asrc vsrc k st' d' hlk hps hnn hlen' hr he hk =>
    obtain ⟨age, hlke, hst, hpr, hws⟩ := hags i ag hlk
    have hkk : k = pcls age.paSt (.LRmw aq rl base tvs data [] []) age.paWs := by
      rw [hst, hk]
      exact (hcls ag.paSt (.LRmw aq rl base tvs data asrc vsrc) _ _ (erWsRelp _ _ hws)).symm
    refine ⟨_, wpPfStep.PFRmw ce age aq rl base tvs data [] [] k st' d' hlke
      ⟨.LRmw aq rl base tvs data asrc vsrc, rfl, by rw [hst, hdev]; exact hps⟩ hnn hlen'
      (by rw [himg, hlog]; exact readOkDEr0 _ _ _ _ _ _ _ _ _ hws hr)
      (by rw [hlog]; exact he) hkk, ?_⟩
    rw [hpr, hlog]
    exact erCfgUpd _ _ _ _ _ _ _ _ _ _ _ _ _ _ himg rfl hlen hags hlk hlke
      (storePostRunDEr0 _ _ _ _ _ _ _ _ (loadPostRunDEr0 _ _ _ _ _ _ hws))
  | PFFence cfg ag pr pw sr sw st' d' hlk hps =>
    obtain ⟨age, hlke, hst, hpr, hws⟩ := hags i ag hlk
    refine ⟨_, wpPfStep.PFFence ce age pr pw sr sw st' d' hlke
      ⟨.LFence pr pw sr sw, rfl, by rw [hst, hdev]; exact hps⟩, ?_⟩
    rw [hpr]
    exact erCfgUpd _ _ _ _ _ _ _ _ _ _ _ _ _ _ himg hlog hlen hags hlk hlke
      (fencePostEr _ _ _ _ _ _ hws)
  | PFDev cfg ag st' d' hlk hps =>
    obtain ⟨age, hlke, hst, hpr, hws⟩ := hags i ag hlk
    refine ⟨_, wpPfStep.PFDev ce age st' d' hlke ⟨.LDev _ _ _ _ _, rfl, by rw [hst, hdev]; exact hps⟩, ?_⟩
    rw [hpr]
    exact erCfgUpd _ _ _ _ _ _ _ _ _ _ _ _ _ _ himg hlog hlen hags hlk hlke hws
  | PFRegW cfg ag rd srcs st' d' hlk hps =>
    -- `LRegW ↦ LSilent`
    obtain ⟨age, hlke, hst, hpr, hws⟩ := hags i ag hlk
    refine ⟨_, wpPfStep.PFSilent ce age st' d' hlke
      ⟨.LRegW rd srcs, rfl, by rw [hst, hdev]; exact hps⟩, ?_⟩
    rw [hpr]
    exact erCfgUpd _ _ _ _ _ _ _ _ _ _ _ _ _ _ himg hlog hlen hags hlk hlke
      (erWsRegwR _ _ _ _ hws)
  | PFCtrl cfg ag srcs st' d' hlk hps =>
    -- `LCtrl ↦ LSilent`
    obtain ⟨age, hlke, hst, hpr, hws⟩ := hags i ag hlk
    refine ⟨_, wpPfStep.PFSilent ce age st' d' hlke
      ⟨.LCtrl srcs, rfl, by rw [hst, hdev]; exact hps⟩, ?_⟩
    rw [hpr]
    exact erCfgUpd _ _ _ _ _ _ _ _ _ _ _ _ _ _ himg hlog hlen hags hlk hlke
      (erWsCtrlR _ _ _ hws)
  | PFInstr cfg ag st' d' hlk hps =>
    -- `LInstr ↦ LSilent`: the `wRes` divergence
    obtain ⟨age, hlke, hst, hpr, hws⟩ := hags i ag hlk
    refine ⟨_, wpPfStep.PFSilent ce age st' d' hlke
      ⟨.LInstr, rfl, by rw [hst, hdev]; exact hps⟩, ?_⟩
    rw [hpr]
    exact erCfgUpd _ _ _ _ _ _ _ _ _ _ _ _ _ _ himg hlog hlen hags hlk hlke
      (erWsInstrR _ _ hws)
  | PFExLoad cfg ag aq base tvs asrc st' d' hlk hps hr =>
    obtain ⟨age, hlke, hst, hpr, hws⟩ := hags i ag hlk
    refine ⟨_, wpPfStep.PFExLoad ce age aq base tvs [] st' d' hlke
      ⟨.LExLoad aq base tvs asrc, rfl, by rw [hst, hdev]; exact hps⟩
      (by rw [himg, hlog]; exact readOkDEr0 _ _ _ _ _ _ _ _ _ hws hr), ?_⟩
    rw [hpr]
    exact erCfgUpd _ _ _ _ _ _ _ _ _ _ _ _ _ _ himg hlog hlen hags hlk hlke
      (exloadPostRunDEr0 _ _ _ _ _ _ hws)
  | PFExStore cfg ag rl base data asrc vsrc k R st' d' hlk hps hnn hres hrb hrlen he hk =>
    -- the reservation transfers with the same base and column
    obtain ⟨age, hlke, hst, hpr, hws⟩ := hags i ag hlk
    obtain ⟨Re, hRe, hrbe, hrtse, _⟩ := erWsRes _ _ hws R hres
    have hkk : k = pcls age.paSt (.LExStore rl base data [] []) age.paWs := by
      rw [hst, hk]
      exact (hcls ag.paSt (.LExStore rl base data asrc vsrc) _ _ (erWsRelp _ _ hws)).symm
    refine ⟨_, wpPfStep.PFExStore ce age rl base data [] [] k Re st' d' hlke
      ⟨.LExStore rl base data asrc vsrc, rfl, by rw [hst, hdev]; exact hps⟩ hnn hRe
      (by rw [hrbe]; exact hrb) (by rw [hrtse]; exact hrlen)
      (by rw [hrtse, hlog]; exact he) hkk, ?_⟩
    rw [hpr, hlog]
    exact erCfgUpd _ _ _ _ _ _ _ _ _ _ _ _ _ _ himg rfl hlen hags hlk hlke
      (storePostRunDEr0 _ _ _ _ _ _ _ _ hws)
  | PFIFetch cfg ag base tvs st' d' hlk hps hif =>
    -- O2 (deviation 6): log-only side condition, identity post-state
    obtain ⟨age, hlke, hst, hpr, hws⟩ := hags i ag hlk
    refine ⟨_, wpPfStep.PFIFetch ce age base tvs st' d' hlke
      ⟨.LIFetch base tvs, rfl, by rw [hst, hdev]; exact hps⟩
      (by rw [himg, hlog]; exact hif), ?_⟩
    rw [hpr]
    exact erCfgUpd _ _ _ _ _ _ _ _ _ _ _ _ _ _ himg hlog hlen hags hlk hlke hws

/-! ## 5. The run level and the endpoint -/

theorem eraseRunStep (ce c c' : Wpcfg P D) :
    pclsErasable pcls → erCfg ce c → wpPfRun pstep pcls c c' →
    ∃ ce', wpPfRun (erasePstep pstep) pcls ce ce' ∧ erCfg ce' c' := by
  rintro hcls hm ⟨i, l, hs⟩
  obtain ⟨ce', hse, hm'⟩ := eraseStep pstep pcls i l c c' ce hcls hm hs
  exact ⟨ce', ⟨i, eraseLbl l, hse⟩, hm'⟩

theorem eraseRtc (ce c c' : Wpcfg P D) :
    pclsErasable pcls → erCfg ce c → rtc (wpPfRun pstep pcls) c c' →
    ∃ ce', rtc (wpPfRun (erasePstep pstep) pcls) ce ce' ∧ erCfg ce' c' := by
  intro hcls hm hrun
  refine rtc_ind_l (fun x => ∀ ce, erCfg ce x →
      ∃ ce', rtc (wpPfRun (erasePstep pstep) pcls) ce ce' ∧ erCfg ce' c') c'
    (fun ce hm => ⟨ce, rtc_refl _, hm⟩) ?_ c hrun ce hm
  intro x y hxy _ ih ce hm
  obtain ⟨ce1, hs1, hm1⟩ := eraseRunStep pstep pcls ce x y hcls hm hxy
  obtain ⟨ce2, hs2, hm2⟩ := ih ce1 hm1
  exact ⟨ce2, rtc_l hs1 hs2, hm2⟩

/-- THE ENDPOINT (stage 1's deliverable): every pf run of the DEPENDENCY-CARRYING instance is
matched by a pf run of the SAME program over the erased alphabet, with the same image, THE SAME
LOG, the same fabric and the same program states — and the erased LTS is `lbDepfree`. -/
theorem eraseRun (img : Image) (d0 : D) (ps : List P) (c : Wpcfg P D) :
    pclsErasable pcls →
    rtc (wpPfRun pstep pcls) (wpInit img d0 ps) c →
    ∃ ce, rtc (wpPfRun (erasePstep pstep) pcls) (wpInit img d0 ps) ce ∧
      ce.pcImg = c.pcImg ∧ ce.pcLog = c.pcLog ∧ ce.pcDev = c.pcDev ∧
      (∀ (i : Nat) (agi : Wpagent P), c.pcAgs[i]? = some agi →
        ∃ age, ce.pcAgs[i]? = some age ∧ age.paSt = agi.paSt) ∧
      pstepDepfree (erasePstep pstep) := by
  intro hcls hrun
  obtain ⟨ce, hrune, himg, hlog, hdev, _, hags⟩ :=
    eraseRtc pstep pcls _ _ c hcls (erCfgInit img d0 ps) hrun
  refine ⟨ce, hrune, himg, hlog, hdev, fun i agi hlk => ?_, erasePstepDepfree pstep⟩
  obtain ⟨age, hlke, hst, _⟩ := hags i agi hlk
  exact ⟨age, hlke, hst⟩

/-- THE STAGE-1 PAYOFF: T2 CONTAINMENT FOR A DEPENDENCY-CARRYING PROGRAM.  `wpPfBridge` asks for
`pstepDepfree`, which the D2 event instance does NOT satisfy; composing it with the erasure
replaces that premise by nothing.  What is left is `lbFused` (stage 2's). -/
theorem eraseBridgeLog (img : Image) (d0 : D) (ps : List P) (c : Wpcfg P D) :
    pclsErasable pcls → pstepFused pstep →
    rtc (wpPfRun pstep pcls) (wpInit img d0 ps) c →
    ∃ E, execWf E ∧ exImg E = img ∧ exLog E = c.pcLog := by
  intro hcls hfu hrun
  obtain ⟨ce, hrune, hm⟩ := eraseRtc pstep pcls _ _ c hcls (erCfgInit img d0 ps) hrun
  obtain ⟨E, hE, himg, hlog⟩ := wpPfBridgeLog (erasePstep pstep) pcls img d0 ps ce
    (erasePstepDepfree pstep) (erasePstepFused pstep hfu) hrune
  exact ⟨E, hE, himg, hlog.trans (erCfgLog _ _ hm)⟩

end erase

end Weak
