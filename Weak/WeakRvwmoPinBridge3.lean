/-
Weak: **W9a, increment 1 — the static pin certificates TARGETING the cat chain's `segPinC`**
(plan `notes/weak-allocproc-plan.md` rev 45 §C W9a; Lean-only, no Rocq twin).

`WeakRvwmoPinBridge` proves `PDep`/`PCtrl`/`PFence` witnesses into the RVWMO⁻ chain's one-step
`segPin`; `WeakRvwmoPinBridge2` discharges its taint hypothesis for the defined site oracle
`psites` (`pinSegPin'`).  The cat chain (`CatLin`, W12) consumes `segPinC GD ad s` — a same-hart
CHAIN of ordered steps (`pinStep`: the six cat arms, deps, rule 12 over `ad`).  This file:

  §1  `segPin ⇒ segPinC` (`pinStepOfSegPinArm`), and the three certifying classes stated INTO
      `segPinC` with the hypothesis discharged by `psites`: `pinSegPinC'` (PDep),
      `pinSegPinCtrlC'` (PCtrl), `pinSegPinFenceC` (PFence).
  §2  The control arm at the emission's REAL label shape: the instance emits
      `LCtrl (erwSrcs dec rds)` (`WeakEvLang.erwOf`'s `nextPC` arm, the DYNAMIC read set, DEC-7),
      not `LCtrl (depsCtrl …)`; `pctrlRowDepsSup` needs only `dsubb (depsCtrl …) srcs`
      (decoded ⊆ emitted), and `WeakRvwmoPinBridge3.dsubbErwSrcs` reduces that to "every decoded
      source register was READ before the write" — the per-instruction residual, named.
  §3  PDep entries ACROSS AN rfi (`segPinCForward`): the PDep edge is TAGGED `DTaddr`/`DTdata` by
      `rowDepsT` (`pdepRowDepsT`, through the untagged → tagged state inclusion `dsLe`), so under
      the tagged conformance clause of `CatLinChain.gdexecQconfT` it is an `AxDeps.gtAd` edge,
      and a same-hart read forwarded from the dep-fed store and itself pinned to the exit pins
      the whole segment (`pdepSegPinCForward`, rule 12).

**What this increment does NOT prove (the R-3 residual; see `PROGRESS-W9a.md`).**  That the
REAL `pstepEv` run's items between the load and the site satisfy `psites` (`reaches`): per
instruction, (a) the group's register writes are at the decoded destinations with every decoded
source READ first (the `dsubb` of §2 — a Sail per-execute-clause fact), at most one write per
destination, in `taintStep`'s order; (b) the run's next pc is the checker's fall-through
successor (`wstep`) — false on a taken branch (the checker's `pdfs` covers it, `psites` does
not), at a `ret` whose `ra` came back from the stack (an ownership fact), and at any
instruction boundary where the hart takes an interrupt (`riscvStep` → `try_step`); (c) the
announced word is `kword pc` (the fetch-from-image clause).  Every theorem here is stated with
`psites` (or the item shapes) as a premise, exactly as `pinSegPin'`.

Spec: no trusted text (proof device; `segPinC`, `gtAd`, `rowDepsT` are the merged W12 / (F-dep)
definitions, unchanged).
-/
import Weak.WeakRvwmoPinBridge2
import Weak.CatLin

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open KernelPinsDef
open WeakRvwmoConf (Dstate dstep)
open CatLin

/-! ## 1. `segPin ⇒ segPinC`, and the three certifying classes into `segPinC` -/

/-- Every one-step `segPin` arm is a `pinStep`, so a `segPin` segment is a `segPinC` one. -/
theorem WeakRvwmoPinBridge3.segPinCOfSegPin (GD : Gdexec) (ad : List (Geid × Geid)) (s : Seg) :
    segPin GD s → segPinC GD ad s :=
  fun h => tc_once (pinStepOfSegPinArm GD ad _ _ h)

/-- **PDep into `segPinC`** — `pinSegPin'` (hypothesis discharged by `psites`), retargeted. -/
theorem pinSegPinC' (GD : Gdexec) (ad : List (Geid × Geid)) (i : Nat) (em : Hemission) (sg : Seg)
    (pcL pc' : Int) (j k : Nat) (own : Bool) (base pre post : List Eitem) (rl : Bool) (a : Int)
    (v : List (BitVec 8)) :
    (∀ jk, jk ∈ rowDeps em.emItems → ((i, jk.1), (i, jk.2)) ∈ GD.gdDeps) →
    sg.sgEntry = (i, j) → sg.sgExit = (i, k) →
    invOk j (dsRun dsInit base) (pinT0 pcL) →
    em.emItems
      = pre ++ (Wlabel.LStore rl a v (depsAddr (krole pc')) (depsVsrc (krole pc')), some k)
        :: post →
    psites pcL own base pre
      (Wlabel.LStore rl a v (depsAddr (krole pc')) (depsVsrc (krole pc')), some k) pc' →
    j < k →
    pinnedb pinFuel pcL (.PDep pc' own) = true →
    segPinC GD ad sg := by
  intro hconf he hx hbase hes hsite hlt hpin
  exact WeakRvwmoPinBridge3.segPinCOfSegPin GD ad sg
    (pinSegPin' GD i em sg pcL pc' j k own base pre post rl a v hconf he hx hbase hes hsite hlt
      hpin)

/-- **PCtrl into `segPinC`** at the decoded label shape (`pctrlRowDeps` with `psites`). -/
theorem pinSegPinCtrlC' (GD : Gdexec) (ad : List (Geid × Geid)) (i : Nat) (em : Hemission)
    (sg : Seg) (pcL pc' : Int) (j k : Nat) (own : Bool) (base pre mid post : List Eitem)
    (kc : Option Nat) (rl : Bool) (a : Int) (v : List (BitVec 8)) (asrc vsrc : List Dsrc) :
    (∀ jk, jk ∈ rowDeps em.emItems → ((i, jk.1), (i, jk.2)) ∈ GD.gdDeps) →
    sg.sgEntry = (i, j) → sg.sgExit = (i, k) →
    invOk j (dsRun dsInit base) (pinT0 pcL) →
    em.emItems = pre ++ (Wlabel.LCtrl (depsCtrl (krole pc')), kc)
      :: (mid ++ (Wlabel.LStore rl a v asrc vsrc, some k) :: post) →
    psites pcL own base pre (Wlabel.LCtrl (depsCtrl (krole pc')), kc) pc' →
    j < k →
    pinnedb pinFuel pcL (.PCtrl pc' own) = true →
    segPinC GD ad sg := by
  intro hconf he hx hbase hes hsite hlt hpin
  exact WeakRvwmoPinBridge3.segPinCOfSegPin GD ad sg
    (segPinOfRowDeps GD i em sg j k hconf he hx
      (pctrlRowDeps _ (psites pcL own base) pcL j own pc' k pre mid post kc rl a v asrc vsrc
        (checkerTaintSubProvProof pcL j own base _ hbase) hes hsite hlt hpin))

/-- **PFence into `segPinC`** (no taint hypothesis, as `segPinOfRowFence`). -/
theorem pinSegPinFenceC (GD : Gdexec) (ad : List (Geid × Geid)) (i : Nat) (s : Seg)
    (j kf k : Nat) (pr pw sr sw : Bool) :
    s.sgEntry = (i, j) → s.sgExit = (i, k) →
    j < kf → kf < k →
    gxLbl GD.gdG (i, kf) = some (Lbl.LFence pr pw sr sw) →
    glblIs GD.gdG (i, j) lbIsR → pr = true →
    glblIs GD.gdG (i, k) lbIsW → sw = true →
    segPinC GD ad s := by
  intro he hx hj hk hf hr hpr hw hsw
  exact WeakRvwmoPinBridge3.segPinCOfSegPin GD ad s
    (segPinOfRowFence GD i s j kf k pr pw sr sw he hx hj hk hf hr hpr hw hsw)

/-! ## 2. The control arm at the REAL label shape -/

/-- `pctrlRowDeps` for an emitted control list that merely COVERS the decoded one. -/
theorem pctrlRowDepsSup (es : List Eitem) (sites : List Eitem → Eitem → Int → Prop) (pcL : Int)
    (j : Nat) (own : Bool) (pc' : Int) (k : Nat) (pre mid post : List Eitem) (srcs : List Dsrc)
    (kc : Option Nat) (rl : Bool) (a : Int) (v : List (BitVec 8)) (asrc vsrc : List Dsrc) :
    checkerTaintSubProv es sites pcL j own →
    es = pre ++ (Wlabel.LCtrl srcs, kc)
      :: (mid ++ (Wlabel.LStore rl a v asrc vsrc, some k) :: post) →
    sites pre (Wlabel.LCtrl srcs, kc) pc' →
    dsubb (depsCtrl (krole pc')) srcs = true →
    j < k →
    pinnedb pinFuel pcL (.PCtrl pc' own) = true →
    (j, k) ∈ rowDeps es := by
  intro hsub hes hsite hcov hlt hpin
  obtain ⟨t, hw, htn⟩ := pinnedbCtrlInv pinFuel pcL pc' own hpin
  obtain ⟨r, hr, ht⟩ := srcsTaintedReg _ _ htn
  have hj := hsub pre _ _ pc' t r hes hsite hw ht
  have hctl : j ∈ (dsRun dsInit (pre ++ [(Wlabel.LCtrl srcs, kc)])).dsCtl := by
    rw [dsRunApp, dsRunCons, dsRunNil]
    exact dstepCtlIntro _ _ _ _ _ (dsubbElem _ _ _ hcov hr) hj
  have hsplit : pre ++ (Wlabel.LCtrl srcs, kc) :: mid
      = (pre ++ [(Wlabel.LCtrl srcs, kc)]) ++ mid := by
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  have hctl' : j ∈ (dsRun dsInit (pre ++ (Wlabel.LCtrl srcs, kc) :: mid)).dsCtl := by
    rw [hsplit, dsRunApp]
    exact dsRunCtlSub _ _ hctl
  apply rowDepsItem _ (pre ++ (Wlabel.LCtrl srcs, kc) :: mid)
    (Wlabel.LStore rl a v asrc vsrc, some k) post
  · rw [hes]; simp only [List.append_assoc, List.cons_append]
  · exact dedgesCtl _ _ _ _ _ hlt hctl'

/-- DEC-7's coverage, as the boolean `dsubb`: the dynamic list `erwSrcs dec rds` covers the
decoded one as soon as every decoded register is in the read set. -/
theorem WeakRvwmoPinBridge3.dsubbErwSrcs (dec : List Dsrc) (rds : List Nat) :
    (∀ r : Nat, Dsrc.DReg r ∈ dec → r ∈ rds) → dsubb dec (erwSrcs dec rds) = true := by
  intro h
  unfold dsubb
  refine List.all_eq_true.2 (fun x hx => List.any_eq_true.2 ⟨x, ?_, decide_eq_true rfl⟩)
  exact erwSrcsCovers dec rds x hx (fun r e => h r (e ▸ hx))

/-- **PCtrl into `segPinC`** at the emitted `LCtrl srcs` (covering the decoded list). -/
theorem pinSegPinCtrlSupC' (GD : Gdexec) (ad : List (Geid × Geid)) (i : Nat) (em : Hemission)
    (sg : Seg) (pcL pc' : Int) (j k : Nat) (own : Bool) (base pre mid post : List Eitem)
    (srcs : List Dsrc) (kc : Option Nat) (rl : Bool) (a : Int) (v : List (BitVec 8))
    (asrc vsrc : List Dsrc) :
    (∀ jk, jk ∈ rowDeps em.emItems → ((i, jk.1), (i, jk.2)) ∈ GD.gdDeps) →
    sg.sgEntry = (i, j) → sg.sgExit = (i, k) →
    invOk j (dsRun dsInit base) (pinT0 pcL) →
    em.emItems = pre ++ (Wlabel.LCtrl srcs, kc)
      :: (mid ++ (Wlabel.LStore rl a v asrc vsrc, some k) :: post) →
    psites pcL own base pre (Wlabel.LCtrl srcs, kc) pc' →
    dsubb (depsCtrl (krole pc')) srcs = true →
    j < k →
    pinnedb pinFuel pcL (.PCtrl pc' own) = true →
    segPinC GD ad sg := by
  intro hconf he hx hbase hes hsite hcov hlt hpin
  exact WeakRvwmoPinBridge3.segPinCOfSegPin GD ad sg
    (segPinOfRowDeps GD i em sg j k hconf he hx
      (pctrlRowDepsSup _ (psites pcL own base) pcL j own pc' k pre mid post srcs kc rl a v asrc
        vsrc (checkerTaintSubProvProof pcL j own base _ hbase) hes hsite hcov hlt hpin))

/-! ## 3. PDep across an rfi — the tagged edge and rule 12 -/

/-- The tagged fold's state after a prefix. -/
def WeakRvwmoPinBridge3.dtRun (s : DstateT) (es : List Eitem) : DstateT :=
  es.foldl (fun s it => (dstepT s it).1) s

open WeakRvwmoPinBridge3 (dtRun)

theorem WeakRvwmoPinBridge3.rowDepsTAuxApp (s : DstateT) (es1 es2 : List Eitem) :
    rowDepsTAux s (es1 ++ es2) = rowDepsTAux s es1 ++ rowDepsTAux (dtRun s es1) es2 := by
  induction es1 generalizing s with
  | nil => rfl
  | cons it es1 ih =>
    show (dstepT s it).2 ++ rowDepsTAux (dstepT s it).1 (es1 ++ es2)
      = ((dstepT s it).2 ++ rowDepsTAux (dstepT s it).1 es1) ++ rowDepsTAux (dtRun s (it :: es1)) es2
    rw [ih, List.append_assoc]
    rfl

/-- The untagged state stays below the tagged one along any prefix (`dstepTState`). -/
theorem WeakRvwmoPinBridge3.dsLeRun (es : List Eitem) :
    ∀ (a : Dstate) (s : DstateT), dsLe a (dsOfT s) → dsLe (dsRun a es) (dsOfT (dtRun s es)) := by
  induction es with
  | nil => intro a s h; exact h
  | cons it es ih =>
    intro a s h
    exact ih _ _ (dstepTState a s it h)

/-- **The PDep edge is TAGGED address/data**: the tainted register is in the store's `asrc` or
`vsrc`, which `dedgesW` tags `DTaddr` / `DTdata`. -/
theorem pdepRowDepsT (es : List Eitem) (sites : List Eitem → Eitem → Int → Prop) (pcL : Int)
    (j : Nat) (own : Bool) (pc' : Int) (k : Nat) (pre post : List Eitem) (rl : Bool) (a : Int)
    (v : List (BitVec 8)) :
    checkerTaintSubProv es sites pcL j own →
    es = pre ++ (Wlabel.LStore rl a v (depsAddr (krole pc')) (depsVsrc (krole pc')), some k)
      :: post →
    sites pre (Wlabel.LStore rl a v (depsAddr (krole pc')) (depsVsrc (krole pc')), some k) pc' →
    j < k →
    pinnedb pinFuel pcL (.PDep pc' own) = true →
    ∃ tg, dtagAd tg = true ∧ ((j, k), tg) ∈ rowDepsT es := by
  intro hsub hes hsite hlt hpin
  obtain ⟨t, hw, htn⟩ := pinnedbDepInv pinFuel pcL pc' own hpin
  let s := dtRun dtInit pre
  have hle : dsLe (dsRun dsInit pre) (dsOfT s) :=
    WeakRvwmoPinBridge3.dsLeRun pre dsInit dtInit dsLeInit
  have hes' : rowDepsT es = rowDepsTAux dtInit pre ++
      ((dedgesW s k (depsAddr (krole pc')) (depsVsrc (krole pc'))) ++
        rowDepsTAux (dstepT s
          (Wlabel.LStore rl a v (depsAddr (krole pc')) (depsVsrc (krole pc')), some k)).1 post) := by
    rw [hes]
    unfold rowDepsT
    rw [WeakRvwmoPinBridge3.rowDepsTAuxApp]
    rfl
  -- the tainted register carries `j` in the TAGGED state too
  have hprov : ∀ r, taintMem r t = true → j ∈ dsrcPos (dsOfT s) (.DReg r) := by
    intro r ht
    exact hle.1 r j (hsub pre _ post pc' t r hes hsite hw ht)
  rw [hes']
  rcases htn with h | h
  · obtain ⟨r, hr, ht⟩ := srcsTaintedReg _ _ h
    refine ⟨Dtag.DTaddr, rfl, List.mem_append_right _ (List.mem_append_left _ ?_)⟩
    refine List.mem_append_left _ ((elemOfTagEdges ..).2 ⟨rfl, rfl, ?_, hlt⟩)
    unfold dtsrcs dsrcsPos
    exact List.mem_flatten.mpr ⟨_, List.mem_map_of_mem hr, hprov r ht⟩
  · obtain ⟨r, hr, ht⟩ := srcsTaintedReg _ _ h
    refine ⟨Dtag.DTdata, rfl, List.mem_append_right _ (List.mem_append_left _ ?_)⟩
    refine List.mem_append_right _ (List.mem_append_left _ ((elemOfTagEdges ..).2 ⟨rfl, rfl, ?_, hlt⟩))
    unfold dtsrcs dsrcsPos
    exact List.mem_flatten.mpr ⟨_, List.mem_map_of_mem hr, hprov r ht⟩

/-- **PDep entries across an rfi** (`segPinCForward`, rule 12 `[R];(addr|data);[W];rfi;[R]`): the
load at row position `j` feeds the store at `km` (a PDep certificate on the `psites` stretch);
a same-hart read `r` reads that store (`grf`) and is itself pinned to `x`.  Under the TAGGED
conformance clause of `gdexecQconfT` the PDep edge is a `gtAd` edge, so the segment from the
load to `x` is `segPinC` on `forget GT` with `ad := gtAd` (the `catADOfCatT` instance). -/
theorem pdepSegPinCForward (GT : GdexecT) (i : Nat) (em : Hemission) (pcL pc' : Int)
    (j km : Nat) (own : Bool) (base pre post : List Eitem) (rl : Bool) (a : Int)
    (v : List (BitVec 8)) (r x : Geid) :
    (∀ e, e ∈ rowDepsT em.emItems → (((i, e.1.1), (i, e.1.2)), e.2) ∈ GT.gtDeps) →
    gisRd GT.gtG (i, j) = true → gisW GT.gtG (i, km) = true →
    invOk j (dsRun dsInit base) (pinT0 pcL) →
    em.emItems
      = pre ++ (Wlabel.LStore rl a v (depsAddr (krole pc')) (depsVsrc (krole pc')), some km)
        :: post →
    psites pcL own base pre
      (Wlabel.LStore rl a v (depsAddr (krole pc')) (depsVsrc (krole pc')), some km) pc' →
    j < km →
    pinnedb pinFuel pcL (.PDep pc' own) = true →
    r.1 = i → WeakRvwmoAcyc.grf GT.gtG (i, km) r →
    tc (pinStep (forget GT) (gtAd GT.gtG GT.gtDeps)) r x →
    segPinC (forget GT) (gtAd GT.gtG GT.gtDeps) ⟨i, (i, j), x⟩ := by
  intro hconfT hrd hwr hbase hes hsite hlt hpin hag hrf hrx
  obtain ⟨tg, htg, hin⟩ := pdepRowDepsT _ (psites pcL own base) pcL j own pc' km pre post rl a v
    (checkerTaintSubProvProof pcL j own base _ hbase) hes hsite hlt hpin
  have had : ((i, j), (i, km)) ∈ gtAd GT.gtG GT.gtDeps :=
    (elemOfGtAd GT.gtG GT.gtDeps (i, j) (i, km)).2 ⟨tg, hconfT _ hin, htg, hrd, hwr⟩
  exact segPinCForward (forget GT) (gtAd GT.gtG GT.gtDeps) (i, j) (i, km) r x hag.symm had hrf hrx

/-- The endpoint facts of §3 from the hart's conformance (`hartConfRowDepsWf` on the untagged
PDep edge), at any graph whose row `i` is the conforming row. -/
theorem WeakRvwmoPinBridge3.pdepEndpoints (G : Gexec) (i : Nat) (row : List Lbl) (p0 : Pexv6)
    (dv : Nat → Efab) (em : Hemission) (j km : Nat) :
    G.gxProg[i]? = some row → hartConf i row p0 dv em → (j, km) ∈ rowDeps em.emItems →
    gisRd G (i, j) = true ∧ gisW G (i, km) = true := by
  intro hrow hcf hjk
  obtain ⟨-, ⟨lr, hlr, hr⟩, lb, hlb, hw⟩ := hartConfRowDepsWf i row p0 dv em (j, km) hcf hjk
  exact ⟨by simp [gisRd, gxLbl, hrow, hlr, hr], by simp [gisW, gxLbl, hrow, hlb, hw]⟩

end Weak
