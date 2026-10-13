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

**Increment 2 — the taken-branch case** (option (A) of `PROGRESS-W9a.md`, provisional):
  §4  `reachesA`: the alignment along ANY `pstep` successor (fall-through OR taken arm), with
      `reachesAInv` (the invariant travels) and `raTaken` (the taken arm is a step);
      `reaches ⇒ reachesA`.
  §5  `pdfs` SOUNDNESS: `allPathsPinnedSound` — when the all-paths search accepts a load site, no
      state reachable from `pinStart` along any arms makes `pstep` fail (DFS invariant
      `pdfsSoundAux`: every path to a failing state meets the visited set, no longer);
      `reachesANoFail` for the aligned run; `pinnedbAllPaths` (every certifying path witness
      carries the verdict).
  §6–§7  At ANY reached state: a pin is a fence / a fed store / a branch on the taint
      (`pstepPinCases`); a reached store that is neither a fence word nor an `own`-excused stack
      store is FED (`pstepStoreFed`); the PDep/PCtrl classes into `segPinC` from the reached
      state's own taint (`pinSegPinStoreA`, `pinSegPinCtrlA`), and `pinSegPinFirstStoreA`, where
      the taint premise is supplied by `pdfs` soundness.  The site oracle is `psitesA` (any-path),
      the NAMED premise; `psites ⇒ psitesA`.
  §8  `laAllPathsNoFail`: the soundness lemma applied at the `pinStarted` site on real bytes.

**What is still NOT proved (the R-3 residual, now `psitesA`; see `PROGRESS-W9a.md`).**  That the
REAL `pstepEv` run's items between the load and the site satisfy `psites` (`reaches`): per
instruction, (a) the group's register writes are at the decoded destinations with every decoded
source READ first (the `dsubb` of §2 — a Sail per-execute-clause fact), at most one write per
destination, in `taintStep`'s order; (b) the run's next pc is the checker's fall-through
successor — for `psitesA` SOME `pstep` successor, so a taken branch is covered; still not at a
`ret` whose `ra` came back from the stack unless it equals the walk's return-stack pc (an
ownership fact), and not at an instruction boundary where the hart takes an interrupt
(`riscvStep` → `try_step` → `handle_interrupt`, redirect to `stvec`; a trap is not a barrier in
RVWMO, so no fence-like reading is taken); (c) the announced word is `kword pc` (the
fetch-from-image clause).  Every theorem here is stated with `psites`/`psitesA` (or the item
shapes) as a premise.

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


/-! ## 4. The ANY-PATH alignment (W9a increment 2: the taken-branch case)

`reaches` (PinBridge2) follows `wstep`, the checker's FIRST successor — the not-taken arm of a
conditional branch — so a run that takes a branch leaves it.  `reachesA` lets each step take ANY
successor `pstep` lists (fall-through or taken; jumps, descended calls and walk-stack returns as
before).  It ends at an arbitrary walk state (no stop pc): the site is where the run is. -/

/-- THE ANY-PATH ALIGNMENT: the emission's item groups follow SOME successor of `pstep` at every
instruction, with the same two per-step obligations as `reaches`. -/
inductive reachesA (own : Bool) : PState → List Eitem → PState → Prop where
  | raStop (s : PState) : reachesA own s [] s
  | raStep (s : PState) (g1 g2 : List Eitem) (l : List PState) (s' : PState) (mid : List Eitem)
      (s'' : PState) :
      grpOkb s.psPc g1 g2 = true →
      pstep own s = some l → s' ∈ l →
      taintSub s'.psT (taintStep s.psT s.psPc) →
      reachesA own s' mid s'' →
      reachesA own s (g1 ++ (g2 ++ mid)) s''

/-- The fall-through alignment is a special case. -/
theorem WeakRvwmoPinBridge3.reachesAOfReaches (own : Bool) (stop : Int) (s : PState)
    (g : List Eitem) (s'' : PState) :
    reaches own stop s g s'' → reachesA own s g s'' := by
  intro hr
  induction hr with
  | rcStop s _ => exact .raStop s
  | rcStep s g1 g2 s' mid s'' _ hg hw hsub _ ih =>
    obtain ⟨l, hp⟩ := wstepPstep own s s' hw
    exact .raStep s g1 g2 _ s' mid s'' hg hp (List.mem_cons_self ..) hsub ih

/-- THE INVARIANT TRAVELS along any path (`reachesInv`'s proof, verbatim). -/
theorem reachesAInv (j : Nat) (own : Bool) (s : PState) (g : List Eitem) (s'' : PState) :
    reachesA own s g s'' → ∀ d0, invOk j d0 s.psT → invOk j (dsRun d0 g) s''.psT := by
  intro hr
  induction hr with
  | raStop s => intro d0 h; exact h
  | raStep s g1 g2 l s' mid s'' hg _ _ hsub _ ih =>
    intro d0 hinv
    rw [← List.append_assoc, dsRunApp]
    apply ih
    intro r hr'
    exact grpSound _ _ _ _ _ _ hg hinv r (hsub r hr')

/-- Every successor's taint is the decoded update or the unchanged taint (`wstepTaint`, for ANY
successor). -/
theorem WeakRvwmoPinBridge3.pstepTaint (own : Bool) (s s' : PState) (l : List PState) :
    pstep own s = some l → s' ∈ l → s'.psT = taintStep s.psT s.psPc ∨ s'.psT = s.psT := by
  obtain ⟨pc, t, rs⟩ := s
  unfold pstep
  dsimp only
  repeat' split
  all_goals intro h hm
  all_goals cases h
  all_goals simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  all_goals first
    | (subst hm; first | exact Or.inl rfl | exact Or.inr rfl)
    | (rcases hm with rfl | rfl <;> exact Or.inl rfl)

/-- ... so the taint obligation is DISCHARGED where the decoder names no destination, and is the
identity elsewhere (`wstepTaintSub`, for any successor). -/
theorem WeakRvwmoPinBridge3.pstepTaintSub (own : Bool) (s s' : PState) (l : List PState) :
    pstep own s = some l → s' ∈ l →
    (depsRd (krole s.psPc) = none ∧ depsRd2 (krole s.psPc) = none)
      ∨ s'.psT = taintStep s.psT s.psPc →
    taintSub s'.psT (taintStep s.psT s.psPc) := by
  intro hp hm h
  rcases h with ⟨h1, h2⟩ | heq
  · rw [taintStepId _ _ h1 h2]
    rcases WeakRvwmoPinBridge3.pstepTaint own s s' l hp hm with he | he
    · rw [he, taintStepId _ _ h1 h2]; exact taintSubRefl _
    · rw [he]; exact taintSubRefl _
  · rw [heq]; exact taintSubRefl _

/-- THE TAKEN ARM IS A STEP: at an untainted conditional branch inside the text, the run may
continue at the branch target. -/
theorem WeakRvwmoPinBridge3.raTaken (own : Bool) (pc : Int) (t : List Nat) (rs : List Int)
    (tgt : Int) (g1 g2 mid : List Eitem) (s'' : PState) :
    (decide (pc < textLo) || decide (textHi ≤ pc)) = false →
    wIsFence (kw pc) = false → roleIsStore (krole pc) = false →
    kflowOf pc = .FLbranch tgt → srcsTainted t (depsCtrl (krole pc)) = false →
    grpOkb pc g1 g2 = true →
    reachesA own (PState.PSt tgt (taintStep t pc) rs) mid s'' →
    reachesA own (PState.PSt pc t rs) (g1 ++ (g2 ++ mid)) s'' := by
  intro htx hf hst hk hc hg hr
  have hp : pstep own (PState.PSt pc t rs)
      = some [PState.PSt (pc + wSize (kw pc)) (taintStep t pc) rs,
              PState.PSt tgt (taintStep t pc) rs] := by
    unfold pstep
    simp only [htx, hf, hst, hk, hc, Bool.false_eq_true, ↓reduceIte]
  exact .raStep _ g1 g2 _ _ mid s'' hg hp (by simp) (taintSubRefl _) hr

/-! ## 5. Soundness of the checker's ALL-PATHS search (`pdfs`)

`pdfs` is a DFS with a visited set; `allPathsPinned own pc = true` must mean that NO state
reachable from `pinStart pc` through `pstep`'s successors makes `pstep` fail.  The invariant: a
path from a work-list state to a failing state passes through the visited set, at no greater
length (`pdfsSoundAux`); at the top the visited set is empty. -/

/-- Reachability in `n` checker steps through `pstep`'s successors. -/
inductive WeakRvwmoPinBridge3.preach (own : Bool) : PState → PState → Nat → Prop where
  | prRefl (s : PState) : WeakRvwmoPinBridge3.preach own s s 0
  | prStep (s s' x : PState) (l : List PState) (n : Nat) :
      pstep own s = some l → s' ∈ l → WeakRvwmoPinBridge3.preach own s' x n →
      WeakRvwmoPinBridge3.preach own s x (n + 1)

open WeakRvwmoPinBridge3 (preach)

theorem WeakRvwmoPinBridge3.listnEqbEq : ∀ a b : List Nat, listnEqb a b = true → a = b
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [listnEqb] at h
  | _ :: _, [], h => by simp [listnEqb] at h
  | x :: a, y :: b, h => by
    simp only [listnEqb, Bool.and_eq_true] at h
    rw [Nat.eq_of_beq_eq_true h.1, WeakRvwmoPinBridge3.listnEqbEq a b h.2]

theorem WeakRvwmoPinBridge3.listzEqbEq : ∀ a b : List Int, listzEqb a b = true → a = b
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [listzEqb] at h
  | _ :: _, [], h => by simp [listzEqb] at h
  | x :: a, y :: b, h => by
    simp only [listzEqb, Bool.and_eq_true] at h
    rw [beq_iff_eq.mp h.1, WeakRvwmoPinBridge3.listzEqbEq a b h.2]

theorem WeakRvwmoPinBridge3.pstateEqbEq (a b : PState) : pstateEqb a b = true → a = b := by
  obtain ⟨pa, ta, ra⟩ := a
  obtain ⟨pb, tb, rb⟩ := b
  intro h
  simp only [pstateEqb, Bool.and_eq_true] at h
  obtain ⟨⟨hp, ht⟩, hr⟩ := h
  rw [beq_iff_eq.mp hp, WeakRvwmoPinBridge3.listnEqbEq _ _ ht,
    WeakRvwmoPinBridge3.listzEqbEq _ _ hr]

theorem WeakRvwmoPinBridge3.pdfsUnfold (f : Nat) (own : Bool) (seen : List PState) (s : PState)
    (w' : List PState) :
    pdfs (f + 1) own seen (s :: w')
      = if seen.any (pstateEqb s) then pdfs f own seen w'
        else match pstep own s with
          | none => false
          | some ns => pdfs f own (s :: seen) (ns ++ w') := rfl

/-- THE DFS INVARIANT: every path from a work-list state to a FAILING state meets the visited set,
at a length no greater than its own. -/
theorem WeakRvwmoPinBridge3.pdfsSoundAux (own : Bool) :
    ∀ (f : Nat) (seen work : List PState), pdfs f own seen work = true →
    ∀ s, s ∈ work → ∀ x n, preach own s x n → pstep own x = none →
      ∃ y m, y ∈ seen ∧ m ≤ n ∧ preach own y x m := by
  intro f
  induction f with
  | zero => intro seen work h; exact absurd h Bool.false_ne_true
  | succ f ih =>
    intro seen work h
    cases work with
    | nil => intro s hs; cases hs
    | cons s0 w' =>
      rw [WeakRvwmoPinBridge3.pdfsUnfold] at h
      by_cases hseen : seen.any (pstateEqb s0) = true
      · rw [if_pos hseen] at h
        intro s hs x n hr hbad
        rcases List.mem_cons.mp hs with rfl | hs
        · obtain ⟨y, hy, he⟩ := List.any_eq_true.mp hseen
          rw [WeakRvwmoPinBridge3.pstateEqbEq _ _ he] at hr
          exact ⟨y, n, hy, Nat.le_refl n, hr⟩
        · exact ih seen w' h s hs x n hr hbad
      · rw [if_neg hseen] at h
        cases hps : pstep own s0 with
        | none => rw [hps] at h; exact absurd h Bool.false_ne_true
        | some ns =>
          rw [hps] at h
          have ih' := ih (s0 :: seen) (ns ++ w') h
          -- THE CASE OF THE POPPED STATE ITSELF, by strong induction on the path length.
          have key : ∀ n x, preach own s0 x n → pstep own x = none →
              ∃ y m, y ∈ seen ∧ m ≤ n ∧ preach own y x m := by
            intro n
            induction n using Nat.strongRecOn with
            | _ n ihn =>
              intro x hr hbad
              cases hr with
              | prRefl => rw [hps] at hbad; cases hbad
              | prStep _ s' _ l n' hp hm hr' =>
                rw [hps] at hp
                cases hp
                obtain ⟨y, m, hy, hmn, hyr⟩ :=
                  ih' s' (List.mem_append_left _ hm) x n' hr' hbad
                rcases List.mem_cons.mp hy with rfl | hy
                · obtain ⟨y', m', hy', hm', hyr'⟩ := ihn m (by omega) x hyr hbad
                  exact ⟨y', m', hy', by omega, hyr'⟩
                · exact ⟨y, m, hy, by omega, hyr⟩
          intro s hs x n hr hbad
          rcases List.mem_cons.mp hs with rfl | hs
          · exact key n x hr hbad
          · obtain ⟨y, m, hy, hmn, hyr⟩ := ih' s (List.mem_append_right _ hs) x n hr hbad
            rcases List.mem_cons.mp hy with rfl | hy
            · obtain ⟨y', m', hy', hm', hyr'⟩ := key m x hyr hbad
              exact ⟨y', m', hy', by omega, hyr'⟩
            · exact ⟨y, m, hy, hmn, hyr⟩

/-- **`pdfs` IS SOUND**: when the all-paths search accepts a load site, no state reachable from
the walk's start, along ANY arms, makes `pstep` fail. -/
theorem allPathsPinnedSound (own : Bool) (pc : Int) :
    allPathsPinned own pc = true → ∀ x n, preach own (pinStart pc) x n → pstep own x ≠ none := by
  intro h x n hr hbad
  obtain ⟨y, _, hy, _⟩ :=
    WeakRvwmoPinBridge3.pdfsSoundAux own pdfsFuel [] [pinStart pc] h (pinStart pc)
      (List.mem_singleton_self _) x n hr hbad
  cases hy

theorem WeakRvwmoPinBridge3.preachOfReachesA (own : Bool) (s : PState) (g : List Eitem)
    (s'' : PState) : reachesA own s g s'' → ∃ n, preach own s s'' n := by
  intro hr
  induction hr with
  | raStop s => exact ⟨0, .prRefl s⟩
  | raStep s _ _ l s' _ s'' _ hp hm _ _ ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, .prStep s s' s'' l n hp hm hn⟩

/-- ... so the REAL run, aligned along any arms, never reaches a state the checker rejects. -/
theorem reachesANoFail (own : Bool) (pcL : Int) (mid : List Eitem) (s : PState) :
    allPathsPinned own pcL = true → reachesA own (pinStart pcL) mid s → pstep own s ≠ none := by
  intro h hr
  obtain ⟨n, hn⟩ := WeakRvwmoPinBridge3.preachOfReachesA own _ _ _ hr
  exact allPathsPinnedSound own pcL h s n hn

/-- Every CERTIFYING path witness (`PDep`/`PCtrl`/`PFence`) carries the all-paths verdict. -/
theorem WeakRvwmoPinBridge3.pinnedbAllPaths (fuel : Nat) (pc pc' : Int) (own : Bool) (w : Pin) :
    (w = .PDep pc' own ∨ w = .PCtrl pc' own ∨ w = .PFence pc' own) →
    pinnedb fuel pc w = true → allPathsPinned own pc = true := by
  intro hw
  rcases hw with rfl | rfl | rfl <;> unfold pinnedb <;>
    cases roleIsLoad (krole pc) <;> simp only [Bool.false_and, Bool.true_and] <;> intro h
  all_goals first | exact absurd h (by decide) | skip
  all_goals split at h <;> simp only [Bool.and_eq_true, Bool.false_eq_true] at h
  all_goals exact h.2

/-! ## 6. What a reached state IS: a pin, or a non-failing step -/

/-- A PIN STATE (`pstep = some []`) is one of the three: a fence, a store the taint feeds, or a
conditional branch on the taint. -/
theorem WeakRvwmoPinBridge3.pstepPinCases (own : Bool) (s : PState) :
    pstep own s = some [] →
    wIsFence (kw s.psPc) = true ∨
    (roleIsStore (krole s.psPc) = true ∧
      (srcsTainted s.psT (depsAddr (krole s.psPc))
        || srcsTainted s.psT (depsVsrc (krole s.psPc))) = true) ∨
    ((∃ tgt, kflowOf s.psPc = .FLbranch tgt) ∧
      srcsTainted s.psT (depsCtrl (krole s.psPc)) = true) := by
  obtain ⟨pc, t, rs⟩ := s
  unfold pstep
  dsimp only
  intro h
  split at h
  · cases h
  · split at h
    · exact Or.inl ‹_›
    · split at h
      · split at h
        · exact Or.inr (Or.inl ⟨‹_›, ‹_›⟩)
        · split at h <;> cases h
      · split at h
        next tgt hk =>
          split at h
          · exact Or.inr (Or.inr ⟨⟨tgt, hk⟩, ‹_›⟩)
          · cases h
        all_goals (first | (cases h; done) | (split at h <;> cases h))

/-- **A REACHED STORE IS FED BY THE LOAD**: on ANY path out of a load site the all-paths search
accepted, a store the run arrives at (not a fence word, not an `own`-excused stack store) has a
tainted address or data source.  No fall-through assumption, no `fwalk`. -/
theorem WeakRvwmoPinBridge3.pstepStoreFed (own : Bool) (s : PState) :
    pstep own s ≠ none → wIsFence (kw s.psPc) = false → roleIsStore (krole s.psPc) = true →
    (own && stackStore (krole s.psPc)) = false →
    (srcsTainted s.psT (depsAddr (krole s.psPc))
      || srcsTainted s.psT (depsVsrc (krole s.psPc))) = true := by
  obtain ⟨pc, t, rs⟩ := s
  dsimp only
  intro h hf hst hown
  cases hb : (srcsTainted t (depsAddr (krole pc)) || srcsTainted t (depsVsrc (krole pc)))
  · apply absurd _ h
    unfold pstep
    simp only [hf, hst, hb, hown, Bool.false_eq_true, ↓reduceIte, ite_self]
  · rfl

/-! ## 7. The certifying classes at ANY reached state -/

/-- THE ANY-PATH SITE ORACLE: the prefix is the load's prefix `base` followed by an any-path
alignment from the walk's start to the walk state `s` of the instruction now executing.  This is
the NAMED alignment premise of W9a option (A): its remaining content is per instruction
(a) `grpOkb` (DEC-7's per-execute-clause dataflow), (b) the run's next pc is SOME `pstep`
successor — this excludes an interrupt taken at the boundary (Sail `try_step` →
`handle_interrupt`, redirect to `stvec`) and needs a descended `ret`'s `ra` to be the walk's
return-stack pc (frame ownership) — and (c) the decidable taint obligation.  The taken branch is
NO LONGER part of it. -/
def psitesA (pcL : Int) (own : Bool) (base pre : List Eitem) (s : PState) : Prop :=
  ∃ mid, pre = base ++ mid ∧ reachesA own (pinStart pcL) mid s

/-- The fall-through alignment ends at its stop pc. -/
theorem WeakRvwmoPinBridge3.reachesStopPc (own : Bool) (stop : Int) (s : PState) (g : List Eitem)
    (s'' : PState) : reaches own stop s g s'' → s''.psPc = stop := by
  intro hr
  induction hr with
  | rcStop s hs => exact beq_iff_eq.mp hs
  | rcStep _ _ _ _ _ _ _ _ _ _ _ ih => exact ih

/-- The fall-through site oracle is a special case (`psites` ⇒ `psitesA`). -/
theorem WeakRvwmoPinBridge3.psitesAOfPsites (pcL : Int) (own : Bool) (base pre : List Eitem)
    (it : Eitem) (pc' : Int) :
    psites pcL own base pre it pc' → ∃ s, s.psPc = pc' ∧ psitesA pcL own base pre s := by
  rintro ⟨mid, s, hpre, hr⟩
  exact ⟨s, WeakRvwmoPinBridge3.reachesStopPc own pc' _ _ _ hr, mid, hpre,
    WeakRvwmoPinBridge3.reachesAOfReaches own pc' _ _ _ hr⟩

theorem psitesAInv (pcL : Int) (j : Nat) (own : Bool) (base pre g0 : List Eitem) (s : PState) :
    invOk j (dsRun dsInit base) (pinT0 pcL) →
    psitesA pcL own base pre s →
    g0.all provNeutralb = true →
    invOk j (dsRun dsInit (pre ++ g0)) s.psT := by
  intro hbase hsite hg0
  obtain ⟨mid, rfl, hr⟩ := hsite
  rw [dsRunApp]
  apply invNeutralRun _ _ _ _ hg0
  rw [dsRunApp]
  exact reachesAInv j own _ _ _ hr _ hbase

/-- **PDep at any reached store**: the store's emitted operand lists COVER the decoded ones; the
taint is the state's own (no `fwalk`).  `g0` is the instruction's provenance-neutral item prefix
(its announce, its register reads). -/
theorem pdepRowDepsA (es : List Eitem) (pcL : Int) (j : Nat) (own : Bool)
    (base pre g0 post : List Eitem) (s : PState) (k : Nat) (rl : Bool) (a : Int)
    (v : List (BitVec 8)) (asrc vsrc : List Dsrc) :
    invOk j (dsRun dsInit base) (pinT0 pcL) →
    es = pre ++ g0 ++ (Wlabel.LStore rl a v asrc vsrc, some k) :: post →
    psitesA pcL own base pre s →
    g0.all provNeutralb = true →
    dsubb (depsAddr (krole s.psPc)) asrc = true → dsubb (depsVsrc (krole s.psPc)) vsrc = true →
    (srcsTainted s.psT (depsAddr (krole s.psPc))
      || srcsTainted s.psT (depsVsrc (krole s.psPc))) = true →
    j < k →
    (j, k) ∈ rowDeps es := by
  intro hbase hes hsite hg0 hca hcv htn hlt
  have hinv := psitesAInv pcL j own base pre g0 s hbase hsite hg0
  apply rowDepsItem _ (pre ++ g0) _ post _ hes
  rw [Bool.or_eq_true] at htn
  rcases htn with h | h
  · obtain ⟨r, hr, ht⟩ := srcsTaintedReg _ _ h
    exact dedgesReg _ _ _ _ _ _ hlt (Or.inl (dsubbElem _ _ _ hca hr)) (hinv r ht)
  · obtain ⟨r, hr, ht⟩ := srcsTaintedReg _ _ h
    exact dedgesReg _ _ _ _ _ _ hlt (Or.inr (dsubbElem _ _ _ hcv hr)) (hinv r ht)

/-- **PCtrl at any reached branch**: the branch's emitted control list covers the decoded one,
and every later store of the emission carries the edge. -/
theorem pctrlRowDepsA (es : List Eitem) (pcL : Int) (j : Nat) (own : Bool)
    (base pre g0 mid post : List Eitem) (s : PState) (srcs : List Dsrc) (kc : Option Nat)
    (k : Nat) (rl : Bool) (a : Int) (v : List (BitVec 8)) (asrc vsrc : List Dsrc) :
    invOk j (dsRun dsInit base) (pinT0 pcL) →
    es = pre ++ g0 ++ (Wlabel.LCtrl srcs, kc)
      :: (mid ++ (Wlabel.LStore rl a v asrc vsrc, some k) :: post) →
    psitesA pcL own base pre s →
    g0.all provNeutralb = true →
    dsubb (depsCtrl (krole s.psPc)) srcs = true →
    srcsTainted s.psT (depsCtrl (krole s.psPc)) = true →
    j < k →
    (j, k) ∈ rowDeps es := by
  intro hbase hes hsite hg0 hcov htn hlt
  have hinv := psitesAInv pcL j own base pre g0 s hbase hsite hg0
  obtain ⟨r, hr, ht⟩ := srcsTaintedReg _ _ htn
  have hctl : j ∈ (dsRun dsInit (pre ++ g0 ++ [(Wlabel.LCtrl srcs, kc)])).dsCtl := by
    rw [dsRunApp, dsRunCons, dsRunNil]
    exact dstepCtlIntro _ _ _ _ _ (dsubbElem _ _ _ hcov hr) (hinv r ht)
  have hctl' : j ∈ (dsRun dsInit (pre ++ g0 ++ (Wlabel.LCtrl srcs, kc) :: mid)).dsCtl := by
    rw [show pre ++ g0 ++ (Wlabel.LCtrl srcs, kc) :: mid
        = (pre ++ g0 ++ [(Wlabel.LCtrl srcs, kc)]) ++ mid by
      simp only [List.append_assoc, List.cons_append, List.nil_append], dsRunApp]
    exact dsRunCtlSub _ _ hctl
  apply rowDepsItem _ (pre ++ g0 ++ (Wlabel.LCtrl srcs, kc) :: mid)
    (Wlabel.LStore rl a v asrc vsrc, some k) post
  · rw [hes]; simp only [List.append_assoc, List.cons_append]
  · exact dedgesCtl _ _ _ _ _ hlt hctl'

/-- **PDep into `segPinC` at any reached store.** -/
theorem pinSegPinStoreA (GD : Gdexec) (ad : List (Geid × Geid)) (i : Nat) (em : Hemission)
    (sg : Seg) (pcL : Int) (j k : Nat) (own : Bool) (base pre g0 post : List Eitem) (s : PState)
    (rl : Bool) (a : Int) (v : List (BitVec 8)) (asrc vsrc : List Dsrc) :
    (∀ jk, jk ∈ rowDeps em.emItems → ((i, jk.1), (i, jk.2)) ∈ GD.gdDeps) →
    sg.sgEntry = (i, j) → sg.sgExit = (i, k) →
    invOk j (dsRun dsInit base) (pinT0 pcL) →
    em.emItems = pre ++ g0 ++ (Wlabel.LStore rl a v asrc vsrc, some k) :: post →
    psitesA pcL own base pre s →
    g0.all provNeutralb = true →
    dsubb (depsAddr (krole s.psPc)) asrc = true → dsubb (depsVsrc (krole s.psPc)) vsrc = true →
    (srcsTainted s.psT (depsAddr (krole s.psPc))
      || srcsTainted s.psT (depsVsrc (krole s.psPc))) = true →
    j < k →
    segPinC GD ad sg := by
  intro hconf he hx hbase hes hsite hg0 hca hcv htn hlt
  exact WeakRvwmoPinBridge3.segPinCOfSegPin GD ad sg
    (segPinOfRowDeps GD i em sg j k hconf he hx
      (pdepRowDepsA _ pcL j own base pre g0 post s k rl a v asrc vsrc hbase hes hsite hg0 hca
        hcv htn hlt))

/-- **PCtrl into `segPinC` at any reached branch.** -/
theorem pinSegPinCtrlA (GD : Gdexec) (ad : List (Geid × Geid)) (i : Nat) (em : Hemission)
    (sg : Seg) (pcL : Int) (j k : Nat) (own : Bool) (base pre g0 mid post : List Eitem)
    (s : PState) (srcs : List Dsrc) (kc : Option Nat) (rl : Bool) (a : Int)
    (v : List (BitVec 8)) (asrc vsrc : List Dsrc) :
    (∀ jk, jk ∈ rowDeps em.emItems → ((i, jk.1), (i, jk.2)) ∈ GD.gdDeps) →
    sg.sgEntry = (i, j) → sg.sgExit = (i, k) →
    invOk j (dsRun dsInit base) (pinT0 pcL) →
    em.emItems = pre ++ g0 ++ (Wlabel.LCtrl srcs, kc)
      :: (mid ++ (Wlabel.LStore rl a v asrc vsrc, some k) :: post) →
    psitesA pcL own base pre s →
    g0.all provNeutralb = true →
    dsubb (depsCtrl (krole s.psPc)) srcs = true →
    srcsTainted s.psT (depsCtrl (krole s.psPc)) = true →
    j < k →
    segPinC GD ad sg := by
  intro hconf he hx hbase hes hsite hg0 hcov htn hlt
  exact WeakRvwmoPinBridge3.segPinCOfSegPin GD ad sg
    (segPinOfRowDeps GD i em sg j k hconf he hx
      (pctrlRowDepsA _ pcL j own base pre g0 mid post s srcs kc k rl a v asrc vsrc hbase hes
        hsite hg0 hcov htn hlt))

/-- **THE FIRST STORE, ON ANY PATH**: at a load site whose all-paths search accepted (any
certifying `PDep`/`PCtrl`/`PFence` witness gives it, `pinnedbAllPaths`), a store the run reaches
along ANY arms before any pin — not a fence word, not an `own`-excused stack store — is
`segPinC`-pinned to the load.  The taint fact is no longer a premise: `pdfs` soundness supplies
it (`reachesANoFail`, `pstepStoreFed`). -/
theorem pinSegPinFirstStoreA (GD : Gdexec) (ad : List (Geid × Geid)) (i : Nat) (em : Hemission)
    (sg : Seg) (pcL : Int) (j k : Nat) (own : Bool) (base pre g0 post : List Eitem) (s : PState)
    (rl : Bool) (a : Int) (v : List (BitVec 8)) (asrc vsrc : List Dsrc) :
    (∀ jk, jk ∈ rowDeps em.emItems → ((i, jk.1), (i, jk.2)) ∈ GD.gdDeps) →
    sg.sgEntry = (i, j) → sg.sgExit = (i, k) →
    invOk j (dsRun dsInit base) (pinT0 pcL) →
    em.emItems = pre ++ g0 ++ (Wlabel.LStore rl a v asrc vsrc, some k) :: post →
    psitesA pcL own base pre s →
    g0.all provNeutralb = true →
    dsubb (depsAddr (krole s.psPc)) asrc = true → dsubb (depsVsrc (krole s.psPc)) vsrc = true →
    allPathsPinned own pcL = true →
    wIsFence (kw s.psPc) = false → roleIsStore (krole s.psPc) = true →
    (own && stackStore (krole s.psPc)) = false →
    j < k →
    segPinC GD ad sg := by
  intro hconf he hx hbase hes hsite hg0 hca hcv hall hf hst hown hlt
  have ⟨mid, _, hr⟩ := hsite
  have hnf := reachesANoFail own pcL mid s hall hr
  exact pinSegPinStoreA GD ad i em sg pcL j k own base pre g0 post s rl a v asrc vsrc hconf he hx
    hbase hes hsite hg0 hca hcv (WeakRvwmoPinBridge3.pstepStoreFed own s hnf hf hst hown) hlt

/-! ## 8. Non-vacuity of the soundness lemma on real image bytes -/

/-- At `WeakRvwmoAdm`'s spin load (`main+0x16`, the `PFence` site `pinStarted`), NO state the run
can reach along any arms is one the checker rejects. -/
theorem laAllPathsNoFail :
    ∀ x n, preach false (pinStart ((KernelSyms.«main» : Int) + 0x16)) x n →
      pstep false x ≠ none :=
  allPathsPinnedSound false _
    (WeakRvwmoPinBridge3.pinnedbAllPaths pinFuel _ ((KernelSyms.«main» : Int) + 0x18) false _
      (Or.inr (Or.inr rfl)) pinStarted)

end Weak
