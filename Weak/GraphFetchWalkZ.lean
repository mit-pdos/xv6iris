/-
Weak: **W13 (R′) [OWN.88] — the certification walk at the Zifencei bundle** (plan
`notes/weak-allocproc-plan.md` §C W11-F's Z-twin surface; the re-measurement
`~/dev/weak-orch/parked/PROGRESS-W13R.md`, option (a): (R) as written retired, (R′) — the S–M
Z-side walk W11-F needs — landed as a NEW leaf before W11-F).  Lean-only, no Rocq twin.

`CatLin.cycleKillOfL2CZ` (`GraphFetchKill` §3) carries the cut and certification supplies
`CatLin.cutSupplyCZ`/`CatLin.certSupplyCZ` as bare premises.  The pinned chain discharges its
twins with the zero cut (`cutSupplyOfCycleC`) and the walk engine (`WeakRvwmoWalk` §1–§2,
§3.3–§3.5, §4.2; `WeakRvwmoGlue2.runDataOfCyc`; `CatLin.certSupplyOfWalkC ∘ walkSupplyOfPolicyC`).
This file is the Zifencei twin:

  §1  THE ENGINE at the unpinned supply: `wlkInvZ`/`wlkStepZ`/`wlkInvStepZ`/**`wlkRunZ`**, the
      start `wlkStartInvZ` (the pinned `wlkStart`, unchanged), the per-graph supply `walkStepsZ`
      and policy **`walkPolicyZ`** — PARAMETRIC in a walk invariant `I` the policy chooses (the
      fabric is not constant: `GraphFetchWalkZ.fabConst`/`GraphFetchWalkZ.fabMove` are the two
      instances, the constant one and `fab ∘ dcnt`, with their starts);
  §2  the segment's log arithmetic (`segStepZLog`/`segStepZMsgs`/`wlkStepZOfSeg`, the twins of
      `segStepLog`/`segStepMsgs`/`wlkStepOfSeg`) and `runDataZOfCyc` (`runDataOfCyc`'s twin);
  §3  the supplies: **`CatLin.walkPolicyCZ`** (THE NAMED PREMISE, W10's job, Z side) and
      **`CatLin.certSupplyOfWalkCZ`**; the zero cut at the bundle — it is in the class
      (`GraphFetchHullZ.fetchSrcClosedCut`: no slot is kept), `gfDev`-closed, its hull has empty
      rows — **`CatLin.cutSupplyOfCycleCZC`** (the class supply `CatLin.cutSupplyCZC`) and
      **`CatLin.cutSupplyOfCycleCZ`** (through the stability `GraphFetchHullZ.gfexecConfZFHull`);
  §4  the glue: **`CatLin.cycleKillOfL2CZC`** (the CLASS kill `CatLin.cycleKillCZC` from the class
      cut supply — `cycleKillOfL2CZ`'s body, the induction hypothesis asked only at the class),
      and the composed forms W11-F consumes: **`CatLin.cycleKillOfWalkCZC`**,
      `CatLin.cycleKillOfWalkCZ`, **`CatLin.t2linOfWalkCZ`** — the kill / T2-LIN from the WP
      package, the fetch-view premise, the L2′ claim and `CatLin.walkPolicyCZ` alone.

**Deviations from the pinned walk.**  (1) THE WALK INVARIANT IS A PARAMETER: the pinned
`wlkInv` fixes the constant fabric through `cstOk`'s end clause; at the Zifencei bundle the fabric
moves (`GraphFetchRun` §3, W13 (R′)), so the policy supplies its own invariant `I` (true at the
start, preserved by its steps) — the constant-fabric pinned shape is the instance
`GraphFetchWalkZ.fabConst d0`.  (2) `wlkStepZ` names the post-state (the policy states `I` of it)
and drops `St'.cstDv 0 = St.cstDv 0` (`cstOkZ` now carries `cstDv 0 = d0`).  (3) `walkPolicyZ` is
the per-state STEP supply (`walkSteps`'s shape), not `walkPolicy`'s "non-writes, then one STORE"
segment shape: that shape is a sufficient condition (`wlkStepZOfSeg`), and an exit at an `LRmw`
write would not fit it.  (4) `CatLin.walkPolicyCZ` is stated at what `certSupplyCZ` hands over
(the image, cat consistency, the Zifencei bundle), as `walkPolicyC` is at cat + `gdexecQconf`.

Spec: RVWMO, riscv.cat, Sail, Zifencei and the PMAs are silent on how a proof certifies a run of a
graph; this is proof organisation (FAITHFUL, no trusted text).  Lean-only helpers file-qualified
(`GraphFetchWalkZ.*`).
-/
import Weak.GraphFetchKill
import Weak.GraphFetchHullZ

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open TsoShadow

/-! # 1. THE ENGINE -/

/-- `wlkInv`'s twin (the fabric's boot value is `cstOkZ`'s). -/
def wlkInvZ (boot : Nat → Pexv6) (d0 : Efab) (N : Nat) (G : Gexec) (St : CycState) (n : Nat) :
    Prop :=
  cstOkZ d0 St ∧
  St.cstC.cdImg = G.gxImg ∧
  St.cstPst 0 = (List.range' 0 N).map boot ∧
  wlogPfx G n (cdLogEnd St.cstC)

/-- ONE STEP to `St'`: a certified segment whose appended messages are exactly the one message of
`G`'s `(n+1)`-st write. -/
def wlkStepZ (G : Gexec) (d0 : Efab) (St St' : CycState) (n : Nat) : Prop :=
  ∃ (o : Segout) (w : Geid) (m : Wmsg),
    segStepZ d0 o St St' ∧
    St'.cstC.cdImg = St.cstC.cdImg ∧
    St'.cstPst 0 = St.cstPst 0 ∧
    gwriteAt G (n + 1) = some w ∧
    WeakRvwmoKillArms.gmsg G w = some m ∧
    cdLogEnd St'.cstC = cdLogEnd St.cstC ++ [m]

theorem wlkInvStepZ (boot : Nat → Pexv6) (d0 : Efab) (N : Nat) (G : Gexec) (St St' : CycState)
    (n : Nat) :
    wlkInvZ boot d0 N G St n →
    wlkStepZ G d0 St St' n →
    ∃ o, segStepZ d0 o St St' ∧ wlkInvZ boot d0 N G St' (n + 1) := by
  rintro ⟨_, himg, hpst, hlog⟩ ⟨o, w, m, hst, himg', hpst', hw, hm, hlog'⟩
  refine ⟨o, hst, hst.2.1, by rw [himg', himg], by rw [hpst', hpst], ?_⟩
  rw [hlog']
  exact wlogPfxSnoc G n _ w m hlog hw hm

/-- The per-graph STEP SUPPLY at a walk invariant `I` (`walkSteps`'s twin): from every invariant
state below the write count, a step to a state that keeps `I`. -/
def walkStepsZ (boot : Nat → Pexv6) (d0 : Efab) (N : Nat) (G : Gexec)
    (I : CycState → Nat → Prop) : Prop :=
  ∀ St n, wlkInvZ boot d0 N G St n → I St n → n < (gwrites G).length →
    ∃ St', wlkStepZ G d0 St St' n ∧ I St' (n + 1)

/-- **THE ITERATION** (`wlkRun`'s twin).  `k` is the number of writes that remain. -/
theorem wlkRunZ (boot : Nat → Pexv6) (d0 : Efab) (N : Nat) (G : Gexec)
    (I : CycState → Nat → Prop) (Hsup : walkStepsZ boot d0 N G I) (k : Nat) :
    ∀ n St, wlkInvZ boot d0 N G St n → I St n → n + k = (gwrites G).length →
      ∃ l Sf, segsRunZ d0 l St Sf ∧ wlkInvZ boot d0 N G Sf (gwrites G).length ∧
        I Sf (gwrites G).length := by
  induction k with
  | zero =>
    intro n St hinv hI hn
    refine ⟨[], St, .segsDone St hinv.1, ?_, ?_⟩
    · rw [← hn, Nat.add_zero]
      exact hinv
    · rw [← hn, Nat.add_zero]
      exact hI
  | succ k ih =>
    intro n St hinv hI hn
    obtain ⟨St', hstep, hI'⟩ := Hsup St n hinv hI (by omega)
    obtain ⟨o, hst, hinv'⟩ := wlkInvStepZ boot d0 N G St St' n hinv hstep
    obtain ⟨l, Sf, hrun, hfin, hIf⟩ := ih (n + 1) St' hinv' hI' (by omega)
    exact ⟨o :: l, Sf, .segsMore o l St St' Sf hst hrun, hfin, hIf⟩

/-- THE START (the pinned `wlkStart`: the empty candidate over the graph's image) is invariant. -/
theorem wlkStartInvZ (boot : Nat → Pexv6) (d0 : Efab) (N : Nat) (G : Gexec) :
    wlkInvZ boot d0 N G (wlkStart boot d0 N G) 0 := by
  refine ⟨⟨?_, ⟨fun _ _ => 0, fun _ _ => false, fun _ => rfl, fun _ => rfl, ?_, ?_, ?_⟩, rfl⟩,
    rfl, rfl, wlogPfxNil G⟩
  · apply srvwmoOfWf
    refine (candReachable _ ?_).1
    intro k s hs
    simp [wlkStart] at hs
  · intro k s hs
    change ([] : List Estep)[k]? = some s at hs
    simp at hs
  · intro k s hs
    change ([] : List Estep)[k]? = some s at hs
    simp at hs
  · intro k s hs
    change ([] : List Estep)[k]? = some s at hs
    simp at hs

/-- **THE PER-GRAPH POLICY** (`walkPolicy`'s twin, deviations (1)/(3)): a walk invariant, true at
the start, and the step supply at it. -/
def walkPolicyZ (boot : Nat → Pexv6) (d0 : Efab) (N : Nat) (G : Gexec) : Prop :=
  ∃ I : CycState → Nat → Prop, I (wlkStart boot d0 N G) 0 ∧ walkStepsZ boot d0 N G I

/-! ## 1.1 The fabric invariants -/

/-- The CONSTANT fabric (the pinned walk's): the run ends at `d0`. -/
def GraphFetchWalkZ.fabConst (d0 : Efab) (St : CycState) (_n : Nat) : Prop :=
  St.cstDv (cdEnd St.cstC) = d0

theorem GraphFetchWalkZ.fabConstStart (boot : Nat → Pexv6) (d0 : Efab) (N : Nat) (G : Gexec) :
    GraphFetchWalkZ.fabConst d0 (wlkStart boot d0 N G) 0 := rfl

/-- An invariant state at the constant fabric is a constant-fabric threaded state. -/
theorem GraphFetchWalkZ.fabConstFix (boot : Nat → Pexv6) (d0 : Efab) (N : Nat) (G : Gexec)
    (St : CycState) (n : Nat) :
    wlkInvZ boot d0 N G St n → GraphFetchWalkZ.fabConst d0 St n → GraphFetchRun.cstOkZFix d0 St :=
  fun hinv he => ⟨hinv.1, he⟩

/-- The MOVING fabric (`fab ∘ dcnt`, the realization route's, `hullRunZ`): the run ends at the
fabric after the device events it ran. -/
def GraphFetchWalkZ.fabMove (GF : Gfexec) (fab : Nat → Efab) (St : CycState) (_n : Nat) : Prop :=
  St.cstDv (cdEnd St.cstC) = fab (dcnt GF St.cstC.cdTr (cdEnd St.cstC))

theorem GraphFetchWalkZ.fabMoveStart (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab)
    (N : Nat) (GF : Gfexec) :
    fab 0 = d0 → GraphFetchWalkZ.fabMove GF fab (wlkStart boot d0 N GF.gfGd.gdG) 0 :=
  fun h => h.symm

/-- A step that runs no device event (the count is unchanged) leaves the moving fabric where it
was — such segments stay on the constant-fabric lemmas (`GraphFetchRun.cstOkZFixStep`). -/
theorem GraphFetchWalkZ.fabMoveQuiet (GF : Gfexec) (fab : Nat → Efab) (St St' : CycState)
    (n n' : Nat) :
    GraphFetchWalkZ.fabMove GF fab St n → GraphFetchWalkZ.fabMove GF fab St' n' →
    dcnt GF St'.cstC.cdTr (cdEnd St'.cstC) = dcnt GF St.cstC.cdTr (cdEnd St.cstC) →
    St'.cstDv (cdEnd St'.cstC) = St.cstDv (cdEnd St.cstC) := by
  intro h h' hc
  unfold GraphFetchWalkZ.fabMove at h h'
  rw [h', h, hc]

/-! # 2. THE SEGMENT'S LOG ARITHMETIC, and the run datum -/

theorem segStepZLog (d0 : Efab) (o : Segout) (St St' : CycState) :
    segStepZ d0 o St St' →
    cdLogEnd St'.cstC = cdLogEnd St.cstC ++ trMsgs o.soTr := by
  rintro ⟨_, _, _, htr, _, _⟩
  rw [cdLogEndFull, cdLogEndFull, htr, trMsgsApp]

/-- A "non-writes, then one store" segment appends ONE message (`segStepMsgs`'s twin). -/
theorem segStepZMsgs (d0 : Efab) (o : Segout) (St St' : CycState) (pre : List Lbl) (rl : Bool)
    (base : Int) (vs : List (BitVec 8)) (kc : WmClass) :
    segStepZ d0 o St St' →
    o.soRow = pre ++ [Lbl.LStore rl base vs kc] →
    (∀ lb ∈ pre, lbIsW lb = false) →
    cdLogEnd St'.cstC = cdLogEnd St.cstC ++ [⟨base, vs, some o.soHart, kc⟩] := by
  intro hst hrow hpre
  have hlog := segStepZLog d0 o St St' hst
  obtain ⟨_, _, _, _, hag, hf2⟩ := hst
  rw [hrow] at hf2
  have hf2' := Forall2_fmap_r.1 hf2
  obtain ⟨t1, t2, h1, h2, htr⟩ := Forall2_app_inv_l.1 hf2'
  obtain ⟨s, hs, hnil⟩ : ∃ s, lblReidxW (Lbl.LStore rl base vs kc) s.esLb ∧ t2 = [s] := by
    cases h2 with
    | cons hab hrest => cases hrest; exact ⟨_, hab, rfl⟩
  subst hnil
  have hes : s.esLb = Lbl.LStore rl base vs kc := lblReidxWStore rl base vs kc _ hs
  have key : ∀ (l1 : List Lbl) (l2 : List Estep),
      List.Forall₂ (fun lb s => lblReidxW lb s.esLb) l1 l2 →
      (∀ lb ∈ l1, lbIsW lb = false) → ∀ s' ∈ l2, lbIsW s'.esLb = false := by
    intro l1 l2 h
    induction h with
    | nil => intro _ s' h; exact absurd h List.not_mem_nil
    | @cons a b l1 l2 hab _ ih =>
      intro hp s' hs'
      rcases List.mem_cons.1 hs' with rfl | hs'
      · exact lblReidxWNotw a _ hab (hp a (List.mem_cons_self ..))
      · exact ih (fun lb hlb => hp lb (List.mem_cons_of_mem _ hlb)) s' hs'
  have hpre' : ∀ s' ∈ t1, lbIsW s'.esLb = false := key pre t1 h1 hpre
  have hsag : s.esAg = o.soHart := hag s (by rw [htr]; simp)
  rw [hlog, htr, trMsgsApp, trMsgsNotw t1 hpre', List.nil_append]
  show cdLogEnd St.cstC ++ (esMsg s ++ []) = _
  rw [List.append_nil]
  simp [esMsg, hes, lbWr, lbCls, hsag]

/-- … hence one `wlkStepZ` (`wlkStepOfSeg`'s twin: the pinned policy's segment shape is a
sufficient condition for a step). -/
theorem wlkStepZOfSeg (G : Gexec) (d0 : Efab) (St St' : CycState) (n : Nat) (o : Segout)
    (pre : List Lbl) (rl : Bool) (base : Int) (vs : List (BitVec 8)) (kc : WmClass)
    (w : Geid) :
    segStepZ d0 o St St' →
    o.soRow = pre ++ [Lbl.LStore rl base vs kc] →
    (∀ lb ∈ pre, lbIsW lb = false) →
    St'.cstC.cdImg = St.cstC.cdImg →
    St'.cstPst 0 = St.cstPst 0 →
    gwriteAt G (n + 1) = some w →
    WeakRvwmoKillArms.gmsg G w = some ⟨base, vs, some o.soHart, kc⟩ →
    wlkStepZ G d0 St St' n :=
  fun hst hrow hpre himg hpst hw hm =>
    ⟨o, w, ⟨base, vs, some o.soHart, kc⟩, hst, himg, hpst, hw, hm,
      segStepZMsgs d0 o St St' pre rl base vs kc hst hrow hpre⟩

/-- A certified configuration IS a `RunDataZ` (`runDataOfCyc`'s twin; the shadow clause `candScaT`
is M2's conjunct's second component). -/
theorem runDataZOfCyc (boot : Nat → Pexv6) (d0 : Efab) (N : Nat) (G : Gexec) (S : CycState) :
    cstOkZ d0 S →
    S.cstC.cdImg = G.gxImg →
    S.cstPst 0 = (List.range' 0 N).map boot →
    RunDataZ boot d0 N G S.cstC S.cstPst S.cstDv := by
  rintro ⟨hc, hpo, hdv⟩ himg hpst
  have hsca : candScaT cohSrc S.cstC := by
    obtain ⟨_, _, _, _, hprg⟩ := hpo
    exact hprg.2.1
  exact ⟨hc, himg, hpst, hdv, hsca, hpo⟩

/-! # 3. THE SUPPLIES -/

namespace CatLin

/-- **(R-2) at the Zifencei bundle — THE NAMED PREMISE (W10's job, Z side)**: the certification
walk's per-graph policy on every cat graph carrying the bundle at the image. -/
def walkPolicyCZ (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image) (N : Nat) :
    Prop :=
  ∀ (GF : Gfexec) (ad : List (Geid × Geid)),
    GF.gfGd.gdG.gxImg = im → rvwmoCatAD GF.gfGd ad → GraphFabConf.gfexecConfZF boot d0 fab GF →
    walkPolicyZ boot d0 N GF.gfGd.gdG

/-- **(G-3) DISCHARGED**: the certification supply from the walk (`certSupplyOfWalkC ∘
walkSupplyOfPolicyC`'s twin). -/
theorem certSupplyOfWalkCZ (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image)
    (N : Nat) :
    walkPolicyCZ boot d0 fab im N → certSupplyCZ boot d0 fab im N := by
  intro hpol GF ad _ _ _ him hc hconf _ _ _ _ _
  obtain ⟨I, hI0, hsteps⟩ := hpol GF ad him hc hconf
  obtain ⟨_, Sf, _, hinv, -⟩ :=
    wlkRunZ boot d0 N GF.gfGd.gdG I hsteps (gwrites GF.gfGd.gdG).length 0
      (wlkStart boot d0 N GF.gfGd.gdG) (wlkStartInvZ boot d0 N GF.gfGd.gdG) hI0 (Nat.zero_add _)
  exact ⟨Sf.cstC, Sf.cstPst, Sf.cstDv,
    runDataZOfCyc boot d0 N GF.gfGd.gdG Sf hinv.1 hinv.2.1 hinv.2.2.1, logOfOfPfx _ _ hinv.2.2.2⟩

end CatLin

/-! ## 3.1 The zero cut at the Zifencei bundle -/

/-- The target of an `ioCross` edge is a labelled event. -/
theorem GraphFetchWalkZ.ioCrossLbl (GF : Gfexec) (x y : Geid) :
    gwf GF.gfGd.gdG → gloadValue GF.gfGd.gdG → ioCross GF x y →
    ∃ l, gxLbl GF.gfGd.gdG y = some l := by
  intro hwf hlv h
  cases hy : gxLbl GF.gfGd.gdG y with
  | some l => exact ⟨l, rfl⟩
  | none =>
    exfalso
    have hgmo : y ∉ GF.gfGd.gdG.gxGmo := fun hin => by
      obtain ⟨l, hl, -⟩ := (hwf.2.1 y).1 hin
      rw [hy] at hl
      cases hl
    have hio : gisIo GF.gfGd.gdG y = false := by simp [gisIo, hy]
    have hpo : ∀ x, ¬ WeakRvwmoGraph.gpo GF.gfGd.gdG x y := fun x hp => by
      have := hp.2.2.2
      rw [hy] at this
      cases this
    have hmem : ¬ gmem GF.gfGd.gdG y := fun ⟨l, hl, _⟩ => by
      rw [hy] at hl
      cases hl
    rcases h with hX | hX
    · exact hgmo (CatLin.gcrossEGmo _ x y hwf hlv hX).2.1
    · rcases hX with hX | hX | hX | hX
      · rcases hX with ⟨hp, _⟩ | ⟨hp, _⟩ | ⟨hp, _⟩ | ⟨_, _, hp⟩ | ⟨_, hm, _⟩
        · exact hpo x hp
        · exact hpo x hp
        · exact hpo x hp
        · exact hpo x hp
        · exact hmem hm
      · have h1 := hX.2.1
        rw [hio] at h1
        cases h1
      · exact hpo x hX.1
      · exact hmem hX.2.2.1

/-- `cycleHasEventC` at `ioCross`: a nonempty raw chain names an event, hence a nonempty row. -/
theorem GraphFetchWalkZ.cycleHasEventCZ (GF : Gfexec) (ad : List (Geid × Geid)) (z : Geid)
    (ss : List Seg) :
    CatLin.rvwmoCatAD GF.gfGd ad →
    ss ≠ [] → CatLin.rawChainC GF.gfGd (ioCross GF) z z ss →
    ∃ i, i < GF.gfGd.gdG.gxProg.length ∧ 0 < nrow GF.gfGd.gdG i := by
  intro hc hne hch
  cases ss with
  | nil => exact absurd rfl hne
  | cons s ss =>
    obtain ⟨hx, -, -⟩ := hch
    have hcore := CatLin.catADCore _ _ hc
    obtain ⟨l, hl⟩ := GraphFetchWalkZ.ioCrossLbl GF z s.sgEntry hcore.1 hcore.2.1 hx
    obtain ⟨h1, h2⟩ := glblNrow GF.gfGd.gdG s.sgEntry l hl
    exact ⟨s.sgEntry.1, h1, by omega⟩

theorem GraphFetchWalkZ.zcutDclosed (G : Gexec) (l : List Geid) : dclosed (zcut G) l :=
  fun _ _ _ e' _ _ _ hc => by rw [gcutZcut] at hc; cases hc

/-- The zero cut is IN THE CLASS: no slot is kept, so every emission is source-closed. -/
theorem GraphFetchWalkZ.zcutFetchSrcClosed (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab)
    (GF : Gfexec) :
    GraphFabConf.gfexecConfZF boot d0 fab GF →
    GraphFetchHullZ.fetchSrcClosedCut boot fab GF (zcut GF.gfGd.gdG) := by
  rintro ⟨-, -, -, hrows⟩ i row hrow
  obtain ⟨em, dvi, dvo, tq, h1, h2, h3, h4, h5⟩ := hrows i row hrow
  refine ⟨em, dvi, dvo, tq, h1, h2, h3, h4, h5, ?_⟩
  intro n base tvs _ hslot
  rw [WeakRvwmoGlue2.zcutGetD] at hslot
  exact absurd hslot (Nat.not_lt_zero _)

/-- (P2) at the zero cut's hull: its rows are empty, so are their emissions. -/
theorem GraphFetchWalkZ.zcutEmPremOk (boot : Nat → Pexv6) (GF : Gfexec) :
    GraphFetchBlocks.emPremOk boot (gfHull GF (zcut GF.gfGd.gdG)).gfGd.gdG := by
  intro i row em dvi dvo tq hrow hem
  have hnil : row = [] := by
    have h := zcutHullRows GF.gfGd.gdG i
    change (((gfHull GF (zcut GF.gfGd.gdG)).gfGd.gdG.gxProg[i]?).getD []) = [] at h
    rw [hrow] at h
    exact h
  subst hnil
  have hes : ∀ (es : List Eitem) (pf : Pexv6),
      hemitf dvi dvo tq 0 wsInit [] (boot i) es pf → es = [] := by
    intro es pf h
    cases h
    rfl
  intro n aq base tvs asrc k hn
  rw [hes _ _ hem] at hn
  simp at hn

namespace CatLin

/-- (G-2) IN THE CLASS: a cut, `gfDev`-closed and fetch-source-closed (the class kill's induction
hypothesis applies at it), whose hull has (P2). -/
def cutSupplyCZC (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image) : Prop :=
  ∀ (GF : Gfexec) (ad : List (Geid × Geid)) (z : Geid) (ss : List Seg),
    GF.gfGd.gdG.gxImg = im → rvwmoCatAD GF.gfGd ad → GraphFabConf.gfexecConfZF boot d0 fab GF →
    ss ≠ [] → rawChainC GF.gfGd (ioCross GF) z z ss →
    ∃ cs, cutOk GF.gfGd.gdG cs ∧ dclosed cs GF.gfDev ∧
      GraphFetchHullZ.fetchSrcClosedCut boot fab GF cs ∧
      GraphFetchBlocks.emPremOk boot (gfHull GF cs).gfGd.gdG

/-- **(G-2) IN THE CLASS, UNCONDITIONALLY** (the zero cut; `cutSupplyOfCycleC`'s twin). -/
theorem cutSupplyOfCycleCZC (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image) :
    cutSupplyCZC boot d0 fab im := by
  intro GF ad z ss _ hc hconf hne hch
  obtain ⟨i, hi, hn⟩ := GraphFetchWalkZ.cycleHasEventCZ GF ad z ss hc hne hch
  exact ⟨zcut GF.gfGd.gdG, zcutCutOk _ i hi hn, GraphFetchWalkZ.zcutDclosed _ _,
    GraphFetchWalkZ.zcutFetchSrcClosed boot d0 fab GF hconf, GraphFetchWalkZ.zcutEmPremOk boot GF⟩

/-- The class supply IS the guarded one: by the stability, the hull carries the bundle. -/
theorem cutSupplyCZOfC (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image) :
    cutSupplyCZC boot d0 fab im → cutSupplyCZ boot d0 fab im := by
  intro hcut GF ad z ss him hc hconf hne hch
  obtain ⟨cs, hok, hdc, hcl, hprem⟩ := hcut GF ad z ss him hc hconf hne hch
  have hcore := catADCore _ _ hc
  exact ⟨cs, hok, hdc,
    GraphFetchHullZ.gfexecConfZFHull boot d0 fab GF cs hcore.1 hcore.2.1 hok.1 hdc hconf hcl, hprem⟩

/-- **(G-2) DISCHARGED** (the guarded supply `cycleKillOfL2CZ` names). -/
theorem cutSupplyOfCycleCZ (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image) :
    cutSupplyCZ boot d0 fab im :=
  cutSupplyCZOfC boot d0 fab im (cutSupplyOfCycleCZC boot d0 fab im)

/-! # 4. THE GLUE -/

section glue

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode
open Language.Notation PrimStep
open LeanRV64D

/-- **`cycleKillOfL2CZC`** — THE CLASS KILL (`cycleKillOfL2CZ` with the induction hypothesis asked
only at a cut in the class): from the class cut supply, the certification supply, the
classification at `ioCross`, the WP package and the fetch-view premise. -/
theorem cycleKillOfL2CZC (hlc : HasLC) (GF0 : BundledGFunctors) [MachGpreS hlc GF0]
    [WeakGpreS GF0] (gen : Nat) (σ0 : WGState) (D : CPU → List Register) (hD : ∀ c, (D c).Nodup)
    (Nm : Int → Int → Namespace) (P : Int → Int → Prop)
    (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (N : Nat) :
    freshEra gen σ0 →
    (List.range' 0 N).map boot = epsInit σ0 →
    d0 = efInit σ0.wgdev →
    wpPackage hlc GF0 gen σ0 D →
    (∀ a base, P a base → wpPackageProt hlc GF0 gen σ0 D (Nm a base) a base) →
    (∀ ρ, rtc epfRun (epInit gen, σ0) ρ → efetchItvOk ρ.1 ρ.2) →
    cutSupplyCZC boot d0 fab (imgZ σ0.wgimg) →
    certSupplyCZ boot d0 fab (imgZ σ0.wgimg) N →
    l2ClaimCZ boot d0 fab (imgZ σ0.wgimg) P (badRun gen σ0) →
    cycleKillCZC boot d0 fab (imgZ σ0.wgimg) := by
  intro hfr hb1 hb2 hwp hwpp hcov hcut hcert hl2
  intro GF ad him hc hconf hres hdr hIH x hcyc
  -- (1) the cycle, as `ioCross`-entered segments
  obtain ⟨z, ss, hne, hch⟩ := cycleSegmentsIO GF ad x hc hcyc
  -- (2) the cut in the class, its hull's bundle (the stability), the induction hypothesis
  obtain ⟨cs, hcutok, hdc, hcl, -⟩ := hcut GF ad z ss him hc hconf hne hch
  have hcore := catADCore _ _ hc
  have hconfH :=
    GraphFetchHullZ.gfexecConfZFHull boot d0 fab GF cs hcore.1 hcore.2.1 hcutok.1 hdc hconf hcl
  have hacyH := hIH cs (GraphFetchKill.properCutFOfCut GF cs hcutok hdc) hcl
  -- (3) the certified run datum
  obtain ⟨c, pst, dv, hrd, hlog⟩ := hcert GF ad cs z ss him hc hconf hcutok hconfH hacyH hne hch
  -- (4) the erased run (M2's replay), and the exports at its log
  obtain ⟨t2, σ2, hrtc, hlgeq⟩ :=
    runErasedZ gen σ0 boot d0 N GF.gfGd.gdG c pst dv hfr hcov hb1 hb2 him hrd
  have hpr : protReg P (cdLog c c.cdTr.length) := by
    rw [← hlgeq]
    exact protRegOfRun hlc GF0 gen σ0 D hD Nm P t2 σ2 hfr hwpp hrtc
  -- (5) the classification, and the kill at `ioCross`
  have hnB : ¬ badRun gen σ0 := noBadRun hlc GF0 gen σ0 D hD hfr hwp
  exact cycleKillIOC GF ad z ss hc hres hdr hne
    (rawChainChainCZ GF ad P (cdLog c c.cdTr.length) (badRun gen σ0) ss hc hres hdr hlog hpr hnB
      (hl2 GF ad him hconf (cdLog c c.cdTr.length) z ss hc hlog hpr hne hch) z z ss
      (fun _ h => h) hch)

/-- **`cycleKillOfWalkCZC`** — WHAT W11-F CONSUMES: the class kill from the WP package, the
fetch-view premise, the L2′ claim and the walk policy (both supplies discharged). -/
theorem cycleKillOfWalkCZC (hlc : HasLC) (GF0 : BundledGFunctors) [MachGpreS hlc GF0]
    [WeakGpreS GF0] (gen : Nat) (σ0 : WGState) (D : CPU → List Register) (hD : ∀ c, (D c).Nodup)
    (Nm : Int → Int → Namespace) (P : Int → Int → Prop)
    (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (N : Nat) :
    freshEra gen σ0 →
    (List.range' 0 N).map boot = epsInit σ0 →
    d0 = efInit σ0.wgdev →
    wpPackage hlc GF0 gen σ0 D →
    (∀ a base, P a base → wpPackageProt hlc GF0 gen σ0 D (Nm a base) a base) →
    (∀ ρ, rtc epfRun (epInit gen, σ0) ρ → efetchItvOk ρ.1 ρ.2) →
    walkPolicyCZ boot d0 fab (imgZ σ0.wgimg) N →
    l2ClaimCZ boot d0 fab (imgZ σ0.wgimg) P (badRun gen σ0) →
    cycleKillCZC boot d0 fab (imgZ σ0.wgimg) :=
  fun hfr hb1 hb2 hwp hwpp hcov hpol hl2 =>
    cycleKillOfL2CZC hlc GF0 gen σ0 D hD Nm P boot d0 fab N hfr hb1 hb2 hwp hwpp hcov
      (cutSupplyOfCycleCZC boot d0 fab _) (certSupplyOfWalkCZ boot d0 fab _ N hpol) hl2

/-- The guarded kill from the same premises (`cycleKillOfL2CZ` with both supplies discharged). -/
theorem cycleKillOfWalkCZ (hlc : HasLC) (GF0 : BundledGFunctors) [MachGpreS hlc GF0]
    [WeakGpreS GF0] (gen : Nat) (σ0 : WGState) (D : CPU → List Register) (hD : ∀ c, (D c).Nodup)
    (Nm : Int → Int → Namespace) (P : Int → Int → Prop)
    (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (N : Nat) :
    freshEra gen σ0 →
    (List.range' 0 N).map boot = epsInit σ0 →
    d0 = efInit σ0.wgdev →
    wpPackage hlc GF0 gen σ0 D →
    (∀ a base, P a base → wpPackageProt hlc GF0 gen σ0 D (Nm a base) a base) →
    (∀ ρ, rtc epfRun (epInit gen, σ0) ρ → efetchItvOk ρ.1 ρ.2) →
    walkPolicyCZ boot d0 fab (imgZ σ0.wgimg) N →
    l2ClaimCZ boot d0 fab (imgZ σ0.wgimg) P (badRun gen σ0) →
    cycleKillCZ boot d0 fab (imgZ σ0.wgimg) :=
  fun hfr hb1 hb2 hwp hwpp hcov hpol hl2 =>
    cycleKillOfL2CZ hlc GF0 gen σ0 D hD Nm P boot d0 fab N hfr hb1 hb2 hwp hwpp hcov
      (cutSupplyOfCycleCZ boot d0 fab _) (certSupplyOfWalkCZ boot d0 fab _ N hpol) hl2

/-- **`t2linOfWalkCZ`**: T2-LIN at the Zifencei bundle from the walk policy (`t2linOfL2CZ` with
both supplies discharged). -/
theorem t2linOfWalkCZ (hlc : HasLC) (GF0 : BundledGFunctors) [MachGpreS hlc GF0] [WeakGpreS GF0]
    (gen : Nat) (σ0 : WGState) (D : CPU → List Register) (hD : ∀ c, (D c).Nodup)
    (Nm : Int → Int → Namespace) (P : Int → Int → Prop)
    (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (N : Nat) :
    freshEra gen σ0 →
    (List.range' 0 N).map boot = epsInit σ0 →
    d0 = efInit σ0.wgdev →
    wpPackage hlc GF0 gen σ0 D →
    (∀ a base, P a base → wpPackageProt hlc GF0 gen σ0 D (Nm a base) a base) →
    (∀ ρ, rtc epfRun (epInit gen, σ0) ρ → efetchItvOk ρ.1 ρ.2) →
    walkPolicyCZ boot d0 fab (imgZ σ0.wgimg) N →
    l2ClaimCZ boot d0 fab (imgZ σ0.wgimg) P (badRun gen σ0) →
    ∀ (GF : Gfexec) (ad : List (Geid × Geid)),
      GF.gfGd.gdG.gxImg = imgZ σ0.wgimg →
      rvwmoCatAD GF.gfGd ad → GraphFabConf.gfexecConfZF boot d0 fab GF →
      ioResidueGmo GF → gdiskRead14 GF.gfGd.gdG →
      ∀ x, ¬ tc (racyDIO GF) x x :=
  fun hfr hb1 hb2 hwp hwpp hcov hpol hl2 =>
    t2linOfL2CZ hlc GF0 gen σ0 D hD Nm P boot d0 fab N hfr hb1 hb2 hwp hwpp hcov
      (cutSupplyOfCycleCZ boot d0 fab _) (certSupplyOfWalkCZ boot d0 fab _ N hpol) hl2

end glue

end CatLin

end Weak
