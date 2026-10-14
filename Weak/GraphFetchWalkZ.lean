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

**W10-0 [OWN.94] — the redesign after the W10 sizing (`weak-orch/parked/PROGRESS-W10size.md`).**
`CatLin.walkPolicyCZ` is FALSE (it forces `gwrowGmo`; the memset counterexample is in its docstring)
and is DEPRECATED, with its three consumers (vacuous).  Added:
  §2.1 the `LRmw` exit (`wlkStepZOfRmw`, through `segStepZMsgsW`, any write exit) and the
       message-free segment (`segStepZQuiet`);
  §2.2 THE MACRO-STEP `wlkStepZ'` (a `segsRunZ` run appending one message: `gfDev`-earlier
       message-free I/O segments of other harts may run first, `wlkStepZ'OfQuiet`), its supply
       `walkStepsZ'`, iteration `wlkRunZ'`, policy `walkPolicyZ'` (`walkPolicyZ'OfZ`), run datum
       `GraphFetchWalkZ.runOfWalkZ'`;
  §3   **`CatLin.walkPolicyCZw`** (the policy WITH `gwrowGmo` and the Q1 (b) residue facts — W10's
       named premise now), the generic member run `CatLin.memberRunCZ` (N1 or N2), and THE
       NORMALIZATION, NAMED: **`CatLin.walkMemberCZ`** (`memberRunOfWalkCZw`: N1's member run);
  §4   **`CatLin.cycleKillOfMemberCZC`** (the class kill at a member) and what W11-F consumes:
       **`CatLin.cycleKillOfWalkCZCw`**, `CatLin.cycleKillOfWalkCZw`, **`CatLin.t2linOfWalkCZw`**.
Q1 (b): `certSupplyCZ` (`GraphFetchKill`) also receives `ioResidueGmo`/`gdiskRead14`.

**SUPERSEDED BY N2′ [OWN.94] (`Weak/GraphFetchN2.lean`).**  The `gwrowGmo` path of §3/§4
(`walkPolicyCZw`, `walkMemberCZ`, `memberRunOfWalkCZw`, `cycleKillOfWalkCZCw`, `cycleKillOfWalkCZw`,
`t2linOfWalkCZw`) is kept but OFF W11-F's path: it kills at a member in program write order, and
`walkMemberCZ`'s rwwD-cyclic (2+2W) case is circular (N1 rejected).  N2′ keeps the cycle and the kill
at `GF` and moves only the log to a realized member; W11-F consumes **`CatLin.cycleKillOfWalkCZRC`**
(`tailPolicyCZ`, `acqAqCZ`, `relCoversCZ`, `l2ClaimCZR`) — no `gwrowGmo GF` premise anywhere.

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
import Weak.WeakRvwmoWalkb

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

/-! ## 2.1 W10-0 [OWN.94]: the `LRmw` exit, and message-free segments -/

/-- A write's re-indexed label publishes the same message (`lbWr`, `lbCls`): `lblReidxW` moves only
a read's timestamps (an `LRmw` keeps base, both value lists and class; a store is verbatim). -/
theorem GraphFetchWalkZ.lblReidxWWr (lb lb' : Lbl) :
    lblReidxW lb lb' → lbIsW lb = true → lbWr lb' = lbWr lb ∧ lbCls lb' = lbCls lb := by
  rintro (h | h | h) hw
  · cases lb <;> cases lb' <;> simp_all [lblReidx, lbIsW, lbWr, lbCls]
  · cases lb <;> cases lb' <;> simp_all [lblReidxSub, lbIsW]
  · cases lb <;> cases lb' <;> simp_all [lblPoisoned, lbIsW]

/-- A write-free row re-indexes to a write-free trace. -/
theorem GraphFetchWalkZ.reidxNotw (l1 : List Lbl) (l2 : List Estep) :
    List.Forall₂ (fun lb s => lblReidxW lb s.esLb) l1 l2 →
    (∀ lb ∈ l1, lbIsW lb = false) → ∀ s' ∈ l2, lbIsW s'.esLb = false := by
  intro h
  induction h with
  | nil => intro _ s' h; exact absurd h List.not_mem_nil
  | @cons a b l1 l2 hab _ ih =>
    intro hp s' hs'
    rcases List.mem_cons.1 hs' with rfl | hs'
    · exact lblReidxWNotw a _ hab (hp a (List.mem_cons_self ..))
    · exact ih (fun lb hlb => hp lb (List.mem_cons_of_mem _ hlb)) s' hs'

/-- A MESSAGE-FREE segment (no write in its row — e.g. one that only runs an I/O event, whose
`LIo` label has no `lbWr`) leaves the log where it was. -/
theorem segStepZQuiet (d0 : Efab) (o : Segout) (St St' : CycState) :
    segStepZ d0 o St St' → (∀ lb ∈ o.soRow, lbIsW lb = false) →
    cdLogEnd St'.cstC = cdLogEnd St.cstC := by
  intro hst hrow
  have hlog := segStepZLog d0 o St St' hst
  obtain ⟨_, _, _, _, _, hf2⟩ := hst
  have hf2' := Forall2_fmap_r.1 hf2
  rw [hlog, trMsgsNotw _ (GraphFetchWalkZ.reidxNotw _ _ hf2' hrow), List.append_nil]

/-- A "non-writes, then one WRITE" segment appends ONE message — the exit label's `lbWr`/`lbCls`
(`segStepZMsgs` generalized from an `LStore` exit to any write exit, `LRmw` included). -/
theorem segStepZMsgsW (d0 : Efab) (o : Segout) (St St' : CycState) (pre : List Lbl) (ex : Lbl)
    (base : Int) (vs : List (BitVec 8)) :
    segStepZ d0 o St St' →
    o.soRow = pre ++ [ex] →
    (∀ lb ∈ pre, lbIsW lb = false) →
    lbWr ex = some (base, vs) →
    cdLogEnd St'.cstC = cdLogEnd St.cstC ++ [⟨base, vs, some o.soHart, lbCls ex⟩] := by
  intro hst hrow hpre hwr
  have hlog := segStepZLog d0 o St St' hst
  obtain ⟨_, _, _, _, hag, hf2⟩ := hst
  rw [hrow] at hf2
  have hf2' := Forall2_fmap_r.1 hf2
  obtain ⟨t1, t2, h1, h2, htr⟩ := Forall2_app_inv_l.1 hf2'
  obtain ⟨s, hs, hnil⟩ : ∃ s, lblReidxW ex s.esLb ∧ t2 = [s] := by
    cases h2 with
    | cons hab hrest => cases hrest; exact ⟨_, hab, rfl⟩
  subst hnil
  have hw : lbIsW ex = true := by
    cases ex with
    | LStore => rfl
    | LRmw => rfl
    | LLoad => simp [lbWr] at hwr
    | LFence => simp [lbWr] at hwr
    | LIo => simp [lbWr] at hwr
  obtain ⟨hwr', hcl'⟩ := GraphFetchWalkZ.lblReidxWWr ex s.esLb hs hw
  have hpre' : ∀ s' ∈ t1, lbIsW s'.esLb = false := GraphFetchWalkZ.reidxNotw pre t1 h1 hpre
  have hsag : s.esAg = o.soHart := hag s (by rw [htr]; simp)
  rw [hlog, htr, trMsgsApp, trMsgsNotw t1 hpre', List.nil_append]
  show cdLogEnd St.cstC ++ (esMsg s ++ []) = _
  rw [List.append_nil]
  simp [esMsg, hwr', hwr, hcl', hsag]

/-- **THE `LRmw` STEP** (W10-0 [OWN.94], Q2): a "non-writes, then one `LRmw`" segment is one
`wlkStepZ`.  xv6's only AMO, `amoswap.w.aq` (`acquire`), is an `LRmw` exit: its `LExLoad`+`LExStore`
pair becomes ONE graph `LRmw` (`HFpair`/`hlblRealizesPair`); there is no LR/SC in the kernel
(`GraphFetchBlocks` header (P2)), so no other write exit arises besides `LStore`
(`wlkStepZOfSeg`). -/
theorem wlkStepZOfRmw (G : Gexec) (d0 : Efab) (St St' : CycState) (n : Nat) (o : Segout)
    (pre : List Lbl) (aq rl : Bool) (base : Int) (ts : List Nat) (rvs wvs : List (BitVec 8))
    (kc : WmClass) (w : Geid) :
    segStepZ d0 o St St' →
    o.soRow = pre ++ [Lbl.LRmw aq rl base ts rvs wvs kc] →
    (∀ lb ∈ pre, lbIsW lb = false) →
    St'.cstC.cdImg = St.cstC.cdImg →
    St'.cstPst 0 = St.cstPst 0 →
    gwriteAt G (n + 1) = some w →
    WeakRvwmoKillArms.gmsg G w = some ⟨base, wvs, some o.soHart, kc⟩ →
    wlkStepZ G d0 St St' n :=
  fun hst hrow hpre himg hpst hw hm =>
    ⟨o, w, ⟨base, wvs, some o.soHart, kc⟩, hst, himg, hpst, hw, hm,
      segStepZMsgsW d0 o St St' pre _ base wvs hst hrow hpre rfl⟩

/-! ## 2.2 W10-0 [OWN.94]: THE MACRO-STEP (device ordering) -/

theorem GraphFetchWalkZ.segsRunZApp (d0 : Efab) (l1 l2 : List Segout) (S1 S2 S3 : CycState) :
    segsRunZ d0 l1 S1 S2 → segsRunZ d0 l2 S2 S3 → segsRunZ d0 (l1 ++ l2) S1 S3 := by
  intro h1
  induction h1 with
  | segsDone _ _ => exact fun h2 => h2
  | segsMore o l St St' _ hst _ ih => exact fun h2 => .segsMore o (l ++ l2) St St' S3 hst (ih h2)

/-- A run of message-free segments leaves the log where it was. -/
theorem GraphFetchWalkZ.segsRunZQuiet (d0 : Efab) (l : List Segout) (St St' : CycState) :
    segsRunZ d0 l St St' → (∀ o ∈ l, ∀ lb ∈ o.soRow, lbIsW lb = false) →
    cdLogEnd St'.cstC = cdLogEnd St.cstC := by
  intro h
  induction h with
  | segsDone _ _ => intro _; rfl
  | segsMore o l St St' St'' hst _ ih =>
    intro hq
    rw [ih (fun o' ho' => hq o' (List.mem_cons_of_mem _ ho')),
      segStepZQuiet d0 o St St' hst (hq o (List.mem_cons_self ..))]

/-- **ONE MACRO-STEP** to `St'` (`wlkStepZ` widened, W10-0 [OWN.94]): a certified RUN of segments
whose appended messages are exactly the one message of `G`'s `(n+1)`-st write.  Under the moving
fabric (`GraphFetchWalkZ.fabMove`) a `gfDev`-earlier I/O event of another hart may have to run
first, as a message-free segment (`segStepZQuiet`), before the writing segment. -/
def wlkStepZ' (G : Gexec) (d0 : Efab) (St St' : CycState) (n : Nat) : Prop :=
  ∃ (l : List Segout) (w : Geid) (m : Wmsg),
    segsRunZ d0 l St St' ∧
    St'.cstC.cdImg = St.cstC.cdImg ∧
    St'.cstPst 0 = St.cstPst 0 ∧
    gwriteAt G (n + 1) = some w ∧
    WeakRvwmoKillArms.gmsg G w = some m ∧
    cdLogEnd St'.cstC = cdLogEnd St.cstC ++ [m]

/-- A single step is a macro-step. -/
theorem wlkStepZ'OfStep (G : Gexec) (d0 : Efab) (St St' : CycState) (n : Nat) :
    wlkStepZ G d0 St St' n → wlkStepZ' G d0 St St' n := by
  rintro ⟨o, w, m, hst, himg, hpst, hw, hm, hlog⟩
  exact ⟨[o], w, m, .segsMore o [] St St' St' hst (.segsDone St' hst.2.1), himg, hpst, hw, hm,
    hlog⟩

/-- A message-free prefix run (keeping the image and the boot programs) composes with a
macro-step. -/
theorem wlkStepZ'OfQuiet (G : Gexec) (d0 : Efab) (St S1 St' : CycState) (n : Nat)
    (l : List Segout) :
    segsRunZ d0 l St S1 → (∀ o ∈ l, ∀ lb ∈ o.soRow, lbIsW lb = false) →
    S1.cstC.cdImg = St.cstC.cdImg → S1.cstPst 0 = St.cstPst 0 →
    wlkStepZ' G d0 S1 St' n → wlkStepZ' G d0 St St' n := by
  intro hrun hq himg hpst ⟨l', w, m, hrun', himg', hpst', hw, hm, hlog'⟩
  refine ⟨l ++ l', w, m, GraphFetchWalkZ.segsRunZApp d0 l l' St S1 St' hrun hrun',
    himg'.trans himg, hpst'.trans hpst, hw, hm, ?_⟩
  rw [hlog', GraphFetchWalkZ.segsRunZQuiet d0 l St S1 hrun hq]

theorem wlkInvStepZ' (boot : Nat → Pexv6) (d0 : Efab) (N : Nat) (G : Gexec) (St St' : CycState)
    (n : Nat) :
    wlkInvZ boot d0 N G St n →
    wlkStepZ' G d0 St St' n →
    ∃ l, segsRunZ d0 l St St' ∧ wlkInvZ boot d0 N G St' (n + 1) := by
  rintro ⟨_, himg, hpst, hlog⟩ ⟨l, w, m, hrun, himg', hpst', hw, hm, hlog'⟩
  refine ⟨l, hrun, segsRunZOk d0 l St St' hrun, by rw [himg', himg], by rw [hpst', hpst], ?_⟩
  rw [hlog']
  exact wlogPfxSnoc G n _ w m hlog hw hm

/-- The per-graph MACRO-STEP SUPPLY at a walk invariant `I` (`walkStepsZ` widened). -/
def walkStepsZ' (boot : Nat → Pexv6) (d0 : Efab) (N : Nat) (G : Gexec)
    (I : CycState → Nat → Prop) : Prop :=
  ∀ St n, wlkInvZ boot d0 N G St n → I St n → n < (gwrites G).length →
    ∃ St', wlkStepZ' G d0 St St' n ∧ I St' (n + 1)

/-- THE ITERATION at the macro-step (`wlkRunZ`'s widening). -/
theorem wlkRunZ' (boot : Nat → Pexv6) (d0 : Efab) (N : Nat) (G : Gexec)
    (I : CycState → Nat → Prop) (Hsup : walkStepsZ' boot d0 N G I) (k : Nat) :
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
    obtain ⟨l1, hrun1, hinv'⟩ := wlkInvStepZ' boot d0 N G St St' n hinv hstep
    obtain ⟨l, Sf, hrun, hfin, hIf⟩ := ih (n + 1) St' hinv' hI' (by omega)
    exact ⟨l1 ++ l, Sf, GraphFetchWalkZ.segsRunZApp d0 l1 l St St' Sf hrun1 hrun, hfin, hIf⟩

/-- **THE PER-GRAPH POLICY at the macro-step** (`walkPolicyZ` widened, W10-0 [OWN.94]). -/
def walkPolicyZ' (boot : Nat → Pexv6) (d0 : Efab) (N : Nat) (G : Gexec) : Prop :=
  ∃ I : CycState → Nat → Prop, I (wlkStart boot d0 N G) 0 ∧ walkStepsZ' boot d0 N G I

theorem walkPolicyZ'OfZ (boot : Nat → Pexv6) (d0 : Efab) (N : Nat) (G : Gexec) :
    walkPolicyZ boot d0 N G → walkPolicyZ' boot d0 N G := by
  rintro ⟨I, h0, hs⟩
  refine ⟨I, h0, fun St n hinv hI hn => ?_⟩
  obtain ⟨St', h, h'⟩ := hs St n hinv hI hn
  exact ⟨St', wlkStepZ'OfStep G d0 St St' n h, h'⟩

/-- The macro-step walk certifies a run datum whose log is the graph's (gmo order). -/
theorem GraphFetchWalkZ.runOfWalkZ' (boot : Nat → Pexv6) (d0 : Efab) (N : Nat) (G : Gexec) :
    walkPolicyZ' boot d0 N G →
    ∃ (c : Cand) (pst : Nat → List Pexv6) (dv : Nat → Efab),
      RunDataZ boot d0 N G c pst dv ∧ logOf G (cdLog c c.cdTr.length) := by
  rintro ⟨I, hI0, hsteps⟩
  obtain ⟨_, Sf, _, hinv, -⟩ :=
    wlkRunZ' boot d0 N G I hsteps (gwrites G).length 0 (wlkStart boot d0 N G)
      (wlkStartInvZ boot d0 N G) hI0 (Nat.zero_add _)
  exact ⟨Sf.cstC, Sf.cstPst, Sf.cstDv, runDataZOfCyc boot d0 N G Sf hinv.1 hinv.2.1 hinv.2.2.1,
    logOfOfPfx _ _ hinv.2.2.2⟩

/-! # 3. THE SUPPLIES -/

namespace CatLin

/-- **DEPRECATED — FALSE (W10 sizing, [OWN.94]); W11-F must NOT consume it — use
`CatLin.walkPolicyCZw` + `CatLin.walkMemberCZ`.**  (Was: (R-2) at the Zifencei bundle, the
certification walk's per-graph policy on every cat graph carrying the bundle at the image.)

Why it is false: `walkPolicyZ G` yields a certified run whose log is `G`'s writes in GMO order
(`certSupplyOfWalkCZ`, unconditionally), while a candidate emits each hart's stores in PROGRAM
order (`execProgOk'SC` threads each agent's program), so the policy forces `gwrowGmo G` — same-hart
stores gmo-ordered as in po, a TSO-like order RVWMO does not impose (ppo orders two same-hart
stores to different addresses only through a fence, an AMO, a dependency or rule 12; riscv.cat's
co is per-location).  THE MEMSET COUNTEREXAMPLE: `memset`'s byte loop `sb a1,0(a5); addi a5,a5,1;
bne` (`memset+0x14`, `Xv6/KernelImage.lean`), called by allocproc on `&p->context` (112 bytes,
`p->lock` held), stores 0 to bytes `b` and `b+1` in consecutive iterations — different addresses,
no fence, no AMO, no load-sourced dependency, so no ppo rule 1–13 orders them; a cat graph of a
real boot prefix may put `sb(b+1)` gmo-before `sb(b)` (no read of `b`/`b+1` between them), and
every candidate run of that hart emits `sb(b)` first, so `walkPolicyZ` fails on that graph.  (The
argument needs the hart deterministic on that stretch; that step is not mechanized.) -/
def walkPolicyCZ (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image) (N : Nat) :
    Prop :=
  ∀ (GF : Gfexec) (ad : List (Geid × Geid)),
    GF.gfGd.gdG.gxImg = im → rvwmoCatAD GF.gfGd ad → GraphFabConf.gfexecConfZF boot d0 fab GF →
    walkPolicyZ boot d0 N GF.gfGd.gdG

/-- (G-3) from the walk (`certSupplyOfWalkC ∘ walkSupplyOfPolicyC`'s twin).  **DEPRECATED
(W10-0 [OWN.94])**: its premise `walkPolicyCZ` is FALSE (see there), so this discharges nothing;
the kill route is `CatLin.cycleKillOfWalkCZCw` (a walk at a normalized member). -/
theorem certSupplyOfWalkCZ (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image)
    (N : Nat) :
    walkPolicyCZ boot d0 fab im N → certSupplyCZ boot d0 fab im N := by
  intro hpol GF ad _ _ _ him hc hconf _ _ _ _ _ _ _
  obtain ⟨I, hI0, hsteps⟩ := hpol GF ad him hc hconf
  obtain ⟨_, Sf, _, hinv, -⟩ :=
    wlkRunZ boot d0 N GF.gfGd.gdG I hsteps (gwrites GF.gfGd.gdG).length 0
      (wlkStart boot d0 N GF.gfGd.gdG) (wlkStartInvZ boot d0 N GF.gfGd.gdG) hI0 (Nat.zero_add _)
  exact ⟨Sf.cstC, Sf.cstPst, Sf.cstDv,
    runDataZOfCyc boot d0 N GF.gfGd.gdG Sf hinv.1 hinv.2.1 hinv.2.2.1, logOfOfPfx _ _ hinv.2.2.2⟩

/-- **SUPERSEDED BY N2′ (`Weak/GraphFetchN2.lean`) — off W11-F's path: it needs a `gwrowGmo` graph at the kill; W11-F consumes `CatLin.cycleKillOfWalkCZRC`.** **THE WALK POLICY, STATED WITH `gwrowGmo` (W10-0 [OWN.94]) — THE NAMED PREMISE (W10-2..4's
job, Z side)**: on every cat graph carrying the bundle at the image, with the I/O residue facts
(Q1 (b)) and whose same-hart writes are gmo-ordered as in po (`gwrowGmo`, the walk's
precondition), the macro-step walk policy holds.  `gwrowGmo` is what makes it no longer false: the
memset counterexample (`walkPolicyCZ`) has `sb(b+1)` gmo-before `sb(b)`, which `gwrowGmo` excludes.
The kill gets a `gwrowGmo` graph from the normalization `walkMemberCZ` (FAITHFUL: a different mo
witness of the same execution). -/
def walkPolicyCZw (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image) (N : Nat) :
    Prop :=
  ∀ (GF : Gfexec) (ad : List (Geid × Geid)),
    GF.gfGd.gdG.gxImg = im → rvwmoCatAD GF.gfGd ad → GraphFabConf.gfexecConfZF boot d0 fab GF →
    ioResidueGmo GF → gdiskRead14 GF.gfGd.gdG →
    gwrowGmo GF.gfGd.gdG →
    walkPolicyZ' boot d0 N GF.gfGd.gdG

/-- The old policy (deprecated) implies the new one (it is only weaker as a premise). -/
theorem walkPolicyCZwOfCZ (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image)
    (N : Nat) :
    walkPolicyCZ boot d0 fab im N → walkPolicyCZw boot d0 fab im N :=
  fun hpol GF ad him hc hconf _ _ _ =>
    walkPolicyZ'OfZ boot d0 N GF.gfGd.gdG (hpol GF ad him hc hconf)

/-- **THE MEMBER RUN** (W10-0 [OWN.94], generic over N1/N2): from every cyclic class graph with the
class induction hypothesis, a cyclic class graph `GF'` (a normalized member) together with a
certified run datum whose log is `GF'`'s.  N1 discharges it by `walkMemberCZ` + the walk
(`memberRunOfWalkCZw`); N2 (the maximal cut, `hullRunZ` + a tail walk) would discharge it
directly at its realized member. -/
def memberRunCZ (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image) (N : Nat) :
    Prop :=
  ∀ (GF : Gfexec) (ad : List (Geid × Geid)),
    GF.gfGd.gdG.gxImg = im → rvwmoCatAD GF.gfGd ad → GraphFabConf.gfexecConfZF boot d0 fab GF →
    ioResidueGmo GF → gdiskRead14 GF.gfGd.gdG →
    (∀ cs, properCutF GF cs → GraphFetchHullZ.fetchSrcClosedCut boot fab GF cs →
      ∀ x, ¬ tc (racyDIO (gfHull GF cs)) x x) →
    ∀ x, tc (racyDIO GF) x x →
    ∃ (GF' : Gfexec) (ad' : List (Geid × Geid)) (x' : Geid) (c : Cand)
      (pst : Nat → List Pexv6) (dv : Nat → Efab),
      GF'.gfGd.gdG.gxImg = im ∧ rvwmoCatAD GF'.gfGd ad' ∧
      GraphFabConf.gfexecConfZF boot d0 fab GF' ∧
      ioResidueGmo GF' ∧ gdiskRead14 GF'.gfGd.gdG ∧
      tc (racyDIO GF') x' x' ∧
      RunDataZ boot d0 N GF'.gfGd.gdG c pst dv ∧ logOf GF'.gfGd.gdG (cdLog c c.cdTr.length)

/-- **SUPERSEDED BY N2′ (`Weak/GraphFetchN2.lean`) — off W11-F's path: it needs a `gwrowGmo` graph at the kill; W11-F consumes `CatLin.cycleKillOfWalkCZRC`.** **THE NORMALIZATION — NAMED (W10-0 [OWN.94]; W10-1's job, option N1 or N2 open)**: every
cyclic class graph (with the class induction hypothesis) has a cyclic class graph satisfying
`gwrowGmo` — intended: an equivalent member `GF'` of its orbit (same events, rf, co, deps and
fabric up to the row renaming; only the mo witness differs) with the bundle, the residue facts
and `gwrowGmo`, the cycle transported.  FAITHFUL: it picks another mo witness of the SAME RVWMO
execution (RVWMO's mo is any total order containing ppo and consistent with rf/co; riscv.cat's
co is per-location); assuming `gwrowGmo` of the graph itself would be STRONGER than RVWMO.  The
equivalence is NOT stated: the glue needs only the listed facts, so either discharge fits.  OPEN
(W10 sizing (5)): the `rwwD`-cyclic case (a 2+2W shape), where no member has `gwrowGmo`. -/
def walkMemberCZ (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image) : Prop :=
  ∀ (GF : Gfexec) (ad : List (Geid × Geid)),
    GF.gfGd.gdG.gxImg = im → rvwmoCatAD GF.gfGd ad → GraphFabConf.gfexecConfZF boot d0 fab GF →
    ioResidueGmo GF → gdiskRead14 GF.gfGd.gdG →
    (∀ cs, properCutF GF cs → GraphFetchHullZ.fetchSrcClosedCut boot fab GF cs →
      ∀ x, ¬ tc (racyDIO (gfHull GF cs)) x x) →
    ∀ x, tc (racyDIO GF) x x →
    ∃ (GF' : Gfexec) (ad' : List (Geid × Geid)) (x' : Geid),
      GF'.gfGd.gdG.gxImg = im ∧ rvwmoCatAD GF'.gfGd ad' ∧
      GraphFabConf.gfexecConfZF boot d0 fab GF' ∧
      ioResidueGmo GF' ∧ gdiskRead14 GF'.gfGd.gdG ∧
      gwrowGmo GF'.gfGd.gdG ∧ tc (racyDIO GF') x' x'

/-- **SUPERSEDED BY N2′ (`Weak/GraphFetchN2.lean`) — off W11-F's path: it needs a `gwrowGmo` graph at the kill; W11-F consumes `CatLin.cycleKillOfWalkCZRC`.** N1's member run: the normalization, then the walk at the normalized member. -/
theorem memberRunOfWalkCZw (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image)
    (N : Nat) :
    walkPolicyCZw boot d0 fab im N → walkMemberCZ boot d0 fab im →
    memberRunCZ boot d0 fab im N := by
  intro hpol hnorm GF ad him hc hconf hres hdr hIH x hcyc
  obtain ⟨GF', ad', x', him', hc', hconf', hres', hdr', hrow', hcyc'⟩ :=
    hnorm GF ad him hc hconf hres hdr hIH x hcyc
  obtain ⟨c, pst, dv, hrd, hlog⟩ := GraphFetchWalkZ.runOfWalkZ' boot d0 N GF'.gfGd.gdG
    (hpol GF' ad' him' hc' hconf' hres' hdr' hrow')
  exact ⟨GF', ad', x', c, pst, dv, him', hc', hconf', hres', hdr', hcyc', hrd, hlog⟩

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
  obtain ⟨c, pst, dv, hrd, hlog⟩ :=
    hcert GF ad cs z ss him hc hconf hres hdr hcutok hconfH hacyH hne hch
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

/-- `cycleKillOfWalkCZC`: the class kill from the WP package, the fetch-view premise, the L2′
claim and the walk policy (both supplies discharged).  **DEPRECATED — VACUOUS (W10-0 [OWN.94])**:
its premise `walkPolicyCZ` is FALSE (the memset counterexample, see there); W11-F consumes
`CatLin.cycleKillOfWalkCZCw` instead. -/
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

/-- The guarded kill from the same premises (`cycleKillOfL2CZ` with both supplies discharged).
**DEPRECATED — VACUOUS (W10-0 [OWN.94])**: `walkPolicyCZ` is FALSE; use
`CatLin.cycleKillOfWalkCZw`. -/
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

/-- `t2linOfWalkCZ`: T2-LIN at the Zifencei bundle from the walk policy (`t2linOfL2CZ` with
both supplies discharged).  **DEPRECATED — VACUOUS (W10-0 [OWN.94])**: `walkPolicyCZ` is FALSE; use
`CatLin.t2linOfWalkCZw`. -/
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

/-- **`cycleKillOfMemberCZC`** (W10-0 [OWN.94]) — THE CLASS KILL AT A MEMBER: from the member run
(N1 or N2), the classification at `ioCross`, the WP package and the fetch-view premise.  The cycle
is killed at the member `GF'`, where the certified run's log is the graph's. -/
theorem cycleKillOfMemberCZC (hlc : HasLC) (GF0 : BundledGFunctors) [MachGpreS hlc GF0]
    [WeakGpreS GF0] (gen : Nat) (σ0 : WGState) (D : CPU → List Register) (hD : ∀ c, (D c).Nodup)
    (Nm : Int → Int → Namespace) (P : Int → Int → Prop)
    (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (N : Nat) :
    freshEra gen σ0 →
    (List.range' 0 N).map boot = epsInit σ0 →
    d0 = efInit σ0.wgdev →
    wpPackage hlc GF0 gen σ0 D →
    (∀ a base, P a base → wpPackageProt hlc GF0 gen σ0 D (Nm a base) a base) →
    (∀ ρ, rtc epfRun (epInit gen, σ0) ρ → efetchItvOk ρ.1 ρ.2) →
    memberRunCZ boot d0 fab (imgZ σ0.wgimg) N →
    l2ClaimCZ boot d0 fab (imgZ σ0.wgimg) P (badRun gen σ0) →
    cycleKillCZC boot d0 fab (imgZ σ0.wgimg) := by
  intro hfr hb1 hb2 hwp hwpp hcov hmem hl2
  intro GF ad him hc hconf hres hdr hIH x hcyc
  -- (1) the member, its cycle and its certified run datum
  obtain ⟨GF', ad', x', c, pst, dv, him', hc', hconf', hres', hdr', hcyc', hrd, hlog⟩ :=
    hmem GF ad him hc hconf hres hdr hIH x hcyc
  -- (2) the member's cycle, as `ioCross`-entered segments
  obtain ⟨z, ss, hne, hch⟩ := cycleSegmentsIO GF' ad' x' hc' hcyc'
  -- (3) the erased run (M2's replay), and the exports at its log
  obtain ⟨t2, σ2, hrtc, hlgeq⟩ :=
    runErasedZ gen σ0 boot d0 N GF'.gfGd.gdG c pst dv hfr hcov hb1 hb2 him' hrd
  have hpr : protReg P (cdLog c c.cdTr.length) := by
    rw [← hlgeq]
    exact protRegOfRun hlc GF0 gen σ0 D hD Nm P t2 σ2 hfr hwpp hrtc
  -- (4) the classification, and the kill at `ioCross`, at the member
  have hnB : ¬ badRun gen σ0 := noBadRun hlc GF0 gen σ0 D hD hfr hwp
  exact cycleKillIOC GF' ad' z ss hc' hres' hdr' hne
    (rawChainChainCZ GF' ad' P (cdLog c c.cdTr.length) (badRun gen σ0) ss hc' hres' hdr' hlog hpr
      hnB (hl2 GF' ad' him' hconf' (cdLog c c.cdTr.length) z ss hc' hlog hpr hne hch) z z ss
      (fun _ h => h) hch)

/-- **SUPERSEDED BY N2′ (`Weak/GraphFetchN2.lean`) — off W11-F's path: it needs a `gwrowGmo` graph at the kill; W11-F consumes `CatLin.cycleKillOfWalkCZRC`.** **`cycleKillOfWalkCZCw`** — (was) WHAT W11-F CONSUMES (W10-0 [OWN.94], replacing the vacuous
`cycleKillOfWalkCZC`): the class kill from the WP package, the fetch-view premise, the L2′ claim,
the walk policy WITH `gwrowGmo` (`walkPolicyCZw`) and the NAMED normalization (`walkMemberCZ`). -/
theorem cycleKillOfWalkCZCw (hlc : HasLC) (GF0 : BundledGFunctors) [MachGpreS hlc GF0]
    [WeakGpreS GF0] (gen : Nat) (σ0 : WGState) (D : CPU → List Register) (hD : ∀ c, (D c).Nodup)
    (Nm : Int → Int → Namespace) (P : Int → Int → Prop)
    (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (N : Nat) :
    freshEra gen σ0 →
    (List.range' 0 N).map boot = epsInit σ0 →
    d0 = efInit σ0.wgdev →
    wpPackage hlc GF0 gen σ0 D →
    (∀ a base, P a base → wpPackageProt hlc GF0 gen σ0 D (Nm a base) a base) →
    (∀ ρ, rtc epfRun (epInit gen, σ0) ρ → efetchItvOk ρ.1 ρ.2) →
    walkPolicyCZw boot d0 fab (imgZ σ0.wgimg) N →
    walkMemberCZ boot d0 fab (imgZ σ0.wgimg) →
    l2ClaimCZ boot d0 fab (imgZ σ0.wgimg) P (badRun gen σ0) →
    cycleKillCZC boot d0 fab (imgZ σ0.wgimg) :=
  fun hfr hb1 hb2 hwp hwpp hcov hpol hnorm hl2 =>
    cycleKillOfMemberCZC hlc GF0 gen σ0 D hD Nm P boot d0 fab N hfr hb1 hb2 hwp hwpp hcov
      (memberRunOfWalkCZw boot d0 fab _ N hpol hnorm) hl2

/-- **SUPERSEDED BY N2′ (`Weak/GraphFetchN2.lean`) — off W11-F's path: it needs a `gwrowGmo` graph at the kill; W11-F consumes `CatLin.cycleKillOfWalkCZRC`.** The guarded kill from the same premises (`cycleKillOfWalkCZCw` through `cycleKillCZOfC`). -/
theorem cycleKillOfWalkCZw (hlc : HasLC) (GF0 : BundledGFunctors) [MachGpreS hlc GF0]
    [WeakGpreS GF0] (gen : Nat) (σ0 : WGState) (D : CPU → List Register) (hD : ∀ c, (D c).Nodup)
    (Nm : Int → Int → Namespace) (P : Int → Int → Prop)
    (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (N : Nat) :
    freshEra gen σ0 →
    (List.range' 0 N).map boot = epsInit σ0 →
    d0 = efInit σ0.wgdev →
    wpPackage hlc GF0 gen σ0 D →
    (∀ a base, P a base → wpPackageProt hlc GF0 gen σ0 D (Nm a base) a base) →
    (∀ ρ, rtc epfRun (epInit gen, σ0) ρ → efetchItvOk ρ.1 ρ.2) →
    walkPolicyCZw boot d0 fab (imgZ σ0.wgimg) N →
    walkMemberCZ boot d0 fab (imgZ σ0.wgimg) →
    l2ClaimCZ boot d0 fab (imgZ σ0.wgimg) P (badRun gen σ0) →
    cycleKillCZ boot d0 fab (imgZ σ0.wgimg) :=
  fun hfr hb1 hb2 hwp hwpp hcov hpol hnorm hl2 =>
    cycleKillCZOfC boot d0 fab _
      (cycleKillOfWalkCZCw hlc GF0 gen σ0 D hD Nm P boot d0 fab N hfr hb1 hb2 hwp hwpp hcov hpol
        hnorm hl2)

/-- **SUPERSEDED BY N2′ (`Weak/GraphFetchN2.lean`) — off W11-F's path: it needs a `gwrowGmo` graph at the kill; W11-F consumes `CatLin.cycleKillOfWalkCZRC`.** **`t2linOfWalkCZw`**: T2-LIN at the Zifencei bundle from the walk policy with `gwrowGmo` and
the named normalization. -/
theorem t2linOfWalkCZw (hlc : HasLC) (GF0 : BundledGFunctors) [MachGpreS hlc GF0]
    [WeakGpreS GF0] (gen : Nat) (σ0 : WGState) (D : CPU → List Register) (hD : ∀ c, (D c).Nodup)
    (Nm : Int → Int → Namespace) (P : Int → Int → Prop)
    (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (N : Nat) :
    freshEra gen σ0 →
    (List.range' 0 N).map boot = epsInit σ0 →
    d0 = efInit σ0.wgdev →
    wpPackage hlc GF0 gen σ0 D →
    (∀ a base, P a base → wpPackageProt hlc GF0 gen σ0 D (Nm a base) a base) →
    (∀ ρ, rtc epfRun (epInit gen, σ0) ρ → efetchItvOk ρ.1 ρ.2) →
    walkPolicyCZw boot d0 fab (imgZ σ0.wgimg) N →
    walkMemberCZ boot d0 fab (imgZ σ0.wgimg) →
    l2ClaimCZ boot d0 fab (imgZ σ0.wgimg) P (badRun gen σ0) →
    ∀ (GF : Gfexec) (ad : List (Geid × Geid)),
      GF.gfGd.gdG.gxImg = imgZ σ0.wgimg →
      rvwmoCatAD GF.gfGd ad → GraphFabConf.gfexecConfZF boot d0 fab GF →
      ioResidueGmo GF → gdiskRead14 GF.gfGd.gdG →
      ∀ x, ¬ tc (racyDIO GF) x x :=
  fun hfr hb1 hb2 hwp hwpp hcov hpol hnorm hl2 =>
    t2linOfCycleKillCZ boot d0 fab _
      (cycleKillOfWalkCZw hlc GF0 gen σ0 D hD Nm P boot d0 fab N hfr hb1 hb2 hwp hwpp hcov hpol
        hnorm hl2)

end glue

end CatLin

end Weak
