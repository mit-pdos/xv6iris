/-
Weak: **W2 CLOSE — `pfStepTso`, the composition of W2's two halves** (allocproc plan
`notes/weak-allocproc-plan.md` §C "W2 CLOSE", [R16.6][R17.2][R17.2-alt], as REPAIRED on day one and
adopted by the coordinator, 2026-10-11).

Lean-only (no Rocq source).  `R_mem := rmem ∧ viewRel cohSrc` (W2a `Weak/PfStepTsoMem.lean` ×
W2b `Weak/PfStepTsoView.lean`).  Main results:

* **`pfStepTso`** — one hart event `o` (the `Outcome` node the hart sits at, `fn = none`, label
  neither `LSilent` nor `LDev`) of a promise-free step is ONE MachCSL `evStep cpu o σ v σ'` for THE
  answer `v` the pf continuation consumed (`p' = .PHart cpu (k v) …`), into an `R_mem`-related
  post-state.  Rows: `regWrite` (inert), fetch (`pfFetchRowMemCut` + the shadow's `itv`), plain
  load (`PfStepTso.loadRow` = `pfLoadRowMem` ∘ `rowLoad` at `minView`), exclusive read
  (`pfExLoadRowMem` + `rowExLoad`), store / exclusive store (`pfStoreRowMem` + `rowStore` /
  `rowExStore`), barrier (`rowFence`), announce (`rowSfenceMarker` / inert).
  `pfStepTsoProposed : PfStepTso.proposedStmt fok` ties it to the adopted statement.
* **the `hsrc` hand-off W2a → W2b**: `PfStepTso.hsrcOfRhist` (`R-hist` + `histOfFind` + the `R-log`
  link give `FlatMem.loadSrcs = shLoadSrcs` at any view where the sources are single-copy atomic).
* companions **`pfStepTsoStutter`** (parked-fence fire / PLIC wire / lost-SC retry: monad kept,
  `σ` unchanged) and **`pfStepTsoSame`** (`LSilent`/`LDev` of any agent, `σ` unchanged), with the
  E-M2 invariances `rmemSameMem`/`viewRelSameRead` and `pfRunSTAuthors` (hypothesis (2) along a
  run from an empty log).

Deviations from the PINNED text (day one, `PROGRESS-W2CLOSE.md`; `PfStepTso.pinnedStmt` is kept
below as a documented NON-theorem): (1) `rest` and `pairAdjacent (st ++ x :: rest)` (a weakening;
the pinned form is unsatisfiable inside an exclusive pair, `PfStepTso.pairAdjacentSnocExLoad`);
(2) the `R-log` link `c.pcLog.map wmTid = (stAuthors st).map some` (without it the statement is
false: `st = []`, a one-message own log, `fence rw,rw` — TsoMem `tv = 1`, shadow `tv = 0`);
(3) the fetch cut `q` (without it false: `ifetchOk … 0` admits a stale fetch after a `fence.i`
that raised `itv` past an own store; `fok` is unconstrained); (4) `ownCoh ∧ exclOkTs` at an
exclusive read (`PFExLoad` checks `readOk … 0` only).  `pfStepTsoStutter` additionally takes "a
parked fence is an `ebarPark`" (an arbitrary `fn = some (_, _, true, _)` would move the shadow).

NOT here: plan item (3), `fiArm` from the instruction structure (hypotheses (c)/(d) of
`pfStepTso`).  It is a fact about the Sail model's event order inside `Functions.try_step` (the
announce follows the cycle's last fetch with no `LInstr` between; no fetch between an announce and
the cycle's barrier), not a step-list fact; see `PROGRESS-W2CLOSE.md`.  `PfStepTsoView.lean`'s
header deviation (4) is therefore left as is (and the brief forbids editing it).
-/
import Weak.PfStepTsoMem
import Weak.PfStepTsoView

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1 LeanRV64D
open TsoShadow PfStepTsoView PfStepTsoMem

namespace PfStepTso

/-- The PINNED statement of plan §C W2 CLOSE ([R16.6][R17.2] + [R17.2-alt]'s five hypotheses),
VERBATIM, as a proposition over `fok`.  A documented NON-theorem: it elaborates but is false at the
fetch row and at every row reading the log length / `ownPub` (header, deviations (2)/(3)), and
vacuous inside an exclusive pair (`pairAdjacentSnocExLoad`).  Superseded by `proposedStmt`. -/
def pinnedStmt (fok : Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop) : Prop :=
  ∀ (c c' : Wpcfg Pexv6 Efab) (st : List (Nat × Wlabel)) (σ : MState) (cpu : CPU)
    (o : Outcome Register RegisterType) (k : o.ret → SailM Unit) (rs : RegFile)
    (fn : Option (Bool × Bool × Bool × Bool)) (ib : Ibch) (l : Wlabel) (p' : Pexv6) (d' : Efab),
    pstepEv (.PHart cpu (.impure (.ok o) k) rs fn ib) c.pcDev l p' d' →
    wpPfStep pstepEv pclsEv (hartAgent cpu) l c c' →
    pairAdjacent (st ++ [(hartAgent cpu, l)]) →
    pfStepFactsT fok TsoShadow.cohSrc st c (hartAgent cpu) l →
    (∀ n va req, o = .memRead n va req → ramBytes req.pa n) →
    (∀ n va req, o = .memWrite n va req → ramBytes req.pa n) →
    rmem c st σ → viewRel TsoShadow.cohSrc σ st →
    fn = none →
    l ≠ .LSilent → (∀ kd ba bs sa sv, l ≠ .LDev kd ba bs sa sv) →
    (o = .barrier .Barrier_RISCV_i →
       (tsoShadow TsoShadow.cohSrc st (hartAgent cpu)).fiArm = true) →
    (∀ n w, o = .instrAnnounce n w → sfAnnB n w = true →
       (tsoShadow TsoShadow.cohSrc st (hartAgent cpu)).fiArm = false) →
    ∃ (v : o.ret) (σ' : MState),
      evStep cpu o σ v σ' ∧
      (∃ rs' fn' ib', p' = .PHart cpu (k v) rs' fn' ib') ∧
      rmem c' (st ++ [(hartAgent cpu, l)]) σ' ∧
      viewRel TsoShadow.cohSrc σ' (st ++ [(hartAgent cpu, l)])

/-- The pinned adjacency hypothesis is unsatisfiable at an exclusive read: the read is the last
step, so no exclusive write follows it. -/
theorem pairAdjacentSnocExLoad (st : List (Nat × Wlabel)) (i : Nat) (aq : Bool) (base : Int)
    (tvs : List (Nat × BitVec 8)) (asrc : List Dsrc) :
    ¬ pairAdjacent (st ++ [(i, .LExLoad aq base tvs asrc)]) := by
  intro h
  obtain ⟨u, hu, -, _, _, _, _, hget, -⟩ := h.1 st.length i aq base tvs asrc (by simp)
  have hl : (st ++ [(i, Wlabel.LExLoad aq base tvs asrc)]).length ≤ u := by
    simp only [List.length_append, List.length_singleton]; omega
  rw [List.getElem?_eq_none hl] at hget
  cases hget

/-- The REPAIRED statement (adopted; proved as `Weak.pfStepTso`, `Weak.pfStepTsoProposed`).  Changes
against `pinnedStmt`, each a hypothesis change, the conclusion and the order of the pinned
explicit parameters unchanged:
(1) `rest` + `pairAdjacent (st ++ (hartAgent cpu, l) :: rest)` — a WEAKENING (`rest = []` is the
    pinned form), so W4 can discharge it inside an exclusive pair;
(2) the `R-log` link `c.pcLog.map wmTid = (stAuthors st).map some` (a `pfRunST` fact from
    `wpInit`, by `wpPfStepAuthors`);
(3) the FETCH cut: a view `q` with `itv ≤ q ≤ |log|` at which every fetched byte's source is at
    or below `q` and not overwritten up to `q` (TsoMem's fetch arm exactly; M1 pristine text: any
    `q ∈ [itv, |log|]`; M2: W5d's cut);
(4) at an exclusive read, `ownCoh c` (preserved by `ownCohStep`) and `exclOkTs` at the read
    (the pair's own write checks it at the store; no foreign step lies between the halves). -/
def proposedStmt (fok : Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop) : Prop :=
  ∀ (c c' : Wpcfg Pexv6 Efab) (st : List (Nat × Wlabel)) (σ : MState) (cpu : CPU)
    (o : Outcome Register RegisterType) (k : o.ret → SailM Unit) (rs : RegFile)
    (fn : Option (Bool × Bool × Bool × Bool)) (ib : Ibch) (l : Wlabel) (p' : Pexv6) (d' : Efab)
    (rest : List (Nat × Wlabel)),
    pstepEv (.PHart cpu (.impure (.ok o) k) rs fn ib) c.pcDev l p' d' →
    wpPfStep pstepEv pclsEv (hartAgent cpu) l c c' →
    pairAdjacent (st ++ (hartAgent cpu, l) :: rest) →                              -- (1)
    pfStepFactsT fok TsoShadow.cohSrc st c (hartAgent cpu) l →
    (∀ n va req, o = .memRead n va req → ramBytes req.pa n) →
    (∀ n va req, o = .memWrite n va req → ramBytes req.pa n) →
    rmem c st σ → viewRel TsoShadow.cohSrc σ st → σ.llog = List.range' 1 σ.log.length →
    c.pcLog.map Wmsg.wmTid = (stAuthors st).map some →                             -- (2)
    (∀ base tvs, l = .LIFetch base tvs →                                           -- (3)
       ∃ q, (tsoShadow TsoShadow.cohSrc st (hartAgent cpu)).itv ≤ q ∧ q ≤ c.pcLog.length ∧
         ifetchOk c.pcImg c.pcLog q base tvs ∧
         ∀ (j t : Nat) (v : BitVec 8), tvs[j]? = some (t, v) → t ≤ q) →
    (∀ aq base tvs asrc, l = .LExLoad aq base tvs asrc →                           -- (4)
       ownCoh c ∧ exclOkTs c.pcLog (hartAgent cpu) base (tvs.map Prod.fst) (c.pcLog.length + 1)) →
    fn = none →
    l ≠ .LSilent → (∀ kd ba bs sa sv, l ≠ .LDev kd ba bs sa sv) →
    (o = .barrier .Barrier_RISCV_i →
       (tsoShadow TsoShadow.cohSrc st (hartAgent cpu)).fiArm = true) →
    (∀ n w, o = .instrAnnounce n w → sfAnnB n w = true →
       (tsoShadow TsoShadow.cohSrc st (hartAgent cpu)).fiArm = false) →
    ∃ (v : o.ret) (σ1 σ' : MState),
      evStep cpu o σ v σ1 ∧
      (σ' = σ1 ∨ (σ1.landOk cpu (σ.top + 1) ∧ σ' = σ1.land cpu (σ.top + 1))) ∧
      (∃ rs' fn' ib', p' = .PHart cpu (k v) rs' fn' ib') ∧
      rmem c' (st ++ [(hartAgent cpu, l)]) σ' ∧
      viewRel TsoShadow.cohSrc σ' (st ++ [(hartAgent cpu, l)]) ∧
      σ'.llog = List.range' 1 σ'.log.length

/-! ## Helpers -/

theorem mapSomeInj {α : Type} : ∀ (l l' : List α), l.map some = l'.map some → l = l'
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | a :: l, b :: l', h => by
    simp only [List.map_cons, List.cons.injEq, Option.some.injEq] at h
    rw [h.1, mapSomeInj l l' h.2]

/-- `R-log` on the TsoMem side: the author log is the step list's. -/
theorem logEq {P D : Type} (c : Wpcfg P D) (st : List (Nat × Wlabel)) (σ : MState)
    (hR : rmem c st σ) (hA : c.pcLog.map Wmsg.wmTid = (stAuthors st).map some) :
    σ.log = stAuthors st :=
  mapSomeInj _ _ (hR.1.1.symm.trans hA)

theorem lenEq {P D : Type} (c : Wpcfg P D) (st : List (Nat × Wlabel)) (σ : MState)
    (hR : rmem c st σ) : σ.log.length = c.pcLog.length := by
  have := congrArg List.length hR.1.1
  simpa using this.symm

/-- A log byte's source, shadow side (`shSrc`) and TsoMem side (`logAuthor`, the author
`TsoOfPf.histOf` records) agree; a source past the image is a log message of that author. -/
theorem srcOf (img : Image) (log : List Wmsg) (au : List Nat)
    (hau : log.map Wmsg.wmTid = au.map some) (t : Nat) (a : Int) (v : BitVec 8)
    (hlb : logByte img log t a = some v) :
    shSrc au t = some (logAuthor log t, t) ∧
    (t = 0 ∨ (0 < t ∧ ∃ m, log[t - 1]? = some m ∧ m.wmTid = some (logAuthor log t))) := by
  cases t with
  | zero => exact ⟨rfl, Or.inl rfl⟩
  | succ p =>
    rw [logByteS] at hlb
    cases hm : log[p]? with
    | none => rw [hm] at hlb; cases hlb
    | some m =>
      have h1 := congrArg (fun l => l[p]?) hau
      simp only [List.getElem?_map, hm, Option.map_some] at h1
      cases hap : au[p]? with
      | none => rw [hap] at h1; cases h1
      | some b =>
        rw [hap] at h1
        simp only [Option.map_some, Option.some.injEq] at h1
        have hla : logAuthor log (p + 1) = b := by simp [logAuthor, hm, h1]
        refine ⟨?_, Or.inr ⟨by omega, m, by simpa using hm, by rw [hla]; exact h1⟩⟩
        simp [shSrc, hap, hla]

/-- A pf plain load's bytes are its sources' log bytes. -/
theorem loadBytes {P D : Type} (pstep : P → D → Wlabel → P → D → Prop)
    (pcls : P → Wlabel → Wstate → WmClass) (i : Nat) (c c' : Wpcfg P D) (aq lat : Bool)
    (base : Int) (tvs : List (Nat × BitVec 8)) (asrc : List Dsrc)
    (h : wpPfStep pstep pcls i (.LLoad aq lat base tvs asrc) c c') :
    ∀ (j t : Nat) (v : BitVec 8), tvs[j]? = some (t, v) → logByte c.pcImg c.pcLog t (base + (j : Int)) = some v := by
  cases h with
  | PFLoad _ _ _ _ _ _ _ _ _ _ _ hrd => exact fun j t v hj => (hrd j t v hj).1

/-- **The `hsrc` hand-off W2a → W2b** ([R13.s3]): under `R-hist` and the `R-log` link, TsoMem's
per-byte sources (`FlatMem.loadSrcs`) at a view where every pf source is single-copy atomic are
the shadow's (`shLoadSrcs`). -/
theorem hsrcOfRhist {P D : Type} (c : Wpcfg P D) (st : List (Nat × Wlabel)) (σ : MState)
    (cpu : CPU) (pa : PAddr) (tvs : List (Nat × BitVec 8)) (tvn : Nat) (hR : rmem c st σ)
    (hA : c.pcLog.map Wmsg.wmTid = (stAuthors st).map some) (hram : ramBytes pa tvs.length)
    (hlb : ∀ (j t : Nat) (v : BitVec 8), tvs[j]? = some (t, v) → logByte c.pcImg c.pcLog t (paZ pa + (j : Int)) = some v)
    (hsca : ∀ (j t : Nat) (v : BitVec 8), tvs[j]? = some (t, v) →
      scaByte c.pcImg c.pcLog (hartAgent cpu) tvn (accAddr (paZ pa) j) t) :
    σ.mem.loadSrcs (hartAgent cpu) tvn pa tvs.length = shLoadSrcs (stAuthors st) tvs := by
  apply List.ext_getElem?
  intro j
  simp only [FlatMem.loadSrcs, shLoadSrcs, List.getElem?_map]
  by_cases hj : j < tvs.length
  · obtain ⟨⟨t, v⟩, htj⟩ : ∃ p, tvs[j]? = some p := ⟨_, List.getElem?_eq_getElem hj⟩
    rw [List.getElem?_range hj, htj]
    obtain ⟨hs, -⟩ := srcOf c.pcImg c.pcLog (stAuthors st) hA t _ v (hlb j t v htj)
    simp only [Option.map_some, hs]
    rw [hR.2.2.1.1 _ (hram j hj), paZAddJ pa _ j (noWrapOfRam pa _ hram) hj]
    simp only [Option.bind_some, Hist.readSrc, Hist.readEnt]
    rw [histOfFind _ _ _ _ (accAddr (paZ pa) j) _ _ (allIsSome c σ hR.1.1) (hlb j t v htj)
      (hsca j t v htj)]
    rfl
  · rw [List.getElem?_eq_none (l := List.range tvs.length) (by simp; omega),
      List.getElem?_eq_none (l := tvs) (by omega)]
    rfl

/-- **The plain-load row, composed** (`pfLoadRowMem` ∘ `rowLoad` at `minView`, the `hsrc` seam
discharged). -/
theorem loadRow {P D : Type} (pstep : P → D → Wlabel → P → D → Prop)
    (pcls : P → Wlabel → Wstate → WmClass) (c c' : Wpcfg P D) (st rest : List (Nat × Wlabel))
    (σ : MState) (cpu : CPU) (pa : PAddr) (aq lat : Bool) (tvs : List (Nat × BitVec 8))
    (asrc : List Dsrc) (w : BitVec (8 * tvs.length)) (hR : rmem c st σ)
    (hV : viewRel cohSrc σ st) (heg : σ.llog = List.range' 1 σ.log.length)
    (hA : c.pcLog.map Wmsg.wmTid = (stAuthors st).map some)
    (hstep : wpPfStep pstep pcls (hartAgent cpu) (.LLoad aq lat (paZ pa) tvs asrc) c c')
    (hadj : pairAdjacent (st ++ (hartAgent cpu, .LLoad aq lat (paZ pa) tvs asrc) :: rest))
    (hram : ramBytes pa tvs.length)
    (hw : ∀ j, j < tvs.length → (tvs.map Prod.snd)[j]? = some (nthByte w j))
    (hsca : scaOkT (tsoShadow cohSrc st (hartAgent cpu)).mem c.pcImg c.pcLog (hartAgent cpu)
      (paZ pa) (tvs.map Prod.fst)) :
    ∃ tvn, σ.tv cpu ≤ tvn ∧ tvn ≤ σ.ltop ∧ (σ.hr cpu).cohOk pa tvs.length tvn ∧
      σ.readFwd cpu tvn pa tvs.length w ∧
      rmem c' (st ++ [(hartAgent cpu, .LLoad aq lat (paZ pa) tvs asrc)])
        (σ.afterLoad cpu pa tvs.length tvn) ∧
      viewRel cohSrc (σ.afterLoad cpu pa tvs.length tvn)
        (st ++ [(hartAgent cpu, .LLoad aq lat (paZ pa) tvs asrc)]) := by
  have hlog := logEq c st σ hR hA
  have hlb := loadBytes pstep pcls _ c c' aq lat (paZ pa) tvs asrc hstep
  obtain ⟨tvn₀, -, hmin, hb₀⟩ := minViewLeSca (tsoShadow cohSrc st (hartAgent cpu)).mem
    c.pcImg c.pcLog (stAuthors st) (hartAgent cpu) (paZ pa) tvs hA hsca
  have hmin' : minView cohSrc st (hartAgent cpu) (paZ pa) tvs ≤ tvn₀ := hmin
  have hvis : ∀ (j t : Nat) (v : BitVec 8), tvs[j]? = some (t, v) →
      scaVis c.pcLog (hartAgent cpu) (minView cohSrc st (hartAgent cpu) (paZ pa) tvs) t := by
    intro j t v hj
    obtain ⟨hs, ho⟩ := srcOf c.pcImg c.pcLog (stAuthors st) hA t _ v (hlb j t v hj)
    rcases ho with rfl | ⟨ht0, m, hm, hmt⟩
    · exact Or.inl (Nat.zero_le _)
    · by_cases hown : logAuthor c.pcLog t = hartAgent cpu
      · exact Or.inr ⟨ht0, m, hm, by rw [hmt, hown]⟩
      · have hsj : (shLoadSrcs (stAuthors st) tvs)[j]? = some (some (logAuthor c.pcLog t, t)) := by
          simp [shLoadSrcs, hj, hs]
        refine Or.inl (Nat.le_trans (shForeignGe _ _ j _ t hsj hown) ?_)
        unfold minView shTvn
        exact Nat.le_max_right _ _
  have hfst : ∀ (j t : Nat) (v : BitVec 8), tvs[j]? = some (t, v) → (tvs.map Prod.fst)[j]? = some t := by
    intro j t v hj; simp [hj]
  have hscaM : ∀ (j t : Nat) (v : BitVec 8), tvs[j]? = some (t, v) → scaByte c.pcImg c.pcLog (hartAgent cpu)
      (minView cohSrc st (hartAgent cpu) (paZ pa) tvs) (accAddr (paZ pa) j) t :=
    fun j t v hj => scaByteMono _ _ _ _ _ _ _ (hb₀ j t (hfst j t v hj)) hmin' (hvis j t v hj)
  have hm := PfStepTsoMem.memEager c st σ hR heg
  have hsrc := hsrcOfRhist c st σ cpu pa tvs _ hR hA hram hlb hscaM
  rw [← PfStepTsoMem.loadSrcsPEager σ.mem σ.lp hm] at hsrc
  have hlt : σ.llog.length = σ.log.length := by rw [heg]; simp
  obtain ⟨⟨h1, h2, h3⟩, hview⟩ :=
    rowLoad σ st cpu pa aq lat tvs asrc hV hlog hlt (ramBytesFit hram) hsrc
  refine ⟨_, h1, h2, h3, ?_,
    (pfFrameRowMem pstep pcls c c' st rest σ _ _ hR hstep (by simp [frameLbl]) hadj).2.2 _ rfl rfl
      rfl rfl, hview⟩
  rw [PfStepTsoMem.readFwdNil σ cpu (hR.2.2.2.2 cpu), PfStepTsoMem.readBytesPEager σ.mem σ.lp hm]
  exact pfLoadRowMem c st σ cpu (hartAgent cpu) pa (paZ pa) tvs.length tvs _ tvn₀ w hR rfl rfl
    hram rfl (fun j t v hj => ⟨hlb j t v hj, hb₀ j t (hfst j t v hj), hvis j t v hj⟩) hmin'
    (fun j hj => by rw [← List.getElem?_map]; exact hw j hj)

/-- The hart's own node step, off a parked fence and the PLIC wire. -/
theorem nodeOf (cpu : CPU) (m : SailM Unit) (rs : RegFile) (fn : Option (Bool × Bool × Bool × Bool))
    (ib : Ibch) (d : Efab) (l : Wlabel) (p' : Pexv6) (d' : Efab)
    (h : pstepEv (.PHart cpu m rs fn ib) d l p' d') (hl : ∀ kd ba bs sa sv, l ≠ .LDev kd ba bs sa sv)
    (hfn : fn = none) :
    ∃ m' ors fn' dd oib obar, pnodeStep m rs ib d.efDev l m' ors fn' dd oib obar ∧
      ∃ rs' ib', p' = .PHart cpu m' rs' fn' ib' := by
  cases p' with
  | PDisk dp => exact h.elim
  | PHart cpu' m' rs' fn' ib' =>
    obtain ⟨rfl, ors, oib, obar, -, -, hh⟩ := h
    rcases hh with ⟨hn, -⟩ | ⟨mm, b, kk, -, hl', -⟩
    · subst hfn
      exact ⟨m', ors, fn', _, oib, obar, hn, rs', ib', rfl⟩
    · exact absurd hl' (hl _ _ _ _ _)

theorem erwInert (e : ErwKind) : lbInert (erwLabel e) = true := by cases e <;> rfl

theorem erwFrame (e : ErwKind) : frameLbl (erwLabel e) := by cases e <;> trivial

theorem ebarFrame (b : barrier_kind) : frameLbl (ebarLabel b) := by
  unfold ebarLabel; split <;> trivial

theorem annFrame (n : Nat) (w : BitVec n) : frameLbl (annLabel n w) := by
  unfold annLabel; split <;> trivial

end PfStepTso

open PfStepTso

/-- **`pfStepTso`** (plan §C W2 CLOSE, [R16.6][R17.2][R17.2-alt] as REPAIRED on day one and
adopted by the coordinator: `PfStepTso.proposedStmt`).  One hart event `o` of a promise-free
step, from an `R_mem`-related pair (`rmem ∧ viewRel cohSrc`), is ONE MachCSL `evStep` answering
THE value `v` the pf continuation took, into an `R_mem`-related post-state. -/
theorem pfStepTso (fok : Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop)
    (c c' : Wpcfg Pexv6 Efab) (st : List (Nat × Wlabel)) (σ : MState) (cpu : CPU)
    (o : Outcome Register RegisterType) (k : o.ret → SailM Unit) (rs : RegFile)
    (fn : Option (Bool × Bool × Bool × Bool)) (ib : Ibch) (l : Wlabel) (p' : Pexv6) (d' : Efab)
    (rest : List (Nat × Wlabel)) :
    pstepEv (.PHart cpu (.impure (.ok o) k) rs fn ib) c.pcDev l p' d' →
    wpPfStep pstepEv pclsEv (hartAgent cpu) l c c' →
    pairAdjacent (st ++ (hartAgent cpu, l) :: rest) →
    pfStepFactsT fok TsoShadow.cohSrc st c (hartAgent cpu) l →
    (∀ n va req, o = .memRead n va req → ramBytes req.pa n) →
    (∀ n va req, o = .memWrite n va req → ramBytes req.pa n) →
    rmem c st σ → viewRel TsoShadow.cohSrc σ st → σ.llog = List.range' 1 σ.log.length →
    c.pcLog.map Wmsg.wmTid = (stAuthors st).map some →
    (∀ base tvs, l = .LIFetch base tvs →
       ∃ q, (tsoShadow TsoShadow.cohSrc st (hartAgent cpu)).itv ≤ q ∧ q ≤ c.pcLog.length ∧
         ifetchOk c.pcImg c.pcLog q base tvs ∧
         ∀ (j t : Nat) (v : BitVec 8), tvs[j]? = some (t, v) → t ≤ q) →
    (∀ aq base tvs asrc, l = .LExLoad aq base tvs asrc →
       ownCoh c ∧ exclOkTs c.pcLog (hartAgent cpu) base (tvs.map Prod.fst) (c.pcLog.length + 1)) →
    fn = none →
    l ≠ .LSilent → (∀ kd ba bs sa sv, l ≠ .LDev kd ba bs sa sv) →
    (o = .barrier .Barrier_RISCV_i →
       (tsoShadow TsoShadow.cohSrc st (hartAgent cpu)).fiArm = true) →
    (∀ n w, o = .instrAnnounce n w → sfAnnB n w = true →
       (tsoShadow TsoShadow.cohSrc st (hartAgent cpu)).fiArm = false) →
    ∃ (v : o.ret) (σ1 σ' : MState),
      evStep cpu o σ v σ1 ∧
      (σ' = σ1 ∨ (σ1.landOk cpu (σ.top + 1) ∧ σ' = σ1.land cpu (σ.top + 1))) ∧
      (∃ rs' fn' ib', p' = .PHart cpu (k v) rs' fn' ib') ∧
      rmem c' (st ++ [(hartAgent cpu, l)]) σ' ∧
      viewRel TsoShadow.cohSrc σ' (st ++ [(hartAgent cpu, l)]) ∧
      σ'.llog = List.range' 1 σ'.log.length := by
  intro hp hstep hadj hfacts hramR hramW hR hV heg hA hfetch hexl hfn hls hld hfi hsf
  have hm := PfStepTsoMem.memEager c st σ hR heg
  have hlog := logEq c st σ hR hA
  obtain ⟨m', ors, fn', dd, oib, obar, hn, rs', ib', rfl⟩ := nodeOf cpu _ rs fn ib c.pcDev l p' d' hp hld hfn
  have frame : frameLbl l → ∀ σ' : MState, σ'.mem = σ.mem → σ'.log = σ.log → σ'.resv = σ.resv →
      σ'.sb = σ.sb → rmem c' (st ++ [(hartAgent cpu, l)]) σ' := fun hl =>
    (pfFrameRowMem pstepEv pclsEv c c' st rest σ _ l hR hstep hl hadj).2.2
  cases o with
  | regRead r => exact absurd hn.1 hls
  | regWrite r v =>
    obtain ⟨rfl, rfl, -⟩ := hn
    exact ⟨PUnit.unit, σ.setReg cpu r v, _, rfl, Or.inl rfl, ⟨_, _, _, rfl⟩, frame (erwFrame _) _ rfl rfl rfl rfl,
      viewRelInert cohSrc σ _ st _ _ (erwInert _) hV (sameReadSetReg σ cpu r v), heg⟩
  | memRead n va req =>
    have hram := hramR n va req rfl
    dsimp only [pnodeStep] at hn
    split at hn
    · obtain ⟨w, -, hl, -⟩ := hn
      exact absurd hl (hld _ _ _ _ _)
    · rcases hn with ⟨hif, w, tvs, hlen, hw, rfl, rfl, -⟩ |
        ⟨hif, ⟨hlat, w, tvs, hlen, hw, rfl, rfl, -⟩ | ⟨hlat, w, tvs, hlen, hw, rfl, rfl, -⟩⟩
      · -- the FETCH
        obtain ⟨q, hq1, hq2, hq3, hq4⟩ := hfetch _ _ rfl
        have hfr := pfFetchRowMemCut c st σ cpu q req.pa (paZ req.pa) n tvs w hR hq3 hq4 rfl hram
          (fun j hj => by rw [← List.getElem?_map]; exact hw j hj)
        refine ⟨.Ok (w, none), σ, σ, Or.inr (Or.inl ⟨hram, hif, q, w, ?_, ?_,
          (PfStepTsoMem.readBytesPEager σ.mem σ.lp hm _ _ _ _ _).2 hfr, rfl, rfl⟩), Or.inl rfl,
          ⟨_, _, _, rfl⟩, frame trivial σ rfl rfl rfl rfl,
          viewRelInert cohSrc σ σ st _ _ rfl hV (sameReadRefl σ), heg⟩
        · rw [(hV cpu).itvEq]; exact hq1
        · show q ≤ σ.llog.length
          rw [heg]; simp only [List.length_range']; rw [lenEq c st σ hR]; exact hq2
      · -- the PLAIN load
        subst hlen
        obtain ⟨tvn, h1, h2, h3, hrb, hrm, hvr⟩ := loadRow pstepEv pclsEv c c' st rest σ cpu req.pa
          _ false tvs [] w hR hV heg hA hstep hadj hram hw hfacts.2.1
        have hpl : akPlain req.access_kind = true := by
          have e1 : akIfetch req.access_kind = false := hif
          have e2 : akExcl req.access_kind = false := hlat
          simp [akPlain, e1, e2]
        exact ⟨.Ok (w, none), _, _, Or.inr (Or.inr (Or.inl ⟨hram, hpl, tvn, w, h1, h2, h3, hrb, rfl,
          rfl⟩)), Or.inl rfl, ⟨_, _, _, rfl⟩, hrm, hvr, heg⟩
      · -- the EXCLUSIVE read
        obtain ⟨hoc, hex⟩ := hexl _ _ _ _ rfl
        obtain ⟨htop, hnor, hrm⟩ := pfExLoadRowMem pstepEv pclsEv c c' st rest σ cpu
          (hartAgent cpu) _ (paZ req.pa) tvs _ req.pa n w hR hstep hoc hex hadj rfl rfl hram hlen
          (fun j hj => by rw [← List.getElem?_map]; exact hw j hj)
        have hlt : σ.llog.length = σ.log.length := by rw [heg]; simp
        exact ⟨.Ok (w, none), _, _, Or.inr (Or.inr (Or.inr ⟨hram, hlat, hnor,
          MState.not_sbOverlaps_of_nil _ _ _ _ (hR.2.2.2.2 cpu), w,
          (PfStepTsoMem.topBytesLEager σ.mem σ.lp hm _ _ _).2 htop, rfl, rfl⟩)), Or.inl rfl,
          ⟨_, _, _, rfl⟩, hrm _ rfl rfl rfl rfl,
          rowExLoad cohSrc σ st cpu req.pa n w _ (paZ req.pa) tvs _ hV hlog hlt, heg⟩
  | memWrite n va req =>
    have hram := hramW n va req rfl
    dsimp only [pnodeStep] at hn
    split at hn
    · split at hn
      · exact absurd hn.2.1 (hld _ _ _ _ _)
      · exact hn.elim
    · split at hn
      · rename_i v hval
        have hd := wbytesLength n v
        have hb : ∀ j, j < n → (WeakInterpProj.wbytes n v)[j]? = some (nthByte v j) :=
          fun j hj => wbytesLookup n v j hj
        have hfit := ramBytesFit hram
        obtain ⟨-, hst⟩ := hn
        rcases hst with ⟨hlat, rfl, rfl, -⟩ | ⟨hlat, ⟨rfl, rfl, -⟩ | ⟨hl, -⟩⟩
        · obtain ⟨hnor, hrm⟩ := pfStoreRowMem pstepEv pclsEv c c' st rest σ cpu (hartAgent cpu)
            false _ (paZ req.pa) _ _ _ req.pa n v hR hstep hadj rfl rfl hram hd hb
          have e : akExcl req.access_kind = false := hlat
          have hsb0 := hR.2.2.2.2 cpu
          have hsbE : ((σ.issue cpu req.pa n v).land cpu (σ.top + 1)).sb = σ.sb := by
            funext c0
            by_cases hc : c0 = cpu
            · subst hc; simp [MState.issue, updCpu, hsb0]
            · simp [MState.land, MState.issue, updCpu, hc]
          refine ⟨.Ok (some true), σ.issue cpu req.pa n v, (σ.issue cpu req.pa n v).land cpu (σ.top + 1),
            Or.inr (Or.inl ⟨hram, e, v, hval, rfl, rfl⟩),
            Or.inr ⟨PfStepTsoMem.landOkIssue σ cpu req.pa n v hm heg hsb0 (Nat.le_of_lt hfit) hnor, rfl⟩,
            ⟨_, _, _, rfl⟩, hrm _ rfl rfl rfl hsbE,
            rowStore σ st cpu req.pa n v _ _ _ _ hd hV hlog hfit, ?_⟩
          show σ.llog ++ [σ.top + 1] = List.range' 1 (σ.log ++ [hartAgent cpu]).length
          rw [heg, List.length_append, List.length_singleton, List.range'_concat]; simp only [MState.top]; congr 2; omega
        · obtain ⟨hnor, hrm⟩ := pfStoreRowMem pstepEv pclsEv c c' st rest σ cpu (hartAgent cpu)
            true _ (paZ req.pa) _ _ _ req.pa n v hR hstep hadj rfl rfl hram hd hb
          have e : akExcl req.access_kind = true := hlat
          have hlt : σ.llog.length = σ.log.length := by rw [heg]; simp
          have hlen : c.pcLog.length = σ.log.length := lenEq c st σ hR |>.symm
          refine ⟨.Ok (some true), σ.storeL cpu req.pa n v, σ.storeL cpu req.pa n v,
            Or.inr (Or.inr ⟨hram, e, v, hval, hnor, MState.landNowOk_of_nil _ _ _ _ _ (hR.2.2.2.2 cpu), rfl,
              rfl⟩), Or.inl rfl, ⟨_, _, _, rfl⟩, hrm _ ?_ rfl rfl rfl,
            rowExStore σ st cpu req.pa n v _ _ _ _ hd hV hlog hlt hfit, ?_⟩
          · show σ.mem.landBytes (lpOf (σ.llog ++ [σ.top + 1])) req.pa n v (σ.top + 1) (hartAgent cpu) = _
            rw [heg]
            exact PfStepTsoMem.landBytesEager σ.mem c.pcImg c.pcLog σ.log.length hlen hR.2.2.1 req.pa n v _
          · show σ.llog ++ [σ.top + 1] = List.range' 1 (σ.log ++ [hartAgent cpu]).length
            rw [heg, List.length_append, List.length_singleton, List.range'_concat]; simp only [MState.top]; congr 2; omega
        · exact absurd hl hls
      · exact hn.elim
  | readRam => exact hn.elim
  | writeRam => exact hn.elim
  | barrier b =>
    obtain ⟨rfl, rfl, -⟩ := hn
    exact ⟨(), σ.fence cpu b, _, ⟨fun _ => hR.2.2.2.2 cpu, rfl⟩, Or.inl rfl, ⟨_, _, _, rfl⟩,
      frame (ebarFrame b) _ rfl rfl rfl rfl,
      rowFence cohSrc σ st cpu b hV hlog heg (fun hb => hfi (by rw [hb])), heg⟩
  | cacheOp _ => exact absurd hn.1 hls
  | tlbi _ => exact absurd hn.1 hls
  | translationStart _ => exact absurd hn.1 hls
  | translationEnd _ => exact absurd hn.1 hls
  | takeException _ => exact absurd hn.1 hls
  | returnException _ => exact absurd hn.1 hls
  | cycleCount => exact absurd hn.1 hls
  | getCycleCount => exact absurd hn.1 hls
  | message _ => exact absurd hn.1 hls
  | choose _ =>
    obtain ⟨_, hl, -⟩ := hn
    exact absurd hl hls
  | instrAnnounce n w =>
    obtain ⟨rfl, rfl, -⟩ := hn
    refine ⟨(), σ, σ, rfl, Or.inl rfl, ⟨_, _, _, rfl⟩, frame (annFrame n w) σ rfl rfl rfl rfl, ?_, heg⟩
    unfold annLabel
    split
    · exact rowSfenceMarker cohSrc σ st cpu hV (hsf n w rfl ‹_›)
    · exact viewRelInert cohSrc σ σ st _ _ rfl hV (sameReadRefl σ)
  | branchAnnounce _ _ => exact absurd hn.1 hls

/-- `pfStepTso` IS the adopted statement. -/
theorem pfStepTsoProposed (fok : Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop) :
    PfStepTso.proposedStmt fok := fun c c' st σ cpu o k rs fn ib l p' d' rest =>
  pfStepTso fok c c' st σ cpu o k rs fn ib l p' d' rest

/-- **`pfStepTsoStutter`** (plan §C W2 CLOSE companion, E-M3): the 0-MachCSL-step hart rows —
a parked-fence fire (`fn = some _`; the PLIC wire too, which keeps the monad) and the lost-SC
retry (`LSilent` at a `memWrite` node) — keep the monad and relate the UNCHANGED `σ`.  Extra
hypothesis: a parked fence is an `ebarPark` (the only `fn'` `pnodeStep` ever sets). -/
theorem pfStepTsoStutter (c c' : Wpcfg Pexv6 Efab) (st : List (Nat × Wlabel)) (σ : MState)
    (cpu : CPU) (o : Outcome Register RegisterType) (k : o.ret → SailM Unit) (rs : RegFile)
    (fn : Option (Bool × Bool × Bool × Bool)) (ib : Ibch) (l : Wlabel) (p' : Pexv6) (d' : Efab)
    (rest : List (Nat × Wlabel)) :
    pstepEv (.PHart cpu (.impure (.ok o) k) rs fn ib) c.pcDev l p' d' →
    wpPfStep pstepEv pclsEv (hartAgent cpu) l c c' →
    pairAdjacent (st ++ (hartAgent cpu, l) :: rest) →
    rmem c st σ → viewRel TsoShadow.cohSrc σ st →
    (∀ f, fn = some f → ∃ b, ebarPark b = some f) →
    (fn ≠ none ∨ ((∃ n va req, o = .memWrite n va req) ∧ l = .LSilent)) →
    (∃ rs' fn' ib', p' = .PHart cpu (.impure (.ok o) k) rs' fn' ib') ∧
      rmem c' (st ++ [(hartAgent cpu, l)]) σ ∧
      viewRel TsoShadow.cohSrc σ (st ++ [(hartAgent cpu, l)]) := by
  intro hp hstep hadj hR hV hpark hcase
  have frame : frameLbl l → rmem c' (st ++ [(hartAgent cpu, l)]) σ := fun hl =>
    (pfFrameRowMem pstepEv pclsEv c c' st rest σ _ l hR hstep hl hadj).2.2 σ rfl rfl rfl rfl
  cases p' with
  | PDisk dp => exact hp.elim
  | PHart cpu' m' rs' fn' ib' =>
    obtain ⟨hc, ors, oib, obar, -, -, hh⟩ := hp
    subst cpu'
    rcases hh with ⟨hn, -⟩ | ⟨mm, b, kk, -, rfl, rfl, -⟩
    · cases fn with
      | some f =>
        obtain ⟨pr, pw, sr, sw⟩ := f
        obtain ⟨rfl, rfl, -⟩ := hn
        obtain ⟨b, hb⟩ := hpark _ rfl
        cases b <;> simp only [ebarPark, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hb
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hb
        refine ⟨⟨_, _, _, rfl⟩, frame trivial, ?_⟩
        exact viewRelStep cohSrc σ σ st cpu _ hV
          (hartRelCongr (hV cpu) (ShSt.fenceNoSucc _ _ true true true) rfl)
          (fun _ _ => ⟨rfl, rfl, rfl⟩)
      | none =>
        obtain ⟨⟨n, va, req, rfl⟩, rfl⟩ := hcase.resolve_left (fun h => h rfl)
        dsimp only [pstepNode, pnodeStep] at hn
        split at hn
        · split at hn
          · cases hn.2.1
          · exact hn.elim
        · split at hn
          · obtain ⟨-, hst⟩ := hn
            rcases hst with ⟨-, h, -⟩ | ⟨-, ⟨h, -⟩ | ⟨-, rfl, -⟩⟩
            · cases h
            · cases h
            · exact ⟨⟨_, _, _, rfl⟩, frame trivial,
                viewRelInert cohSrc σ σ st _ _ rfl hV (sameReadRefl σ)⟩
          · exact hn.elim
    · exact ⟨⟨_, _, _, rfl⟩, frame trivial,
        viewRelInert cohSrc σ σ st _ _ rfl hV (sameReadRefl σ)⟩

/-- **`pfStepTsoSame`** (plan §C W2 CLOSE companion, E-M2/E-M3): an `LSilent` or `LDev` step of
ANY agent relates the UNCHANGED `σ` (MachCSL then moves only `regs`/`devs`/the PLIC pin, under
which `R_mem` is invariant: `rmemSameMem`, `viewRelSameRead`).  Hypotheses weakened from the
hart-node form: no `pstepEv`, no fabric, any `P`/`D`. -/
theorem pfStepTsoSame {P D : Type} (pstep : P → D → Wlabel → P → D → Prop)
    (pcls : P → Wlabel → Wstate → WmClass) (c c' : Wpcfg P D) (st : List (Nat × Wlabel))
    (σ : MState) (i : Nat) (l : Wlabel) (rest : List (Nat × Wlabel)) :
    wpPfStep pstep pcls i l c c' →
    pairAdjacent (st ++ (i, l) :: rest) →
    rmem c st σ → viewRel TsoShadow.cohSrc σ st →
    (l = .LSilent ∨ ∃ kd ba bs sa sv, l = .LDev kd ba bs sa sv) →
    rmem c' (st ++ [(i, l)]) σ ∧ viewRel TsoShadow.cohSrc σ (st ++ [(i, l)]) := by
  intro hstep hadj hR hV hl
  have hfr : frameLbl l := by rcases hl with rfl | ⟨_, _, _, _, _, _, _, rfl⟩ <;> trivial
  have hin : lbInert l = true := by rcases hl with rfl | ⟨_, _, _, _, _, _, _, rfl⟩ <;> rfl
  exact ⟨(pfFrameRowMem pstep pcls c c' st rest σ i l hR hstep hfr hadj).2.2 σ rfl rfl rfl rfl,
    viewRelInert cohSrc σ σ st i l hin hV (sameReadRefl σ)⟩

/-- E-M2: `rmem` reads only `mem`, `log`, `resv`. -/
theorem rmemSameMem {P D : Type} (c : Wpcfg P D) (st : List (Nat × Wlabel)) (σ σ' : MState)
    (hm : σ'.mem = σ.mem) (hl : σ'.log = σ.log) (hr : σ'.resv = σ.resv) (h : rmem c st σ)
    (hx : σ'.sb = σ.sb := by rfl) :
    rmem c st σ' := by
  obtain ⟨⟨h1, h2⟩, h3, h4, h5, h6⟩ := h
  exact ⟨⟨by rw [hl]; exact h1, by rw [hl]; exact h2⟩, h3, by rw [hm]; exact h4,
    fun cpu => by rw [hr]; exact h5 cpu, fun cpu => by rw [hx]; exact h6 cpu⟩

/-- E-M2: `viewRel` reads only `tv`, `hr`, `itv`. -/
theorem viewRelSameRead (stamp : CohStamp) (σ σ' : MState) (st : List (Nat × Wlabel))
    (hs : sameRead σ σ') (h : viewRel stamp σ st) : viewRel stamp σ' st := fun c =>
  hartRelOther σ σ' c _ (h c) (by rw [hs.1]) (by rw [hs.2.1]) (by rw [hs.2.2])

/-- Hypothesis (2) of `pfStepTso` along a run from an empty log (`wpInit`). -/
theorem pfRunSTAuthors {P D : Type} (pstep : P → D → Wlabel → P → D → Prop)
    (pcls : P → Wlabel → Wstate → WmClass)
    (fok : Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop) (stamp : CohStamp)
    {fcutT : Nat → Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop}
    (c0 c : Wpcfg P D) (st : List (Nat × Wlabel)) (h0 : c0.pcLog = [])
    (h : pfRunSTC pstep pcls fok stamp fcutT c0 st c) :
    c.pcLog.map Wmsg.wmTid = (stAuthors st).map some := by
  induction h with
  | nil => simp [h0, stAuthors]
  | snoc c1 c2 st i l _ hs _ _ _ ih =>
    rw [wpPfStepAuthors pstep pcls i l c1 c2 hs, ih, stAuthorsSnoc]
    cases lbWrites l <;> simp

end Weak
