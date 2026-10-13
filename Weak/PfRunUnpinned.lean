/-
Weak: **M2, the fork path on the pf side — the UNPINNED shaped replay with the cut-form fetch
clause** (allocproc plan W5d, §B(4)(iii), §C Stage 1b "W5d"; [OWN.3], [R28.4], [R29.1], [R30.1],
[R31.1] route (i), [R31.s1]–[R31.s3]).

Lean-only (no Rocq source).  M1 (`srvwmoXv6M1Core`) replays a candidate whose program LTS is
PINNED to the boot image (`pstepPin`, every fetch reads image bytes at timestamp 0), so a fetch of
a user page written after boot (`uvmfirst`, `exec`) is not a candidate there.  M2 drops the pin:
the candidate runs on `pstepEv` itself, and the fetch clause is the Zifencei CUT FORM at the
TsoMem instruction view `itv` (plan §B(4)(iii) "Fix now"):

  `fcutM2 itv img log i base tvs := ∃ q, itv ≤ q ∧ q ≤ |log| ∧ ifetchOk img log q base tvs ∧
     ∀ byte (t, v) of tvs, t ≤ q`

(per-byte `t ≤ q` is [W2s]'s correction: `ifetchByteOk … q` admits a source `t > q`, which
TsoMem at `tvn := q` cannot read).  The pf machine has no `itv`; the clause's `itv` is the
step-list SHADOW's (`tsoShadow`, `TsoShadow.lean`), which the Exec side cannot compute (the two
`LFence false×4` labels — `fence.i` and the `sfence.vma` marker — are the same `Estep`, and the
raise is decided by the shadow's `fiArm` STATE, [R31.1]).  So M2's premise set carries TWO FREE
functions (no shared definition takes them [R30.1]):

* `itvOf : Nat → Nat → Nat` — per trace index and agent, the instruction view;
* `fiOf : Nat → Nat → Bool` — per trace index and agent, the `fiArm` bit (route (i) of [R31.1]),

constrained per index by M2's instance `fcutEM2` of `execProgOk'SC`'s per-index clause `fcutE`
(closing over the execution `E`, [R31.s1]): the leading star's fetches satisfy `fcutM2` at
`itvOf k ag`; `fiOf (k+1) ag` is the star's `LInstr`/`LIFetch` fold of `fiOf k ag` (`fiFold`);
`itvOf (k+1) ag` raises at a `LFence false×4` realizing label iff that fold is armed, to
`max itv (fencePost true false tv rv (ownPub ag au))` at the trace shadow's `tv`/`rv` and the
log's authors (MachCSL's `fence.i` arm, `Lang.lean:155-163`); every other agent is framed; the
boot values are `itvOf 0 i = 0`, `fiOf 0 i = false` (`ShFull.zero`, [R31.s3]).

Main results:
* `execPrefixPfRunProgF` / **`execWfPfRunProgF`** — THE M2 REPLAY: under `execProgOk'STC` at
  `fcutEM2` (unpinned LTS, any `fok`), every prefix of an `execWf` execution is the projection of
  a `pfRunSTC … fcutM2` run (each fetch carrying the cut clause at ITS prefix shadow's `itv`),
  `pairAdjacent`, with the memory projection lemma and THE REPLAY INVARIANT
  `(tsoShadow stamp st i).itv = itvOf n i ∧ (tsoShadow stamp st i).fiArm = fiOf n i` — proved by
  construction, no Sail fact used ([R31.1] (i)).  The admin star is replayed WITHOUT the pin: a
  fetch's pf-admissibility `ifetchOk … 0` (`PFIFetch`) follows from the cut form (`fcutM2Ifetch0`).
* `srvwmoXv6M2Premises` — M2's premise set (M1's with the unpinned LTS, `fok := fokTriv`, the
  per-index clause `fcutEM2 cohSrc (candExec c) itvOf fiOf`, and the boot values).
* `srvwmoXv6M2PfRun`, `PfRunUnpinned.m2Hyps` (`MachOfPf.HypsC` at `fcutM2`: `cut` IS the step's
  `pfCutFactsT` verbatim, `fi` from `sailCycleOrder` by `fiOfSco`) and **`srvwmoXv6M2Core`** — the
  composed theorem: M1's conclusions (the MachCSL run, every closed xv6 theorem at it, the
  allocproc shadow) for every M2 candidate.

Deviations from the plan's text: (1) the M2 premise set uses `fok := fokTriv` (the plan's
"worker's choice"): the cut clause lives in `fcutEM2`/`fcutM2`, whose cut form also supplies the
pf view-0 check; (2) `fcutEM2` reads the realizing label from `E.exTr[k]?` (closing over `E`,
[R31.s1]); (3) `srvwmoXv6M2Core` also returns the replay invariant (`itv`/`fiArm` of the run's
shadow are `itvOf`/`fiOf` at the trace's end).

Lean-only helpers are file-qualified (`PfRunUnpinned.*`).  Axioms: `propext`, `Classical.choice`,
`Quot.sound` for the replay; `srvwmoXv6M2Core` adds `xv6FsAdequacy_closed`'s cone, as M1.
-/
import Weak.SrvwmoXv6Adequacy

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open TsoShadow PfStepTsoView

/-! ## (1) The M2 clauses -/

/-- The `fiArm` bit after one label (`shStepF`'s third component): `LInstr` arms, `LIFetch`
disarms, every other label keeps it. -/
def PfRunUnpinned.fiStep (b : Bool) (l : Wlabel) : Bool :=
  match l with
  | .LInstr => true
  | .LIFetch .. => false
  | _ => b

/-- The `fiArm` bit after a star's labels. -/
def PfRunUnpinned.fiFold (b : Bool) (ls : List Wlabel) : Bool := ls.foldl PfRunUnpinned.fiStep b

/-- The all-false fence on the axiomatic alphabet (`fence.i` / the `sfence.vma` marker). -/
def PfRunUnpinned.lbFenceZeroL (lb : Lbl) : Bool :=
  match lb with
  | .LFence false false false false => true
  | _ => false

/-- **THE M2 FETCH CLAUSE** (the cut form, §B(4)(iii)): a cut `q` between the instruction view and
the log's end at which the fetch is admissible, every byte's source at or below `q`. -/
def PfRunUnpinned.fcutM2 (itv : Nat) (img : Image) (log : List Wmsg) (_i : Nat) (base : Int)
    (tvs : List (Nat × BitVec 8)) : Prop :=
  ∃ q, itv ≤ q ∧ q ≤ log.length ∧ ifetchOk img log q base tvs ∧
    ∀ (j t : Nat) (v : BitVec 8), tvs[j]? = some (t, v) → t ≤ q

/-- The cut form implies the pf machine's view-0 fetch check (`PFIFetch`). -/
theorem PfRunUnpinned.fcutM2Ifetch0 (itv : Nat) (img : Image) (log : List Wmsg) (i : Nat)
    (base : Int) (tvs : List (Nat × BitVec 8)) :
    PfRunUnpinned.fcutM2 itv img log i base tvs → ifetchOk img log 0 base tvs := by
  rintro ⟨q, -, -, hif, -⟩ j t v hj
  exact (ifetchByteOk0 img log _ t v).2 (hif j t v hj).1

/-- The instruction view after index `k` of agent `ag` (the realizing label read from `E`): a
`LFence false×4` raises it iff `arm` (the `fiArm` bit after the leading star), to MachCSL's
`fence.i` value at the trace shadow's `tv`/`rv` and the log's authors before the step. -/
def PfRunUnpinned.itvStep (stamp : CohStamp) (E : Exec) (k ag itv : Nat) (arm : Bool) : Nat :=
  match E.exTr[k]? with
  | some s =>
    if PfRunUnpinned.lbFenceZeroL s.esLb && arm then
      max itv (MachCSL.fencePost true false (shadowRun stamp ag (E.exTr.take k)).2.tv
        (shadowRun stamp ag (E.exTr.take k)).2.rv
        (MachCSL.ownPub ag (shadowRun stamp ag (E.exTr.take k)).1))
    else itv
  | none => itv

/-- **M2's PER-INDEX CLAUSE** (`execProgOk'SC`'s `fcutE` at M2, closing over `E` [R31.s1]; route
(i) of [R31.1]): the cut at every fetch of the leading star, the `fiOf` recurrence, the `itvOf`
recurrence and the frame condition on every other agent. -/
def PfRunUnpinned.fcutEM2 (stamp : CohStamp) (E : Exec) (itvOf : Nat → Nat → Nat)
    (fiOf : Nat → Nat → Bool) (k ag : Nat) (ls : List Wlabel) (σ : Mstate) : Prop :=
  (∀ (base : Int) (tvs : List (Nat × BitVec 8)), Wlabel.LIFetch base tvs ∈ ls →
    PfRunUnpinned.fcutM2 (itvOf k ag) σ.msImg σ.msLog ag base tvs) ∧
  fiOf (k + 1) ag = PfRunUnpinned.fiFold (fiOf k ag) ls ∧
  itvOf (k + 1) ag = PfRunUnpinned.itvStep stamp E k ag (itvOf k ag)
    (PfRunUnpinned.fiFold (fiOf k ag) ls) ∧
  ∀ i, i ≠ ag → fiOf (k + 1) i = fiOf k i ∧ itvOf (k + 1) i = itvOf k i

/-- The trivial fetch clause (M2's `fok`; the cut lives in `fcutEM2`). -/
abbrev PfRunUnpinned.fokTriv : Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop :=
  fun _ _ _ _ _ => True

/-! ## (2) The shadow's `itv`/`fiArm` over admin steps, fused steps and pair blocks -/

/-- Another agent's steps leave the shadow alone. -/
theorem PfRunUnpinned.shadowAppOther (stamp : CohStamp) (j : Nat) :
    ∀ (b st : List (Nat × Wlabel)), (∀ y, y ∈ b → y.1 ≠ j) →
      tsoShadow stamp (st ++ b) j = tsoShadow stamp st j
  | [], st, _ => by simp
  | y :: b, st, h => by
    rw [show st ++ y :: b = (st ++ [y]) ++ b by simp,
      PfRunUnpinned.shadowAppOther stamp j b _ (fun z hz => h z (by simp [hz]))]
    obtain ⟨a, l⟩ := y
    exact tsoShadowOther stamp st a l j (h (a, l) (by simp))

/-- An own administrative step keeps `itv` and folds `fiArm`. -/
theorem PfRunUnpinned.shadowAdmin (stamp : CohStamp) (instr : Bool) (st : List (Nat × Wlabel))
    (i : Nat) (l : Wlabel) (h : lbAdmin instr l) :
    (tsoShadow stamp (st ++ [(i, l)]) i).itv = (tsoShadow stamp st i).itv ∧
    (tsoShadow stamp (st ++ [(i, l)]) i).fiArm =
      PfRunUnpinned.fiStep (tsoShadow stamp st i).fiArm l := by
  rw [tsoShadowOwn]
  cases l <;> simp_all [lbAdmin, shStepF, lbFenceZero, PfRunUnpinned.fiStep]

/-- An own administrative star keeps `itv` and folds `fiArm` over its labels. -/
theorem PfRunUnpinned.shadowAdminRun (stamp : CohStamp) (instr : Bool) (i : Nat) :
    ∀ (ls : List Wlabel) (st : List (Nat × Wlabel)), (∀ l, l ∈ ls → lbAdmin instr l) →
      (tsoShadow stamp (st ++ ls.map (fun l => (i, l))) i).itv = (tsoShadow stamp st i).itv ∧
      (tsoShadow stamp (st ++ ls.map (fun l => (i, l))) i).fiArm =
        PfRunUnpinned.fiFold (tsoShadow stamp st i).fiArm ls
  | [], st, _ => by simp [PfRunUnpinned.fiFold]
  | l :: ls, st, h => by
    rw [show st ++ (l :: ls).map (fun l => (i, l)) = (st ++ [(i, l)]) ++ ls.map (fun l => (i, l))
      by simp]
    obtain ⟨h1, h2⟩ := PfRunUnpinned.shadowAdminRun stamp instr i ls (st ++ [(i, l)])
      (fun l' hl' => h l' (by simp [hl']))
    obtain ⟨h3, h4⟩ := PfRunUnpinned.shadowAdmin stamp instr st i l (h l (by simp))
    refine ⟨h1.trans h3, ?_⟩
    rw [h2, h4]
    rfl

/-- A block of own steps none of which is a `LFence false×4`, an `LInstr` or a fetch keeps `itv`
and `fiArm`. -/
theorem PfRunUnpinned.shadowInert (stamp : CohStamp) (i : Nat) :
    ∀ (b st : List (Nat × Wlabel)),
      (∀ y, y ∈ b → lbFenceZero y.2 = false ∧ y.2 ≠ .LInstr ∧ ∀ base tvs, y.2 ≠ .LIFetch base tvs) →
      (tsoShadow stamp (st ++ b) i).itv = (tsoShadow stamp st i).itv ∧
      (tsoShadow stamp (st ++ b) i).fiArm = (tsoShadow stamp st i).fiArm
  | [], st, _ => by simp
  | y :: b, st, h => by
    rw [show st ++ y :: b = (st ++ [y]) ++ b by simp]
    obtain ⟨h1, h2⟩ := PfRunUnpinned.shadowInert stamp i b (st ++ [y])
      (fun z hz => h z (by simp [hz]))
    rw [h1, h2]
    obtain ⟨a, l⟩ := y
    obtain ⟨hf, hi, hif⟩ := h (a, l) (by simp)
    rw [tsoShadowSnoc]
    split
    · refine ⟨?_, ?_⟩
      · simp [shStepF, hf]
      · cases l <;> simp_all [shStepF]
    · exact ⟨rfl, rfl⟩

/-- A label with a projection is not a cycle label. -/
theorem PfRunUnpinned.projNotCyc (k : WmClass) (l : Wlabel) (lb : Lbl) (h : projLbl k l = some lb) :
    l ≠ .LInstr ∧ ∀ base tvs, l ≠ .LIFetch base tvs := by
  refine ⟨?_, fun base tvs => ?_⟩ <;> rintro rfl <;> simp [projLbl] at h

/-- The realizing label is `LFence false×4` iff its projection is. -/
theorem PfRunUnpinned.projFenceZero (k : WmClass) (l : Wlabel) (lb : Lbl)
    (h : projLbl k l = some lb) : lbFenceZero l = PfRunUnpinned.lbFenceZeroL lb := by
  cases l <;> simp only [projLbl, Option.some.injEq, reduceCtorEq] at h <;> subst h
  all_goals first
    | rfl
    | (rename_i a b c d; cases a <;> cases b <;> cases c <;> cases d <;> rfl)

/-! ## (3) The unpinned admin star, cut-carrying -/

section unpinned

variable {P D : Type}
variable (pstep : P → D → Wlabel → P → D → Prop)
variable (pcls : P → Wlabel → Wstate → WmClass)
variable (fok : Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop)
variable (stamp : CohStamp)

/-- `admStepPf` WITHOUT the pin: a fetch is pf-admissible when its view-0 check holds. -/
theorem PfRunUnpinned.admStepPfF (instr : Bool) (c : Wpcfg P D) (i : Nat) (ag : Wpagent P)
    (l : Wlabel) (p' : P) (d' : D) :
    lbAdmin instr l →
    (∀ base tvs, l = .LIFetch base tvs → ifetchOk c.pcImg c.pcLog 0 base tvs) →
    c.pcAgs[i]? = some ag →
    pstep ag.paSt c.pcDev l p' d' →
    ∃ (c' : Wpcfg P D) (ag' : Wpagent P),
      wpPfStep pstep pcls i l c c' ∧ cfgEqr c c' ∧ c'.pcDev = d' ∧
      c'.pcAgs[i]? = some ag' ∧ ag'.paSt = p' ∧
      wsEqr ag.paWs ag'.paWs ∧
      (instr = false → ag'.paWs.wRes = ag.paWs.wRes) ∧
      c'.pcAgs.map Wpagent.paSt = (c.pcAgs.map Wpagent.paSt).set i p' := by
  intro hadm hif hlk hps
  by_cases hf : ∃ base tvs, l = .LIFetch base tvs
  · obtain ⟨base, tvs, rfl⟩ := hf
    have hlt := lookup_lt_Some hlk
    refine ⟨⟨c.pcImg, c.pcLog, d', c.pcAgs.set i ⟨p', ag.paWs, ag.paProm⟩⟩, ⟨p', ag.paWs, ag.paProm⟩,
      wpPfStep.PFIFetch c ag base tvs p' d' hlk hps (hif base tvs rfl),
      ⟨rfl, rfl, fun j agj' hj => ?_⟩, rfl, list_lookup_insert hlt, rfl, wsEqrRefl _,
      fun _ => rfl, list_fmap_insert⟩
    rcases lookupSetCases hj with ⟨rfl, rfl⟩ | ⟨_, hj⟩
    · exact ⟨ag, hlk, wsEqrRefl _⟩
    · exact ⟨agj', hj, wsEqrRefl _⟩
  · have hpin : WeakAxRealize.fetchPin c.pcImg l := by
      cases l <;> first | trivial | exact absurd ⟨_, _, rfl⟩ hf
    exact admStepPf pstep pcls instr c i ag l p' d' hadm hpin hlk hps

/-- **The unpinned leading star, appended to a cut-carrying run**: every fetch of the star
satisfies `fok`, the view-0 check, and the cut clause at the shadow's `itv` before the star (an
admin star moves neither the image, the log nor `itv`). -/
theorem PfRunUnpinned.admRunGPfC
    (fcutT : Nat → Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop)
    (instr : Bool) (p : P) (d : D) (ls : List Wlabel) (p' : P) (d' : D) :
    admRunG pstep instr p d ls p' d' →
    ∀ (c0 c : Wpcfg P D) (st : List (Nat × Wlabel)) (i : Nat) (ag : Wpagent P),
      pfRunSTC pstep pcls fok stamp fcutT c0 st c →
      c.pcAgs[i]? = some ag → ag.paSt = p → c.pcDev = d →
      (∀ (base : Int) (tvs : List (Nat × BitVec 8)), Wlabel.LIFetch base tvs ∈ ls →
        fok c.pcImg c.pcLog i base tvs ∧ ifetchOk c.pcImg c.pcLog 0 base tvs ∧
        fcutT (tsoShadow stamp st i).itv c.pcImg c.pcLog i base tvs) →
      ∃ (c' : Wpcfg P D) (ag' : Wpagent P),
        pfRunSTC pstep pcls fok stamp fcutT c0 (st ++ ls.map (fun l => (i, l))) c' ∧
        cfgEqr c c' ∧ c'.pcDev = d' ∧
        c'.pcAgs[i]? = some ag' ∧ ag'.paSt = p' ∧
        wsEqr ag.paWs ag'.paWs ∧
        (instr = false → ag'.paWs.wRes = ag.paWs.wRes) ∧
        c'.pcAgs.map Wpagent.paSt = (c.pcAgs.map Wpagent.paSt).set i p' := by
  intro h
  induction h with
  | nil p d =>
    intro c0 c st i ag hrun hlk hst hdev _
    refine ⟨c, ag, by simpa using hrun, cfgEqrRefl c, hdev, hlk, hst, wsEqrRefl _, fun _ => rfl,
      ?_⟩
    exact (listSetLookupId (by simp [List.getElem?_map, hlk, hst])).symm
  | cons p d l p1 d1 ls p' d' hadm hps _ ih =>
    intro c0 c st i ag hrun hlk hst hdev hf
    obtain ⟨c1, ag1, hstep, he1, hd1, hl1, hs1, hw1, hr1, hf1⟩ :=
      PfRunUnpinned.admStepPfF pstep pcls instr c i ag l p1 d1 hadm
        (fun b t hl => by subst hl; exact (hf b t (List.mem_cons.2 (.inl rfl))).2.1) hlk
        (by rw [hst, hdev]; exact hps)
    have hfacts : pfStepFacts fok c i l := by
      cases l with
      | LIFetch b t => exact (hf b t (List.mem_cons.2 (.inl rfl))).1
      | LLoad => simp [lbAdmin] at hadm
      | _ => trivial
    have hcut : pfCutFactsT fcutT stamp st c i l := by
      intro b t hl
      subst hl
      exact (hf b t (List.mem_cons.2 (.inl rfl))).2.2
    have hrun1 : pfRunSTC pstep pcls fok stamp fcutT c0 (st ++ [(i, l)]) c1 :=
      .snoc c c1 st i l hrun hstep hfacts (pfLoadFactsTNonload stamp _ _ _ _
        (lbAdminNotLoad instr l hadm)) hcut
    have hitv := (PfRunUnpinned.shadowAdmin stamp instr st i l hadm).1
    obtain ⟨c2, ag2, hrun2, he2, hd2, hl2, hs2, hw2, hr2, hf2⟩ :=
      ih c0 c1 (st ++ [(i, l)]) i ag1 hrun1 hl1 hs1 hd1
        (fun b t hm => by
          rw [he1.1, he1.2.1, hitv]
          exact hf b t (List.mem_cons.2 (.inr hm)))
    refine ⟨c2, ag2, by simpa using hrun2, cfgEqrTrans _ _ _ he1 he2, hd2, hl2, hs2,
      wsEqrTrans hw1 hw2, fun hi => (hr2 hi).trans (hr1 hi), ?_⟩
    rw [hf2, hf1, list_insert_insert]

/-- Load-free, fetch-free steps append to a cut-carrying run (their load and cut facts are
vacuous). -/
theorem PfRunUnpinned.pfRunSTCApp
    (fcutT : Nat → Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop)
    (c c1 c2 : Wpcfg P D) (st0 ms : List (Nat × Wlabel)) :
    pfRunSTC pstep pcls fok stamp fcutT c st0 c1 → pfRunS pstep pcls fok c1 ms c2 →
    (∀ y, y ∈ ms → lbIsLoad y.2 = false ∧ ∀ base tvs, y.2 ≠ .LIFetch base tvs) →
    pfRunSTC pstep pcls fok stamp fcutT c (st0 ++ ms) c2 := by
  intro h1 h2
  induction h2 with
  | nil => intro _; simpa using h1
  | snoc c3 c4 st i l _ hs hf ih =>
    intro hnl
    rw [← List.append_assoc]
    have hy := hnl (i, l) (by simp)
    exact .snoc _ _ _ _ _ (ih (fun y hy => hnl y (List.mem_append_left _ hy))) hs hf
      (pfLoadFactsTNonload stamp _ _ _ _ hy.1)
      (fun b t hl => absurd hl (hy.2 b t))

/-- A fetch-free admin star of the unpinned LTS is one of the pinned LTS (its labels are pinned
vacuously). -/
theorem PfRunUnpinned.admRunGPin (img : Image) (p : P) (d : D) (ls : List Wlabel) (p' : P)
    (d' : D) : admRunG pstep false p d ls p' d' → admRunG (pstepPin img pstep) false p d ls p' d' := by
  intro h
  induction h with
  | nil p d => exact .nil p d
  | cons p d l p1 d1 ls p' d' ha hs _ ih =>
    have hpin : WeakAxRealize.fetchPin img l := by
      cases l <;> first | trivial | simp [lbAdmin] at ha
    exact .cons p d l p1 d1 ls p' d' ha ⟨hs, hpin⟩ ih

end unpinned

/-! ## (4) THE M2 REPLAY -/

section replay

variable {P D : Type}
variable (pstep : P → D → Wlabel → P → D → Prop)
variable (pcls : P → Wlabel → Wstate → WmClass)
variable (fok : Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop)
variable (stamp : CohStamp)

/-- **THE M2 REPLAY, prefix form** (the snoc of `execPrefixPfRunProgShapedT` WITHOUT the pin, at
M2's per-index clause): every prefix of an `execWf` execution satisfying `execProgOk'STC` at
`fcutEM2 stamp E itvOf fiOf` (with the boot values) is the projection of a labelled pf run of the
UNPINNED LTS whose every step carries `pfStepFactsT` and the cut clause `fcutM2` at its prefix,
`pairAdjacent`, with the memory projection lemma and THE REPLAY INVARIANT: the step-list shadow's
`itv`/`fiArm` ARE `itvOf`/`fiOf` at the prefix's length. -/
theorem execPrefixPfRunProgF (pst : Nat → List P) (dv : Nat → D) (E : Exec)
    (itvOf : Nat → Nat → Nat) (fiOf : Nat → Nat → Bool) (n : Nat) :
    pclsEqr pcls → execWf E →
    execProgOk'STC pstep pcls fok stamp (PfRunUnpinned.fcutEM2 stamp E itvOf fiOf) pst dv E →
    (∀ i, itvOf 0 i = 0) → (∀ i, fiOf 0 i = false) →
    n ≤ E.exTr.length →
    ∃ (c : Wpcfg P D) (st : List (Nat × Wlabel)),
      pfRunSTC pstep pcls fok stamp PfRunUnpinned.fcutM2 (wpInit (exImg E) (dv 0) (pst 0)) st c ∧
      pairAdjacent st ∧
      c.pcAgs.map Wpagent.paSt = pst n ∧ c.pcDev = dv n ∧
      cfgMatchd c (stt E n) ∧
      (∀ i, TsoShadow.memOf (tsoRun stamp i st) = shadowRun stamp i (E.exTr.take n)) ∧
      ∀ i, (tsoShadow stamp st i).itv = itvOf n i ∧ (tsoShadow stamp st i).fiArm = fiOf n i := by
  intro hce hE hprT hi0 hf0
  obtain ⟨hpr, hscaT, hlat⟩ := hprT
  induction n with
  | zero =>
    intro _
    refine ⟨wpInit (exImg E) (dv 0) (pst 0), [], .nil, pairAdjacentNil,
      by simp [wpInit, List.map_map, Function.comp_def], rfl, ⟨rfl, execLogInit E hE, ?_⟩,
      fun i => by simp [tsoRun, shadowRun, TsoShadow.memOf, ShFull.zero],
      fun i => ⟨by rw [hi0 i]; try rfl, by rw [hf0 i]; try rfl⟩⟩
    intro i ag hlk
    simp only [wpInit, List.getElem?_map] at hlk
    cases hp : (pst 0)[i]? with
    | none => rw [hp] at hlk; cases hlk
    | some p =>
      rw [hp] at hlk; injection hlk with hlk; subst hlk
      show wsEqr (ews E 0 i) wsInit
      rw [execWsInit E i hE]
      exact wsEqrRefl _
  | succ n ih =>
    intro hn
    obtain ⟨c, st, hrun, hadj, hst, hdev, hm, hsh0, hinv⟩ := ih (by omega)
    have hsh : ∀ i, tsoRunM stamp i st = shadowRun stamp i (E.exTr.take n) :=
      fun i => (tsoRunMem stamp i st).symm.trans (hsh0 i)
    obtain ⟨s, hs⟩ := someOfIsSome (execTrLookup E n (by omega))
    have hms := execStepAt E n s hE hs
    have htake : E.exTr.take (n + 1) = E.exTr.take n ++ [s] := by
      rw [List.take_add_one, hs]; rfl
    obtain ⟨hsca, p, pa, da, p', ls, hp, hnext, hstar, hfetch, hfc, hsup⟩ := hpr n s hs
    obtain ⟨hcut, hfiN, hitvN, hframe⟩ := hfc
    have hex : ∃ ag, c.pcAgs[s.esAg]? = some ag ∧ ag.paSt = p := by
      rw [← hst, List.getElem?_map] at hp
      cases hag : c.pcAgs[s.esAg]? with
      | none => rw [hag] at hp; cases hp
      | some ag => rw [hag] at hp; injection hp with hp; exact ⟨ag, rfl, hp⟩
    obtain ⟨ag, hag, hagp⟩ := hex
    -- the leading administrative star, labelled, UNPINNED: the view-0 check from the cut
    obtain ⟨c0, ag0, hrun0, heq0, hd0, hlk0, hs0, _, _, hfm0⟩ :=
      PfRunUnpinned.admRunGPfC pstep pcls fok stamp PfRunUnpinned.fcutM2 true p (dv n) ls pa da hstar
        _ c st s.esAg ag hrun hag hagp hdev
        (fun b t hmem => by
          have hc := hcut b t hmem
          rw [hm.1, hm.2.1] at hc
          refine ⟨by rw [← hm.1, ← hm.2.1]; exact hfetch b t hmem,
            PfRunUnpinned.fcutM2Ifetch0 _ _ _ _ _ _ hc, ?_⟩
          rw [(hinv s.esAg).1]
          exact hc)
    have hm0 : cfgMatchd c0 (stt E n) := cfgEqrMatchd _ _ _ heq0 hm
    have hadmL : ∀ y, y ∈ ls.map (fun l => (s.esAg, l)) → lbAdmin true y.2 := by
      intro y hy
      obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hy
      exact admRunGAdmin pstep true _ _ _ _ _ hstar l hl
    have hadm0 : pairAdjacent (ls.map (fun l => (s.esAg, l))) :=
      pairAdjacentFused _ (fun x hx => by
        obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hx
        have := admRunGAdmin pstep true _ _ _ _ _ hstar l hl
        cases l <;> simp_all [lbAdmin, lbFused])
    have hshA : ∀ i, tsoRunM stamp i (st ++ ls.map (fun l => (s.esAg, l)))
        = shadowRun stamp i (E.exTr.take n) := by
      intro i
      rw [tsoRunMApp, foldlAdmin stamp i true _ _ hadmL]
      exact hsh i
    -- the shadow's `itv`/`fiArm` after the star
    obtain ⟨hitvA, hfiA⟩ := PfRunUnpinned.shadowAdminRun stamp true s.esAg ls st
      (fun l hl => admRunGAdmin pstep true _ _ _ _ _ hstar l hl)
    have hothA : ∀ j, j ≠ s.esAg →
        tsoShadow stamp (st ++ ls.map (fun l => (s.esAg, l))) j = tsoShadow stamp st j := by
      intro j hj
      refine PfRunUnpinned.shadowAppOther stamp j _ st (fun y hy => ?_)
      obtain ⟨l, -, rfl⟩ := List.mem_map.1 hy
      exact fun h => hj h.symm
    have eA1 : (tsoShadow stamp (st ++ ls.map (fun l => (s.esAg, l))) s.esAg).mem
        = (shadowRun stamp s.esAg (E.exTr.take n)).2 := by
      rw [tsoShadowMem, hshA]
    have eA2 : stAuthors (st ++ ls.map (fun l => (s.esAg, l)))
        = (shadowRun stamp s.esAg (E.exTr.take n)).1 := by
      rw [← tsoRunMAuthors stamp s.esAg, hshA]
    have eA3 : (tsoShadow stamp (st ++ ls.map (fun l => (s.esAg, l))) s.esAg).itv = itvOf n s.esAg :=
      hitvA.trans (hinv s.esAg).1
    have eA4 : (tsoShadow stamp (st ++ ls.map (fun l => (s.esAg, l))) s.esAg).fiArm
        = PfRunUnpinned.fiFold (fiOf n s.esAg) ls := by
      rw [hfiA, (hinv s.esAg).2]
    -- the other agents: framed
    have hothInv : ∀ (b : List (Nat × Wlabel)) (j : Nat), j ≠ s.esAg → (∀ y, y ∈ b → y.1 = s.esAg) →
        (tsoShadow stamp ((st ++ ls.map (fun l => (s.esAg, l))) ++ b) j).itv = itvOf (n + 1) j ∧
        (tsoShadow stamp ((st ++ ls.map (fun l => (s.esAg, l))) ++ b) j).fiArm = fiOf (n + 1) j := by
      intro b j hj hb
      rw [PfRunUnpinned.shadowAppOther stamp j b _ (fun y hy => by rw [hb y hy]; exact fun h => hj h.symm),
        hothA j hj, (hframe j hj).1, (hframe j hj).2]
      exact hinv j
    rcases hsup with ⟨l, hfu, hre, hps⟩ | ⟨pm, dm, ls2, pm2, dm2, l1, l2, hre, hps1, hstar2, hps2⟩
    · obtain ⟨c2, hstep, hm2, hst2, hdev2⟩ :=
        mstepWpPfStepProg pstep pcls (stt E n) (stt E (n + 1)) s.esAg s.esLb c0 ag0 pa p' l
          (dv (n + 1)) hce hm0 hlk0 hs0 hre (by rw [hd0]; exact hps) hms
      have hpr' := hre.2.2.2
      have hfacts : pfStepFacts fok c0 s.esAg l := by
        cases l with
        | LLoad aq lat base tvs asrc =>
          simp only [projLbl, Option.some.injEq] at hpr'
          show scaOk c0.pcImg c0.pcLog s.esAg base (tvs.map Prod.fst)
          rw [← hm0.1, ← hm0.2.1]
          exact hsca aq base _ _ hpr'.symm
        | LIFetch b t => simp [projLbl] at hpr'
        | _ => trivial
      have hlf : pfLoadFactsT stamp (st ++ ls.map (fun l => (s.esAg, l))) c0 s.esAg l := by
        cases l with
        | LLoad aq lat base tvs asrc =>
          simp only [projLbl, Option.some.injEq] at hpr'
          show scaOkT (tsoShadow stamp _ s.esAg).mem c0.pcImg c0.pcLog s.esAg base
              (tvs.map Prod.fst) ∧ diskLatOk c0.pcImg c0.pcLog s.esAg base (tvs.map Prod.fst)
          rw [← hm0.1, ← hm0.2.1, tsoShadowMem, hshA]
          exact ⟨hscaT n s hs aq base _ _ hpr'.symm, hlat n s hs aq base _ _ hpr'.symm⟩
        | _ => trivial
      have hcf : pfCutFactsT PfRunUnpinned.fcutM2 stamp (st ++ ls.map (fun l => (s.esAg, l))) c0
          s.esAg l := by
        intro b t hl
        subst hl
        simp [projLbl] at hpr'
      obtain ⟨hnI, hnF⟩ := PfRunUnpinned.projNotCyc _ l s.esLb hpr'
      refine ⟨c2, (st ++ ls.map (fun l => (s.esAg, l))) ++ [(s.esAg, l)],
        .snoc _ _ _ _ _ hrun0 hstep hfacts hlf hcf, ?_, ?_, hdev2, hm2, ?_, ?_⟩
      · exact pairAdjacentApp _ _ (pairAdjacentApp _ _ hadj hadm0)
          (pairAdjacentFused _ (fun x hx => by
            simp only [List.mem_singleton] at hx; subst hx; exact hfu))
      · rw [hst2, hfm0, hst, list_insert_insert, ← hnext]
      · intro i
        rw [tsoRunMem, tsoRunMSnoc, hshA i, htake, shadowRunSnoc]
        exact shActFused stamp i _ s.esAg l _ s.esLb hfu hre.2.2.2
      · intro i
        by_cases hi : i = s.esAg
        · subst hi
          rw [tsoShadowOwn]
          refine ⟨?_, ?_⟩
          · rw [hitvN]
            simp only [shStepF, PfRunUnpinned.itvStep, hs, eA1, eA2, eA3, eA4,
              PfRunUnpinned.projFenceZero _ l s.esLb hpr']
          · rw [hfiN, ← eA4]
            cases l <;> simp_all [shStepF]
        · exact hothInv [(s.esAg, l)] i hi (fun y hy => by simp at hy; rw [hy])
    · have hre' := hre
      obtain ⟨aq, rl, base, tvs, data, a1, a2, v2, rfl, rfl, _, _, hlb⟩ := hre'
      obtain ⟨c2, hstepP, hadjP, hm2, hst2, hdev2⟩ :=
        mstepWpPfStepPairS (pstepPin c0.pcImg pstep) pcls fok (stt E n) (stt E (n + 1)) s.esAg
          s.esLb c0 ag0 pa pm pm2 p' _ _ ls2 dm dm2 (dv (n + 1)) hce (pstepPinPinned _ _) hm0 hlk0
          hs0 hre ⟨by rw [hd0]; exact hps1, trivial⟩
          (PfRunUnpinned.admRunGPin pstep c0.pcImg _ _ _ _ _ hstar2) ⟨hps2, trivial⟩ hms
      have hstep := pfRunSPinSub pstep pcls fok c0.pcImg _ _ _ hstepP
      have hadm2 : ∀ y, y ∈ ls2.map (fun l => (s.esAg, l)) → lbAdmin false y.2 := by
        intro y hy
        obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hy
        exact admRunGAdmin pstep false _ _ _ _ _ hstar2 l hl
      have hnl : ∀ y, y ∈ ((s.esAg, Wlabel.LExLoad aq base tvs a1) ::
          (ls2.map (fun l => (s.esAg, l)) ++ [(s.esAg, Wlabel.LExStore rl base data a2 v2)])) →
          lbIsLoad y.2 = false ∧ ∀ b t, y.2 ≠ .LIFetch b t := by
        intro y hy
        simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | hy | rfl
        · exact ⟨rfl, fun _ _ h => by cases h⟩
        · refine ⟨lbAdminNotLoad false y.2 (hadm2 y hy), fun b t h => ?_⟩
          have := hadm2 y hy
          rw [h] at this
          simp [lbAdmin] at this
        · exact ⟨rfl, fun _ _ h => by cases h⟩
      have hinert : ∀ y, y ∈ ((s.esAg, Wlabel.LExLoad aq base tvs a1) ::
          (ls2.map (fun l => (s.esAg, l)) ++ [(s.esAg, Wlabel.LExStore rl base data a2 v2)])) →
          lbFenceZero y.2 = false ∧ y.2 ≠ .LInstr ∧ ∀ b t, y.2 ≠ .LIFetch b t := by
        intro y hy
        refine ⟨?_, ?_, (hnl y hy).2⟩
        · simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hy
          rcases hy with rfl | hy | rfl
          · rfl
          · have := hadm2 y hy
            obtain ⟨j, l⟩ := y
            cases l <;> simp_all [lbAdmin, lbFenceZero]
          · rfl
        · simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hy
          rcases hy with rfl | hy | rfl
          · exact fun h => by cases h
          · intro h
            have := hadm2 y hy
            rw [h] at this
            simp [lbAdmin] at this
          · exact fun h => by cases h
      refine ⟨c2, _, PfRunUnpinned.pfRunSTCApp pstep pcls fok stamp _ _ _ _ _ _ hrun0 hstep hnl,
        pairAdjacentApp _ _ (pairAdjacentApp _ _ hadj hadm0) hadjP, ?_, hdev2, hm2, ?_, ?_⟩
      · rw [hst2, hfm0, hst, list_insert_insert, ← hnext]
      · intro i
        rw [tsoRunMem, tsoRunMApp, hshA i, htake, shadowRunSnoc]
        exact shRunPair stamp i _ s aq rl base tvs data a1 a2 v2 _ _ false hadm2 hlb
      · intro i
        by_cases hi : i = s.esAg
        · subst hi
          obtain ⟨h1, h2⟩ := PfRunUnpinned.shadowInert stamp s.esAg _ _ hinert
          rw [h1, h2, eA3, eA4, hitvN, hfiN]
          refine ⟨?_, rfl⟩
          simp only [PfRunUnpinned.itvStep, hs, hlb, PfRunUnpinned.lbFenceZeroL, Bool.false_and,
            Bool.false_eq_true, if_false]
        · refine hothInv _ i hi (fun y hy => ?_)
          simp only [List.mem_cons, List.mem_append, List.mem_map, List.not_mem_nil,
            or_false] at hy
          rcases hy with rfl | ⟨l, -, rfl⟩ | rfl <;> rfl

/-- **THE M2 REPLAY** (`execWfPfRunProgF`, plan §C W5d): the whole trace — the unpinned,
cut-carrying run with its projections and the replay invariant at the trace's end. -/
theorem execWfPfRunProgF (pst : Nat → List P) (dv : Nat → D) (E : Exec)
    (itvOf : Nat → Nat → Nat) (fiOf : Nat → Nat → Bool) :
    pclsEqr pcls → execWf E →
    execProgOk'STC pstep pcls fok stamp (PfRunUnpinned.fcutEM2 stamp E itvOf fiOf) pst dv E →
    (∀ i, itvOf 0 i = 0) → (∀ i, fiOf 0 i = false) →
    ∃ (c : Wpcfg P D) (st : List (Nat × Wlabel)),
      pfRunSTC pstep pcls fok stamp PfRunUnpinned.fcutM2 (wpInit (exImg E) (dv 0) (pst 0)) st c ∧
      pairAdjacent st ∧
      c.pcAgs.map Wpagent.paSt = pst E.exTr.length ∧ c.pcDev = dv E.exTr.length ∧
      cfgMatchd c (stt E E.exTr.length) ∧
      (∀ i, (tsoShadow stamp st i).mem = shadowOf stamp E.exTr i) ∧
      ∀ i, (tsoShadow stamp st i).itv = itvOf E.exTr.length i ∧
        (tsoShadow stamp st i).fiArm = fiOf E.exTr.length i := by
  intro hce hE hpr hi0 hf0
  obtain ⟨c, st, h1, h2, h3, h4, h5, h6, h7⟩ :=
    execPrefixPfRunProgF pstep pcls fok stamp pst dv E itvOf fiOf E.exTr.length hce hE hpr hi0 hf0
      (Nat.le_refl _)
  refine ⟨c, st, h1, h2, h3, h4, h5, fun i => ?_, h7⟩
  have := congrArg Prod.snd (h6 i)
  simpa only [tsoShadow, shadowOf, TsoShadow.memOf, List.take_length] using this

end replay

/-! ## (5) M2's premise set, its run, `HypsC` at M2, THE COMPOSITION -/

section m2

open Sail Sail.ConcurrencyInterfaceV1 LeanRV64D
open PfStepTsoMem
open Iris.ProgramLogic

/-- **M2's premise set** (plan §A "M1/M2 (internal)", §C W5d): M1's (`srvwmoXv6M1Premises`) with
the program LTS UNPINNED (`pstepEv`), the fetch clause carried by M2's per-index clause
`fcutEM2 cohSrc (candExec c) itvOf fiOf` (the cut form at `itvOf`, the `itvOf`/`fiOf` recurrences
and frame condition; `fok := fokTriv`), and the boot values `itvOf 0 i = 0`, `fiOf 0 i = false`
[R31.s3].  `itvOf` and `fiOf` are FREE: parameters of this definition only [R30.1]. -/
def srvwmoXv6M2Premises (σ0 : WGState) (c : Cand) (pst : Nat → List Pexv6) (dv : Nat → Efab)
    (itvOf : Nat → Nat → Nat) (fiOf : Nat → Nat → Bool) : Prop :=
  wbootFacts σ0 ∧ σ0.wggen = 0 ∧
  (∃ ds : DevStates, σ0.wgdev = ds.reset ∧ diskOf ds = Xv6.fsImgDisk) ∧
  srvwmoConsistent c ∧ c.cdImg = imgZ σ0.wgimg ∧
  pst 0 = epsInit σ0 ∧ dv 0 = efInit σ0.wgdev ∧
  execProgOk'STC pstepEv pclsEv PfRunUnpinned.fokTriv TsoShadow.cohSrc
    (PfRunUnpinned.fcutEM2 TsoShadow.cohSrc (candExec c) itvOf fiOf) pst dv (candExec c) ∧
  candScaT TsoShadow.cohSrc c ∧ candDiskLat c ∧
  (∀ i, itvOf 0 i = 0) ∧ (∀ i, fiOf 0 i = false)

/-- Every M2 premise set FEEDS the M2 replay (`execWfPfRunProgF`): the unpinned, cut-carrying pf
run from the booted initial configuration, `pairAdjacent`, ending at the supplied program states
and fabric, matched to the candidate's last state, with the memory projection and the replay
invariant. -/
theorem srvwmoXv6M2PfRun (σ0 : WGState) (c : Cand) (pst : Nat → List Pexv6) (dv : Nat → Efab)
    (itvOf : Nat → Nat → Nat) (fiOf : Nat → Nat → Bool) :
    srvwmoXv6M2Premises σ0 c pst dv itvOf fiOf →
    ∃ (cf : Wpcfg Pexv6 Efab) (st : List (Nat × Wlabel)),
      pfRunSTC pstepEv pclsEv PfRunUnpinned.fokTriv TsoShadow.cohSrc PfRunUnpinned.fcutM2
        (wpInit (imgZ σ0.wgimg) (efInit σ0.wgdev) (epsInit σ0)) st cf ∧
      pairAdjacent st ∧
      cf.pcAgs.map Wpagent.paSt = pst c.cdTr.length ∧ cf.pcDev = dv c.cdTr.length ∧
      cfgMatchd cf (stt (candExec c) c.cdTr.length) ∧
      (∀ i, (tsoShadow TsoShadow.cohSrc st i).mem = shadowOf TsoShadow.cohSrc c.cdTr i) ∧
      ∀ i, (tsoShadow TsoShadow.cohSrc st i).itv = itvOf c.cdTr.length i ∧
        (tsoShadow TsoShadow.cohSrc st i).fiArm = fiOf c.cdTr.length i := by
  rintro ⟨-, -, -, hcons, himg, hpst, hdv, hprog, -, -, hi0, hf0⟩
  obtain ⟨hwf, -, heximg⟩ := srvwmoRealizable c hcons
  obtain ⟨cf, st, hrun, hadj, h1, h2, h3, h4, h5⟩ :=
    execWfPfRunProgF pstepEv pclsEv _ TsoShadow.cohSrc pst dv (candExec c) itvOf fiOf
      pclsEvEqr hwf hprog hi0 hf0
  rw [heximg, himg, hpst, hdv] at hrun
  exact ⟨cf, st, hrun, hadj, h1, h2, h3, h4, h5⟩

/-- **`MachOfPf.HypsC` at M2** (`fok = fokTriv`, `fcutT = fcutM2`, the pf boot configuration):
`tso` and `safe` as at M1; `cut` IS the step's cut clause (`pfCutFactsT`) verbatim — no
MachCSL-side source; `fi` from the named premise `sailCycleOrder` (`fiOfSco`). -/
theorem PfRunUnpinned.m2Hyps (σ0 : WGState) (hb : wbootFacts σ0) (g0 : GState) (hg0 : g0.gen = 0)
    (hp0 : g0.pow = false) (hfs : diskOf g0.m.devs = Xv6.fsImgDisk)
    (hsco : sailCycleOrder) :
    MachOfPf.HypsC PfRunUnpinned.fokTriv PfRunUnpinned.fcutM2 g0
      (wpInit (imgZ σ0.wgimg) (efInit σ0.wgdev) (epsInit σ0)) where
  tso := pfStepTsoProposed _
  safe := fun n κs t g hm =>
    (Xv6.xv6FsAdequacy_closed (hlc := Iris.HasLC.hasLC) g0 hg0 hp0 hfs n κs t g hm).1
  cut := fun _ _ _ _ _ _ _ _ _ _ base tvs _ _ _ hcf => hcf base tvs rfl
  fi := fun st c _ _ _ _ hrun _ _ => SrvwmoXv6Adequacy.fiOfSco hsco _ σ0 hb st c hrun

/-- **M2 — THE FORK PATH, COMPOSED** (plan §C W5d; [OWN.3]).  From M2's premise set (an
UNPINNED sRVWMO candidate whose fetches satisfy the Zifencei cut form at the free instruction
view `itvOf`), a MachCSL machine off `g0` matching the pf boot and the named premise
`sailCycleOrder` [OWN.35]: the unpinned, cut-carrying pf run `srvwmoXv6M2PfRun` gives (with its
projections and the replay invariant), its run record `r`, and a MachCSL run of `([power], g0)`
observing `powerOn :: pfObsOf r` to `(t, g)`, related to the pf run's end by `SimRel`, at which
every thread is reducible, the trace is pure, the NI and union conclusions hold, the kernel's
read-only window is pristine, and the allocproc shadow (`allocprocTraceAns`) holds of the trace —
M1's conclusions, now for candidates that fetch user text written after boot. -/
theorem srvwmoXv6M2Core (σ0 : WGState) (c : Cand) (pst : Nat → List Pexv6) (dv : Nat → Efab)
    (itvOf : Nat → Nat → Nat) (fiOf : Nat → Nat → Bool)
    (hP : srvwmoXv6M2Premises σ0 c pst dv itvOf fiOf)
    (g0 : GState) (hg0 : g0.gen = 0) (hp0 : g0.pow = false) (hgd : σ0.wgdev = g0.m.devs.reset)
    (hfs : diskOf g0.m.devs = Xv6.fsImgDisk)
    (hsco : sailCycleOrder) :
    ∃ (cf : Wpcfg Pexv6 Efab) (st : List (Nat × Wlabel)) (r : List MachOfPf.PfRec) (n : Nat)
      (t : List Expr) (g : GState),
      -- the unpinned, cut-carrying pf run (W5d)
      pfRunSTC pstepEv pclsEv PfRunUnpinned.fokTriv TsoShadow.cohSrc PfRunUnpinned.fcutM2
        (wpInit (imgZ σ0.wgimg) (efInit σ0.wgdev) (epsInit σ0)) st cf ∧
      pairAdjacent st ∧
      cf.pcAgs.map Wpagent.paSt = pst c.cdTr.length ∧ cf.pcDev = dv c.cdTr.length ∧
      cfgMatchd cf (stt (candExec c) c.cdTr.length) ∧
      (∀ i, (tsoShadow TsoShadow.cohSrc st i).mem = shadowOf TsoShadow.cohSrc c.cdTr i) ∧
      (∀ i, (tsoShadow TsoShadow.cohSrc st i).itv = itvOf c.cdTr.length i ∧
        (tsoShadow TsoShadow.cohSrc st i).fiArm = fiOf c.cdTr.length i) ∧
      -- its run record and the realizing MachCSL run (W4)
      MachOfPf.contRC PfRunUnpinned.fokTriv PfRunUnpinned.fcutM2
        (wpInit (imgZ σ0.wgimg) (efInit σ0.wgdev) (epsInit σ0)) [] r cf ∧
      MachOfPf.recLabels r = st ∧
      MachOfPf.MRun n ([Expr.power], g0) (Obs.powerOn :: MachOfPf.pfObsOf r) (t, g) ∧
      MachOfPf.SimRel cf st t g ∧
      -- the closed xv6 theorems at that run
      (∀ e, e ∈ t → PrimStep.Reducible (e, g)) ∧
      Xv6.xv6TracePure Xv6.fsimgCov Xv6.fsimgSb.sbLogstart g ∧
      Xv6.xv6NiPhi g (Obs.powerOn :: MachOfPf.pfObsOf r) ∧
      Xv6.unionPhiSync (Obs.powerOn :: MachOfPf.pfObsOf r) ∧
      Xv6.textPristine g ∧
      SrvwmoXv6Adequacy.allocprocAns (Obs.powerOn :: MachOfPf.pfObsOf r) := by
  have hb : wbootFacts σ0 := hP.1
  obtain ⟨cf, st, hrun, hadj, h1, h2, h3, h4, h5⟩ :=
    srvwmoXv6M2PfRun σ0 c pst dv itvOf fiOf hP
  have hH := PfRunUnpinned.m2Hyps σ0 hb g0 hg0 hp0 hfs hsco
  obtain ⟨r, hr, hl, n, t, g, hm, hR⟩ :=
    MachOfPf.machRunOfPfRun _ σ0 g0.m.devs g0 hb hgd hg0 hp0 rfl hH st cf hrun hadj
  obtain ⟨hred, hpure, hni, hun, htext, hap⟩ :=
    SrvwmoXv6Adequacy.xv6Concl g0 hg0 hp0 hfs n _ t g hm
  exact ⟨cf, st, r, n, t, g, hrun, hadj, h1, h2, h3, h4, h5, hr, hl, hm, hR, hred, hpure, hni, hun,
    htext hR.pow, hap⟩

/-! ## (6) Non-vacuity: M2's premise set is satisfiable -/

/-- A pinned admin star is an unpinned one whose every label is pinned. -/
theorem PfRunUnpinned.admRunGUnpin {P D : Type} (pstep : P → D → Wlabel → P → D → Prop)
    (img : Image) (instr : Bool) (p : P) (d : D) (ls : List Wlabel) (p' : P) (d' : D) :
    admRunG (pstepPin img pstep) instr p d ls p' d' →
    admRunG pstep instr p d ls p' d' ∧ ∀ l, l ∈ ls → WeakAxRealize.fetchPin img l := by
  intro h
  induction h with
  | nil p d => exact ⟨.nil p d, fun l hl => absurd hl List.not_mem_nil⟩
  | cons p d l p1 d1 ls p' d' ha hs _ ih =>
    refine ⟨.cons p d l p1 d1 ls p' d' ha hs.1 ih.1, fun l0 hl0 => ?_⟩
    rcases List.mem_cons.1 hl0 with rfl | hl0
    · exact hs.2
    · exact ih.2 l0 hl0

/-- A ONE-STEP M1 candidate whose step is no `LFence false×4` is an M2 candidate, at `itvOf := 0`
and `fiOf` its star's fold at index 1: a pinned fetch at the empty log passes the cut at `q = 0`. -/
theorem PfRunUnpinned.m2OfM1One (σ0 : WGState) (c : Cand) (pst : Nat → List Pexv6)
    (dv : Nat → Efab) (hP : srvwmoXv6M1Premises σ0 c pst dv) (hlen : c.cdTr.length = 1)
    (hnf : ∀ s, c.cdTr[0]? = some s → PfRunUnpinned.lbFenceZeroL s.esLb = false) :
    ∃ (itvOf : Nat → Nat → Nat) (fiOf : Nat → Nat → Bool),
      srvwmoXv6M2Premises σ0 c pst dv itvOf fiOf := by
  obtain ⟨hb, hgen, hds, hcons, himg, hpst, hdv, ⟨hprog, hscaT', hlat'⟩, hscaT, hlat⟩ := hP
  obtain ⟨hwf, htr, heximg⟩ := srvwmoRealizable c hcons
  obtain ⟨s0, hs0⟩ : ∃ s0, c.cdTr[0]? = some s0 :=
    someOfIsSome (by rw [List.getElem?_eq_getElem (by omega)]; rfl)
  have hs0' : (candExec c).exTr[0]? = some s0 := by rw [htr]; exact hs0
  obtain ⟨hsca0, p, pa, da, p', ls0, hp0, hn0, hstar0, -, -, hsup0⟩ := hprog 0 s0 hs0'
  obtain ⟨hstarU, hpinL⟩ := PfRunUnpinned.admRunGUnpin pstepEv _ true _ _ _ _ _ hstar0
  refine ⟨fun _ _ => 0, fun k i => if k = 0 then false else
      if i = s0.esAg then PfRunUnpinned.fiFold false ls0 else false,
    hb, hgen, hds, hcons, himg, hpst, hdv, ⟨?_, hscaT', hlat'⟩, hscaT, hlat, fun _ => rfl,
    fun _ => rfl⟩
  intro k s hs
  have hk : k = 0 := by
    have := lookup_lt_Some hs
    rw [htr, hlen] at this
    omega
  subst hk
  have hss : s = s0 := Option.some.inj (hs.symm.trans hs0')
  subst hss
  refine ⟨hsca0, p, pa, da, p', ls0, hp0, hn0, hstarU, fun _ _ _ => trivial, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro base tvs hm
    have hpin := hpinL _ hm
    have hlog : (stt (candExec c) 0).msLog = [] := execLogInit _ hwf
    have himg0 : (stt (candExec c) 0).msImg = imgZ σ0.wgimg := by
      show exImg (candExec c) = _
      rw [heximg, himg]
    refine ⟨0, Nat.le_refl _, Nat.zero_le _, ?_, fun j t v hj => ?_⟩
    · rw [himg0]; exact fetchPinIfetchOk _ _ _ _ hpin
    · have ht := hpin.1 t (List.mem_map.2 ⟨(t, v), List.mem_iff_getElem?.2 ⟨j, hj⟩, rfl⟩)
      omega
  · simp
  · simp only [PfRunUnpinned.itvStep, hs, hnf s hs0, Bool.false_and, Bool.false_eq_true,
      if_false]
  · intro i hi
    simp [hi]
  · rcases hsup0 with ⟨l, hfu, hre, hps⟩ | ⟨pm, dm, ls2, pm2, dm2, l1, l2, hre, hps1, hstar2, hps2⟩
    · exact .inl ⟨l, hfu, hre, hps.1⟩
    · exact .inr ⟨pm, dm, ls2, pm2, dm2, l1, l2, hre, hps1.1,
        (PfRunUnpinned.admRunGUnpin pstepEv _ false _ _ _ _ _ hstar2).1, hps2.1⟩

/-- **M2's PREMISE SET IS SATISFIABLE** (non-vacuity, as W5c's for M1): M1's witness — `_entry`'s
`ld sp,1000(sp)` on hart 0, its fetches from the kernel image — is an M2 candidate. -/
theorem srvwmoXv6M2Satisfiable :
    ∃ (σ0 : WGState) (c : Cand) (pst : Nat → List Pexv6) (dv : Nat → Efab)
      (itvOf : Nat → Nat → Nat) (fiOf : Nat → Nat → Bool),
      srvwmoXv6M2Premises σ0 c pst dv itvOf fiOf ∧
      c.cdTr = [⟨0, .LLoad false 0x8000a3e8 SrvwmoXv6Witness.ts8
        (SrvwmoXv6Witness.vs8 SrvwmoXv6Witness.wl)⟩] := by
  obtain ⟨σ0, c, pst, dv, hP, htr, -⟩ := srvwmoXv6M1Satisfiable
  obtain ⟨itvOf, fiOf, hP2⟩ := PfRunUnpinned.m2OfM1One σ0 c pst dv hP (by rw [htr]; rfl)
    (fun s hs => by
      rw [htr] at hs
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hs
      subst hs
      rfl)
  exact ⟨σ0, c, pst, dv, itvOf, fiOf, hP2, htr⟩

end m2

end Weak

#print axioms Weak.execWfPfRunProgF
#print axioms Weak.PfRunUnpinned.m2Hyps
#print axioms Weak.srvwmoXv6M2Core
#print axioms Weak.srvwmoXv6M2Satisfiable
