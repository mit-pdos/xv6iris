/-
Weak: **the SHAPED program-carrying replay** (allocproc plan W5b, §B(10) / §C Stage 0).

Lean-only (no Rocq source).  `WeakAxRealize.execProgOk'` supplies, per trace
event, an administrative star and either ONE realizing step or the exclusive
PAIR; its stars are label-free (`admStar = rtc admStep`) and its realizing
step may be a dangling `LExLoad` (`lbNobarex`).  The TsoMem direction (W2)
needs more, and per [R3.2] it cannot be a separate conjunct (the realizing
label and the stars are existential per index), so this file DEFINES the one
shaped conformance predicate `execProgOk'S` with the plan's three clauses:

  (i)   the LEFT arm's realizing label is `lbFused` (no `LExLoad`; `lbNobarex`
        already excludes `LExStore`) — stated for ANY label with a `projLbl`
        image, so a payload-carrying `LDev` (D38 / W13 (E)) joins unchanged;
  (ii)  the stars are LABEL-CARRYING runs `admRunG` (the generic twin of
        `WeakRvwmoConf.admRun`), the leading star's every `LIFetch` satisfying
        the FETCH CLAUSE `fok` (M1: `candKfetch lo hi`, the pristine window;
        M2: the cut-form Zifencei check, W5d) at the event's pre-state;
  (iii) every axiomatic `LLoad` is single-copy-atomic: `scaOk` (one view
        `tvn`, TsoMem's per-byte reading rule `Hist.read` — the latest write
        at or below `tvn` OR the hart's own), collected as `execSca` /
        `candSca`.

and `pairAdjacent`, over the STEP LIST of a pf run: every exclusive read is
followed, after only the SAME hart's `lbAdmin false` steps, by its exclusive
write (same base, same width, nonempty data), and every exclusive write is so
preceded — no other agent's step lies between the halves.

Main result: `execPrefixPfRunProgShaped` / `execWfPfRunProgShaped` — the
replay of `WeakAxRealize.execPrefixPfRunProg` that consumes `execProgOk'S` and
produces a LABELLED pf run `pfRunS` whose step list is `pairAdjacent` and
whose every step carries its facts (`pfStepFacts`: a fetch satisfies `fok` at
the step's pre-configuration, a plain load is `scaOk` at it — the per-load
`tvn`).  `execWfPfRunPinShaped` is the pinned-supply form projected to the
unpinned LTS.  Forgetful maps: `execProgOk'SForget` (to `execProgOk'`),
`execProgOk'SSca` (to `execSca`), `pfRunSRtc` (to `rtc wpPfRun`).

NOT a change to `WeakAxRealize` (the plan: a new theorem in `Weak/`).

W5d [R30.1]: the predicate is `execProgOk'SC … fcutE` with a PER-INDEX clause `fcutE k s.esAg ls
(stt E k)` beside `fetchesOk` (sharing that index's `ls`); `execProgOk'S` is its M1 instance at
`fcutETriv` (a reducible abbreviation), `execProgOk'SCForget` the forgetful map.
-/
import Weak.WeakAxRealize
import Weak.WeakAxiomatic2

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std

/-! ## (0) The fetch clause (M1 instance) -/

/-- M1's fetch clause: every byte of the fetch footprint lies in the window
`[lo, hi)` (instantiated at W3's pristine window `[bcRoLo, bcRoHi)`).  The
image, log and agent arguments are those of the general fetch clause and are
unused here. -/
def candKfetch (lo hi : Int) (_img : Image) (_log : List Wmsg) (_i : Nat) (base : Int)
    (tvs : List (Nat × BitVec 8)) : Prop :=
  ∀ j, j < tvs.length → lo ≤ base + (j : Int) ∧ base + (j : Int) < hi

/-! ## (1) Single-copy atomicity of a plain load (clause (iii)) -/

/-- Timestamp `t` is visible to agent `i` at view `tvn` (TsoMem's
`HEnt.visible`): at or below the view, or a message of `i`'s own. -/
def scaVis (log : List Wmsg) (i tvn t : Nat) : Prop :=
  t ≤ tvn ∨ (0 < t ∧ ∃ m, log[t - 1]? = some m ∧ m.wmTid = some i)

/-- Byte `a` read from timestamp `t` is TsoMem's reading at view `tvn`
(`Hist.read`): `t` writes `a`, is visible, and no LATER write to `a` is. -/
def scaByte (img : Image) (log : List Wmsg) (i tvn : Nat) (a : Int) (t : Nat) : Prop :=
  (logByte img log t a).isSome ∧ scaVis log i tvn t ∧
  ∀ t', t < t' → (logByte img log t' a).isSome → ¬ scaVis log i tvn t'

/-- A load of agent `i` at `base` reading timestamps `ts` is SINGLE-COPY
ATOMIC: ONE view `tvn ≤ |log|` explains every byte. -/
def scaOk (img : Image) (log : List Wmsg) (i : Nat) (base : Int) (ts : List Nat) : Prop :=
  ∃ tvn, tvn ≤ log.length ∧
    ∀ (j t : Nat), ts[j]? = some t → scaByte img log i tvn (accAddr base j) t

/-- Every plain load of the execution is single-copy atomic, at its pre-state
(RMWs are exempt: `rmwLatest`). -/
def execSca (E : Exec) : Prop :=
  ∀ (k : Nat) (s : Estep), E.exTr[k]? = some s →
    ∀ (aq : Bool) (base : Int) (ts : List Nat) (vs : List (BitVec 8)),
      s.esLb = .LLoad aq base ts vs →
      scaOk (stt E k).msImg (stt E k).msLog s.esAg base ts

/-- `execSca` of a candidate. -/
def candSca (c : Cand) : Prop := execSca (candExec c)

/-! ## (2) The step list: `pairAdjacent` -/

/-- THE ADJACENCY OF EXCLUSIVE PAIRS over a pf run's step list `(agent,
label)`: every `LExLoad` of agent `i` at position `v` is followed, at some
`u > v`, by an `LExStore` of `i` at the same base, with nonempty data of the
read's width, and every position strictly between is a step of `i` with an
`lbAdmin false` label; and every `LExStore` is so preceded.  (No other agent's
step lies between the halves; no dangling exclusive of either kind.) -/
def pairAdjacent (st : List (Nat × Wlabel)) : Prop :=
  (∀ (v i : Nat) (aq : Bool) (base : Int) (tvs : List (Nat × BitVec 8)) (asrc1 : List Dsrc),
     st[v]? = some (i, .LExLoad aq base tvs asrc1) →
     ∃ u, v < u ∧
       (∀ w, v < w → w < u → ∃ l, st[w]? = some (i, l) ∧ lbAdmin false l) ∧
       ∃ (rl : Bool) (data : List (BitVec 8)) (asrc2 vsrc2 : List Dsrc),
         st[u]? = some (i, .LExStore rl base data asrc2 vsrc2) ∧
         data ≠ [] ∧ tvs.length = data.length) ∧
  (∀ (u i : Nat) (rl : Bool) (base : Int) (data : List (BitVec 8)) (asrc2 vsrc2 : List Dsrc),
     st[u]? = some (i, .LExStore rl base data asrc2 vsrc2) →
     ∃ v, v < u ∧
       (∀ w, v < w → w < u → ∃ l, st[w]? = some (i, l) ∧ lbAdmin false l) ∧
       ∃ (aq : Bool) (tvs : List (Nat × BitVec 8)) (asrc1 : List Dsrc),
         st[v]? = some (i, .LExLoad aq base tvs asrc1) ∧
         data ≠ [] ∧ tvs.length = data.length)

theorem pairAdjacentNil : pairAdjacent [] :=
  ⟨fun _ _ _ _ _ _ h => by simp at h, fun _ _ _ _ _ _ _ h => by simp at h⟩

/-- `pairAdjacent` is closed under concatenation (pairs stay inside their part). -/
theorem pairAdjacentApp (st b : List (Nat × Wlabel)) :
    pairAdjacent st → pairAdjacent b → pairAdjacent (st ++ b) := by
  rintro ⟨hf1, hb1⟩ ⟨hf2, hb2⟩
  have hL : ∀ w, w < st.length → (st ++ b)[w]? = st[w]? := fun _ hw => List.getElem?_append_left hw
  have hR : ∀ w, st.length ≤ w → (st ++ b)[w]? = b[w - st.length]? :=
    fun _ hw => List.getElem?_append_right hw
  refine ⟨?_, ?_⟩
  · intro v i aq base tvs asrc1 hv
    by_cases hvl : v < st.length
    · rw [hL v hvl] at hv
      obtain ⟨u, hvu, hbt, rl, data, a2, v2, hu, hne, hlen⟩ := hf1 v i aq base tvs asrc1 hv
      have hul : u < st.length := lookup_lt_Some hu
      refine ⟨u, hvu, fun w h1 h2 => ?_, rl, data, a2, v2, by rw [hL u hul]; exact hu, hne, hlen⟩
      rw [hL w (by omega)]; exact hbt w h1 h2
    · rw [hR v (by omega)] at hv
      obtain ⟨u, hvu, hbt, rl, data, a2, v2, hu, hne, hlen⟩ := hf2 _ i aq base tvs asrc1 hv
      refine ⟨u + st.length, by omega, fun w h1 h2 => ?_, rl, data, a2, v2, ?_, hne, hlen⟩
      · rw [hR w (by omega)]; exact hbt (w - st.length) (by omega) (by omega)
      · rw [hR _ (by omega), Nat.add_sub_cancel]; exact hu
  · intro u i rl base data asrc2 vsrc2 hu
    by_cases hul : u < st.length
    · rw [hL u hul] at hu
      obtain ⟨v, hvu, hbt, aq, tvs, a1, hv, hne, hlen⟩ := hb1 u i rl base data asrc2 vsrc2 hu
      refine ⟨v, hvu, fun w h1 h2 => ?_, aq, tvs, a1, by rw [hL v (by omega)]; exact hv, hne, hlen⟩
      rw [hL w (by omega)]; exact hbt w h1 h2
    · rw [hR u (by omega)] at hu
      obtain ⟨v, hvu, hbt, aq, tvs, a1, hv, hne, hlen⟩ := hb2 _ i rl base data asrc2 vsrc2 hu
      refine ⟨v + st.length, by omega, fun w h1 h2 => ?_, aq, tvs, a1, ?_, hne, hlen⟩
      · rw [hR w (by omega)]; exact hbt (w - st.length) (by omega) (by omega)
      · rw [hR _ (by omega), Nat.add_sub_cancel]; exact hv

/-- A step list of fused labels has no exclusive half: vacuously adjacent. -/
theorem pairAdjacentFused (ms : List (Nat × Wlabel)) :
    (∀ x, x ∈ ms → lbFused x.2) → pairAdjacent ms := by
  intro h
  refine ⟨fun v i aq base tvs asrc1 hv => ?_, fun u i rl base data asrc2 vsrc2 hu => ?_⟩
  · have := h _ (List.mem_of_getElem? hv); simp [lbFused] at this
  · have := h _ (List.mem_of_getElem? hu); simp [lbFused] at this

/-- THE PAIR BLOCK: an exclusive read, the same agent's `lbAdmin false` steps,
the exclusive write. -/
theorem pairAdjacentBlk (i : Nat) (aq : Bool) (base : Int) (tvs : List (Nat × BitVec 8))
    (asrc1 : List Dsrc) (rl : Bool) (data : List (BitVec 8)) (asrc2 vsrc2 : List Dsrc)
    (ms : List (Nat × Wlabel)) :
    (∀ x, x ∈ ms → x.1 = i ∧ lbAdmin false x.2) → data ≠ [] → tvs.length = data.length →
    pairAdjacent ((i, .LExLoad aq base tvs asrc1) ::
      (ms ++ [(i, .LExStore rl base data asrc2 vsrc2)])) := by
  intro hms hne hlen
  -- where a position of the block points
  have hlk : ∀ w x, ((i, Wlabel.LExLoad aq base tvs asrc1) ::
      (ms ++ [(i, Wlabel.LExStore rl base data asrc2 vsrc2)]))[w]? = some x →
      (w = 0 ∧ x = (i, .LExLoad aq base tvs asrc1)) ∨ (0 < w ∧ w ≤ ms.length ∧ x ∈ ms) ∨
      (w = ms.length + 1 ∧ x = (i, .LExStore rl base data asrc2 vsrc2)) := by
    intro w x h
    cases w with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at h; exact .inl ⟨rfl, h.symm⟩
    | succ w =>
      rw [List.getElem?_cons_succ] at h
      by_cases hw : w < ms.length
      · rw [List.getElem?_append_left hw] at h
        exact .inr (.inl ⟨by omega, by omega, List.mem_of_getElem? h⟩)
      · rw [List.getElem?_append_right (by omega)] at h
        have h1 : w - ms.length < 1 := lookup_lt_Some h
        have hw' : w = ms.length := by omega
        subst hw'
        simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at h
        exact .inr (.inr ⟨rfl, h.symm⟩)
  have hmid : ∀ w, 0 < w → w ≤ ms.length →
      ∃ l, ((i, Wlabel.LExLoad aq base tvs asrc1) ::
        (ms ++ [(i, Wlabel.LExStore rl base data asrc2 vsrc2)]))[w]? = some (i, l) ∧
        lbAdmin false l := by
    intro w h0 h1
    obtain ⟨w', rfl⟩ : ∃ w', w = w' + 1 := ⟨w - 1, by omega⟩
    rw [List.getElem?_cons_succ, List.getElem?_append_left (by omega)]
    obtain ⟨x, hx⟩ : ∃ x, ms[w']? = some x :=
      ⟨ms[w'], List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨h1, h2⟩ := hms x (List.mem_of_getElem? hx)
    exact ⟨x.2, by rw [hx, ← h1], h2⟩
  have hend : ((i, Wlabel.LExLoad aq base tvs asrc1) ::
      (ms ++ [(i, Wlabel.LExStore rl base data asrc2 vsrc2)]))[ms.length + 1]?
      = some (i, .LExStore rl base data asrc2 vsrc2) := by
    rw [List.getElem?_cons_succ, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl
  refine ⟨fun v j aq' base' tvs' a1' hv => ?_, fun u j rl' base' data' a2' v2' hu => ?_⟩
  · rcases hlk v _ hv with ⟨rfl, hx⟩ | ⟨_, _, hx⟩ | ⟨_, hx⟩
    · simp only [Prod.mk.injEq, Wlabel.LExLoad.injEq] at hx
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hx
      exact ⟨ms.length + 1, by omega, fun w h1 h2 => hmid w h1 (by omega),
        rl, data, asrc2, vsrc2, hend, hne, hlen⟩
    · have := (hms _ hx).2; simp [lbAdmin] at this
    · simp at hx
  · rcases hlk u _ hu with ⟨_, hx⟩ | ⟨_, _, hx⟩ | ⟨rfl, hx⟩
    · simp at hx
    · have := (hms _ hx).2; simp [lbAdmin] at this
    · simp only [Prod.mk.injEq, Wlabel.LExStore.injEq] at hx
      obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := hx
      exact ⟨0, by omega, fun w h1 h2 => hmid w h1 (by omega), aq, tvs, asrc1, rfl, hne, hlen⟩

section shape

variable {P D : Type}
variable (pstep : P → D → Wlabel → P → D → Prop)
variable (pcls : P → Wlabel → Wstate → WmClass)
variable (fok : Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop)

/-! ## (3) The label-carrying administrative run (clause (ii)) -/

/-- A finite run of administrative program steps WITH ITS LABELS, fabric
threaded (the generic twin of `WeakRvwmoConf.admRun`). -/
inductive admRunG (instr : Bool) : P → D → List Wlabel → P → D → Prop where
  | nil (p : P) (d : D) : admRunG instr p d [] p d
  | cons (p : P) (d : D) (l : Wlabel) (p1 : P) (d1 : D) (ls : List Wlabel) (p' : P) (d' : D) :
      lbAdmin instr l → pstep p d l p1 d1 →
      admRunG instr p1 d1 ls p' d' →
      admRunG instr p d (l :: ls) p' d'

/-- The fetch clause on a star's labels, at the event's pre-state. -/
def fetchesOk (σ : Mstate) (i : Nat) (ls : List Wlabel) : Prop :=
  ∀ (base : Int) (tvs : List (Nat × BitVec 8)), Wlabel.LIFetch base tvs ∈ ls →
    fok σ.msImg σ.msLog i base tvs

/-! ## (4) THE SHAPED CONFORMANCE PREDICATE -/

/-- The trivial per-index clause (M1's instance of `execProgOk'SC`'s `fcutE`). -/
abbrev fcutETriv : Nat → Nat → List Wlabel → Mstate → Prop := fun _ _ _ _ => True

/-- `execProgOk'` with (i) the left arm's realizing label `lbFused`, (ii) the
stars label-carrying `admRunG`s, the leading one's fetches satisfying `fok`
(the intra-pair star is `lbAdmin false`, hence fetch-free), (iii) every plain
axiomatic load single-copy atomic; and (W5d [R29.1][R30.1]) a PER-INDEX clause
`fcutE k s.esAg ls (stt E k)` on the leading star's labels, beside `fetchesOk`
(M1: `fcutETriv`; M2: the cut form at `itvOf` with its recurrence and frame
condition, `Weak/PfRunUnpinned.lean`). -/
def execProgOk'SC (fcutE : Nat → Nat → List Wlabel → Mstate → Prop) (pst : Nat → List P)
    (dv : Nat → D) (E : Exec) : Prop :=
  ∀ (k : Nat) (s : Estep), E.exTr[k]? = some s →
    (∀ (aq : Bool) (base : Int) (ts : List Nat) (vs : List (BitVec 8)),
       s.esLb = .LLoad aq base ts vs →
       scaOk (stt E k).msImg (stt E k).msLog s.esAg base ts) ∧
    ∃ (p pa : P) (da : D) (p' : P) (ls : List Wlabel),
      (pst k)[s.esAg]? = some p ∧
      pst (k + 1) = (pst k).set s.esAg p' ∧
      admRunG pstep true p (dv k) ls pa da ∧
      fetchesOk fok (stt E k) s.esAg ls ∧
      fcutE k s.esAg ls (stt E k) ∧
      ((∃ l, lbFused l ∧ lblRealizes pcls pa (stt E k) s.esAg s.esLb l ∧
          pstep pa da l p' (dv (k + 1)))
       ∨ (∃ (pm : P) (dm : D) (ls2 : List Wlabel) (pm2 : P) (dm2 : D) (l1 l2 : Wlabel),
            lblRealizesPair pcls pa pm2 (stt E k) s.esAg s.esLb l1 l2 ∧
            pstep pa da l1 pm dm ∧
            admRunG pstep false pm dm ls2 pm2 dm2 ∧
            pstep pm2 dm2 l2 p' (dv (k + 1))))

/-- THE SHAPED CONFORMANCE PREDICATE (M1): `execProgOk'SC` at the trivial per-index clause. -/
abbrev execProgOk'S (pst : Nat → List P) (dv : Nat → D) (E : Exec) : Prop :=
  execProgOk'SC pstep pcls fok fcutETriv pst dv E

/-- Any per-index clause forgets to the trivial one. -/
theorem execProgOk'SCForget (fcutE : Nat → Nat → List Wlabel → Mstate → Prop)
    (pst : Nat → List P) (dv : Nat → D) (E : Exec) :
    execProgOk'SC pstep pcls fok fcutE pst dv E → execProgOk'S pstep pcls fok pst dv E := by
  intro h k s hs
  obtain ⟨hsca, p, pa, da, p', ls, hp, hn, hrun, hf, _, hsup⟩ := h k s hs
  exact ⟨hsca, p, pa, da, p', ls, hp, hn, hrun, hf, trivial, hsup⟩

/-! ## (5) The labelled pf run -/

/-- The facts a shaped run carries at each step, read at the step's
PRE-configuration: a fetch satisfies the fetch clause; a plain load is
single-copy atomic (its `tvn`). -/
def pfStepFacts (c : Wpcfg P D) (i : Nat) (l : Wlabel) : Prop :=
  match l with
  | .LIFetch base tvs => fok c.pcImg c.pcLog i base tvs
  | .LLoad _ _ base tvs _ => scaOk c.pcImg c.pcLog i base (tvs.map Prod.fst)
  | _ => True

/-- A promise-free run WITH ITS STEP LIST (built from the last step), each
step carrying `pfStepFacts`. -/
inductive pfRunS (c : Wpcfg P D) : List (Nat × Wlabel) → Wpcfg P D → Prop where
  | nil : pfRunS c [] c
  | snoc (c1 c2 : Wpcfg P D) (st : List (Nat × Wlabel)) (i : Nat) (l : Wlabel) :
      pfRunS c st c1 → wpPfStep pstep pcls i l c1 c2 → pfStepFacts fok c1 i l →
      pfRunS c (st ++ [(i, l)]) c2

/-! ## (6) Forgetful maps -/

theorem admRunGStar (instr : Bool) (p : P) (d : D) (ls : List Wlabel) (p' : P) (d' : D) :
    admRunG pstep instr p d ls p' d' → admStar pstep instr p d p' d' := by
  intro h
  induction h with
  | nil p d => exact admStarRefl pstep instr p d
  | cons p d l p1 d1 ls p' d' ha hs _ ih => exact admStarL pstep instr p d l p1 d1 p' d' ha hs ih

theorem admRunGAdmin (instr : Bool) (p : P) (d : D) (ls : List Wlabel) (p' : P) (d' : D) :
    admRunG pstep instr p d ls p' d' → ∀ l, l ∈ ls → lbAdmin instr l := by
  intro h
  induction h with
  | nil p d => intro l hl; exact absurd hl List.not_mem_nil
  | cons p d l p1 d1 ls p' d' ha _ _ ih =>
    intro l0 hl0
    rcases List.mem_cons.1 hl0 with rfl | hl0
    · exact ha
    · exact ih l0 hl0

/-- The shaped predicate is an `execProgOk'`. -/
theorem execProgOk'SForget (pst : Nat → List P) (dv : Nat → D) (E : Exec) :
    execProgOk'S pstep pcls fok pst dv E → execProgOk' pstep pcls pst dv E := by
  intro h k s hs
  obtain ⟨_, p, pa, da, p', ls, hp, hn, hrun, _, _, hsup⟩ := h k s hs
  refine ⟨p, pa, da, p', hp, hn, admRunGStar pstep true _ _ _ _ _ hrun, ?_⟩
  rcases hsup with ⟨l, _, hre, hps⟩ | ⟨pm, dm, ls2, pm2, dm2, l1, l2, hre, hps1, hrun2, hps2⟩
  · exact .inl ⟨l, hre, hps⟩
  · exact .inr ⟨pm, dm, pm2, dm2, l1, l2, hre, hps1, admRunGStar pstep false _ _ _ _ _ hrun2, hps2⟩

/-- ... and collects clause (iii). -/
theorem execProgOk'SSca (pst : Nat → List P) (dv : Nat → D) (E : Exec) :
    execProgOk'S pstep pcls fok pst dv E → execSca E :=
  fun h k s hs => (h k s hs).1

theorem pfRunSRtc (c c' : Wpcfg P D) (st : List (Nat × Wlabel)) :
    pfRunS pstep pcls fok c st c' → rtc (wpPfRun pstep pcls) c c' := by
  intro h
  induction h with
  | nil => exact rtc_refl _
  | snoc c1 c2 st i l _ hs _ ih => exact rtc_r ih ⟨i, l, hs⟩

/-- A labelled run of the pinned LTS is one of the LTS. -/
theorem pfRunSPinSub (img : Image) (c c' : Wpcfg P D) (st : List (Nat × Wlabel)) :
    pfRunS (pstepPin img pstep) pcls fok c st c' → pfRunS pstep pcls fok c st c' := by
  intro h
  induction h with
  | nil => exact .nil
  | snoc c1 c2 st i l _ hs hf ih =>
    exact .snoc c1 c2 st i l ih (wpPfStepPinSub img pstep pcls i l c1 c2 hs) hf

/-! ## (7) Composition of labelled runs -/

theorem pfRunSTrans (c c1 c2 : Wpcfg P D) (st1 st2 : List (Nat × Wlabel)) :
    pfRunS pstep pcls fok c st1 c1 → pfRunS pstep pcls fok c1 st2 c2 →
    pfRunS pstep pcls fok c (st1 ++ st2) c2 := by
  intro h1 h2
  induction h2 with
  | nil => simpa using h1
  | snoc c3 c4 st i l _ hs hf ih =>
    rw [← List.append_assoc]
    exact .snoc _ _ _ _ _ ih hs hf

theorem pfRunSOne (c c' : Wpcfg P D) (i : Nat) (l : Wlabel) :
    wpPfStep pstep pcls i l c c' → pfStepFacts fok c i l → pfRunS pstep pcls fok c [(i, l)] c' := by
  intro hs hf
  have h := pfRunS.snoc (c := c) c c' [] i l pfRunS.nil hs hf
  simpa using h

/-! ## (8) The labelled administrative run, on the MACHINE side -/

theorem admRunGPf (instr : Bool) (p : P) (d : D) (ls : List Wlabel) (p' : P) (d' : D) :
    admRunG pstep instr p d ls p' d' →
    ∀ (c : Wpcfg P D) (i : Nat) (ag : Wpagent P),
      pstepPinned c.pcImg pstep →
      c.pcAgs[i]? = some ag → ag.paSt = p → c.pcDev = d →
      (∀ (base : Int) (tvs : List (Nat × BitVec 8)), Wlabel.LIFetch base tvs ∈ ls →
        fok c.pcImg c.pcLog i base tvs) →
      ∃ (c' : Wpcfg P D) (ag' : Wpagent P),
        pfRunS pstep pcls fok c (ls.map (fun l => (i, l))) c' ∧ cfgEqr c c' ∧ c'.pcDev = d' ∧
        c'.pcAgs[i]? = some ag' ∧ ag'.paSt = p' ∧
        wsEqr ag.paWs ag'.paWs ∧
        (instr = false → ag'.paWs.wRes = ag.paWs.wRes) ∧
        c'.pcAgs.map Wpagent.paSt = (c.pcAgs.map Wpagent.paSt).set i p' := by
  intro h
  induction h with
  | nil p d =>
    intro c i ag _ hlk hst hdev _
    refine ⟨c, ag, pfRunS.nil, cfgEqrRefl c, hdev, hlk, hst, wsEqrRefl _, fun _ => rfl, ?_⟩
    exact (listSetLookupId (by simp [List.getElem?_map, hlk, hst])).symm
  | cons p d l p1 d1 ls p' d' hadm hps _ ih =>
    intro c i ag hpin hlk hst hdev hf
    obtain ⟨c1, ag1, hstep, he1, hd1, hl1, hs1, hw1, hr1, hf1⟩ :=
      admStepPf pstep pcls instr c i ag l p1 d1 hadm (hpin _ _ _ _ _ hps) hlk
        (by rw [hst, hdev]; exact hps)
    have hfacts : pfStepFacts fok c i l := by
      cases l with
      | LIFetch b t => exact hf b t (List.mem_cons.2 (.inl rfl))
      | LLoad => simp [lbAdmin] at hadm
      | _ => trivial
    obtain ⟨c2, ag2, hrun, he2, hd2, hl2, hs2, hw2, hr2, hf2⟩ :=
      ih c1 i ag1 (by rw [he1.1]; exact hpin) hl1 hs1 hd1
        (fun b t hm => by rw [he1.1, he1.2.1]; exact hf b t (List.mem_cons.2 (.inr hm)))
    refine ⟨c2, ag2, ?_, cfgEqrTrans _ _ _ he1 he2, hd2, hl2, hs2, wsEqrTrans hw1 hw2,
      fun hi => (hr2 hi).trans (hr1 hi), ?_⟩
    · have h := pfRunSTrans pstep pcls fok _ _ _ _ _ (pfRunSOne pstep pcls fok _ _ _ _ hstep hfacts) hrun
      simpa using h
    · rw [hf2, hf1, list_insert_insert]

/-- The `LInstr`-free star is fetch-free. -/
theorem admRunGFetchFree (p : P) (d : D) (ls : List Wlabel) (p' : P) (d' : D) :
    admRunG pstep false p d ls p' d' →
    ∀ (base : Int) (tvs : List (Nat × BitVec 8)), Wlabel.LIFetch base tvs ∉ ls := by
  intro h base tvs hm
  have := admRunGAdmin pstep false p d ls p' d' h _ hm
  simp [lbAdmin] at this

/-! ## (9) The PAIR step, labelled

`mstepWpPfStepPair` with the intra-pair star label-carrying: the step list is
the pair block. -/
theorem mstepWpPfStepPairS (σ σ' : Mstate) (i : Nat) (lb : Lbl) (c : Wpcfg P D) (ag : Wpagent P)
    (p pm pm2 p' : P) (l1 l2 : Wlabel) (ls2 : List Wlabel) (dm dm2 dn : D) :
    pclsEqr pcls → pstepPinned c.pcImg pstep →
    cfgMatchd c σ → c.pcAgs[i]? = some ag → ag.paSt = p →
    lblRealizesPair pcls p pm2 σ i lb l1 l2 →
    pstep p c.pcDev l1 pm dm →
    admRunG pstep false pm dm ls2 pm2 dm2 →
    pstep pm2 dm2 l2 p' dn →
    mstep σ i lb σ' →
    ∃ c', pfRunS pstep pcls fok c ((i, l1) :: (ls2.map (fun l => (i, l)) ++ [(i, l2)])) c' ∧
      pairAdjacent ((i, l1) :: (ls2.map (fun l => (i, l)) ++ [(i, l2)])) ∧
      cfgMatchd c' σ' ∧
      c'.pcAgs.map Wpagent.paSt = (c.pcAgs.map Wpagent.paSt).set i p' ∧
      c'.pcDev = dn := by
  intro hce hpin hm hlk hag hre hps1 hstar hps2 hms
  subst hag
  have hew := cfgMatchdWs c σ i ag hm hlk
  have hlti := lookup_lt_Some hlk
  obtain ⟨aq, rl, base, tvs, data, asrc1, asrc2, vsrc2, rfl, rfl, hnn, hlen, hlb⟩ := hre
  have hadj := pairAdjacentBlk i aq base tvs asrc1 rl data asrc2 vsrc2
    (ls2.map (fun l => (i, l)))
    (fun x hx => by
      obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hx
      exact ⟨rfl, admRunGAdmin pstep false _ _ _ _ _ hstar l hl⟩) hnn hlen
  obtain ⟨img, lg, f⟩ := σ
  obtain ⟨himg, hlg, hf⟩ := hm
  dsimp only at himg hlg hf hew hlb
  subst himg hlg hlb
  cases hms with
  | MStepRmw _ _ _ _ _ _ _ _ _ hrd hlt =>
    have hro : readOk c.pcImg c.pcLog ag.paWs aq false base tvs := by
      have h := wsEqrReadOk _ _ _ _ _ _ _ _ hew (rdOkReadOk _ _ _ _ _ _ _ hrd)
      rwa [zip_fst_snd] at h
    have hstep1 : wpPfStep pstep pcls i (.LExLoad aq base tvs asrc1) c
        ⟨c.pcImg, c.pcLog, dm, c.pcAgs.set i
          ⟨pm, exloadPostRunD ag.paWs aq (srcsView ag.paWs asrc1) base (tvs.map Prod.fst),
           ag.paProm⟩⟩ :=
      wpPfStep.PFExLoad c ag aq base tvs asrc1 pm dm hlk hps1 hro
    have hlk1 : (c.pcAgs.set i
          ⟨pm, exloadPostRunD ag.paWs aq (srcsView ag.paWs asrc1) base (tvs.map Prod.fst),
           ag.paProm⟩)[i]?
        = some ⟨pm, exloadPostRunD ag.paWs aq (srcsView ag.paWs asrc1) base (tvs.map Prod.fst),
            ag.paProm⟩ :=
      list_lookup_insert hlti
    obtain ⟨c2, ag2, hrun2, heq2, hd2, hlk2, hs2, hw2, hr2, hfm2⟩ :=
      admRunGPf pstep pcls fok false pm dm ls2 pm2 dm2 hstar
        ⟨c.pcImg, c.pcLog, dm, c.pcAgs.set i
          ⟨pm, exloadPostRunD ag.paWs aq (srcsView ag.paWs asrc1) base (tvs.map Prod.fst),
           ag.paProm⟩⟩ i
        ⟨pm, exloadPostRunD ag.paWs aq (srcsView ag.paWs asrc1) base (tvs.map Prod.fst),
         ag.paProm⟩ hpin hlk1 rfl rfl
        (fun b t hm => absurd hm (admRunGFetchFree pstep _ _ _ _ _ hstar b t))
    have hres2 : ag2.paWs.wRes
        = some ⟨base, tvs.map Prod.fst, ldvOf ag.paWs aq 0 base (tvs.map Prod.fst)⟩ :=
      (hr2 rfl).trans (exloadPostRunDRes _ _ _ _ _)
    have himg2 : c2.pcImg = c.pcImg := heq2.1
    have hlog2 : c2.pcLog = c.pcLog := heq2.2.1
    have hoth : ∀ j agj, j ≠ i → c2.pcAgs[j]? = some agj → wsEqr (f j) agj.paWs := by
      intro j agj hne hj
      obtain ⟨agj1, hj1, he1⟩ := heq2.2.2 j agj hj
      rcases lookupSetCases hj1 with ⟨hji, _⟩ | ⟨_, hj1'⟩
      · exact absurd hji hne
      · exact wsEqrTrans (hf j agj1 hj1') he1
    have hwm : wsEqr (loadPostRun (f i) aq base (tvs.map Prod.fst)) ag2.paWs :=
      wsEqrTrans (wsEqrExloadPostRunD _ _ _ _ _ _ hew) hw2
    have hk : pcls pm2 (.LExStore rl base data asrc2 vsrc2)
          (loadPostRun (f i) aq base (tvs.map Prod.fst))
        = pcls ag2.paSt (.LExStore rl base data asrc2 vsrc2) ag2.paWs := by
      rw [hs2]; exact hce _ _ _ _ hwm
    have hstep2 : wpPfStep pstep pcls i (.LExStore rl base data asrc2 vsrc2) c2
        ⟨c2.pcImg, c2.pcLog ++
            [⟨base, data, some i, pcls ag2.paSt (.LExStore rl base data asrc2 vsrc2) ag2.paWs⟩],
          dn, c2.pcAgs.set i
          ⟨p', storePostRunD ag2.paWs rl (srcsView ag2.paWs asrc2) (srcsView ag2.paWs vsrc2)
                base data.length (c2.pcLog.length + 1), ag2.paProm⟩⟩ :=
      wpPfStep.PFExStore c2 ag2 rl base data asrc2 vsrc2 _
        ⟨base, tvs.map Prod.fst, ldvOf ag.paWs aq 0 base (tvs.map Prod.fst)⟩ p' dn hlk2
        (by rw [hs2, hd2]; exact hps2) hnn hres2 rfl
        (by show (tvs.map Prod.fst).length = data.length; rw [List.length_map]; exact hlen)
        (by rw [hlog2]; exact rmwLatestExclOkTs c.pcImg c.pcLog i base _ hlt) rfl
    have hrunS := pfRunS.snoc _ _ _ _ _
      (pfRunSTrans pstep pcls fok _ _ _ _ _
        (pfRunSOne pstep pcls fok _ _ _ _ hstep1 (by unfold pfStepFacts; trivial)) hrun2)
      hstep2 (by unfold pfStepFacts; trivial)
    refine ⟨_, by simpa using hrunS, hadj, ?_, ?_, rfl⟩
    · dsimp only
      rw [hlog2, himg2, hk]
      refine cfgMatchdUpdGen _ _ _ _ i ag2 p' _ _ (updWs f i ag2.paWs) _ ?_ hlk2 ?_ ?_
      · intro j agj hj
        by_cases hji : j = i
        · subst hji
          rw [hlk2] at hj
          cases hj
          rw [updWsEq]
          exact wsEqrRefl _
        · rw [updWsNe _ _ _ _ hji]
          exact hoth j agj hji hj
      · rw [updWsEq]
        exact wsEqrStorePostRunD _ _ _ _ _ _ _ _ hwm
      · intro j hne
        rw [updWsNe _ _ _ _ hne, updWsNe _ _ _ _ hne]
    · dsimp only
      rw [list_fmap_insert, hfm2, list_insert_insert]
      dsimp only
      rw [list_fmap_insert, list_insert_insert]

/-! ## (10) THE SHAPED REPLAY -/

/-- THE SHAPED PROGRAM-CARRYING REPLAY.  Under `execProgOk'S`, every prefix of
an `execWf` execution is the projection of a LABELLED promise-free run whose
step list is `pairAdjacent` and whose every step carries `pfStepFacts` (fetch
clause at each fetch, the per-load single-copy view at each plain load). -/
theorem execPrefixPfRunProgShaped (pst : Nat → List P) (dv : Nat → D) (E : Exec) (n : Nat) :
    pclsEqr pcls → pstepPinned (exImg E) pstep →
    execWf E → execProgOk'S pstep pcls fok pst dv E →
    n ≤ E.exTr.length →
    ∃ (c : Wpcfg P D) (st : List (Nat × Wlabel)),
      pfRunS pstep pcls fok (wpInit (exImg E) (dv 0) (pst 0)) st c ∧
      pairAdjacent st ∧
      c.pcAgs.map Wpagent.paSt = pst n ∧ c.pcDev = dv n ∧
      cfgMatchd c (stt E n) := by
  intro hce hpin hE hpr
  induction n with
  | zero =>
    intro _
    refine ⟨wpInit (exImg E) (dv 0) (pst 0), [], pfRunS.nil, pairAdjacentNil,
      by simp [wpInit, List.map_map, Function.comp_def], rfl, rfl, execLogInit E hE, ?_⟩
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
    obtain ⟨c, st, hrun, hadj, hst, hdev, hm⟩ := ih (by omega)
    obtain ⟨s, hs⟩ := someOfIsSome (execTrLookup E n (by omega))
    have hms := execStepAt E n s hE hs
    obtain ⟨hsca, p, pa, da, p', ls, hp, hnext, hstar, hfetch, -, hsup⟩ := hpr n s hs
    have hex : ∃ ag, c.pcAgs[s.esAg]? = some ag ∧ ag.paSt = p := by
      rw [← hst, List.getElem?_map] at hp
      cases hag : c.pcAgs[s.esAg]? with
      | none => rw [hag] at hp; cases hp
      | some ag => rw [hag] at hp; injection hp with hp; exact ⟨ag, rfl, hp⟩
    obtain ⟨ag, hag, hagp⟩ := hex
    have hpc : pstepPinned c.pcImg pstep := by
      have himg : c.pcImg = exImg E := by
        rw [← hm.1]; exact execImgConst E n hE (by omega)
      rw [himg]; exact hpin
    -- the leading administrative star, labelled
    obtain ⟨c0, ag0, hrun0, heq0, hd0, hlk0, hs0, _, _, hfm0⟩ :=
      admRunGPf pstep pcls fok true p (dv n) ls pa da hstar c s.esAg ag hpc hag hagp hdev
        (fun b t hmem => by rw [← hm.1, ← hm.2.1]; exact hfetch b t hmem)
    have hm0 : cfgMatchd c0 (stt E n) := cfgEqrMatchd _ _ _ heq0 hm
    have hadm0 : pairAdjacent (ls.map (fun l => (s.esAg, l))) :=
      pairAdjacentFused _ (fun x hx => by
        obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hx
        have := admRunGAdmin pstep true _ _ _ _ _ hstar l hl
        cases l <;> simp_all [lbAdmin, lbFused])
    have hrunA := pfRunSTrans pstep pcls fok _ _ _ _ _ hrun hrun0
    rcases hsup with ⟨l, hfu, hre, hps⟩ | ⟨pm, dm, ls2, pm2, dm2, l1, l2, hre, hps1, hstar2, hps2⟩
    · obtain ⟨c2, hstep, hm2, hst2, hdev2⟩ :=
        mstepWpPfStepProg pstep pcls (stt E n) (stt E (n + 1)) s.esAg s.esLb c0 ag0 pa p' l
          (dv (n + 1)) hce hm0 hlk0 hs0 hre (by rw [hd0]; exact hps) hms
      have hfacts : pfStepFacts fok c0 s.esAg l := by
        cases l with
        | LLoad aq lat base tvs asrc =>
          have hpr' := hre.2.2.2
          simp only [projLbl, Option.some.injEq] at hpr'
          show scaOk c0.pcImg c0.pcLog s.esAg base (tvs.map Prod.fst)
          rw [← hm0.1, ← hm0.2.1]
          exact hsca aq base _ _ hpr'.symm
        | LIFetch b t =>
          have hpr' := hre.2.2.2
          simp [projLbl] at hpr'
        | _ => trivial
      refine ⟨c2, (st ++ ls.map (fun l => (s.esAg, l))) ++ [(s.esAg, l)],
        pfRunS.snoc _ _ _ _ _ hrunA hstep hfacts, ?_, ?_, hdev2, hm2⟩
      · exact pairAdjacentApp _ _ (pairAdjacentApp _ _ hadj hadm0)
          (pairAdjacentFused _ (fun x hx => by
            simp only [List.mem_singleton] at hx; subst hx; exact hfu))
      · rw [hst2, hfm0, hst, list_insert_insert, ← hnext]
    · obtain ⟨c2, hstep, hadjP, hm2, hst2, hdev2⟩ :=
        mstepWpPfStepPairS pstep pcls fok (stt E n) (stt E (n + 1)) s.esAg s.esLb c0 ag0 pa pm pm2
          p' l1 l2 ls2 dm dm2 (dv (n + 1)) hce (by rw [heq0.1]; exact hpc) hm0 hlk0 hs0 hre
          (by rw [hd0]; exact hps1) hstar2 hps2 hms
      refine ⟨c2, _, pfRunSTrans pstep pcls fok _ _ _ _ _ hrunA hstep,
        pairAdjacentApp _ _ (pairAdjacentApp _ _ hadj hadm0) hadjP, ?_, hdev2, hm2⟩
      rw [hst2, hfm0, hst, list_insert_insert, ← hnext]

/-- The whole trace. -/
theorem execWfPfRunProgShaped (pst : Nat → List P) (dv : Nat → D) (E : Exec) :
    pclsEqr pcls → pstepPinned (exImg E) pstep →
    execWf E → execProgOk'S pstep pcls fok pst dv E →
    ∃ (c : Wpcfg P D) (st : List (Nat × Wlabel)),
      pfRunS pstep pcls fok (wpInit (exImg E) (dv 0) (pst 0)) st c ∧
      pairAdjacent st ∧
      c.pcAgs.map Wpagent.paSt = pst E.exTr.length ∧ c.pcDev = dv E.exTr.length ∧
      cfgMatchd c (stt E E.exTr.length) := by
  intro hce hpin hE hpr
  exact execPrefixPfRunProgShaped pstep pcls fok pst dv E E.exTr.length hce hpin hE hpr
    (Nat.le_refl _)

/-- The replay of a PINNED shaped supply, projected to the unpinned LTS (the
M1 form: `pstep := pstepEv`, supply at `pstepPin img pstepEv`). -/
theorem execWfPfRunPinShaped (img : Image) (pst : Nat → List P) (dv : Nat → D) (E : Exec) :
    pclsEqr pcls → exImg E = img →
    execWf E → execProgOk'S (pstepPin img pstep) pcls fok pst dv E →
    ∃ (c : Wpcfg P D) (st : List (Nat × Wlabel)),
      pfRunS pstep pcls fok (wpInit (exImg E) (dv 0) (pst 0)) st c ∧
      pairAdjacent st ∧
      c.pcAgs.map Wpagent.paSt = pst E.exTr.length ∧ c.pcDev = dv E.exTr.length ∧
      cfgMatchd c (stt E E.exTr.length) := by
  intro hce himg hE hpr
  subst himg
  obtain ⟨c, st, h1, h2, h3, h4, h5⟩ :=
    execWfPfRunProgShaped (pstepPin (exImg E) pstep) pcls fok pst dv E hce (pstepPinPinned _ _)
      hE hpr
  exact ⟨c, st, pfRunSPinSub pstep pcls fok _ _ _ _ h1, h2, h3, h4, h5⟩

end shape

end Weak
