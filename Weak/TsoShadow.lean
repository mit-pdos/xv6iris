/-
Weak: **the TsoMem view SHADOW over a pf step list** (allocproc plan W5b′, §B(10) "The redesign",
§C Stage 0 "W5b′"; reviews [R10.3], [R11.1], [R11.3]).

Lean-only (no Rocq source).  TsoMem's per-hart READ SIDE (`tv`, `rv`, `coh`, `acq`;
`MachCSL/Lang.lean:127-163`, `MachCSL/TsoMem.lean:253-277`) is REPLAYED deterministically over a
promise-free run's STEP LIST: the shadow is a function of the step-list PREFIX, not of the
configuration ([R10.3]: fences, plain loads and acquire pairs move the read side and leave no
trace in `pcLog`).  A plain load runs at the MINIMAL legal view
`tvn := max(F, max_{foreign j} t_j)`, `F := max(tv, coh over the footprint)` (`shTvn`).

* **The `coh` stamp is a PARAMETER** ([R11.1]; W-COH is changing MachCSL's `afterLoad`/`store` in
  parallel, so nothing here reads the compiled TsoMem's `HRead.afterLoad`): `CohStamp` is the PAIR
  (load stamp, store effect).  Three instances: `cohFoot` (TODAY's TsoMem: every footprint byte
  := `tvn`; stores leave `coh`), `cohSrc` (G2-Q RULED (a′), BOTH components [OWN.20][OWN.23]:
  `coh a := max (coh a) t_a` for a FOREIGN-sourced byte only; a store RESETS its footprint to 0),
  `cohOff` ((a‴): no coherence floor).  The load stamp's per-byte input is
  `List (Option (Agent × Nat))` — byte `j`'s (author, timestamp), mirrored from the pf log
  (`wmTid`, position + 1), `none` for an image byte (timestamp 0, where any stamp is a no-op).
* **Memory fields only** ([R11.3]): `itv` is NOT part of the shadow (`fence.i` and the
  `sfence.vma` marker are the same `LFence false×4`; W5d's `itvOf`).  Both move no memory field
  here (`TsoShadow.ShSt.fenceNoSucc`).
* `scaOkT`/`execScaT`/`candScaT` (G1-Q RULED (e) [OWN.17]): `scaOk` plus `F ≤ tvn` at the shadow
  of the trace prefix (`shadowOf (E.exTr.take k)`, computed from `E.exTr`: `LRmw aq`, the
  `LFence` bits, `LStore` for the store effect, the log authors for foreign-ness and `ownPub`).
* `diskLatOk`/`execDiskLat`/`candDiskLat` (G3-Q RULED (a″) [OWN.17]): every load of agent `NCPU`
  (the disk row, `epsInit`) reads the `latest` write per byte — a SHAPE clause, no label change.
* `execProgOk'ST` = `execProgOk'S` ∧ clause (iii)′ `execScaT` ∧ clause (iv) `execDiskLat`;
  `pfStepFactsT` / `pfRunST`: the labelled run whose every step carries, besides `pfStepFacts`,
  `scaOkT` at the shadow of the step-list PREFIX before it and `diskLatOk`.
* **The re-proved replay** `execPrefixPfRunProgShapedT` (the snoc of `execPrefixPfRunProgShaped`
  with the shadow threaded): it also returns the PROJECTION LEMMA `tsoRun st = shadowRun
  (E.exTr.take n)` — the step-list shadow (admin steps inert, an exclusive pair block = the fused
  `LRmw`) equals the trace shadow, authors included.  Whole-trace and pinned (M1) forms.
* Spot checks (the redesign's two gaps, now as shadow facts): `TsoShadow.g1NotScaT` (G1: after
  the `.aq` pair the shadow floor is the pair's write position 2, so the spike's stale load is
  `scaOk` but NOT `scaOkT`, under every stamp); `TsoShadow.g2ScaTSrc` / `TsoShadow.g2NotScaTFoot`
  (G2: the spike's mixed-size pair is `scaOkT` under (a′) and NOT under today's footprint stamp).

Deviations from the plan's text: (1) the shadow is indexed by the AGENT `Nat` (a `CPU` is
`hartAgent c`; the disk row's shadow exists and is unused); (2) `Weak/PfRunShape.lean` is NOT
edited — the strengthened clauses are new names (`execProgOk'ST`, `pfRunST`, …) beside the
landed ones, with forgetful maps back, so W5c and every importer stay untouched (W5 re-points
`srvwmoXv6M1Premises`); (3) `scaOkT` is required of EVERY plain load (the disk row's included —
there it follows from `latest`), as clause (iii) is.
-/
import Weak.TsoOfPf

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1 LeanRV64D

namespace TsoShadow

/-! ## (1) The stamp pair and the shadow state -/

/-- The footprint index of `a` in an `n`-byte access at `base`: `some j` iff `a = base + j`,
`j < n`. -/
def footIdx (base : Int) (n : Nat) (a : Int) : Option Nat :=
  if base ≤ a ∧ a < base + n then some (a - base).toNat else none

theorem footIdxSome (base : Int) (n : Nat) (a : Int) (j : Nat) :
    footIdx base n a = some j ↔ j < n ∧ a = accAddr base j := by
  unfold footIdx accAddr
  constructor
  · intro hs
    split at hs
    · rename_i hc
      cases hs
      have h := Int.toNat_of_nonneg (a := a - base) (by omega)
      omega
    · cases hs
  · rintro ⟨hj, rfl⟩
    rw [if_pos (by omega)]
    congr 1
    rw [show base + (j : Int) - base = (j : Int) by omega]
    simp

theorem footIdxAcc (base : Int) (n j : Nat) (hj : j < n) : footIdx base n (accAddr base j) = some j :=
  (footIdxSome base n _ j).2 ⟨hj, rfl⟩

/-- THE `coh` STAMP PAIR [R11.1]: the load stamp (viewer agent, old floors, base, per-byte
(author, timestamp) sources, the load's view `tvn`) and the store effect (old floors, base,
width). -/
structure CohStamp where
  load : Nat → (Int → Nat) → Int → List (Option (Nat × Nat)) → Nat → (Int → Nat)
  store : (Int → Nat) → Int → Nat → (Int → Nat)

/-- TODAY's TsoMem (`HRead.afterLoad`, `TsoMem.lean:268-270`): every footprint byte := `tvn`;
`MState.store` leaves `coh`. -/
def cohFoot : CohStamp where
  load _ coh base srcs tvn a :=
    match footIdx base srcs.length a with
    | some _ => tvn
    | none => coh a
  store coh _ _ := coh

/-- G2-Q RULED (a′), BOTH components [OWN.20][OWN.23]: a FOREIGN-sourced byte is stamped with its
source's timestamp (`coh a := max (coh a) t_a`), own-sourced and image bytes unstamped; a store
RESETS its footprint's floors to 0. -/
def cohSrc : CohStamp where
  load i coh base srcs _ a :=
    match footIdx base srcs.length a with
    | some j =>
      match srcs[j]? with
      | some (some (au, t)) => if au = i then coh a else max (coh a) t
      | _ => coh a
    | none => coh a
  store coh base n a :=
    match footIdx base n a with
    | some _ => 0
    | none => coh a

/-- (a‴): no coherence floor. -/
def cohOff : CohStamp := ⟨fun _ coh _ _ _ => coh, fun coh _ _ => coh⟩

theorem cohFootLoad (i : Nat) (coh : Int → Nat) (base : Int) (srcs : List (Option (Nat × Nat)))
    (tvn j : Nat) (hj : j < srcs.length) : cohFoot.load i coh base srcs tvn (accAddr base j) = tvn := by
  simp only [cohFoot, footIdxAcc base _ j hj]

theorem cohSrcLoadForeign (i : Nat) (coh : Int → Nat) (base : Int) (srcs : List (Option (Nat × Nat)))
    (tvn j au t : Nat) (hj : srcs[j]? = some (some (au, t))) (hne : au ≠ i) :
    cohSrc.load i coh base srcs tvn (accAddr base j) = max (coh (accAddr base j)) t := by
  have hl : j < srcs.length := lookup_lt_Some hj
  simp only [cohSrc, footIdxAcc base _ j hl, hj, if_neg hne]

theorem cohSrcLoadOwn (i : Nat) (coh : Int → Nat) (base : Int) (srcs : List (Option (Nat × Nat)))
    (tvn j t : Nat) (hj : srcs[j]? = some (some (i, t))) :
    cohSrc.load i coh base srcs tvn (accAddr base j) = coh (accAddr base j) := by
  have hl : j < srcs.length := lookup_lt_Some hj
  simp [cohSrc, footIdxAcc base _ j hl, hj]

theorem cohSrcLoadOut (i : Nat) (coh : Int → Nat) (base : Int) (srcs : List (Option (Nat × Nat)))
    (tvn : Nat) (a : Int) (ha : footIdx base srcs.length a = none) :
    cohSrc.load i coh base srcs tvn a = coh a := by
  simp only [cohSrc, ha]

theorem cohSrcStoreIn (coh : Int → Nat) (base : Int) (n j : Nat) (hj : j < n) :
    cohSrc.store coh base n (accAddr base j) = 0 := by
  simp only [cohSrc, footIdxAcc base n j hj]

theorem cohSrcStoreOut (coh : Int → Nat) (base : Int) (n : Nat) (a : Int) (ha : footIdx base n a = none) :
    cohSrc.store coh base n a = coh a := by
  simp only [cohSrc, ha]

/-- The shadow of one agent's TsoMem read side (memory fields only [R11.3]). -/
structure ShSt where
  tv : Nat
  rv : Nat
  coh : Int → Nat
  acq : Bool

/-- TsoMem's boot read side (`tv = 0`, `HRead.zero`). -/
def ShSt.zero : ShSt := ⟨0, 0, fun _ => 0, false⟩

/-- Byte source: (author, timestamp) of log message `t` (authors `au`, timestamp = position + 1);
`none` for the image (timestamp 0). -/
def shSrc (au : List Nat) (t : Nat) : Option (Nat × Nat) :=
  if t = 0 then none else (au[t - 1]?).map (fun a => (a, t))

/-- The largest FOREIGN source timestamp of a footprint (viewer `i`). -/
def shForeign (i : Nat) : List (Option (Nat × Nat)) → Nat
  | [] => 0
  | some (a, t) :: r => if a = i then shForeign i r else max t (shForeign i r)
  | none :: r => shForeign i r

/-- The largest coherence floor over the first `n` footprint bytes. -/
def cohMax (coh : Int → Nat) (base : Int) : Nat → Nat
  | 0 => 0
  | n + 1 => max (cohMax coh base n) (coh (accAddr base n))

/-- The load floor `F := max(tv, coh over the footprint)`. -/
def shFloor (sh : ShSt) (base : Int) (n : Nat) : Nat := max sh.tv (cohMax sh.coh base n)

/-- The MINIMAL legal view of a plain load: `max(F, max_{foreign j} t_j)`. -/
def shTvn (i : Nat) (sh : ShSt) (base : Int) (srcs : List (Option (Nat × Nat))) : Nat :=
  max (shFloor sh base srcs.length) (shForeign i srcs)

theorem cohMaxGe (coh : Int → Nat) (base : Int) : ∀ (n j : Nat), j < n →
    coh (accAddr base j) ≤ cohMax coh base n
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, j, h => by
    simp only [cohMax]
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | rfl
    · exact Nat.le_trans (cohMaxGe coh base n j h) (Nat.le_max_left _ _)
    · exact Nat.le_max_right _ _

/-- The floor dominates `tv` and every footprint floor. -/
theorem shFloorGe (sh : ShSt) (base : Int) (n : Nat) :
    sh.tv ≤ shFloor sh base n ∧ ∀ j, j < n → sh.coh (accAddr base j) ≤ shFloor sh base n :=
  ⟨Nat.le_max_left _ _, fun j hj => Nat.le_trans (cohMaxGe _ _ n j hj) (Nat.le_max_right _ _)⟩

/-! ## (2) TsoMem's read-side moves, on the shadow -/

/-- `MState.afterLoad` at the minimal view: `rv := max rv tvn`, the load stamp. -/
def ShSt.load (stamp : CohStamp) (i : Nat) (sh : ShSt) (base : Int)
    (srcs : List (Option (Nat × Nat))) : ShSt :=
  { sh with rv := max sh.rv (shTvn i sh base srcs),
            coh := stamp.load i sh.coh base srcs (shTvn i sh base srcs) }

/-- `MState.afterExcl` at the top: the floor to the top iff an acquire, `rv := top`, the acquire
bit recorded; `coh` kept. -/
def ShSt.excl (sh : ShSt) (top : Nat) (aq : Bool) : ShSt :=
  { sh with tv := if aq then top else sh.tv, rv := top, acq := aq }

/-- `MState.store`: the floor passes the store iff the write half of an acquire pair; the acquire
bit clears; the store effect on `coh`. -/
def ShSt.store (stamp : CohStamp) (sh : ShSt) (top : Nat) (excl : Bool) (base : Int) (n : Nat) :
    ShSt :=
  { sh with tv := if excl && sh.acq then top + 1 else sh.tv,
            coh := stamp.store sh.coh base n, acq := false }

/-- `MState.fence` on the memory fields, from the label's bits: a W→R edge (`pw ∧ sr`) drains,
an R→R edge (`pr ∧ sr`) acquires (`TsoShadow.fenceBitsNow`). -/
def ShSt.fence (sh : ShSt) (pub : Nat) (pr pw sr sw : Bool) : ShSt :=
  { sh with tv := MachCSL.fencePost (pw && sr) (pr && sr) sh.tv sh.rv pub }

/-- A fence with no read successor moves no memory field: the parked `fence rw,w`, `w,w`,
`r,w`, and `fence.i` / the `sfence.vma` marker (`LFence false×4`). -/
theorem ShSt.fenceNoSucc (sh : ShSt) (pub : Nat) (pr pw sw : Bool) :
    sh.fence pub pr pw false sw = sh := by
  cases sh
  simp [ShSt.fence, MachCSL.fencePost]

/-- The label bits of every `ebarNow` barrier give TsoMem's `fenceDrains`/`fenceAcq`. -/
theorem fenceBitsNow (b : barrier_kind) (pr pw sr sw : Bool)
    (hb : ebarNow b = some (pr, pw, sr, sw)) :
    (pw && sr) = fenceDrains b ∧ (pr && sr) = fenceAcq b := by
  cases b <;> simp only [ebarNow, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hb <;>
    (try obtain ⟨rfl, rfl, rfl, rfl⟩ := hb) <;> simp [fenceDrains, fenceAcq]

/-- The parked half of `fence.tso` has no read successor. -/
theorem fenceBitsPark (b : barrier_kind) (pr pw sr sw : Bool)
    (hb : ebarPark b = some (pr, pw, sr, sw)) : sr = false := by
  cases b <;> simp only [ebarPark, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hb
  exact hb.2.2.1.symm

/-! ## (3) The step-list shadow -/

/-- The labels that append ONE log message. -/
def lbWrites (l : Wlabel) : Bool :=
  match l with
  | .LStore .. | .LRmw .. | .LExStore .. => true
  | _ => false

/-- The plain loads. -/
def lbIsLoad (l : Wlabel) : Bool :=
  match l with
  | .LLoad .. => true
  | _ => false

theorem lbAdminNotLoad (instr : Bool) (l : Wlabel) (h : lbAdmin instr l) : lbIsLoad l = false := by
  cases l <;> simp_all [lbAdmin, lbIsLoad]

/-- The viewer's OWN step on its read side (authors `au` = the log before the step; `top =
|au|`).  Every other label (admin, `LDev`, fetches) moves no memory field. -/
def shStep (stamp : CohStamp) (i : Nat) (au : List Nat) (sh : ShSt) (l : Wlabel) : ShSt :=
  match l with
  | .LLoad _ _ base tvs _ => sh.load stamp i base ((tvs.map Prod.fst).map (shSrc au))
  | .LStore _ base data _ _ => sh.store stamp au.length false base data.length
  | .LRmw aq _ base _ data _ _ => (sh.excl au.length aq).store stamp au.length true base data.length
  | .LFence pr pw sr sw => sh.fence (MachCSL.ownPub i au) pr pw sr sw
  | .LExLoad aq _ _ _ => sh.excl au.length aq
  | .LExStore _ base data _ _ => sh.store stamp au.length true base data.length
  | _ => sh

/-- One step of the fold: the authors grow by a writing step's agent; the viewer's read side
moves on its own steps only. -/
def shAct (stamp : CohStamp) (i : Nat) (x : List Nat × ShSt) (y : Nat × Wlabel) : List Nat × ShSt :=
  (if lbWrites y.2 then x.1 ++ [y.1] else x.1, if y.1 = i then shStep stamp i x.1 x.2 y.2 else x.2)

/-- The shadow fold over a step list, from the empty log and the boot read side. -/
def tsoRun (stamp : CohStamp) (i : Nat) (st : List (Nat × Wlabel)) : List Nat × ShSt :=
  st.foldl (shAct stamp i) ([], ShSt.zero)

/-- The authors of a step list's writes, in order. -/
def stAuthors (st : List (Nat × Wlabel)) : List Nat :=
  st.filterMap (fun y => if lbWrites y.2 then some y.1 else none)

/-! ## (4) The trace shadow (computable from `E.exTr`) -/

/-- The trace twin of `shStep` over the axiomatic alphabet (an `LRmw` = exclusive read then
exclusive write). -/
def shStepL (stamp : CohStamp) (i : Nat) (au : List Nat) (sh : ShSt) (lb : Lbl) : ShSt :=
  match lb with
  | .LLoad _ base ts _ => sh.load stamp i base (ts.map (shSrc au))
  | .LStore _ base vs _ => sh.store stamp au.length false base vs.length
  | .LFence pr pw sr sw => sh.fence (MachCSL.ownPub i au) pr pw sr sw
  | .LRmw aq _ base _ _ wvs _ => (sh.excl au.length aq).store stamp au.length true base wvs.length

def shActL (stamp : CohStamp) (i : Nat) (x : List Nat × ShSt) (s : Estep) : List Nat × ShSt :=
  (if lbIsW s.esLb then x.1 ++ [s.esAg] else x.1,
   if s.esAg = i then shStepL stamp i x.1 x.2 s.esLb else x.2)

def shadowRun (stamp : CohStamp) (i : Nat) (tr : List Estep) : List Nat × ShSt :=
  tr.foldl (shActL stamp i) ([], ShSt.zero)

def stAuthorsL (tr : List Estep) : List Nat :=
  tr.filterMap (fun s => if lbIsW s.esLb then some s.esAg else none)

/-! ## (5) The fold laws: admin steps inert, fused steps = their projection, a pair block = the
fused `LRmw` -/

theorem tsoRunSnoc (stamp : CohStamp) (i : Nat) (st : List (Nat × Wlabel)) (y : Nat × Wlabel) :
    tsoRun stamp i (st ++ [y]) = shAct stamp i (tsoRun stamp i st) y := by
  simp [tsoRun, List.foldl_append]

theorem tsoRunApp (stamp : CohStamp) (i : Nat) (st b : List (Nat × Wlabel)) :
    tsoRun stamp i (st ++ b) = b.foldl (shAct stamp i) (tsoRun stamp i st) := by
  simp [tsoRun, List.foldl_append]

theorem shadowRunSnoc (stamp : CohStamp) (i : Nat) (tr : List Estep) (s : Estep) :
    shadowRun stamp i (tr ++ [s]) = shActL stamp i (shadowRun stamp i tr) s := by
  simp [shadowRun, List.foldl_append]

theorem shActAdmin (stamp : CohStamp) (i : Nat) (instr : Bool) (x : List Nat × ShSt)
    (y : Nat × Wlabel) (h : lbAdmin instr y.2) : shAct stamp i x y = x := by
  obtain ⟨j, l⟩ := y
  obtain ⟨au, sh⟩ := x
  cases l <;> simp_all [lbAdmin, shAct, lbWrites, shStep]

theorem foldlAdmin (stamp : CohStamp) (i : Nat) (instr : Bool) :
    ∀ (ms : List (Nat × Wlabel)) (x : List Nat × ShSt), (∀ y, y ∈ ms → lbAdmin instr y.2) →
      ms.foldl (shAct stamp i) x = x
  | [], _, _ => rfl
  | y :: ms, x, h => by
    rw [List.foldl_cons, shActAdmin stamp i instr x y (h y (by simp))]
    exact foldlAdmin stamp i instr ms x (fun z hz => h z (by simp [hz]))

/-- A FUSED step is its projection's trace step (for any class `k`). -/
theorem shActFused (stamp : CohStamp) (i : Nat) (x : List Nat × ShSt) (j : Nat) (l : Wlabel)
    (k : WmClass) (lb : Lbl) (hf : lbFused l) (hp : projLbl k l = some lb) :
    shAct stamp i x (j, l) = shActL stamp i x ⟨j, lb⟩ := by
  cases l <;> simp only [lbFused, projLbl, Option.some.injEq, reduceCtorEq] at hf hp <;>
    subst hp <;> rfl

/-- THE PAIR BLOCK (an exclusive read, any `lbAdmin` steps, the exclusive write of the same
agent) is the fused `LRmw`'s trace step. -/
theorem shRunPair (stamp : CohStamp) (i : Nat) (x : List Nat × ShSt) (e : Estep) (aq rl : Bool)
    (base : Int) (tvs : List (Nat × BitVec 8)) (data : List (BitVec 8)) (a1 a2 v2 : List Dsrc)
    (k : WmClass) (ms : List (Nat × Wlabel)) (instr : Bool) (hms : ∀ y, y ∈ ms → lbAdmin instr y.2)
    (hlb : e.esLb = .LRmw aq rl base (tvs.map Prod.fst) (tvs.map Prod.snd) data k) :
    ((e.esAg, .LExLoad aq base tvs a1) :: (ms ++ [(e.esAg, .LExStore rl base data a2 v2)])).foldl
      (shAct stamp i) x = shActL stamp i x e := by
  obtain ⟨j, lb⟩ := e
  simp only at hlb
  subst hlb
  rw [List.foldl_cons, List.foldl_append, foldlAdmin stamp i instr ms _ hms]
  obtain ⟨au, sh⟩ := x
  by_cases hj : j = i
  · subst hj
    simp [shAct, shActL, shStep, shStepL, lbWrites, lbIsW]
  · simp [shAct, shActL, lbWrites, lbIsW, hj]

/-- The authors component of the fold. -/
theorem foldlAuthors (stamp : CohStamp) (i : Nat) :
    ∀ (st : List (Nat × Wlabel)) (au : List Nat) (sh : ShSt),
      (st.foldl (shAct stamp i) (au, sh)).1 = au ++ stAuthors st
  | [], au, sh => by simp [stAuthors]
  | y :: st, au, sh => by
    simp only [List.foldl_cons, shAct]
    rw [foldlAuthors stamp i st]
    cases h : lbWrites y.2 <;> simp [stAuthors, h]

theorem tsoRunAuthors (stamp : CohStamp) (i : Nat) (st : List (Nat × Wlabel)) :
    (tsoRun stamp i st).1 = stAuthors st := by
  simp [tsoRun, foldlAuthors]

theorem foldlAuthorsL (stamp : CohStamp) (i : Nat) :
    ∀ (tr : List Estep) (au : List Nat) (sh : ShSt),
      (tr.foldl (shActL stamp i) (au, sh)).1 = au ++ stAuthorsL tr
  | [], au, sh => by simp [stAuthorsL]
  | s :: tr, au, sh => by
    simp only [List.foldl_cons, shActL]
    rw [foldlAuthorsL stamp i tr]
    cases h : lbIsW s.esLb <;> simp [stAuthorsL, h]

theorem shadowRunAuthors (stamp : CohStamp) (i : Nat) (tr : List Estep) :
    (shadowRun stamp i tr).1 = stAuthorsL tr := by
  simp [shadowRun, foldlAuthorsL]

theorem stAuthorsSnoc (st : List (Nat × Wlabel)) (i : Nat) (l : Wlabel) :
    stAuthors (st ++ [(i, l)]) = stAuthors st ++ (if lbWrites l then [i] else []) := by
  cases h : lbWrites l <;> simp [stAuthors, List.filterMap_append, h]

/-- The step list's authors ARE the pf log's (the shadow's foreign test reads the log). -/
theorem wpPfStepAuthors {P D : Type} (pstep : P → D → Wlabel → P → D → Prop)
    (pcls : P → Wlabel → Wstate → WmClass) (i : Nat) (l : Wlabel) (c1 c2 : Wpcfg P D)
    (h : wpPfStep pstep pcls i l c1 c2) :
    c2.pcLog.map Wmsg.wmTid = c1.pcLog.map Wmsg.wmTid ++ (if lbWrites l then [some i] else []) := by
  cases h <;> simp [lbWrites]

/-- The trace's authors ARE the axiomatic log's. -/
theorem execAuthors (E : Exec) (hE : execWf E) :
    ∀ n, n ≤ E.exTr.length → (stt E n).msLog.map Wmsg.wmTid = (stAuthorsL (E.exTr.take n)).map some
  | 0, _ => by
    have h0 := execLogInit E hE
    simp only [elog] at h0
    simp [h0, stAuthorsL]
  | n + 1, hn => by
    have ih := execAuthors E hE n (by omega)
    obtain ⟨s, hs⟩ := someOfIsSome (execTrLookup E n (by omega))
    have hms := execStepAt E n s hE hs
    rw [List.take_add_one, hs]
    simp only [Option.toList_some, stAuthorsL, List.filterMap_append] at ih ⊢
    cases hw : lbIsW s.esLb
    · rw [mstepLogNw _ _ _ _ hms hw, ih]; simp [hw]
    · obtain ⟨base, vs, _, _, hlog⟩ := mstepLogW _ _ _ _ hms hw
      rw [hlog]; simp [ih, hw]

end TsoShadow

open TsoShadow

/-! ## (6) THE SHADOW and the strengthened clauses -/

/-- THE TsoMem VIEW SHADOW of agent `i` after the step list `st` (memory fields), PARAMETRIC in
the `coh` stamp pair. -/
def tsoShadow (stamp : CohStamp) (st : List (Nat × Wlabel)) (i : Nat) : ShSt :=
  (tsoRun stamp i st).2

/-- The trace shadow of agent `i` after the trace prefix `tr`. -/
def shadowOf (stamp : CohStamp) (tr : List Estep) (i : Nat) : ShSt :=
  (shadowRun stamp i tr).2

/-- G1-Q (e): a plain load is single-copy atomic at a view `tvn` AT OR ABOVE the shadow's floor
`F = max(tv, coh over the footprint)`. -/
def scaOkT (sh : ShSt) (img : Image) (log : List Wmsg) (i : Nat) (base : Int) (ts : List Nat) :
    Prop :=
  ∃ tvn, tvn ≤ log.length ∧ shFloor sh base ts.length ≤ tvn ∧
    ∀ (j t : Nat), ts[j]? = some t → scaByte img log i tvn (accAddr base j) t

theorem scaOkTSca (sh : ShSt) (img : Image) (log : List Wmsg) (i : Nat) (base : Int)
    (ts : List Nat) : scaOkT sh img log i base ts → scaOk img log i base ts :=
  fun ⟨tvn, h1, _, h3⟩ => ⟨tvn, h1, h3⟩

/-- G3-Q (a″): a load of the DISK ROW (agent `NCPU`) reads the latest write per byte. -/
def diskLatOk (img : Image) (log : List Wmsg) (i : Nat) (base : Int) (ts : List Nat) : Prop :=
  i = NCPU → ∀ (j t : Nat), ts[j]? = some t → latest img log (accAddr base j) t

/-- Clause (iii)′: every plain load is `scaOkT` at the shadow of the trace prefix before it. -/
def execScaT (stamp : CohStamp) (E : Exec) : Prop :=
  ∀ (k : Nat) (s : Estep), E.exTr[k]? = some s →
    ∀ (aq : Bool) (base : Int) (ts : List Nat) (vs : List (BitVec 8)),
      s.esLb = .LLoad aq base ts vs →
      scaOkT (shadowOf stamp (E.exTr.take k) s.esAg) (stt E k).msImg (stt E k).msLog s.esAg base ts

/-- Clause (iv): every disk-row load reads the latest write per byte. -/
def execDiskLat (E : Exec) : Prop :=
  ∀ (k : Nat) (s : Estep), E.exTr[k]? = some s →
    ∀ (aq : Bool) (base : Int) (ts : List Nat) (vs : List (BitVec 8)),
      s.esLb = .LLoad aq base ts vs →
      diskLatOk (stt E k).msImg (stt E k).msLog s.esAg base ts

def candScaT (stamp : CohStamp) (c : Cand) : Prop := execScaT stamp (candExec c)

def candDiskLat (c : Cand) : Prop := execDiskLat (candExec c)

theorem execScaTSca (stamp : CohStamp) (E : Exec) : execScaT stamp E → execSca E :=
  fun h k s hs aq base ts vs hl => scaOkTSca _ _ _ _ _ _ (h k s hs aq base ts vs hl)

theorem candScaTSca (stamp : CohStamp) (c : Cand) : candScaT stamp c → candSca c :=
  execScaTSca stamp (candExec c)

section shapeT

variable {P D : Type}
variable (pstep : P → D → Wlabel → P → D → Prop)
variable (pcls : P → Wlabel → Wstate → WmClass)
variable (fok : Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop)
variable (stamp : CohStamp)

/-- THE SHAPED CONFORMANCE PREDICATE with the shadow clauses: `execProgOk'S` ∧ (iii)′ ∧ (iv). -/
def execProgOk'ST (pst : Nat → List P) (dv : Nat → D) (E : Exec) : Prop :=
  execProgOk'S pstep pcls fok pst dv E ∧ execScaT stamp E ∧ execDiskLat E

theorem execProgOk'STForget (pst : Nat → List P) (dv : Nat → D) (E : Exec) :
    execProgOk'ST pstep pcls fok stamp pst dv E → execProgOk'S pstep pcls fok pst dv E :=
  fun h => h.1

/-- The load facts a step carries, read at the step-list PREFIX `st` before it (the shadow) and
the pre-configuration `c` (image, log). -/
def pfLoadFactsT (st : List (Nat × Wlabel)) (c : Wpcfg P D) (i : Nat) (l : Wlabel) : Prop :=
  match l with
  | .LLoad _ _ base tvs _ =>
    scaOkT (tsoShadow stamp st i) c.pcImg c.pcLog i base (tvs.map Prod.fst) ∧
    diskLatOk c.pcImg c.pcLog i base (tvs.map Prod.fst)
  | _ => True

/-- `pfStepFacts` extended by the shadow-threaded load facts. -/
def pfStepFactsT (st : List (Nat × Wlabel)) (c : Wpcfg P D) (i : Nat) (l : Wlabel) : Prop :=
  pfStepFacts fok c i l ∧ pfLoadFactsT stamp st c i l

theorem pfLoadFactsTNonload (st : List (Nat × Wlabel)) (c : Wpcfg P D) (i : Nat) (l : Wlabel)
    (h : lbIsLoad l = false) : pfLoadFactsT stamp st c i l := by
  cases l <;> simp_all [lbIsLoad, pfLoadFactsT]

/-- A labelled promise-free run whose every step carries `pfStepFactsT` at its prefix. -/
inductive pfRunST (c : Wpcfg P D) : List (Nat × Wlabel) → Wpcfg P D → Prop where
  | nil : pfRunST c [] c
  | snoc (c1 c2 : Wpcfg P D) (st : List (Nat × Wlabel)) (i : Nat) (l : Wlabel) :
      pfRunST c st c1 → wpPfStep pstep pcls i l c1 c2 → pfStepFacts fok c1 i l →
      pfLoadFactsT stamp st c1 i l →
      pfRunST c (st ++ [(i, l)]) c2

theorem pfRunSTForget (c c' : Wpcfg P D) (st : List (Nat × Wlabel)) :
    pfRunST pstep pcls fok stamp c st c' → pfRunS pstep pcls fok c st c' := by
  intro h
  induction h with
  | nil => exact .nil
  | snoc c1 c2 st i l _ hs hf _ ih => exact .snoc c1 c2 st i l ih hs hf

/-- Every step carries `pfStepFactsT` at its prefix (the inductive's content, unpacked). -/
theorem pfRunSTFacts (c c' : Wpcfg P D) (st : List (Nat × Wlabel)) :
    pfRunST pstep pcls fok stamp c st c' →
    ∀ (st0 : List (Nat × Wlabel)) (i : Nat) (l : Wlabel) (rest : List (Nat × Wlabel)),
      st = st0 ++ (i, l) :: rest →
      ∃ c1 c2, pfRunST pstep pcls fok stamp c st0 c1 ∧ wpPfStep pstep pcls i l c1 c2 ∧
        pfStepFactsT fok stamp st0 c1 i l := by
  intro h
  induction h with
  | nil => intro st0 i l rest he; simp at he
  | snoc c1 c2 st j l' hr hs hf hl ih =>
    intro st0 i l rest he
    by_cases hr0 : rest = []
    · subst hr0
      have h1 := List.append_inj' he rfl
      simp only [List.cons.injEq, Prod.mk.injEq, and_true] at h1
      obtain ⟨rfl, rfl, rfl⟩ := h1
      exact ⟨c1, c2, hr, hs, hf, hl⟩
    · obtain ⟨rest', y, rfl⟩ := List.eq_nil_or_concat rest |>.resolve_left hr0
      have h1 : st ++ [(j, l')] = (st0 ++ (i, l) :: rest') ++ [y] := by simpa using he
      have h2 := List.append_inj' h1 rfl
      exact ih st0 i l rest' h2.1

/-- A run of LOAD-FREE steps appends to a shadow-threaded run (its load facts are vacuous). -/
theorem pfRunSTApp (c c1 c2 : Wpcfg P D) (st0 ms : List (Nat × Wlabel)) :
    pfRunST pstep pcls fok stamp c st0 c1 → pfRunS pstep pcls fok c1 ms c2 →
    (∀ y, y ∈ ms → lbIsLoad y.2 = false) → pfRunST pstep pcls fok stamp c (st0 ++ ms) c2 := by
  intro h1 h2
  induction h2 with
  | nil => intro _; simpa using h1
  | snoc c3 c4 st i l _ hs hf ih =>
    intro hnl
    rw [← List.append_assoc]
    exact .snoc _ _ _ _ _ (ih (fun y hy => hnl y (List.mem_append_left _ hy))) hs hf
      (pfLoadFactsTNonload stamp _ _ _ _ (hnl (i, l) (by simp)))

theorem pfRunSTPinSub (img : Image) (c c' : Wpcfg P D) (st : List (Nat × Wlabel)) :
    pfRunST (pstepPin img pstep) pcls fok stamp c st c' → pfRunST pstep pcls fok stamp c st c' := by
  intro h
  induction h with
  | nil => exact .nil
  | snoc c1 c2 st i l _ hs hf hl ih =>
    exact .snoc c1 c2 st i l ih (wpPfStepPinSub img pstep pcls i l c1 c2 hs) hf hl

/-- The run's authors ARE its log's. -/
theorem pfRunSAuthors (c c' : Wpcfg P D) (st : List (Nat × Wlabel)) :
    pfRunS pstep pcls fok c st c' →
    c'.pcLog.map Wmsg.wmTid = c.pcLog.map Wmsg.wmTid ++ (stAuthors st).map some := by
  intro h
  induction h with
  | nil => simp [stAuthors]
  | snoc c1 c2 st i l _ hs _ ih =>
    rw [wpPfStepAuthors pstep pcls i l c1 c2 hs, ih, stAuthorsSnoc]
    cases lbWrites l <;> simp

/-! ## (7) THE SHAPED REPLAY, SHADOW THREADED -/

/-- THE SHAPED REPLAY WITH THE SHADOW THREADED (the snoc of `execPrefixPfRunProgShaped`
re-proved).  Under `execProgOk'ST`, every prefix of an `execWf` execution is the projection of a
labelled pf run whose step list is `pairAdjacent`, whose every step carries `pfStepFactsT` at its
prefix, and whose step-list shadow (authors included) IS the trace shadow of the prefix — the
projection lemma. -/
theorem execPrefixPfRunProgShapedT (pst : Nat → List P) (dv : Nat → D) (E : Exec) (n : Nat) :
    pclsEqr pcls → pstepPinned (exImg E) pstep →
    execWf E → execProgOk'ST pstep pcls fok stamp pst dv E →
    n ≤ E.exTr.length →
    ∃ (c : Wpcfg P D) (st : List (Nat × Wlabel)),
      pfRunST pstep pcls fok stamp (wpInit (exImg E) (dv 0) (pst 0)) st c ∧
      pairAdjacent st ∧
      c.pcAgs.map Wpagent.paSt = pst n ∧ c.pcDev = dv n ∧
      cfgMatchd c (stt E n) ∧
      ∀ i, tsoRun stamp i st = shadowRun stamp i (E.exTr.take n) := by
  intro hce hpin hE hprT
  obtain ⟨hpr, hscaT, hlat⟩ := hprT
  induction n with
  | zero =>
    intro _
    refine ⟨wpInit (exImg E) (dv 0) (pst 0), [], pfRunST.nil, pairAdjacentNil,
      by simp [wpInit, List.map_map, Function.comp_def], rfl, ⟨rfl, execLogInit E hE, ?_⟩,
      fun i => by simp [tsoRun, shadowRun]⟩
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
    obtain ⟨c, st, hrun, hadj, hst, hdev, hm, hsh⟩ := ih (by omega)
    obtain ⟨s, hs⟩ := someOfIsSome (execTrLookup E n (by omega))
    have hms := execStepAt E n s hE hs
    have htake : E.exTr.take (n + 1) = E.exTr.take n ++ [s] := by
      rw [List.take_add_one, hs]; rfl
    obtain ⟨hsca, p, pa, da, p', ls, hp, hnext, hstar, hfetch, hsup⟩ := hpr n s hs
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
    have hadmL : ∀ y, y ∈ ls.map (fun l => (s.esAg, l)) → lbAdmin true y.2 := by
      intro y hy
      obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hy
      exact admRunGAdmin pstep true _ _ _ _ _ hstar l hl
    have hadm0 : pairAdjacent (ls.map (fun l => (s.esAg, l))) :=
      pairAdjacentFused _ (fun x hx => by
        obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hx
        have := admRunGAdmin pstep true _ _ _ _ _ hstar l hl
        cases l <;> simp_all [lbAdmin, lbFused])
    have hrunA := pfRunSTApp pstep pcls fok stamp _ _ _ _ _ hrun hrun0
      (fun y hy => lbAdminNotLoad true y.2 (hadmL y hy))
    have hshA : ∀ i, tsoRun stamp i (st ++ ls.map (fun l => (s.esAg, l)))
        = shadowRun stamp i (E.exTr.take n) := by
      intro i
      rw [tsoRunApp, foldlAdmin stamp i true _ _ hadmL]
      exact hsh i
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
      have hlf : pfLoadFactsT stamp (st ++ ls.map (fun l => (s.esAg, l))) c0 s.esAg l := by
        cases l with
        | LLoad aq lat base tvs asrc =>
          have hpr' := hre.2.2.2
          simp only [projLbl, Option.some.injEq] at hpr'
          show scaOkT (tsoShadow stamp _ s.esAg) c0.pcImg c0.pcLog s.esAg base (tvs.map Prod.fst) ∧
            diskLatOk c0.pcImg c0.pcLog s.esAg base (tvs.map Prod.fst)
          rw [← hm0.1, ← hm0.2.1, tsoShadow, hshA]
          exact ⟨hscaT n s hs aq base _ _ hpr'.symm, hlat n s hs aq base _ _ hpr'.symm⟩
        | _ => trivial
      refine ⟨c2, (st ++ ls.map (fun l => (s.esAg, l))) ++ [(s.esAg, l)],
        pfRunST.snoc _ _ _ _ _ hrunA hstep hfacts hlf, ?_, ?_, hdev2, hm2, ?_⟩
      · exact pairAdjacentApp _ _ (pairAdjacentApp _ _ hadj hadm0)
          (pairAdjacentFused _ (fun x hx => by
            simp only [List.mem_singleton] at hx; subst hx; exact hfu))
      · rw [hst2, hfm0, hst, list_insert_insert, ← hnext]
      · intro i
        rw [tsoRunSnoc, hshA i, htake, shadowRunSnoc]
        exact shActFused stamp i _ s.esAg l _ s.esLb hfu hre.2.2.2
    · obtain ⟨c2, hstep, hadjP, hm2, hst2, hdev2⟩ :=
        mstepWpPfStepPairS pstep pcls fok (stt E n) (stt E (n + 1)) s.esAg s.esLb c0 ag0 pa pm pm2
          p' l1 l2 ls2 dm dm2 (dv (n + 1)) hce (by rw [heq0.1]; exact hpc) hm0 hlk0 hs0 hre
          (by rw [hd0]; exact hps1) hstar2 hps2 hms
      have hadm2 : ∀ y, y ∈ ls2.map (fun l => (s.esAg, l)) → lbAdmin false y.2 := by
        intro y hy
        obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hy
        exact admRunGAdmin pstep false _ _ _ _ _ hstar2 l hl
      obtain ⟨aq, rl, base, tvs, data, a1, a2, v2, rfl, rfl, _, _, hlb⟩ := hre
      have hnl : ∀ y, y ∈ ((s.esAg, Wlabel.LExLoad aq base tvs a1) ::
          (ls2.map (fun l => (s.esAg, l)) ++ [(s.esAg, Wlabel.LExStore rl base data a2 v2)])) →
          lbIsLoad y.2 = false := by
        intro y hy
        simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | hy | rfl
        · rfl
        · exact lbAdminNotLoad false y.2 (hadm2 y hy)
        · rfl
      refine ⟨c2, _, pfRunSTApp pstep pcls fok stamp _ _ _ _ _ hrunA hstep hnl,
        pairAdjacentApp _ _ (pairAdjacentApp _ _ hadj hadm0) hadjP, ?_, hdev2, hm2, ?_⟩
      · rw [hst2, hfm0, hst, list_insert_insert, ← hnext]
      · intro i
        rw [tsoRunApp, hshA i, htake, shadowRunSnoc]
        exact shRunPair stamp i _ s aq rl base tvs data a1 a2 v2 _ _ false hadm2 hlb

/-- The whole trace. -/
theorem execWfPfRunProgShapedT (pst : Nat → List P) (dv : Nat → D) (E : Exec) :
    pclsEqr pcls → pstepPinned (exImg E) pstep →
    execWf E → execProgOk'ST pstep pcls fok stamp pst dv E →
    ∃ (c : Wpcfg P D) (st : List (Nat × Wlabel)),
      pfRunST pstep pcls fok stamp (wpInit (exImg E) (dv 0) (pst 0)) st c ∧
      pairAdjacent st ∧
      c.pcAgs.map Wpagent.paSt = pst E.exTr.length ∧ c.pcDev = dv E.exTr.length ∧
      cfgMatchd c (stt E E.exTr.length) ∧
      ∀ i, tsoShadow stamp st i = shadowOf stamp E.exTr i := by
  intro hce hpin hE hpr
  obtain ⟨c, st, h1, h2, h3, h4, h5, h6⟩ :=
    execPrefixPfRunProgShapedT pstep pcls fok stamp pst dv E E.exTr.length hce hpin hE hpr
      (Nat.le_refl _)
  refine ⟨c, st, h1, h2, h3, h4, h5, fun i => ?_⟩
  simp only [tsoShadow, shadowOf, h6 i, List.take_length]

/-- The replay of a PINNED shaped supply with the shadow clauses, projected to the unpinned LTS
(the M1 form). -/
theorem execWfPfRunPinShapedT (img : Image) (pst : Nat → List P) (dv : Nat → D) (E : Exec) :
    pclsEqr pcls → exImg E = img →
    execWf E → execProgOk'ST (pstepPin img pstep) pcls fok stamp pst dv E →
    ∃ (c : Wpcfg P D) (st : List (Nat × Wlabel)),
      pfRunST pstep pcls fok stamp (wpInit (exImg E) (dv 0) (pst 0)) st c ∧
      pairAdjacent st ∧
      c.pcAgs.map Wpagent.paSt = pst E.exTr.length ∧ c.pcDev = dv E.exTr.length ∧
      cfgMatchd c (stt E E.exTr.length) ∧
      ∀ i, tsoShadow stamp st i = shadowOf stamp E.exTr i := by
  intro hce himg hE hpr
  subst himg
  obtain ⟨c, st, h1, h2, h3, h4, h5, h6⟩ :=
    execWfPfRunProgShapedT (pstepPin (exImg E) pstep) pcls fok stamp pst dv E hce
      (pstepPinPinned _ _) hE hpr
  exact ⟨c, st, pfRunSTPinSub pstep pcls fok stamp _ _ _ _ h1, h2, h3, h4, h5, h6⟩

end shapeT

/-! ## (8) Spot checks: the spike's G1 / G2 runs against the shadow -/

namespace TsoShadow

/-- G1, the shadow side: after B's store and A's `.aq` exclusive pair, A's floor is the pair's
write position 2 (TsoMem's `top + 1`, `TsoOfPf.tsoAqPairTv`), under EVERY stamp. -/
theorem g1Tv (stamp : CohStamp) : (tsoShadow stamp (TsoOfPf.g1St.take 3) 0).tv = 2 := rfl

/-- G1's final load (byte 0 from the IMAGE) is single-copy atomic at view 0 ... -/
theorem g1Sca : scaOk TsoOfPf.img0 TsoOfPf.g1Log 0 0 [0] := by
  refine ⟨0, by decide, fun j t h => ?_⟩
  rcases j with _ | j <;> simp at h
  subst h
  refine ⟨by decide, Or.inl (Nat.le_refl _), TsoOfPf.later _ _ _ _ _ _ ?_⟩
  intro tq h1 h2 hs hv
  simp only [TsoOfPf.g1Log, List.length_cons, List.length_nil] at h2
  rcases (show tq = 1 ∨ tq = 2 by omega) with rfl | rfl
  · simp_all [scaVis, TsoOfPf.g1Log, TsoOfPf.mx]
  · simp_all [logByte, msgByte, accAddr, TsoOfPf.g1Log, TsoOfPf.mx, TsoOfPf.my]

/-- ... but NOT at or above the shadow's floor: `candScaT` excludes the G1 run (G1-Q (e)). -/
theorem g1NotScaT (stamp : CohStamp) :
    ¬ scaOkT (tsoShadow stamp (TsoOfPf.g1St.take 3) 0) TsoOfPf.img0 TsoOfPf.g1Log 0 0 [0] := by
  rintro ⟨tvn, _, hF, hb⟩
  have h2 : 2 ≤ tvn := by
    have := (shFloorGe (tsoShadow stamp (TsoOfPf.g1St.take 3) 0) 0 [0].length).1
    rw [g1Tv] at this; omega
  obtain ⟨_, _, hlater⟩ := hb 0 0 rfl
  exact hlater 1 (by omega) (by decide) (Or.inl (by omega))

/-- G2 under (a′): the first load stamps only its FOREIGN byte `a` (with 2); the second load's
footprint `(b, c)` keeps floor 0. -/
theorem g2FloorSrc : shFloor (tsoShadow cohSrc (TsoOfPf.g2St.take 3) 0) 1 2 = 0 := by decide

/-- G2 under today's footprint stamp: byte `b` is stamped with the first load's view 2. -/
theorem g2FloorFoot : shFloor (tsoShadow cohFoot (TsoOfPf.g2St.take 3) 0) 1 2 = 2 := by decide

/-- G2's second load reading `(b, c) = (0, 0)` is `scaOkT` under (a′) ... -/
theorem g2ScaTSrc :
    scaOkT (tsoShadow cohSrc (TsoOfPf.g2St.take 3) 0) TsoOfPf.img0 TsoOfPf.g2Log 0 1 [0, 0] := by
  refine ⟨0, by decide, by show shFloor _ 1 2 ≤ 0; rw [g2FloorSrc]; exact Nat.le_refl 0,
    fun j t h => ?_⟩
  rcases j with _ | _ | j <;> simp at h <;> subst h
  all_goals refine ⟨by decide, Or.inl (Nat.le_refl _), TsoOfPf.later _ _ _ _ _ _ ?_⟩
  all_goals intro tq h1 h2 hs hv
  all_goals simp only [TsoOfPf.g2Log, List.length_cons, List.length_nil] at h2
  all_goals rcases (show tq = 1 ∨ tq = 2 by omega) with rfl | rfl
  all_goals simp_all [scaVis, logByte, msgByte, accAddr, TsoOfPf.g2Log, TsoOfPf.mc, TsoOfPf.ma]

/-- ... and NOT under today's footprint stamp (the spike's `g2Tso`, as a shadow fact). -/
theorem g2NotScaTFoot :
    ¬ scaOkT (tsoShadow cohFoot (TsoOfPf.g2St.take 3) 0) TsoOfPf.img0 TsoOfPf.g2Log 0 1 [0, 0] := by
  rintro ⟨tvn, _, hF, hb⟩
  change shFloor _ 1 2 ≤ tvn at hF
  rw [g2FloorFoot] at hF
  obtain ⟨_, _, hlater⟩ := hb 1 0 rfl
  exact hlater 1 (by omega) (by decide) (Or.inl (by omega))

end TsoShadow

end Weak
