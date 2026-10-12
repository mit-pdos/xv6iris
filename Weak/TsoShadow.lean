/-
Weak: **the TsoMem view SHADOW over a pf step list** (allocproc plan W5b′, §B(10) "The redesign",
§C Stage 0 "W5b′"; reviews [R10.3], [R11.1], [R11.3]).

Lean-only (no Rocq source).  TsoMem's per-hart READ SIDE (`tv`, `rv`, `coh`, `acq`, and the
instruction view `itv`; `MachCSL/Lang.lean:127-163`, `MachCSL/TsoMem.lean:253-277`) is REPLAYED deterministically over a
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
  (`wmTid`, position + 1), `some (0, 0)` for an image byte (`TsoOfPf.histOf`'s image entry, author
  0 at timestamp 0) — the same input W-COH's `FlatMem.loadSrcs`/`Hist.readSrc` builds.
* **`itv` on the STEP LIST only** (plan §C W5b′, §B(4)(iii)(ii), §B(10) `R-view`): the step-list
  shadow `tsoShadow` is `ShFull` = the memory fields `ShSt` + `itv` (+ `fiArm`, the bookkeeping
  bit of `emFenceI`'s criterion).  `itv` moves only at an own `LFence false×4` whose latest own
  `LInstr`/`LIFetch` step is `LInstr` (fence.i: boundary `LInstr`, fetch, announce `LInstr`,
  barrier; the `sfence.vma` marker: boundary `LInstr`, fetch, marker — `notes/W5dG-spike.md`
  `emFenceI`): `itv := max itv (fencePost true false tv rv ownPub)`, MachCSL's `fence.i` arm
  (`Lang.lean:155-163`).  The TRACE shadow `shadowOf` stays MEMORY-ONLY ([R11.3]: the two
  `LFence false×4` are indistinguishable in `E.exTr`; W5d's `itvOf` carries `itv` there).
  Neither `LFence false×4` moves a memory field (`TsoShadow.ShSt.fenceNoSucc`).
* `scaOkT`/`execScaT`/`candScaT` (G1-Q RULED (e) [OWN.17]): `scaOk` plus `F ≤ tvn` at the shadow
  of the trace prefix (`shadowOf (E.exTr.take k)`, computed from `E.exTr`: `LRmw aq`, the
  `LFence` bits, `LStore` for the store effect, the log authors for foreign-ness and `ownPub`).
* `diskLatOk`/`execDiskLat`/`candDiskLat` (G3-Q RULED (a″) [OWN.17]): every load of agent `NCPU`
  (the disk row, `epsInit`) reads the `latest` write per byte — a SHAPE clause, no label change.
* `execProgOk'ST` = `execProgOk'S` ∧ clause (iii)′ `execScaT` ∧ clause (iv) `execDiskLat`;
  `pfStepFactsT` / `pfRunST`: the labelled run whose every step carries, besides `pfStepFacts`,
  `scaOkT` at the shadow of the step-list PREFIX before it and `diskLatOk`.
* **The re-proved replay** `execPrefixPfRunProgShapedT` (the snoc of `execPrefixPfRunProgShaped`
  with the shadow threaded): it also returns the PROJECTION LEMMA `memOf (tsoRun st) = shadowRun
  (E.exTr.take n)` — the step-list shadow's MEMORY component (admin steps inert, an exclusive pair
  block = the fused `LRmw`) equals the trace shadow, authors included.  Whole-trace and pinned
  (M1) forms.
* Spot checks (the redesign's two gaps, now as shadow facts): `TsoShadow.g1NotScaT` (G1: after
  the `.aq` pair the prefix shadow's floor is the pair's write position 2, so the spike's stale
  load is `scaOk` but NOT `scaOkT` at that prefix, under every stamp) and the run-level
  `TsoShadow.g1NoRunT` (no `pfRunST` follows `g1St`); `TsoShadow.g2ScaTSrc` /
  `TsoShadow.g2NotScaTFoot` (G2: the spike's mixed-size pair is `scaOkT` under (a′) and NOT under
  today's footprint stamp) and the run-level `TsoShadow.g2RunT` (a `pfRunST` under (a′) follows
  `g2St`, both loads `scaOkT`); `TsoShadow.itvFenceI` / `TsoShadow.itvSfence` (`itv` rises at
  `fence.i`, not at the `sfence.vma` marker).

Deviations from the plan's text: (1) the shadow is indexed by the AGENT `Nat` (a `CPU` is
`hartAgent c`; the disk row's shadow exists and is unused); (2) `Weak/PfRunShape.lean` is NOT
edited — the strengthened clauses are new names (`execProgOk'ST`, `pfRunST`, …) beside the
landed ones, with forgetful maps back, so W5c and every importer stay untouched (W5 re-points
`srvwmoXv6M1Premises`); (3) `scaOkT` is required of EVERY plain load (the disk row's included —
there it follows from `latest`), as clause (iii) is; (4) (W5d [R29.1][R30.1], the M2 cut clause's
carriers) the shadow-threaded run is `pfRunSTC … fcutT`, whose `snoc` carries a THIRD fact
`pfCutFactsT fcutT` (the clause at the prefix shadow's `itv`), and the shaped predicate is
`execProgOk'STC … fcutE` (the per-index clause of `execProgOk'SC`, `Weak/PfRunShape.lean`); the plan's
names `pfRunST`/`execProgOk'ST` are their M1 instances at `fcutTTriv`/`fcutETriv` (reducible
abbreviations; `pfRunST.nil`/`pfRunST.snoc` keep the constructor shape), so M1's statements read
as before.  `pfRunSTForgetCut` forgets the clause; `pfRunSTFactsC` unpacks all three facts.
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
`some (0, 0)` for the image (timestamp 0: `TsoOfPf.histOf`'s image entry has author 0, as W-COH's
`Hist.readSrc` reads it). -/
def shSrc (au : List Nat) (t : Nat) : Option (Nat × Nat) :=
  if t = 0 then some (0, 0) else (au[t - 1]?).map (fun a => (a, t))

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

/-- One step of the MEMORY fold: the authors grow by a writing step's agent; the viewer's read
side moves on its own steps only. -/
def shAct (stamp : CohStamp) (i : Nat) (x : List Nat × ShSt) (y : Nat × Wlabel) : List Nat × ShSt :=
  (if lbWrites y.2 then x.1 ++ [y.1] else x.1, if y.1 = i then shStep stamp i x.1 x.2 y.2 else x.2)

/-- The memory-field fold over a step list, from the empty log and the boot read side. -/
def tsoRunM (stamp : CohStamp) (i : Nat) (st : List (Nat × Wlabel)) : List Nat × ShSt :=
  st.foldl (shAct stamp i) ([], ShSt.zero)

/-- THE STEP-LIST SHADOW's state: the memory fields, the instruction view `itv`, and `fiArm`
(`emFenceI`'s criterion: the latest own `LInstr`/`LIFetch` step was `LInstr`). -/
structure ShFull where
  mem : ShSt
  itv : Nat
  fiArm : Bool

/-- Boot: TsoMem's `itv = 0`. -/
def ShFull.zero : ShFull := ⟨ShSt.zero, 0, false⟩

/-- The all-false fence label (`fence.i`'s and the `sfence.vma` marker's). -/
def lbFenceZero (l : Wlabel) : Bool :=
  match l with
  | .LFence false false false false => true
  | _ => false

/-- The viewer's own step on the full shadow: the memory step; `itv` raised at a `fence.i`
(`lbFenceZero` with `fiArm`) to `max itv (fencePost true false tv rv ownPub)` at the PRE-step
`tv`/`rv` (MachCSL's `fence.i` arm, `Lang.lean:155-163`); `fiArm` set by `LInstr`, cleared by
`LIFetch`. -/
def shStepF (stamp : CohStamp) (i : Nat) (au : List Nat) (f : ShFull) (l : Wlabel) : ShFull :=
  ⟨shStep stamp i au f.mem l,
   if lbFenceZero l && f.fiArm then
     max f.itv (MachCSL.fencePost true false f.mem.tv f.mem.rv (MachCSL.ownPub i au))
   else f.itv,
   match l with
   | .LInstr => true
   | .LIFetch .. => false
   | _ => f.fiArm⟩

/-- One step of the full fold. -/
def shActF (stamp : CohStamp) (i : Nat) (x : List Nat × ShFull) (y : Nat × Wlabel) :
    List Nat × ShFull :=
  (if lbWrites y.2 then x.1 ++ [y.1] else x.1, if y.1 = i then shStepF stamp i x.1 x.2 y.2 else x.2)

/-- The step-list shadow fold (authors, full shadow). -/
def tsoRun (stamp : CohStamp) (i : Nat) (st : List (Nat × Wlabel)) : List Nat × ShFull :=
  st.foldl (shActF stamp i) ([], ShFull.zero)

/-- The memory component of a full fold state. -/
def memOf (x : List Nat × ShFull) : List Nat × ShSt := (x.1, x.2.mem)

theorem memOfShActF (stamp : CohStamp) (i : Nat) (x : List Nat × ShFull) (y : Nat × Wlabel) :
    memOf (shActF stamp i x y) = shAct stamp i (memOf x) y := by
  obtain ⟨au, f⟩ := x
  obtain ⟨j, l⟩ := y
  by_cases hj : j = i <;> simp [memOf, shActF, shAct, shStepF, hj]

theorem memOfFoldl (stamp : CohStamp) (i : Nat) :
    ∀ (st : List (Nat × Wlabel)) (x : List Nat × ShFull),
      memOf (st.foldl (shActF stamp i) x) = st.foldl (shAct stamp i) (memOf x)
  | [], _ => rfl
  | y :: st, x => by
    rw [List.foldl_cons, List.foldl_cons, memOfFoldl stamp i st, memOfShActF]

/-- The full fold's memory component IS the memory fold. -/
theorem tsoRunMem (stamp : CohStamp) (i : Nat) (st : List (Nat × Wlabel)) :
    memOf (tsoRun stamp i st) = tsoRunM stamp i st :=
  memOfFoldl stamp i st _

/-- The authors of a step list's writes, in order. -/
def stAuthors (st : List (Nat × Wlabel)) : List Nat :=
  st.filterMap (fun y => if lbWrites y.2 then some y.1 else none)

/-! ## (4) The trace shadow (computable from `E.exTr`) -/

-- the wildcard arm is unused today; W13 (E)'s `Lbl.LIo` joins through it without a rebase
set_option match.ignoreUnusedAlts true in
/-- The trace twin of `shStep` over the axiomatic alphabet (an `LRmw` = exclusive read then
exclusive write; any other label moves nothing). -/
def shStepL (stamp : CohStamp) (i : Nat) (au : List Nat) (sh : ShSt) (lb : Lbl) : ShSt :=
  match lb with
  | .LLoad _ base ts _ => sh.load stamp i base (ts.map (shSrc au))
  | .LStore _ base vs _ => sh.store stamp au.length false base vs.length
  | .LFence pr pw sr sw => sh.fence (MachCSL.ownPub i au) pr pw sr sw
  | .LRmw aq _ base _ _ wvs _ => (sh.excl au.length aq).store stamp au.length true base wvs.length
  | _ => sh

def shActL (stamp : CohStamp) (i : Nat) (x : List Nat × ShSt) (s : Estep) : List Nat × ShSt :=
  (if lbIsW s.esLb then x.1 ++ [s.esAg] else x.1,
   if s.esAg = i then shStepL stamp i x.1 x.2 s.esLb else x.2)

def shadowRun (stamp : CohStamp) (i : Nat) (tr : List Estep) : List Nat × ShSt :=
  tr.foldl (shActL stamp i) ([], ShSt.zero)

def stAuthorsL (tr : List Estep) : List Nat :=
  tr.filterMap (fun s => if lbIsW s.esLb then some s.esAg else none)

/-! ## (5) The fold laws: admin steps inert, fused steps = their projection, a pair block = the
fused `LRmw` -/

theorem tsoRunMSnoc (stamp : CohStamp) (i : Nat) (st : List (Nat × Wlabel)) (y : Nat × Wlabel) :
    tsoRunM stamp i (st ++ [y]) = shAct stamp i (tsoRunM stamp i st) y := by
  simp [tsoRunM, List.foldl_append]

theorem tsoRunMApp (stamp : CohStamp) (i : Nat) (st b : List (Nat × Wlabel)) :
    tsoRunM stamp i (st ++ b) = b.foldl (shAct stamp i) (tsoRunM stamp i st) := by
  simp [tsoRunM, List.foldl_append]

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

theorem tsoRunMAuthors (stamp : CohStamp) (i : Nat) (st : List (Nat × Wlabel)) :
    (tsoRunM stamp i st).1 = stAuthors st := by
  simp [tsoRunM, foldlAuthors]

theorem tsoRunAuthors (stamp : CohStamp) (i : Nat) (st : List (Nat × Wlabel)) :
    (tsoRun stamp i st).1 = stAuthors st := by
  rw [← tsoRunMAuthors stamp i st, ← tsoRunMem]; rfl

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

/-- THE TsoMem VIEW SHADOW of agent `i` after the step list `st`: `(tv, rv, coh, acq)` in
`.mem`, and `.itv`; PARAMETRIC in the `coh` stamp pair. -/
def tsoShadow (stamp : CohStamp) (st : List (Nat × Wlabel)) (i : Nat) : ShFull :=
  (tsoRun stamp i st).2

theorem tsoShadowMem (stamp : CohStamp) (st : List (Nat × Wlabel)) (i : Nat) :
    (tsoShadow stamp st i).mem = (tsoRunM stamp i st).2 := by
  rw [← tsoRunMem]; rfl

/-- The trace shadow of agent `i` after the trace prefix `tr` (MEMORY fields only [R11.3]). -/
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

/-- THE M2 CUT CLAUSE'S CARRIER (W5d [R29.1]): at a fetch `l = .LIFetch base tvs`, the clause
`fcutT` at the step-list shadow's `itv` (the prefix `st` before the step), the pre-configuration's
image and log, the agent, and the fetch (M1: `fcutTTriv`; M2: the cut form). -/
def pfCutFactsT {P D : Type}
    (fcutT : Nat → Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop)
    (stamp : CohStamp) (st : List (Nat × Wlabel)) (c : Wpcfg P D) (i : Nat) (l : Wlabel) : Prop :=
  ∀ (base : Int) (tvs : List (Nat × BitVec 8)), l = .LIFetch base tvs →
    fcutT (tsoShadow stamp st i).itv c.pcImg c.pcLog i base tvs

/-- The trivial cut clause (M1's instance of `pfRunSTC`'s `fcutT`). -/
abbrev fcutTTriv : Nat → Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop :=
  fun _ _ _ _ _ _ => True

theorem pfCutFactsTTriv {P D : Type} (stamp : CohStamp) (st : List (Nat × Wlabel))
    (c : Wpcfg P D) (i : Nat) (l : Wlabel) : pfCutFactsT fcutTTriv stamp st c i l :=
  fun _ _ _ => trivial

section shapeT

variable {P D : Type}
variable (pstep : P → D → Wlabel → P → D → Prop)
variable (pcls : P → Wlabel → Wstate → WmClass)
variable (fok : Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop)
variable (stamp : CohStamp)

/-- THE SHAPED CONFORMANCE PREDICATE with the shadow clauses, at a per-index clause `fcutE`
(W5d [R30.1]): `execProgOk'SC` ∧ (iii)′ ∧ (iv). -/
def execProgOk'STC (fcutE : Nat → Nat → List Wlabel → Mstate → Prop) (pst : Nat → List P)
    (dv : Nat → D) (E : Exec) : Prop :=
  execProgOk'SC pstep pcls fok fcutE pst dv E ∧ execScaT stamp E ∧ execDiskLat E

/-- THE SHAPED CONFORMANCE PREDICATE with the shadow clauses (M1): `execProgOk'STC` at the trivial
per-index clause, i.e. `execProgOk'S` ∧ (iii)′ ∧ (iv). -/
abbrev execProgOk'ST (pst : Nat → List P) (dv : Nat → D) (E : Exec) : Prop :=
  execProgOk'STC pstep pcls fok stamp fcutETriv pst dv E

theorem execProgOk'STCForget (fcutE : Nat → Nat → List Wlabel → Mstate → Prop)
    (pst : Nat → List P) (dv : Nat → D) (E : Exec) :
    execProgOk'STC pstep pcls fok stamp fcutE pst dv E → execProgOk'ST pstep pcls fok stamp pst dv E :=
  fun h => ⟨execProgOk'SCForget pstep pcls fok fcutE pst dv E h.1, h.2⟩

theorem execProgOk'STForget (pst : Nat → List P) (dv : Nat → D) (E : Exec) :
    execProgOk'ST pstep pcls fok stamp pst dv E → execProgOk'S pstep pcls fok pst dv E :=
  fun h => h.1

/-- The load facts a step carries, read at the step-list PREFIX `st` before it (the shadow) and
the pre-configuration `c` (image, log). -/
def pfLoadFactsT (st : List (Nat × Wlabel)) (c : Wpcfg P D) (i : Nat) (l : Wlabel) : Prop :=
  match l with
  | .LLoad _ _ base tvs _ =>
    scaOkT (tsoShadow stamp st i).mem c.pcImg c.pcLog i base (tvs.map Prod.fst) ∧
    diskLatOk c.pcImg c.pcLog i base (tvs.map Prod.fst)
  | _ => True

/-- `pfStepFacts` extended by the shadow-threaded load facts. -/
def pfStepFactsT (st : List (Nat × Wlabel)) (c : Wpcfg P D) (i : Nat) (l : Wlabel) : Prop :=
  pfStepFacts fok c i l ∧ pfLoadFactsT stamp st c i l

theorem pfLoadFactsTNonload (st : List (Nat × Wlabel)) (c : Wpcfg P D) (i : Nat) (l : Wlabel)
    (h : lbIsLoad l = false) : pfLoadFactsT stamp st c i l := by
  cases l <;> simp_all [lbIsLoad, pfLoadFactsT]

/-- A labelled promise-free run whose every step carries `pfStepFactsT` at its prefix and the
cut clause `pfCutFactsT fcutT` (W5d [R29.1]: the THIRD fact; M1: `fcutTTriv`, so `pfRunST`). -/
inductive pfRunSTC (fcutT : Nat → Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop)
    (c : Wpcfg P D) : List (Nat × Wlabel) → Wpcfg P D → Prop where
  | nil : pfRunSTC fcutT c [] c
  | snoc (c1 c2 : Wpcfg P D) (st : List (Nat × Wlabel)) (i : Nat) (l : Wlabel) :
      pfRunSTC fcutT c st c1 → wpPfStep pstep pcls i l c1 c2 → pfStepFacts fok c1 i l →
      pfLoadFactsT stamp st c1 i l → pfCutFactsT fcutT stamp st c1 i l →
      pfRunSTC fcutT c (st ++ [(i, l)]) c2

/-- THE SHADOW-THREADED RUN (M1): `pfRunSTC` at the trivial cut clause. -/
abbrev pfRunST (c : Wpcfg P D) (st : List (Nat × Wlabel)) (c' : Wpcfg P D) : Prop :=
  pfRunSTC pstep pcls fok stamp fcutTTriv c st c'

variable {pstep pcls fok stamp} in
/-- `pfRunSTC.nil` at `pfRunST` (constructor-shaped: the parameters implicit). -/
theorem pfRunST.nil {c : Wpcfg P D} : pfRunST pstep pcls fok stamp c [] c := pfRunSTC.nil

variable {pstep pcls fok stamp} in
/-- `pfRunSTC.snoc` at `pfRunST`: the cut clause is `trivial`. -/
theorem pfRunST.snoc {c : Wpcfg P D} (c1 c2 : Wpcfg P D) (st : List (Nat × Wlabel)) (i : Nat)
    (l : Wlabel) (h : pfRunST pstep pcls fok stamp c st c1) (hs : wpPfStep pstep pcls i l c1 c2)
    (hf : pfStepFacts fok c1 i l) (hl : pfLoadFactsT stamp st c1 i l) :
    pfRunST pstep pcls fok stamp c (st ++ [(i, l)]) c2 :=
  pfRunSTC.snoc c1 c2 st i l h hs hf hl (pfCutFactsTTriv stamp st c1 i l)

theorem pfRunSTForget {fcutT : Nat → Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop}
    (c c' : Wpcfg P D) (st : List (Nat × Wlabel)) :
    pfRunSTC pstep pcls fok stamp fcutT c st c' → pfRunS pstep pcls fok c st c' := by
  intro h
  induction h with
  | nil => exact .nil
  | snoc c1 c2 st i l _ hs hf _ _ ih => exact .snoc c1 c2 st i l ih hs hf

/-- Any cut clause forgets to the trivial one (`sailCycleOrder` and `Hyps.cut`/`Hyps.fi` are
stated at `pfRunST` [R30.s3]). -/
theorem pfRunSTForgetCut
    {fcutT : Nat → Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop}
    (c c' : Wpcfg P D) (st : List (Nat × Wlabel)) :
    pfRunSTC pstep pcls fok stamp fcutT c st c' → pfRunST pstep pcls fok stamp c st c' := by
  intro h
  induction h with
  | nil => exact pfRunSTC.nil
  | snoc c1 c2 st i l _ hs hf hl _ ih =>
    exact pfRunSTC.snoc c1 c2 st i l ih hs hf hl (pfCutFactsTTriv stamp st c1 i l)

/-- Every step carries `pfStepFactsT` AND its cut clause at its prefix (the inductive's content,
unpacked [R30.s2]). -/
theorem pfRunSTFactsC
    {fcutT : Nat → Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop}
    (c c' : Wpcfg P D) (st : List (Nat × Wlabel)) :
    pfRunSTC pstep pcls fok stamp fcutT c st c' →
    ∀ (st0 : List (Nat × Wlabel)) (i : Nat) (l : Wlabel) (rest : List (Nat × Wlabel)),
      st = st0 ++ (i, l) :: rest →
      ∃ c1 c2, pfRunSTC pstep pcls fok stamp fcutT c st0 c1 ∧ wpPfStep pstep pcls i l c1 c2 ∧
        pfStepFactsT fok stamp st0 c1 i l ∧ pfCutFactsT fcutT stamp st0 c1 i l := by
  intro h
  induction h with
  | nil => intro st0 i l rest he; simp at he
  | snoc c1 c2 st j l' hr hs hf hl hc ih =>
    intro st0 i l rest he
    by_cases hr0 : rest = []
    · subst hr0
      have h1 := List.append_inj' he rfl
      simp only [List.cons.injEq, Prod.mk.injEq, and_true] at h1
      obtain ⟨rfl, rfl, rfl⟩ := h1
      exact ⟨c1, c2, hr, hs, ⟨hf, hl⟩, hc⟩
    · obtain ⟨rest', y, rfl⟩ := List.eq_nil_or_concat rest |>.resolve_left hr0
      have h1 : st ++ [(j, l')] = (st0 ++ (i, l) :: rest') ++ [y] := by simpa using he
      have h2 := List.append_inj' h1 rfl
      exact ih st0 i l rest' h2.1

/-- Every step carries `pfStepFactsT` at its prefix (`pfRunSTFactsC` without the cut clause). -/
theorem pfRunSTFacts
    {fcutT : Nat → Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop}
    (c c' : Wpcfg P D) (st : List (Nat × Wlabel)) :
    pfRunSTC pstep pcls fok stamp fcutT c st c' →
    ∀ (st0 : List (Nat × Wlabel)) (i : Nat) (l : Wlabel) (rest : List (Nat × Wlabel)),
      st = st0 ++ (i, l) :: rest →
      ∃ c1 c2, pfRunSTC pstep pcls fok stamp fcutT c st0 c1 ∧ wpPfStep pstep pcls i l c1 c2 ∧
        pfStepFactsT fok stamp st0 c1 i l := by
  intro h st0 i l rest he
  obtain ⟨c1, c2, hr, hs, hf, -⟩ := pfRunSTFactsC pstep pcls fok stamp c c' st h st0 i l rest he
  exact ⟨c1, c2, hr, hs, hf⟩

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
    exact pfRunST.snoc _ _ _ _ _
      (ih (fun y hy => hnl y (List.mem_append_left _ hy))) hs hf
      (pfLoadFactsTNonload stamp _ _ _ _ (hnl (i, l) (by simp)))

theorem pfRunSTPinSub {fcutT : Nat → Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop}
    (img : Image) (c c' : Wpcfg P D) (st : List (Nat × Wlabel)) :
    pfRunSTC (pstepPin img pstep) pcls fok stamp fcutT c st c' →
      pfRunSTC pstep pcls fok stamp fcutT c st c' := by
  intro h
  induction h with
  | nil => exact .nil
  | snoc c1 c2 st i l _ hs hf hl hc ih =>
    exact .snoc c1 c2 st i l ih (wpPfStepPinSub img pstep pcls i l c1 c2 hs) hf hl hc

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
prefix, and whose step-list shadow's MEMORY component (authors included) IS the trace shadow of
the prefix — the projection lemma (`itv` is the step list's own; W5d ties it to `itvOf`). -/
theorem execPrefixPfRunProgShapedT (pst : Nat → List P) (dv : Nat → D) (E : Exec) (n : Nat) :
    pclsEqr pcls → pstepPinned (exImg E) pstep →
    execWf E → execProgOk'ST pstep pcls fok stamp pst dv E →
    n ≤ E.exTr.length →
    ∃ (c : Wpcfg P D) (st : List (Nat × Wlabel)),
      pfRunST pstep pcls fok stamp (wpInit (exImg E) (dv 0) (pst 0)) st c ∧
      pairAdjacent st ∧
      c.pcAgs.map Wpagent.paSt = pst n ∧ c.pcDev = dv n ∧
      cfgMatchd c (stt E n) ∧
      ∀ i, memOf (tsoRun stamp i st) = shadowRun stamp i (E.exTr.take n) := by
  intro hce hpin hE hprT
  obtain ⟨hpr, hscaT, hlat⟩ := hprT
  induction n with
  | zero =>
    intro _
    refine ⟨wpInit (exImg E) (dv 0) (pst 0), [], pfRunST.nil, pairAdjacentNil,
      by simp [wpInit, List.map_map, Function.comp_def], rfl, ⟨rfl, execLogInit E hE, ?_⟩,
      fun i => by simp [tsoRun, shadowRun, memOf, ShFull.zero]⟩
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
    obtain ⟨c, st, hrun, hadj, hst, hdev, hm, hsh0⟩ := ih (by omega)
    have hsh : ∀ i, tsoRunM stamp i st = shadowRun stamp i (E.exTr.take n) :=
      fun i => (tsoRunMem stamp i st).symm.trans (hsh0 i)
    obtain ⟨s, hs⟩ := someOfIsSome (execTrLookup E n (by omega))
    have hms := execStepAt E n s hE hs
    have htake : E.exTr.take (n + 1) = E.exTr.take n ++ [s] := by
      rw [List.take_add_one, hs]; rfl
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
    have hshA : ∀ i, tsoRunM stamp i (st ++ ls.map (fun l => (s.esAg, l)))
        = shadowRun stamp i (E.exTr.take n) := by
      intro i
      rw [tsoRunMApp, foldlAdmin stamp i true _ _ hadmL]
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
          show scaOkT (tsoShadow stamp _ s.esAg).mem c0.pcImg c0.pcLog s.esAg base
              (tvs.map Prod.fst) ∧ diskLatOk c0.pcImg c0.pcLog s.esAg base (tvs.map Prod.fst)
          rw [← hm0.1, ← hm0.2.1, tsoShadowMem, hshA]
          exact ⟨hscaT n s hs aq base _ _ hpr'.symm, hlat n s hs aq base _ _ hpr'.symm⟩
        | _ => trivial
      refine ⟨c2, (st ++ ls.map (fun l => (s.esAg, l))) ++ [(s.esAg, l)],
        pfRunST.snoc _ _ _ _ _ hrunA hstep hfacts hlf, ?_, ?_, hdev2, hm2, ?_⟩
      · exact pairAdjacentApp _ _ (pairAdjacentApp _ _ hadj hadm0)
          (pairAdjacentFused _ (fun x hx => by
            simp only [List.mem_singleton] at hx; subst hx; exact hfu))
      · rw [hst2, hfm0, hst, list_insert_insert, ← hnext]
      · intro i
        rw [tsoRunMem, tsoRunMSnoc, hshA i, htake, shadowRunSnoc]
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
        rw [tsoRunMem, tsoRunMApp, hshA i, htake, shadowRunSnoc]
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
      ∀ i, (tsoShadow stamp st i).mem = shadowOf stamp E.exTr i := by
  intro hce hpin hE hpr
  obtain ⟨c, st, h1, h2, h3, h4, h5, h6⟩ :=
    execPrefixPfRunProgShapedT pstep pcls fok stamp pst dv E E.exTr.length hce hpin hE hpr
      (Nat.le_refl _)
  refine ⟨c, st, h1, h2, h3, h4, h5, fun i => ?_⟩
  have := congrArg Prod.snd (h6 i)
  simpa only [tsoShadow, shadowOf, memOf, List.take_length] using this

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
      ∀ i, (tsoShadow stamp st i).mem = shadowOf stamp E.exTr i := by
  intro hce himg hE hpr
  subst himg
  obtain ⟨c, st, h1, h2, h3, h4, h5, h6⟩ :=
    execWfPfRunProgShapedT (pstepPin (exImg E) pstep) pcls fok stamp pst dv E hce
      (pstepPinPinned _ _) hE hpr
  exact ⟨c, st, pfRunSTPinSub pstep pcls fok stamp _ _ _ _ h1, h2, h3, h4, h5, h6⟩

end shapeT

/-! ## (8) Spot checks: the spike's G1 / G2 runs against the shadow; `itv` at `fence.i` -/

namespace TsoShadow

/-- The message a step appends when every class is `k`. -/
def msgOf (k : WmClass) (y : Nat × Wlabel) : Option Wmsg :=
  match y.2 with
  | .LStore _ base data _ _ => some ⟨base, data, some y.1, k⟩
  | .LRmw _ _ base _ data _ _ => some ⟨base, data, some y.1, k⟩
  | .LExStore _ base data _ _ => some ⟨base, data, some y.1, k⟩
  | _ => none

/-- Under a constant class function, a step keeps the image and appends `msgOf`. -/
theorem wpPfStepLogK {P D : Type} (pstep : P → D → Wlabel → P → D → Prop)
    (pcls : P → Wlabel → Wstate → WmClass) (k : WmClass) (hk : ∀ p l w, pcls p l w = k)
    (i : Nat) (l : Wlabel) (c1 c2 : Wpcfg P D) (h : wpPfStep pstep pcls i l c1 c2) :
    c2.pcImg = c1.pcImg ∧ c2.pcLog = c1.pcLog ++ (msgOf k (i, l)).toList := by
  cases h <;> simp_all [msgOf]

theorem pfRunSLogK {P D : Type} (pstep : P → D → Wlabel → P → D → Prop)
    (pcls : P → Wlabel → Wstate → WmClass)
    (fok : Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop) (k : WmClass)
    (hk : ∀ p l w, pcls p l w = k) (c c' : Wpcfg P D) (st : List (Nat × Wlabel)) :
    pfRunS pstep pcls fok c st c' →
    c'.pcImg = c.pcImg ∧ c'.pcLog = c.pcLog ++ st.filterMap (msgOf k) := by
  intro h
  induction h with
  | nil => simp
  | snoc c1 c2 st i l _ hs _ ih =>
    obtain ⟨h1, h2⟩ := wpPfStepLogK pstep pcls k hk i l c1 c2 hs
    refine ⟨h1.trans ih.1, ?_⟩
    rw [h2, ih.2, List.filterMap_append, List.append_assoc]
    cases hm : msgOf k (i, l) <;> simp [hm]

/-- G1, the shadow side: after B's store and A's `.aq` exclusive pair, A's floor is the pair's
write position 2 (TsoMem's `top + 1`, `TsoOfPf.tsoAqPairTv`), under EVERY stamp. -/
theorem g1Tv (stamp : CohStamp) : (tsoShadow stamp (TsoOfPf.g1St.take 3) 0).mem.tv = 2 := rfl

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

/-- ... but NOT `scaOkT` at the shadow of its step-list PREFIX (`g1St.take 3`), under every stamp:
every view at or above that floor (2) sees B's store to byte 0.  The run-level consequence is
`g1NoRunT`. -/
theorem g1NotScaT (stamp : CohStamp) :
    ¬ scaOkT (tsoShadow stamp (TsoOfPf.g1St.take 3) 0).mem TsoOfPf.img0 TsoOfPf.g1Log 0 0 [0] := by
  rintro ⟨tvn, _, hF, hb⟩
  have h2 : 2 ≤ tvn := by
    have := (shFloorGe (tsoShadow stamp (TsoOfPf.g1St.take 3) 0).mem 0 [0].length).1
    rw [g1Tv] at this; omega
  obtain ⟨_, _, hlater⟩ := hb 0 0 rfl
  exact hlater 1 (by omega) (by decide) (Or.inl (by omega))

/-- RUN LEVEL, G1: NO shadow-threaded run follows the spike's G1 step list (whatever the fetch
clause and the stamp) — although a `pfRunS` does (`TsoOfPf.g1Run`). -/
theorem g1NoRunT (fok : Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop)
    (stamp : CohStamp) :
    ¬ ∃ c, pfRunST TsoOfPf.anyStep TsoOfPf.anyCls fok stamp TsoOfPf.cfg0 TsoOfPf.g1St c := by
  rintro ⟨c, h⟩
  obtain ⟨c1, _, hr1, _, _, hl⟩ :=
    pfRunSTFacts _ _ fok stamp _ _ _ h (TsoOfPf.g1St.take 3) 0
      (.LLoad false false 0 [(0, 0#8)] []) [] rfl
  obtain ⟨himg, hlog⟩ := pfRunSLogK _ _ fok .WCplain (fun _ _ _ => rfl) _ _ _
    (pfRunSTForget _ _ fok stamp _ _ _ hr1)
  have himg' : c1.pcImg = TsoOfPf.img0 := himg
  have hlog' : c1.pcLog = TsoOfPf.g1Log := by rw [hlog]; rfl
  have h1 := hl.1
  rw [himg', hlog'] at h1
  exact g1NotScaT stamp h1

/-- G2 under (a′): the first load stamps only its FOREIGN byte `a` (with 2); the second load's
footprint `(b, c)` keeps floor 0. -/
theorem g2FloorSrc : shFloor (tsoShadow cohSrc (TsoOfPf.g2St.take 3) 0).mem 1 2 = 0 := by decide

/-- G2 under today's footprint stamp: byte `b` is stamped with the first load's view 2. -/
theorem g2FloorFoot : shFloor (tsoShadow cohFoot (TsoOfPf.g2St.take 3) 0).mem 1 2 = 2 := by decide

/-- G2's first load reading `(a, b) = (1, 0)` is `scaOkT` at view 2 (its prefix shadow is
untouched: only B ran), under (a′) ... -/
theorem g2Ld1ScaTSrc :
    scaOkT (tsoShadow cohSrc (TsoOfPf.g2St.take 2) 0).mem TsoOfPf.img0 TsoOfPf.g2Log 0 0 [2, 0] := by
  refine ⟨2, by decide, by show shFloor _ 0 2 ≤ 2; decide, fun j t h => ?_⟩
  rcases j with _ | _ | j <;> simp at h <;> subst h
  all_goals refine ⟨by decide, Or.inl (by decide), TsoOfPf.later _ _ _ _ _ _ ?_⟩
  all_goals intro tq h1 h2 hs hv
  all_goals simp only [TsoOfPf.g2Log, List.length_cons, List.length_nil] at h2
  all_goals rcases (show tq = 1 ∨ tq = 2 by omega) with rfl | rfl
  all_goals simp_all [logByte, msgByte, accAddr, TsoOfPf.g2Log, TsoOfPf.mc, TsoOfPf.ma]

/-- ... and its second load reading `(b, c) = (0, 0)` is `scaOkT` under (a′) ... -/
theorem g2ScaTSrc :
    scaOkT (tsoShadow cohSrc (TsoOfPf.g2St.take 3) 0).mem TsoOfPf.img0 TsoOfPf.g2Log 0 1 [0, 0] := by
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
    ¬ scaOkT (tsoShadow cohFoot (TsoOfPf.g2St.take 3) 0).mem TsoOfPf.img0 TsoOfPf.g2Log 0 1 [0, 0] := by
  rintro ⟨tvn, _, hF, hb⟩
  change shFloor _ 1 2 ≤ tvn at hF
  rw [g2FloorFoot] at hF
  obtain ⟨_, _, hlater⟩ := hb 1 0 rfl
  exact hlater 1 (by omega) (by decide) (Or.inl (by omega))

-- The G2 run's per-byte read obligations (`readOkD`), by evaluation (`TsoOfPf`'s local recipe).
set_option hygiene false in
local macro "tsoShRd" : tactic => `(tactic| (intro j t v h; rcases j with _ | _ | j <;> simp at h <;>
  (obtain ⟨rfl, rfl⟩ := h) <;>
  exact ⟨by decide, ⟨by decide, TsoOfPf.notWritesInLe _ _ _ _ (by decide)⟩, by simp⟩))

/-- RUN LEVEL, G2: under (a′) a shadow-threaded run follows the spike's G2 step list, BOTH loads
`scaOkT` at their prefix shadows (`g2Ld1ScaTSrc`, `g2ScaTSrc`). -/
theorem g2RunT :
    ∃ c, pfRunST TsoOfPf.anyStep TsoOfPf.anyCls (candKfetch 0 0) cohSrc TsoOfPf.cfg0
      TsoOfPf.g2St c := by
  refine ⟨_, pfRunST.snoc _ _
    [(1, .LStore false 2 [1#8] [] []), (1, .LStore false 0 [1#8] [] []),
     (0, .LLoad false false 0 [(2, 1#8), (0, 0#8)] [])] 0
    (.LLoad false false 1 [(0, 0#8), (0, 0#8)] [])
    (pfRunST.snoc _ _ [(1, .LStore false 2 [1#8] [] []), (1, .LStore false 0 [1#8] [] [])] 0
      (.LLoad false false 0 [(2, 1#8), (0, 0#8)] [])
      (pfRunST.snoc _ _ [(1, .LStore false 2 [1#8] [] [])] 1 (.LStore false 0 [1#8] [] [])
        (pfRunST.snoc _ _ [] 1 (.LStore false 2 [1#8] [] []) pfRunST.nil
          (wpPfStep.PFStore TsoOfPf.cfg0 ⟨(), wsInit, ∅⟩ false 2 [1#8] [] [] .WCplain () ()
            rfl trivial (by simp) rfl) trivial trivial)
        (wpPfStep.PFStore _ _ false 0 [1#8] [] [] .WCplain () () rfl trivial (by simp) rfl)
        trivial trivial)
      (wpPfStep.PFLoad _ ⟨(), wsInit, ∅⟩ false false 0 [(2, 1#8), (0, 0#8)] [] () () rfl
        trivial ?r3) ?f3 ?l3)
    (wpPfStep.PFLoad _ _ false false 1 [(0, 0#8), (0, 0#8)] [] () () rfl trivial ?r4) ?f4 ?l4⟩
  case r3 => tsoShRd
  case r4 => tsoShRd
  case f3 => exact scaOkTSca _ _ _ _ _ _ g2Ld1ScaTSrc
  case l3 => exact ⟨g2Ld1ScaTSrc, fun h => absurd h (by decide)⟩
  case f4 => exact scaOkTSca _ _ _ _ _ _ g2ScaTSrc
  case l4 => exact ⟨g2ScaTSrc, fun h => absurd h (by decide)⟩

/-- `fence.i` (boundary `LInstr`, fetch, announce `LInstr`, a silent step, the all-false barrier)
after an own store at timestamp 1: `itv` rises to the store (`ownPub`). -/
def fiSt : List (Nat × Wlabel) :=
  [(0, .LStore false 0 [1#8] [] []), (0, .LInstr), (0, .LIFetch 0 []), (0, .LInstr), (0, .LSilent),
   (0, .LFence false false false false)]

/-- The `sfence.vma` marker (boundary `LInstr`, fetch, the all-false marker) after the same store:
`itv` stays. -/
def sfSt : List (Nat × Wlabel) :=
  [(0, .LStore false 0 [1#8] [] []), (0, .LInstr), (0, .LIFetch 0 []),
   (0, .LFence false false false false)]

theorem itvFenceI (stamp : CohStamp) : (tsoShadow stamp fiSt 0).itv = 1 := rfl

theorem itvSfence (stamp : CohStamp) : (tsoShadow stamp sfSt 0).itv = 0 := rfl

end TsoShadow

end Weak
