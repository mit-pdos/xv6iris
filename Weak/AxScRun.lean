/-
Weak: **THE CERTIFICATE TOOLKIT, graph side** — an SC execution (per-hart label rows + an
interleaving + per-hart emissions) becomes a tagged graph that provably meets the theorems' graph
premises.  PURE (no Iris, no Sail).

Rocq: `iris/AxScRun.v` @ xxvzwolszwmp.

## The Rocq header, in substance

Spinlock plan, owner decision 2026-10-02: certificate graphs get CONSISTENCY from the general
lemma `AxScCat.scGraphCatT`, not from deciding 600-event graphs.  This file CONSTRUCTS the graph
from the run and proves, ONCE AND GENERICALLY, that the construction is `scGraph` (hence
`rvwmoCatConsistentT`) and `ctrlClosed` (AxSpinGate) whenever cheap linear/quadratic boolean checks
on the INPUTS hold.  (The driver/run side is `AxScRun2`; a demo is `AxScRun3`.)

THE CONSTRUCTION `graphOfSc img rows il ems`.
  - `rows : List (List Lbl)`: hart i's row of graph labels; only the IDENTITY and WRITE DATA of
    each label are used, read timestamps and values are recomputed.
  - `il : List Geid`: the interleaving (every memory event, in execution order) = `gxGmo`.
  - `img : Int → BitVec 8`: the initial memory (graph image `fun a => some (img a)`, total).
  - `ems : List (List Eitem)`: hart i's emission; the tagged deps are `rowDepsT` of each, lifted
    to hart i (`gdepsOf`).
  Memory is SIMULATED along `il` (`sim`: a byte map to (write index, value)); each read label is
  REFILLED (`fill`) with the timestamps/values of the gmo-latest earlier same-byte write (or the
  image, ts 0).

WHAT IS PROVED (generic): `graphOfScSc` (`scInputsOkB … = true → scGraph …`), `graphOfScCatT`,
`graphOfScCtrlClosed` (`ctrlOkB … = true → ctrlClosed …`), `graphOfScValue` (a
simulated read's graph label is the row label refilled from the memory after `il.take p`),
`graphOfScErase` (`valsOkB … = true →` every graph row equals the input row up to read
timestamps).  THE CHECKS: `shapesOkB`, `ilOkB`, `emsOkB` (together `scInputsOkB`), `ctrlOkB`,
`valsOkB` (bridge only).  §11 SANITY (`ScRunSanity`): a message-passing instance end to end.

HONEST SCOPE (Rocq).  The construction never fails: ANY rows and il satisfying the checks give an
SC graph; whether a hart's REAL code produces that row is the RUN premise (`AxScRun2`).  The deps
are exactly `rowDepsT` of the supplied emissions.  The image is total.

FETCHES (O2 Stage C).  Graph labels (`Lbl`) have no fetch; an emission's `LIFetch` item is
administrative: `dstepT`'s `LIFetch` arm is `(s, [])` (no edge, no state change), so it is one
more inert arm in the §7/§9 case analyses (`dinvStep`, `dstepEdge`, `dstepTTgt`), and
`itemOkB`/`elbIsR`/`elbIsW` treat it as neither read nor write.

## Deviations from Rocq

1. NAMES: the tree's camelCase (map below).  Duplicated Rocq names are file-qualified:
   `AxScRun.lv`, `AxScRun.coverB`, `AxScRun.accAddr0`, `AxScRun.gwritesByteIsW`, `AxScRun.rdb`,
   `AxScRun.gshape`.  The Rocq `Module ScRunSanity` is `namespace ScRunSanity`; its duplicated
   names `mp`, `r5`, `mp_rows` live there as `ScRunSanity.mp`, `ScRunSanity.r5`,
   `ScRunSanity.mpRows` (already qualified by the module name, which no other file uses).
2. MAPS: Rocq's `gmap Z (nat * bv 8)` (`mem_t`) and `gmap geid lbl` (`s_out`) are total
   functions to `Option` (`MemT := Int → Option (Nat × BitVec 8)`, `Geid → Option Lbl`); `∅` is
   `fun _ => none`, `<[k := v]> m` is the Lean-only `AxScRun.finsert m k v`, `m !! k` is `m k`.
   Kernel-reducible, so the §11 `vm_compute` verdicts are `decide +kernel`.
3. VOCABULARY: as `AxScCat`/`AxDeps` (`forallb` ↦ `List.all`, `existsb` ↦ `List.any`,
   `implb a b` ↦ `!a || b`, `Nat.leb`/`Nat.ltb`/`Nat.eqb`/`bv_eqb`/`bool_decide` ↦ `decide`,
   `imap` ↦ `List.mapIdx`, `seq 0 n` ↦ `List.range' 0 n`, `omap` ↦ `List.filterMap`,
   `mjoin` ↦ `List.flatten`, `default d o` ↦ `o.getD d`, `StronglySorted` ↦ `List.Pairwise`,
   `.*1`/`.*2` ↦ `map Prod.fst`/`map Prod.snd`, `filter (λ k, b k = true)` ↦ `filter b`).
   Edges are `((j, k), tg)` and deps `(((i, j), (i, k)), tg)` (AxDeps deviation 2).  The
   `if dtag_w tg then …` of `dstepEdge`/`rowEdges` is the Prop-level `if dtagW tg = true`.
4. `ss_split`'s list is written `l1 ++ x :: (l2 ++ y :: l3)` (Rocq's right-associative reading).
5. Sections: the section variables become explicit leading arguments, in Rocq's order (as the
   Rocq terms after `End`), e.g. `gLbl img rows il ems e`, `ilOkMem rows il hok i k`,
   `INV img rows il ems P`, `dinv rows i s`, `Rd rows i j`.  The `Let G := …` abbreviations are
   inlined as `(graphOfSc img rows il ems).gtG`.
6. Lean-only helpers (file-qualified): `AxScRun.finsert`, `AxScRun.finsertSame`,
   `AxScRun.finsertNe`, `AxScRun.sStepOut`, `AxScRun.sStepNone`, `AxScRun.rdbsLookup`, `AxScRun.dedgesRMem`, `AxScRun.dedgesWMem`,
   `AxScRun.dinvWSrcs`, `AxScRun.ilOkBIff`.
7. §12 `Print Assumptions`: no Lean twin (the lint's axiom check covers it).

**Name map** (Rocq → Lean): `mem_t` `MemT`; `wr_mem` `wrMem`; `lbl_at` `lblAt`; `rdb`
`AxScRun.rdb`; `rdbs` `rdbs`; `fill` `fill`; `sst`/`SSt`/`s_M`/`s_nw`/`s_out`
`Sst`/`Sst.SSt`/`sM`/`sNw`/`sOut`; `s_step` `sStep`; `sim` `sim`; `sc_prog` `scProg`;
`lift_deps` `liftDeps`; `gdeps_of` `gdepsOf`; `graph_of_sc` `graphOfSc`; `is_at` `isAt`;
`row_len` `rowLen`; `mem_pos` `memPos`; `hproj` `hproj`; `il_ok_b` `ilOkB`; `shape_in_b`
`shapeInB`; `shapes_ok_b` `shapesOkB`; `item_ok_b` `itemOkB`; `ems_ok_b` `emsOkB`;
`sc_inputs_ok_b` `scInputsOkB`; `mono_b` `monoB`; `cover_b` `AxScRun.coverB`; `ctrl_ok_b`
`ctrlOkB`; `lv` `AxScRun.lv`; `bvs_eqb` `bvsEqb`; `lv_eqb` `lvEqb`; `vals_ok_b` `valsOkB`;
`erase` `erase`; `row_of` `rowOf`; `acc_addr_0` `AxScRun.accAddr0`; `acc_addr_S` `accAddrS`;
`wr_mem_in` `wrMemIn`; `wr_mem_out` `wrMemOut`; `addr_cases` `addrCases`; `kind_eq` `kindEq`;
`kind_eq_refl` `kindEqRefl`; `fill_kind` `fillKind`; `kind_w`/`kind_r`/`kind_mem`
`kindW`/`kindR`/`kindMem`; `sim_snoc` `simSnoc`; `out_kind` `outKind`; `out_none` `outNone`;
`out_some` `outSome`; `G_lbl` `gLbl`; `G_lbl_kind` `gLblKind`; `rows_lbl_kind` `rowsLblKind`;
`G_lbl_None` `gLblNone`; `glbl_is_at` `glblIsAt`; `gis_w_at` `gisWAt`; `gmem_at` `gmemAt`;
`gwrites_byte_at` `gwritesByteAt`; `elem_hproj` `elemHproj`; `is_at_lt` `isAtLt`; `is_at_hart`
`isAtHart`; `elem_mem_pos` `elemMemPos`; `seq_sorted` `seqSorted`; `mem_pos_sorted`
`memPosSorted`; `ss_lt_nodup` `ssLtNodup`; `ss_split` `ssSplit`; `hproj_app` `hprojApp`;
`hproj_cons_same` `hprojConsSame`; `NoDup_of_hproj` `nodupOfHproj`; `il_ok_harts`
`ilOkHarts`; `il_ok_proj` `ilOkProj`; `il_ok_sorted` `ilOkSorted`; `il_ok_nodup` `ilOkNodup`;
`il_ok_mem` `ilOkMem`; `il_ok_order` `ilOkOrder`; `W` `W`; `INV` `INV`; `W_snoc` `wSnoc`;
`W_elem` `wElem`; `gwrites_byte_is_w` `AxScRun.gwritesByteIsW`; `INV_nil` `invNil`;
`INV_snoc` `invSnoc`; `INV_all` `invAll`; `fill_rd` `fillRd`; `lb_rd_mem` `lbRdMem`;
`is_at_r_mem` `isAtRMem`; `is_at_w_mem` `isAtWMem`; `lbl_at_lookup` `lblAtLookup`; `gshape`
`AxScRun.gshape`; `fill_shape` `fillShape`; `prefix_gmo_lt` `prefixGmoLt`; `gmo_lt_prefix`
`gmoLtPrefix`; `G_sc_rf` `gScRf`; `G_gwf` `gGwf`; `G_po` `gPo`; `ems_ok_items` `emsOkItems`;
`elem_gdeps_of` `elemGdepsOf`; `Rd` `Rd`; `dinv` `dinv`; `dinv_init` `dinvInit`; `dinv_srcs`
`dinvSrcs`; `dinv_ctx` `dinvCtx`; `dinv_acc` `dinvAcc`; `dinv_step` `dinvStep`; `dstep_edge`
`dstepEdge`; `row_edges` `rowEdges`; `G_deps_wf` `gDepsWf`; `graph_of_sc_sc` `graphOfScSc`;
`graph_of_sc_cat_t` `graphOfScCatT`; `dstep_t_tgt` `dstepTTgt`; `row_tgt` `rowTgt`;
`mono_b_ge` `monoBGe`; `mono_b_tail` `monoBTail`; `cover_b_spec` `coverBSpec`;
`ctrl_ok_hart` `ctrlOkHart`; `graph_of_sc_ctrl_closed` `graphOfScCtrlClosed`;
`graph_of_sc_value` `graphOfScValue`; `bvs_eqb_spec` `bvsEqbSpec`; `lv_eqb_spec` `lvEqbSpec`;
`erase_fill` `eraseFill`; `graph_of_sc_erase` `graphOfScErase`; `ScRunSanity.{mp_rows, r5,
mp_ems, mp_il, mp, mp_inputs, mp_ctrl, mp_cat_t, mp_ctrl_closed, mp_deps, mp_reads, mp_sc_b,
mp_bad_il}` `ScRunSanity.{mpRows, r5, mpEms, mpIl, mp, mpInputs, mpCtrl, mpCatT, mpCtrlClosed,
mpDeps, mpReads, mpScB, mpBadIl}`.

**Dropped:** nothing.

**W13 (I) (plan `notes/weak-allocproc-plan.md` §C W13 (I); [OWN.27]).** `shapeInB` accepts an `LIo` row item and `AxScRun.gshape`'s `LIo` arm is `True` (`gwf`'s flip).
-/
import Weak.AxScCat
import Weak.AxSpinGate

namespace Weak

open MachCSL MachCSL.Stdpp
open Wlabel Dtag

/-! # 1. The construction -/

/-- (Lean-only) `<[k := v]> m` on a function map (deviation 2). -/
def AxScRun.finsert {K V : Type} [DecidableEq K] (m : K → Option V) (k : K) (v : V) :
    K → Option V :=
  fun x => if x = k then some v else m x

theorem AxScRun.finsertSame {K V : Type} [DecidableEq K] (m : K → Option V) (k : K) (v : V) :
    AxScRun.finsert m k v k = some v := by
  simp [AxScRun.finsert]

theorem AxScRun.finsertNe {K V : Type} [DecidableEq K] (m : K → Option V) (k x : K) (v : V) :
    k ≠ x → AxScRun.finsert m k v x = m x := by
  intro h
  simp only [AxScRun.finsert]
  rw [if_neg (fun h' => h h'.symm)]

abbrev MemT : Type := Int → Option (Nat × BitVec 8)

/-- Write `vs` at `base..` with write index `t`. -/
def wrMem (M : MemT) (t : Nat) (base : Int) (vs : List (BitVec 8)) : MemT :=
  match vs with
  | [] => M
  | v :: vs' => AxScRun.finsert (wrMem M t (base + 1) vs') base (t, v)

def lblAt (rows : List (List Lbl)) (e : Geid) : Option Lbl := (rows[e.1]?).bind (fun r => r[e.2]?)

/-- One byte as the simulation holds it: (write index, value); the image (index 0) when no write
has touched it. -/
def AxScRun.rdb (img : Int → BitVec 8) (M : MemT) (a : Int) : Nat × BitVec 8 :=
  (M a).getD (0, img a)

def rdbs (img : Int → BitVec 8) (M : MemT) (base : Int) (n : Nat) : List (Nat × BitVec 8) :=
  (List.range' 0 n).map (fun j => AxScRun.rdb img M (accAddr base j))

/-- Refill a read label from memory `M`; everything else is kept. -/
def fill (img : Int → BitVec 8) (M : MemT) (l : Lbl) : Lbl :=
  match l with
  | .LLoad aq base _ vs =>
      let bs := rdbs img M base vs.length
      .LLoad aq base (bs.map Prod.fst) (bs.map Prod.snd)
  | .LRmw aq rl base _ _ wvs k =>
      let bs := rdbs img M base wvs.length
      .LRmw aq rl base (bs.map Prod.fst) (bs.map Prod.snd) wvs k
  | _ => l

/-- The simulation state: memory, number of writes so far, refilled labels. -/
structure Sst where
  SSt ::
  sM : MemT
  sNw : Nat
  sOut : Geid → Option Lbl

def sStep (img : Int → BitVec 8) (rows : List (List Lbl)) (s : Sst) (e : Geid) : Sst :=
  match lblAt rows e with
  | none => s
  | some l =>
      let out := AxScRun.finsert s.sOut e (fill img s.sM l)
      match lbWr l with
      | some (base, vs) => ⟨wrMem s.sM (s.sNw + 1) base vs, s.sNw + 1, out⟩
      | none => ⟨s.sM, s.sNw, out⟩

def sim (img : Int → BitVec 8) (rows : List (List Lbl)) (P : List Geid) : Sst :=
  P.foldl (sStep img rows) ⟨fun _ => none, 0, fun _ => none⟩

def scProg (rows : List (List Lbl)) (out : Geid → Option Lbl) : List (List Lbl) :=
  rows.mapIdx (fun i r => r.mapIdx (fun k l => (out (i, k)).getD l))

/-- Lift hart `i`'s row-level edges to graph edges. -/
def liftDeps (i : Nat) (ds : List Redge) : List Tdep :=
  ds.map (fun d : Redge => (((i, d.1.1), (i, d.1.2)), d.2))

def gdepsOf (ems : List (List Eitem)) : List Tdep :=
  (ems.mapIdx (fun i es => liftDeps i (rowDepsT es))).flatten

/-- THE CONSTRUCTION. -/
def graphOfSc (img : Int → BitVec 8) (rows : List (List Lbl)) (il : List Geid)
    (ems : List (List Eitem)) : GdexecT :=
  ⟨⟨fun a => some (img a), scProg rows (sim img rows il).sOut, il⟩, gdepsOf ems⟩

/-! # 2. The checks -/

def isAt (rows : List (List Lbl)) (P : Lbl → Bool) (i k : Nat) : Bool :=
  match lblAt rows (i, k) with
  | some l => P l
  | none => false

def rowLen (rows : List (List Lbl)) (i : Nat) : Nat := ((rows[i]?).getD []).length

def memPos (rows : List (List Lbl)) (i : Nat) : List Nat :=
  (List.range' 0 (rowLen rows i)).filter (fun k => isAt rows lbIsMem i k)

def hproj (il : List Geid) (i : Nat) : List Nat :=
  il.filterMap (fun e : Geid => if e.1 = i then some e.2 else none)

def ilOkB (rows : List (List Lbl)) (il : List Geid) : Bool :=
  il.all (fun e : Geid => decide (e.1 < rows.length)) &&
  (List.range' 0 rows.length).all (fun i => decide (hproj il i = memPos rows i))

def shapeInB (l : Lbl) : Bool :=
  match l with
  | .LStore _ _ vs _ => !decide (vs = [])
  | .LRmw _ _ _ _ _ wvs _ => !decide (wvs = [])
  -- W13 (I): an I/O-class row item is accepted (`gwf`'s `LIo` shape arm is `True`)
  | _ => true

def shapesOkB (rows : List (List Lbl)) : Bool := rows.all (fun r => r.all shapeInB)

def itemOkB (rows : List (List Lbl)) (i : Nat) (it : Eitem) : Bool :=
  match it.2 with
  | none => true
  | some k => !elbIsIoRd it.1 && !elbIsIoWr it.1 &&
      (!elbIsR it.1 || isAt rows lbIsR i k) && (!elbIsW it.1 || isAt rows lbIsW i k)

def emsOkB (rows : List (List Lbl)) (ems : List (List Eitem)) : Bool :=
  (ems.mapIdx (·, ·)).all (fun ies : Nat × List Eitem => ies.2.all (itemOkB rows ies.1))

def scInputsOkB (rows : List (List Lbl)) (il : List Geid) (ems : List (List Eitem)) : Bool :=
  shapesOkB rows && ilOkB rows il && emsOkB rows ems

def monoB (k0 : Nat) (es : List Eitem) : Bool :=
  match es with
  | [] => true
  | it :: es' =>
      match it.2 with
      | some k => decide (k0 ≤ k) && monoB k es'
      | none => monoB k0 es'

def AxScRun.coverB (rows : List (List Lbl)) (i : Nat) (es : List Eitem) : Bool :=
  (List.range' 0 (rowLen rows i)).all (fun k => !isAt rows lbIsW i k ||
    es.any (fun it : Eitem => match it.2 with
                              | some k' => decide (k = k') && elbIsW it.1
                              | none => false))

def ctrlOkB (rows : List (List Lbl)) (ems : List (List Eitem)) : Bool :=
  (ems.mapIdx (·, ·)).all (fun ies : Nat × List Eitem =>
    monoB 0 ies.2 && AxScRun.coverB rows ies.1 ies.2)

/-- The read values a label carries. -/
def AxScRun.lv (l : Lbl) : Option (List (BitVec 8)) :=
  match l with
  | .LLoad _ _ _ vs => some vs
  | .LRmw _ _ _ _ rvs _ _ => some rvs
  | _ => none

def bvsEqb (xs ys : List (BitVec 8)) : Bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' => decide (x = y) && bvsEqb xs' ys'
  | _, _ => false

def lvEqb (o o' : Option (List (BitVec 8))) : Bool :=
  match o, o' with
  | some xs, some ys => bvsEqb xs ys
  | none, none => true
  | _, _ => false

/-- The input rows carry the SC values (bridge for runs on the input rows). -/
def valsOkB (img : Int → BitVec 8) (rows : List (List Lbl)) (il : List Geid) : Bool :=
  let out := (sim img rows il).sOut
  (rows.mapIdx (·, ·)).all (fun ir : Nat × List Lbl =>
    (ir.2.mapIdx (·, ·)).all (fun kl : Nat × Lbl =>
      match out (ir.1, kl.1) with
      | some l' => lvEqb (AxScRun.lv l') (AxScRun.lv kl.2)
      | none => true))

/-- Timestamps erased. -/
def erase (l : Lbl) : Lbl :=
  match l with
  | .LLoad aq base _ vs => .LLoad aq base [] vs
  | .LRmw aq rl base _ rvs wvs k => .LRmw aq rl base [] rvs wvs k
  | _ => l

def rowOf (G : Gexec) (i : Nat) : List Lbl := (G.gxProg[i]?).getD []

/-! # 3. Basic facts -/

theorem AxScRun.accAddr0 (base : Int) : accAddr base 0 = base := by
  unfold accAddr; omega

theorem accAddrS (base : Int) (j : Nat) : accAddr base (j + 1) = accAddr (base + 1) j := by
  unfold accAddr; omega

theorem wrMemIn (M : MemT) (t : Nat) (base : Int) (vs : List (BitVec 8)) (j : Nat)
    (v : BitVec 8) :
    vs[j]? = some v → wrMem M t base vs (accAddr base j) = some (t, v) := by
  induction vs generalizing base j with
  | nil => intro h; simp at h
  | cons v' vs ih =>
    intro hj
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst hj
      rw [AxScRun.accAddr0]
      exact AxScRun.finsertSame _ _ _
    | succ j =>
      simp only [List.getElem?_cons_succ] at hj
      simp only [wrMem]
      rw [AxScRun.finsertNe _ _ _ _ (by unfold accAddr; omega), accAddrS]
      exact ih _ _ hj

theorem wrMemOut (M : MemT) (t : Nat) (base : Int) (vs : List (BitVec 8)) (a : Int) :
    (∀ j, j < vs.length → accAddr base j ≠ a) → wrMem M t base vs a = M a := by
  induction vs generalizing base with
  | nil => intro _; rfl
  | cons v' vs ih =>
    intro ha
    simp only [wrMem]
    rw [AxScRun.finsertNe]
    · apply ih
      intro j hj
      rw [← accAddrS]
      exact ha (j + 1) (by simp; omega)
    · intro h
      subst h
      exact ha 0 (by simp) (AxScRun.accAddr0 _)

theorem addrCases (base : Int) (n : Nat) (a : Int) :
    (∃ j, j < n ∧ accAddr base j = a) ∨ (∀ j, j < n → accAddr base j ≠ a) := by
  by_cases h : base ≤ a ∧ a < base + (n : Int)
  · left
    refine ⟨(a - base).toNat, ?_, ?_⟩ <;> unfold accAddr at * <;> omega
  · right
    intro j hj
    unfold accAddr
    omega

/-- Kinds are preserved by refilling. -/
def kindEq (l l' : Lbl) : Prop :=
  lbWr l' = lbWr l ∧ lbIsW l' = lbIsW l ∧ lbIsR l' = lbIsR l ∧ lbIsMem l' = lbIsMem l

theorem kindEqRefl (l : Lbl) : kindEq l l := ⟨rfl, rfl, rfl, rfl⟩

theorem fillKind (img : Int → BitVec 8) (M : MemT) (l : Lbl) : kindEq l (fill img M l) := by
  cases l <;> exact ⟨rfl, rfl, rfl, rfl⟩

theorem kindW (l l' : Lbl) : kindEq l l' → lbIsW l' = lbIsW l := fun h => h.2.1
theorem kindR (l l' : Lbl) : kindEq l l' → lbIsR l' = lbIsR l := fun h => h.2.2.1
theorem kindMem (l l' : Lbl) : kindEq l l' → lbIsMem l' = lbIsMem l := fun h => h.2.2.2

theorem simSnoc (img : Int → BitVec 8) (rows : List (List Lbl)) (P : List Geid) (e : Geid) :
    sim img rows (P ++ [e]) = sStep img rows (sim img rows P) e := by
  simp [sim, List.foldl_append]

/-- (Lean-only) the out-map of one step. -/
theorem AxScRun.sStepOut (img : Int → BitVec 8) (rows : List (List Lbl)) (s : Sst)
    (e : Geid) (l : Lbl) :
    lblAt rows e = some l →
    (sStep img rows s e).sOut = AxScRun.finsert s.sOut e (fill img s.sM l) := by
  intro hl
  simp only [sStep, hl]
  cases lbWr l with
  | none => rfl
  | some p => obtain ⟨_, _⟩ := p; rfl

theorem AxScRun.sStepNone (img : Int → BitVec 8) (rows : List (List Lbl)) (s : Sst)
    (e : Geid) : lblAt rows e = none → sStep img rows s e = s := by
  intro hl
  simp only [sStep, hl]

theorem outKind (img : Int → BitVec 8) (rows : List (List Lbl)) (P : List Geid) (e : Geid)
    (l' : Lbl) :
    (sim img rows P).sOut e = some l' →
    ∃ M l, lblAt rows e = some l ∧ l' = fill img M l := by
  induction P using snocInd with
  | h0 => intro h; simp [sim] at h
  | hs P x ih =>
    rw [simSnoc]
    cases hx : lblAt rows x with
    | none => rw [AxScRun.sStepNone _ _ _ _ hx]; exact ih
    | some lx =>
      rw [AxScRun.sStepOut _ _ _ _ _ hx]
      by_cases hxe : x = e
      · subst hxe
        rw [AxScRun.finsertSame]
        intro h
        cases h
        exact ⟨_, lx, hx, rfl⟩
      · rw [AxScRun.finsertNe _ _ _ _ hxe]
        exact ih

theorem outNone (img : Int → BitVec 8) (rows : List (List Lbl)) (P : List Geid) (e : Geid) :
    e ∉ P → (sim img rows P).sOut e = none := by
  induction P using snocInd with
  | h0 => intro _; rfl
  | hs P x ih =>
    intro hn
    have hx : x ≠ e := by
      intro h; subst h; exact hn (List.mem_append.2 (.inr (List.mem_singleton.2 rfl)))
    have hP : e ∉ P := fun h => hn (List.mem_append.2 (.inl h))
    rw [simSnoc]
    cases hxl : lblAt rows x with
    | none => rw [AxScRun.sStepNone _ _ _ _ hxl]; exact ih hP
    | some lx =>
      rw [AxScRun.sStepOut _ _ _ _ _ hxl, AxScRun.finsertNe _ _ _ _ hx]
      exact ih hP

theorem outSome (img : Int → BitVec 8) (rows : List (List Lbl)) (P : List Geid) (p : Nat)
    (e : Geid) (l : Lbl) :
    P.Nodup → P[p]? = some e → lblAt rows e = some l →
    (sim img rows P).sOut e = some (fill img (sim img rows (P.take p)).sM l) := by
  induction P using snocInd with
  | h0 => intro _ h; simp at h
  | hs P x ih =>
    intro hnd hp hl
    obtain ⟨hndP, hdisj, _⟩ := NoDup_app.1 hnd
    rw [simSnoc]
    by_cases hlt : p < P.length
    · rw [lookup_app_l hlt] at hp
      have hne : x ≠ e := by
        intro h; subst h
        exact hdisj x (elem_of_list_lookup_2 hp) (List.mem_singleton.2 rfl)
      rw [take_app_le (by omega)]
      cases hxl : lblAt rows x with
      | none => rw [AxScRun.sStepNone _ _ _ _ hxl]; exact ih hndP hp hl
      | some lx =>
        rw [AxScRun.sStepOut _ _ _ _ _ hxl, AxScRun.finsertNe _ _ _ _ hne]
        exact ih hndP hp hl
    · rw [lookup_app_r (by omega)] at hp
      have hq : p - P.length = 0 := by
        cases hq : p - P.length with
        | zero => rfl
        | succ q => rw [hq] at hp; simp at hp
      rw [hq] at hp
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hp
      subst hp
      have hpl : p = P.length := by omega
      subst hpl
      rw [take_app_length, AxScRun.sStepOut _ _ _ _ _ hl, AxScRun.finsertSame]

/-! The graph's label at `e`: the row's, refilled if `e` was simulated. -/

section graph
variable (img : Int → BitVec 8) (rows : List (List Lbl)) (il : List Geid)
  (ems : List (List Eitem))

theorem gLbl (e : Geid) :
    gxLbl (graphOfSc img rows il ems).gtG e =
      (lblAt rows e).map (fun l => ((sim img rows il).sOut e).getD l) := by
  obtain ⟨i, k⟩ := e
  simp only [gxLbl, graphOfSc, scProg, lblAt, list_lookup_imap]
  cases rows[i]? with
  | none => rfl
  | some r => simp

theorem gLblKind (e : Geid) (l' : Lbl) :
    gxLbl (graphOfSc img rows il ems).gtG e = some l' → ∃ l, lblAt rows e = some l ∧ kindEq l l' := by
  rw [gLbl]
  cases hl : lblAt rows e with
  | none => intro h; cases h
  | some l =>
    intro h
    simp only [Option.map_some, Option.some.injEq] at h
    subst h
    refine ⟨l, rfl, ?_⟩
    cases ho : (sim img rows il).sOut e with
    | none => exact kindEqRefl l
    | some l1 =>
      obtain ⟨M, l0, hl0, rfl⟩ := outKind img rows il e l1 ho
      rw [hl] at hl0
      cases hl0
      exact fillKind img M l

theorem rowsLblKind (e : Geid) (l : Lbl) :
    lblAt rows e = some l → ∃ l', gxLbl (graphOfSc img rows il ems).gtG e = some l' ∧ kindEq l l' := by
  intro hl
  rw [gLbl, hl]
  refine ⟨_, rfl, ?_⟩
  cases ho : (sim img rows il).sOut e with
  | none => exact kindEqRefl l
  | some l1 =>
    obtain ⟨M, l0, hl0, rfl⟩ := outKind img rows il e l1 ho
    rw [hl] at hl0
    cases hl0
    exact fillKind img M l

theorem gLblNone (e : Geid) : lblAt rows e = none → gxLbl (graphOfSc img rows il ems).gtG e = none := by
  intro h
  rw [gLbl, h]
  rfl

theorem glblIsAt (P : Lbl → Bool) (e : Geid) :
    (∀ l l', kindEq l l' → P l' = P l) →
    (glblIs (graphOfSc img rows il ems).gtG e P ↔ isAt rows P e.1 e.2 = true) := by
  intro hP
  obtain ⟨i, k⟩ := e
  simp only [isAt]
  constructor
  · rintro ⟨l', hl', hPl⟩
    obtain ⟨l, hl, hk⟩ := gLblKind img rows il ems _ l' hl'
    simp only [hl]
    rw [← hP _ _ hk]
    exact hPl
  · cases hl : lblAt rows (i, k) with
    | none => intro h; cases h
    | some l =>
      intro hPl
      obtain ⟨l', hl', hk⟩ := rowsLblKind img rows il ems _ l hl
      exact ⟨l', hl', by rw [hP _ _ hk]; exact hPl⟩

theorem gisWAt (e : Geid) : gisW (graphOfSc img rows il ems).gtG e = isAt rows lbIsW e.1 e.2 := by
  obtain ⟨i, k⟩ := e
  simp only [gisW, isAt]
  cases hl' : gxLbl (graphOfSc img rows il ems).gtG (i, k) with
  | some l' =>
    obtain ⟨l, hl, hk⟩ := gLblKind img rows il ems _ l' hl'
    rw [hl]
    exact kindW l l' hk
  | none =>
    cases hl : lblAt rows (i, k) with
    | none => rfl
    | some l =>
      obtain ⟨l', hl'', _⟩ := rowsLblKind img rows il ems _ l hl
      rw [hl'] at hl''
      cases hl''

theorem gmemAt (e : Geid) : gmem (graphOfSc img rows il ems).gtG e ↔ isAt rows lbIsMem e.1 e.2 = true :=
  glblIsAt img rows il ems lbIsMem e kindMem

theorem gwritesByteAt (e : Geid) (a : Int) (v : BitVec 8) :
    gwritesByte (graphOfSc img rows il ems).gtG e a v ↔
    ∃ l base vs j, lblAt rows e = some l ∧ lbWr l = some (base, vs) ∧
                   vs[j]? = some v ∧ accAddr base j = a := by
  constructor
  · rintro ⟨l', base, vs, j, hl', hw, hj, ha⟩
    obtain ⟨l, hl, hk, _⟩ := gLblKind img rows il ems _ l' hl'
    exact ⟨l, base, vs, j, hl, by rw [← hk]; exact hw, hj, ha⟩
  · rintro ⟨l, base, vs, j, hl, hw, hj, ha⟩
    obtain ⟨l', hl', hk, _⟩ := rowsLblKind img rows il ems _ l hl
    exact ⟨l', base, vs, j, hl', by rw [hk]; exact hw, hj, ha⟩

end graph

/-! # 4. What `ilOkB` buys: membership, NoDup, po ⊆ gmo -/

theorem elemHproj (il : List Geid) (i k : Nat) : k ∈ hproj il i ↔ (i, k) ∈ il := by
  simp only [hproj, elem_of_list_omap]
  constructor
  · rintro ⟨⟨i', k'⟩, hin, hf⟩
    by_cases h : i' = i
    · subst h
      simp only [if_true, Option.some.injEq] at hf
      subst hf
      exact hin
    · simp [h] at hf
  · intro hin
    exact ⟨(i, k), hin, by simp⟩

theorem isAtLt (rows : List (List Lbl)) (P : Lbl → Bool) (i k : Nat) :
    isAt rows P i k = true → k < rowLen rows i := by
  simp only [isAt, lblAt, rowLen]
  cases rows[i]? with
  | none => intro h; simp at h
  | some r =>
    simp only [Option.bind_some, Option.getD_some]
    cases hk : r[k]? with
    | none => intro h; cases h
    | some l => intro _; exact lookup_lt_Some hk

theorem isAtHart (rows : List (List Lbl)) (P : Lbl → Bool) (i k : Nat) :
    isAt rows P i k = true → i < rows.length := by
  simp only [isAt, lblAt]
  cases hr : rows[i]? with
  | none => intro h; simp at h
  | some r => intro _; exact lookup_lt_Some hr

theorem elemMemPos (rows : List (List Lbl)) (i k : Nat) :
    k ∈ memPos rows i ↔ isAt rows lbIsMem i k = true := by
  simp only [memPos, elem_of_list_filter, elem_of_seq]
  constructor
  · exact fun h => h.1
  · intro h
    have := isAtLt _ _ _ _ h
    exact ⟨h, by omega, by omega⟩

theorem seqSorted (n : Nat) : List.Pairwise (· < ·) (List.range' 0 n) := by
  apply stronglySortedLookupIntro
  intro i j x y hi hj hlt
  obtain ⟨rfl, _⟩ := lookup_seq.1 hi
  obtain ⟨rfl, _⟩ := lookup_seq.1 hj
  omega

theorem memPosSorted (rows : List (List Lbl)) (i : Nat) :
    List.Pairwise (· < ·) (memPos rows i) :=
  stronglySortedFilter _ _ _ (seqSorted _)

theorem ssLtNodup (l : List Nat) : List.Pairwise (· < ·) l → l.Nodup :=
  fun h => h.imp (fun h' => Nat.ne_of_lt h')

theorem ssSplit {A : Type _} (R : A → A → Prop) (l1 : List A) (x : A) (l2 : List A) (y : A)
    (l3 : List A) : List.Pairwise R (l1 ++ x :: (l2 ++ y :: l3)) → R x y := by
  intro h
  rw [List.pairwise_append] at h
  obtain ⟨_, h2, _⟩ := h
  rw [List.pairwise_cons] at h2
  exact h2.1 y (List.mem_append.2 (.inr (List.mem_cons_self ..)))

theorem hprojApp (il1 il2 : List Geid) (i : Nat) :
    hproj (il1 ++ il2) i = hproj il1 i ++ hproj il2 i := by
  simp [hproj, List.filterMap_append]

theorem hprojConsSame (k : Nat) (il : List Geid) (i : Nat) :
    hproj ((i, k) :: il) i = k :: hproj il i := by
  simp [hproj]

theorem nodupOfHproj (il : List Geid) : (∀ i, (hproj il i).Nodup) → il.Nodup := by
  induction il with
  | nil => intro _; exact List.nodup_nil
  | cons e il ih =>
    obtain ⟨i, k⟩ := e
    intro H
    refine List.nodup_cons.2 ⟨?_, ih ?_⟩
    · intro hin
      have h := H i
      rw [hprojConsSame] at h
      exact (List.nodup_cons.1 h).1 ((elemHproj il i k).2 hin)
    · intro j
      have h := H j
      by_cases hij : i = j
      · subst hij
        rw [hprojConsSame] at h
        exact (List.nodup_cons.1 h).2
      · have : hproj ((i, k) :: il) j = hproj il j := by simp [hproj, hij]
        rw [this] at h
        exact h

section il_ok
variable (rows : List (List Lbl)) (il : List Geid)

theorem AxScRun.ilOkBIff :
    ilOkB rows il = true ↔
    (∀ e, e ∈ il → e.1 < rows.length) ∧
    (∀ i, i ∈ List.range' 0 rows.length → hproj il i = memPos rows i) := by
  simp only [ilOkB, Bool.and_eq_true, forallbForallTrue, decide_eq_true_eq]

theorem ilOkHarts (hok : ilOkB rows il = true) : ∀ e, e ∈ il → e.1 < rows.length :=
  ((AxScRun.ilOkBIff rows il).1 hok).1

theorem ilOkProj (hok : ilOkB rows il = true) (i : Nat) :
    i < rows.length → hproj il i = memPos rows i := by
  intro hi
  exact ((AxScRun.ilOkBIff rows il).1 hok).2 i (elem_of_seq.2 ⟨Nat.zero_le _, by omega⟩)

theorem ilOkSorted (hok : ilOkB rows il = true) (i : Nat) :
    List.Pairwise (· < ·) (hproj il i) := by
  by_cases hi : i < rows.length
  · rw [ilOkProj rows il hok i hi]; exact memPosSorted _ _
  · cases e : hproj il i with
    | nil => exact List.Pairwise.nil
    | cons k ks =>
      exfalso
      have hk : k ∈ hproj il i := by rw [e]; exact List.mem_cons_self ..
      have := ilOkHarts rows il hok _ ((elemHproj il i k).1 hk)
      exact hi this

theorem ilOkNodup (hok : ilOkB rows il = true) : il.Nodup :=
  nodupOfHproj il (fun i => ssLtNodup _ (ilOkSorted rows il hok i))

theorem ilOkMem (hok : ilOkB rows il = true) (i k : Nat) :
    (i, k) ∈ il ↔ isAt rows lbIsMem i k = true := by
  constructor
  · intro hin
    have hi := ilOkHarts rows il hok _ hin
    apply (elemMemPos rows i k).1
    rw [← ilOkProj rows il hok i hi]
    exact (elemHproj il i k).2 hin
  · intro h
    apply (elemHproj il i k).1
    rw [ilOkProj rows il hok i (isAtHart _ _ _ _ h)]
    exact (elemMemPos rows i k).2 h

/-- The hart order inside `il` follows the row order. -/
theorem ilOkOrder (hok : ilOkB rows il = true) (p1 p2 i k1 k2 : Nat) :
    il[p1]? = some (i, k1) → il[p2]? = some (i, k2) → p2 < p1 → k2 < k1 := by
  intro h1 h2 hlt
  have hsplit := take_drop_middle h2
  have hin : (i, k1) ∈ il.drop (p2 + 1) := by
    apply elem_of_list_lookup_2 (i := p1 - (p2 + 1))
    rw [lookup_drop]
    rw [show p2 + 1 + (p1 - (p2 + 1)) = p1 by omega]
    exact h1
  obtain ⟨l2, l3, hd⟩ := elem_of_list_split hin
  have hss := ilOkSorted rows il hok i
  rw [← hsplit, hd] at hss
  simp only [hprojApp, hprojConsSame] at hss
  exact ssSplit _ _ _ _ _ _ hss

end il_ok

/-! # 5. The simulation invariant -/

section inv
variable (img : Int → BitVec 8) (rows : List (List Lbl)) (il : List Geid)
  (ems : List (List Eitem))

def W (P : List Geid) : List Geid := P.filter (gisW (graphOfSc img rows il ems).gtG)

def INV (P : List Geid) : Prop :=
  (sim img rows P).sNw = (W img rows il ems P).length ∧
  (∀ a, (sim img rows P).sM a = none → ∀ w v, w ∈ P →
     ¬ gwritesByte (graphOfSc img rows il ems).gtG w a v) ∧
  (∀ a t v, (sim img rows P).sM a = some (t, v) →
     ∃ t' w, t = t' + 1 ∧ (W img rows il ems P)[t']? = some w ∧
       gwritesByte (graphOfSc img rows il ems).gtG w a v ∧
       ∀ j w' v', (W img rows il ems P)[j]? = some w' →
         gwritesByte (graphOfSc img rows il ems).gtG w' a v' → j < t)

theorem wSnoc (P : List Geid) (e : Geid) :
    W img rows il ems (P ++ [e]) =
      if gisW (graphOfSc img rows il ems).gtG e then W img rows il ems P ++ [e]
      else W img rows il ems P := by
  simp only [W, List.filter_append, List.filter_cons, List.filter_nil]
  cases gisW (graphOfSc img rows il ems).gtG e <;> simp

theorem wElem (P : List Geid) (w : Geid) :
    w ∈ W img rows il ems P ↔ w ∈ P ∧ gisW (graphOfSc img rows il ems).gtG w = true := by
  simp only [W, elem_of_list_filter]
  exact And.comm

theorem AxScRun.gwritesByteIsW (w : Geid) (a : Int) (v : BitVec 8) :
    gwritesByte (graphOfSc img rows il ems).gtG w a v →
    gisW (graphOfSc img rows il ems).gtG w = true :=
  WeakRvwmoGraph.gwritesByteGisW _ w a v

theorem invNil : INV img rows il ems [] := by
  refine ⟨rfl, ?_, ?_⟩
  · intro a _ w v hw; exact absurd hw List.not_mem_nil
  · intro a t v h; simp [sim] at h

theorem invSnoc (P : List Geid) (e : Geid) :
    INV img rows il ems P → INV img rows il ems (P ++ [e]) := by
  rintro ⟨hnw, hnone, hsome⟩
  unfold INV
  rw [simSnoc, wSnoc]
  cases hl : lblAt rows e with
  | none =>
    -- no label: nothing changes, and e is not a write
    have hw : gisW (graphOfSc img rows il ems).gtG e = false := by
      simp only [gisW, gLblNone img rows il ems e hl]
    rw [AxScRun.sStepNone _ _ _ _ hl, hw]
    simp only [Bool.false_eq_true, if_false]
    refine ⟨hnw, ?_, hsome⟩
    intro a ha w v hin
    rcases List.mem_append.1 hin with hin | hin
    · exact hnone a ha w v hin
    · rw [List.mem_singleton] at hin
      subst hin
      intro hb
      have := AxScRun.gwritesByteIsW img rows il ems _ _ _ hb
      rw [hw] at this
      cases this
  | some l =>
    obtain ⟨l', hl', hk⟩ := rowsLblKind img rows il ems e l hl
    have hgw : gisW (graphOfSc img rows il ems).gtG e = lbIsW l := by
      simp only [gisW, hl']
      exact kindW l l' hk
    cases hwr : lbWr l with
    | none =>
      -- a non-write
      have hw : gisW (graphOfSc img rows il ems).gtG e = false := by
        rw [hgw]
        cases h : lbIsW l with
        | false => rfl
        | true =>
          obtain ⟨_, _, h'⟩ := lbIsWWr l h
          rw [hwr] at h'
          cases h'
      have hst : sStep img rows (sim img rows P) e =
          ⟨(sim img rows P).sM, (sim img rows P).sNw,
           AxScRun.finsert (sim img rows P).sOut e (fill img (sim img rows P).sM l)⟩ := by
        simp only [sStep, hl, hwr]
      rw [hst, hw]
      simp only [Bool.false_eq_true, if_false]
      refine ⟨hnw, ?_, hsome⟩
      intro a ha w v hin
      rcases List.mem_append.1 hin with hin | hin
      · exact hnone a ha w v hin
      · rw [List.mem_singleton] at hin
        subst hin
        rintro ⟨l0, base, vs, j, hl0, hw0, _⟩
        rw [hl'] at hl0
        cases hl0
        rw [hk.1, hwr] at hw0
        cases hw0
    | some bv =>
      obtain ⟨base, vs⟩ := bv
      -- a write
      have hw : gisW (graphOfSc img rows il ems).gtG e = true := by
        rw [hgw]
        cases l <;> simp_all [lbWr, lbIsW]
      have hwb : ∀ a v, gwritesByte (graphOfSc img rows il ems).gtG e a v ↔
          ∃ j, vs[j]? = some v ∧ accAddr base j = a := by
        intro a v
        rw [gwritesByteAt img rows il ems]
        constructor
        · rintro ⟨l0, b0, vs0, j, hl0, hw0, hj, ha⟩
          rw [hl] at hl0
          cases hl0
          rw [hwr] at hw0
          cases hw0
          exact ⟨j, hj, ha⟩
        · rintro ⟨j, hj, ha⟩
          exact ⟨l, base, vs, j, hl, hwr, hj, ha⟩
      have hst : sStep img rows (sim img rows P) e =
          ⟨wrMem (sim img rows P).sM ((sim img rows P).sNw + 1) base vs,
           (sim img rows P).sNw + 1,
           AxScRun.finsert (sim img rows P).sOut e (fill img (sim img rows P).sM l)⟩ := by
        simp only [sStep, hl, hwr]
      rw [hst, hw]
      simp only [if_true]
      refine ⟨?_, ?_, ?_⟩
      · simp [hnw]
      · intro a ha w v hin hb
        rcases addrCases base vs.length a with ⟨j, hj, hja⟩ | hn
        · obtain ⟨v0, hv0⟩ := Option.isSome_iff_exists.1 (lookup_lt_is_Some_2 hj)
          rw [← hja, wrMemIn _ _ _ _ _ _ hv0] at ha
          cases ha
        · rw [wrMemOut _ _ _ _ _ hn] at ha
          rcases List.mem_append.1 hin with hin | hin
          · exact hnone a ha w v hin hb
          · rw [List.mem_singleton] at hin
            subst hin
            obtain ⟨j, hj, hja⟩ := (hwb a v).1 hb
            exact hn j (lookup_lt_Some hj) hja
      · intro a t v ha
        rcases addrCases base vs.length a with ⟨j, hj, hja⟩ | hn
        · obtain ⟨v0, hv0⟩ := Option.isSome_iff_exists.1 (lookup_lt_is_Some_2 hj)
          rw [← hja, wrMemIn _ _ _ _ _ _ hv0] at ha
          simp only [Option.some.injEq, Prod.mk.injEq] at ha
          obtain ⟨rfl, rfl⟩ := ha
          refine ⟨(W img rows il ems P).length, e, by rw [hnw], ?_, ?_, ?_⟩
          · rw [lookup_app_r (Nat.le_refl _), Nat.sub_self]; rfl
          · exact (hwb _ _).2 ⟨j, hv0, hja⟩
          · intro j' w' v' hj' _
            have := lookup_lt_Some hj'
            simp only [List.length_append, List.length_singleton] at this
            omega
        · rw [wrMemOut _ _ _ _ _ hn] at ha
          obtain ⟨t', w, rfl, hwt, hwb', hmax⟩ := hsome a t v ha
          refine ⟨t', w, rfl, lookup_app_l_Some hwt, hwb', ?_⟩
          intro j w' v' hj hb'
          by_cases hlt : j < (W img rows il ems P).length
          · rw [lookup_app_l hlt] at hj
            exact hmax j w' v' hj hb'
          · rw [lookup_app_r (by omega)] at hj
            cases hq : j - (W img rows il ems P).length with
            | succ q => rw [hq] at hj; simp at hj
            | zero =>
              rw [hq] at hj
              simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
              subst hj
              obtain ⟨j0, hj0, hja⟩ := (hwb a v').1 hb'
              exact absurd hja (hn j0 (lookup_lt_Some hj0))

theorem invAll (P : List Geid) : INV img rows il ems P := by
  induction P using snocInd with
  | h0 => exact invNil img rows il ems
  | hs P x ih => exact invSnoc img rows il ems P x ih

end inv

/-! # 6. SC: rf, gwf, po -/

/-- (Lean-only) a refilled byte is the simulated byte. -/
theorem AxScRun.rdbsLookup (img : Int → BitVec 8) (M : MemT) (base : Int) (n j : Nat)
    (x : Nat × BitVec 8) :
    (rdbs img M base n)[j]? = some x → x = AxScRun.rdb img M (accAddr base j) := by
  simp only [rdbs, List.getElem?_map]
  cases hs : (List.range' 0 n)[j]? with
  | none => intro h; cases h
  | some j' =>
    obtain ⟨rfl, _⟩ := lookup_seq.1 hs
    intro h
    simp only [Option.map_some, Option.some.injEq] at h
    rw [← h, Nat.zero_add]

theorem fillRd (img : Int → BitVec 8) (M : MemT) (l : Lbl) (base : Int) (ts : List Nat)
    (vs : List (BitVec 8)) (j t : Nat) (v : BitVec 8) :
    lbRd (fill img M l) = some (base, ts, vs) → ts[j]? = some t → vs[j]? = some v →
    AxScRun.rdb img M (accAddr base j) = (t, v) := by
  intro hrd ht hv
  have key : ∀ n, ts = (rdbs img M base n).map Prod.fst → vs = (rdbs img M base n).map Prod.snd →
      AxScRun.rdb img M (accAddr base j) = (t, v) := by
    intro n hts hvs
    subst hts hvs
    rw [List.getElem?_map] at ht hv
    cases hx : (rdbs img M base n)[j]? with
    | none => rw [hx] at ht; cases ht
    | some x =>
      rw [hx] at ht hv
      simp only [Option.map_some, Option.some.injEq] at ht hv
      rw [← AxScRun.rdbsLookup img M base n j x hx, ← ht, ← hv]
  cases l with
  | LLoad aq b ts0 vs0 =>
    simp only [fill, lbRd, Option.some.injEq, Prod.mk.injEq] at hrd
    obtain ⟨rfl, hts, hvs⟩ := hrd
    exact key _ hts.symm hvs.symm
  | LStore => simp [fill, lbRd] at hrd
  | LFence => simp [fill, lbRd] at hrd
  | LIo => simp [fill, lbRd] at hrd
  | LRmw aq rl b ts0 rvs0 wvs0 c =>
    simp only [fill, lbRd, Option.some.injEq, Prod.mk.injEq] at hrd
    obtain ⟨rfl, hts, hvs⟩ := hrd
    exact key _ hts.symm hvs.symm

theorem lbRdMem (l : Lbl) (base : Int) (ts : List Nat) (vs : List (BitVec 8)) :
    lbRd l = some (base, ts, vs) → lbIsMem l = true := by
  cases l <;> simp [lbRd, lbIsMem, lbIsR]

theorem isAtRMem (rows : List (List Lbl)) (i k : Nat) :
    isAt rows lbIsR i k = true → isAt rows lbIsMem i k = true := by
  simp only [isAt]
  cases lblAt rows (i, k) with
  | none => exact id
  | some l => intro h; simp [lbIsMem, h]

theorem isAtWMem (rows : List (List Lbl)) (i k : Nat) :
    isAt rows lbIsW i k = true → isAt rows lbIsMem i k = true := by
  simp only [isAt]
  cases lblAt rows (i, k) with
  | none => exact id
  | some l => intro h; simp [lbIsMem, h]

theorem lblAtLookup (rows : List (List Lbl)) (i k : Nat) (l : Lbl) :
    lblAt rows (i, k) = some l → ∃ r, rows[i]? = some r ∧ r[k]? = some l := by
  simp only [lblAt]
  cases rows[i]? with
  | none => intro h; cases h
  | some r => intro h; exact ⟨r, rfl, h⟩

/-- The shape `gwf` demands of a label. -/
def AxScRun.gshape (l : Lbl) : Prop :=
  match l with
  | .LLoad _ _ ts vs => vs.length = ts.length
  | .LStore _ _ vs _ => vs ≠ []
  | .LFence _ _ _ _ => True
  | .LRmw _ _ _ ts rvs wvs _ => wvs ≠ [] ∧ wvs.length = ts.length ∧ rvs.length = ts.length
  | .LIo .. => True

theorem fillShape (img : Int → BitVec 8) (M : MemT) (l : Lbl) :
    shapeInB l = true → AxScRun.gshape (fill img M l) := by
  cases l with
  | LLoad => intro _; simp [fill, AxScRun.gshape]
  | LStore => intro h; simpa [shapeInB, AxScRun.gshape, fill] using h
  | LFence => intro _; trivial
  | LIo => intro _; simp [fill, AxScRun.gshape]
  | LRmw =>
    intro h
    simp only [shapeInB, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h
    simp [fill, AxScRun.gshape, rdbs, h]

section sc
variable (img : Int → BitVec 8) (rows : List (List Lbl)) (il : List Geid)
  (ems : List (List Eitem))

theorem prefixGmoLt (p : Nat) (e w : Geid) :
    il.Nodup → il[p]? = some e → w ∈ il.take p → gmoLt (graphOfSc img rows il ems).gtG w e := by
  intro hnd hp hw
  obtain ⟨q, hq⟩ := elem_of_list_lookup_1 hw
  have hql := lookup_lt_Some hq
  rw [List.length_take] at hql
  rw [lookup_take (by omega)] at hq
  refine ⟨elem_of_list_lookup_2 hq, elem_of_list_lookup_2 hp, ?_⟩
  rw [gposOfLookup _ q w hnd hq, gposOfLookup _ p e hnd hp]
  omega

theorem gmoLtPrefix (p : Nat) (e w : Geid) :
    il.Nodup → il[p]? = some e → gmoLt (graphOfSc img rows il ems).gtG w e → w ∈ il.take p := by
  rintro hnd hp ⟨hw, _, hlt⟩
  rw [gposOfLookup _ p e hnd hp] at hlt
  apply elem_of_list_lookup_2 (i := gpos (graphOfSc img rows il ems).gtG w)
  rw [lookup_take hlt]
  exact gposElemLookup _ w hw

theorem gScRf : ilOkB rows il = true → scRf (graphOfSc img rows il ems).gtG := by
  intro hok e a t v ⟨l', base, ts, vs, j, hl', hrd, ht, hv, ha⟩
  obtain ⟨l, hl, hk⟩ := gLblKind img rows il ems e l' hl'
  have hmem : isAt rows lbIsMem e.1 e.2 = true := by
    obtain ⟨i, k⟩ := e
    simp only [isAt]
    simp only [hl]
    rw [← kindMem _ _ hk]
    exact lbRdMem _ _ _ _ hrd
  have hin : e ∈ il := by
    obtain ⟨i, k⟩ := e
    exact (ilOkMem rows il hok i k).2 hmem
  obtain ⟨p, hp⟩ := elem_of_list_lookup_1 hin
  have hnd := ilOkNodup rows il hok
  have hout := outSome img rows il p e l hnd hp hl
  have hl'' : l' = fill img (sim img rows (il.take p)).sM l := by
    rw [gLbl img rows il ems, hl, Option.map_some, hout] at hl'
    simp only [Option.getD_some, Option.some.injEq] at hl'
    exact hl'.symm
  subst hl''
  have hrdb := fillRd img _ l base ts vs j t v hrd ht hv
  rw [ha] at hrdb
  obtain ⟨hnw, hnone, hsome⟩ := invAll img rows il ems (il.take p)
  have hgw : gwrites (graphOfSc img rows il ems).gtG =
      W img rows il ems (il.take p) ++ W img rows il ems (il.drop p) := by
    simp only [W, ← List.filter_append, List.take_append_drop]
    rfl
  simp only [AxScRun.rdb] at hrdb
  cases hM : (sim img rows (il.take p)).sM a with
  | some tv =>
    obtain ⟨t0, v0⟩ := tv
    rw [hM] at hrdb
    simp only [Option.getD_some, Prod.mk.injEq] at hrdb
    obtain ⟨rfl, rfl⟩ := hrdb
    obtain ⟨t', w, rfl, hwt, hwb, hmax⟩ := hsome a _ _ hM
    refine ⟨⟨w, ?_, hwb, ?_⟩, ?_⟩
    · show (gwrites (graphOfSc img rows il ems).gtG)[t']? = some w
      rw [hgw]
      exact lookup_app_l_Some hwt
    · apply prefixGmoLt img rows il ems p e w hnd hp
      exact ((wElem img rows il ems _ w).1 (elem_of_list_lookup_2 hwt)).1
    · intro w' v' hw' hlt
      have hpre := gmoLtPrefix img rows il ems p e w' hnd hp hlt
      have hw'w : w' ∈ W img rows il ems (il.take p) :=
        (wElem img rows il ems _ w').2 ⟨hpre, AxScRun.gwritesByteIsW img rows il ems _ _ _ hw'⟩
      obtain ⟨jj, hjj⟩ := elem_of_list_lookup_1 hw'w
      rw [gwixOfLookup _ jj w' hnd (by rw [hgw]; exact lookup_app_l_Some hjj)]
      have := hmax jj w' v' hjj hw'
      omega
  | none =>
    rw [hM] at hrdb
    simp only [Option.getD_none, Prod.mk.injEq] at hrdb
    obtain ⟨rfl, rfl⟩ := hrdb
    refine ⟨rfl, ?_⟩
    intro w' v' hw' hlt
    exact absurd hw' (hnone a hM w' v' (gmoLtPrefix img rows il ems p e w' hnd hp hlt))

theorem gGwf : shapesOkB rows = true → ilOkB rows il = true → gwf (graphOfSc img rows il ems).gtG := by
  intro hsh hok
  refine ⟨ilOkNodup rows il hok, ?_, ?_⟩
  · intro e
    obtain ⟨i, k⟩ := e
    rw [gmemAt img rows il ems]
    exact ilOkMem rows il hok i k
  · intro i p k l hp hk
    have hl : gxLbl (graphOfSc img rows il ems).gtG (i, k) = some l := by
      simp only [gxLbl]
      rw [hp]
      exact hk
    rw [gLbl img rows il ems] at hl
    cases hl0 : lblAt rows (i, k) with
    | none => rw [hl0] at hl; cases hl
    | some l0 =>
      rw [hl0] at hl
      simp only [Option.map_some, Option.some.injEq] at hl
      subst hl
      have hsh0 : shapeInB l0 = true := by
        obtain ⟨r, hr, hrk⟩ := lblAtLookup _ _ _ _ hl0
        simp only [shapesOkB, forallbForallTrue] at hsh
        exact hsh r (elem_of_list_lookup_2 hr) l0 (elem_of_list_lookup_2 hrk)
      cases ho : (sim img rows il).sOut (i, k) with
      | some l1 =>
        obtain ⟨M, l2, hl2, rfl⟩ := outKind img rows il _ l1 ho
        rw [hl0] at hl2
        cases hl2
        exact fillShape img M l0 hsh0
      | none =>
        have hnin : (i, k) ∉ il := by
          intro hin
          obtain ⟨q, hq⟩ := elem_of_list_lookup_1 hin
          rw [outSome img rows il q (i, k) l0 (ilOkNodup rows il hok) hq hl0] at ho
          cases ho
        have hnm : isAt rows lbIsMem i k = false := by
          cases h : isAt rows lbIsMem i k with
          | false => rfl
          | true => exact absurd ((ilOkMem rows il hok i k).2 h) hnin
        simp only [isAt, hl0] at hnm
        simp only [Option.getD_none]
        cases l0 <;> first | (simp [shapeInB] at hsh0; done) | simp_all [lbIsMem, lbIsR, lbIsW, lbIsIo]

theorem gPo : ilOkB rows il = true → scPoGmo (graphOfSc img rows il ems).gtG := by
  intro hok e1 e2 hpo hm1 hm2
  obtain ⟨i1, k1⟩ := e1
  obtain ⟨i2, k2⟩ := e2
  obtain ⟨hi, hlt, _, _⟩ := hpo
  simp only at hi hlt
  subst hi
  have hm1' : (i1, k1) ∈ (graphOfSc img rows il ems).gtG.gxGmo :=
    (ilOkMem rows il hok _ _).2 ((gmemAt img rows il ems _).1 hm1)
  have hm2' : (i1, k2) ∈ (graphOfSc img rows il ems).gtG.gxGmo :=
    (ilOkMem rows il hok _ _).2 ((gmemAt img rows il ems _).1 hm2)
  have hnd := ilOkNodup rows il hok
  rcases gmoLtTotal _ (i1, k1) (i1, k2) hnd hm1' hm2'
      (by intro h; simp only [Prod.mk.injEq] at h; omega) with h | h
  · exact h
  · exfalso
    obtain ⟨_, _, hpos⟩ := h
    have L1 := gposElemLookup (graphOfSc img rows il ems).gtG _ hm1'
    have L2 := gposElemLookup (graphOfSc img rows il ems).gtG _ hm2'
    have := ilOkOrder rows il hok _ _ i1 k1 k2 L1 L2 hpos
    omega

end sc

/-! # 7. Dependencies: well-formed (sources are reads, targets the right kind) -/

theorem emsOkItems (rows : List (List Lbl)) (ems : List (List Eitem)) (i : Nat)
    (es : List Eitem) :
    emsOkB rows ems = true → ems[i]? = some es → ∀ it, it ∈ es → itemOkB rows i it = true := by
  intro H hes it hit
  simp only [emsOkB, forallbForallTrue] at H
  exact H (i, es) (elem_of_lookup_imap.2 ⟨i, es, rfl, hes⟩) it hit

theorem elemGdepsOf (d : Tdep) (ems : List (List Eitem)) :
    d ∈ gdepsOf ems ↔
    ∃ i es dd, ems[i]? = some es ∧ dd ∈ rowDepsT es ∧ d = (((i, dd.1.1), (i, dd.1.2)), dd.2) := by
  simp only [gdepsOf, elem_of_list_join]
  constructor
  · rintro ⟨L, hd, hL⟩
    obtain ⟨i, es, rfl, hes⟩ := elem_of_lookup_imap.1 hL
    obtain ⟨dd, rfl, hdd⟩ := elem_of_list_fmap.1 hd
    exact ⟨i, es, dd, hes, hdd, rfl⟩
  · rintro ⟨i, es, dd, hes, hdd, rfl⟩
    exact ⟨liftDeps i (rowDepsT es), elem_of_list_fmap.2 ⟨dd, rfl, hdd⟩,
      elem_of_lookup_imap.2 ⟨i, es, rfl, hes⟩⟩

/-- (Lean-only) the shape of a read item's edges. -/
theorem AxScRun.dedgesRMem (s : DstateT) (k0 : Nat) (asrc : List Dsrc) (j k : Nat) (tg : Dtag) :
    ((j, k), tg) ∈ dedgesR s k0 asrc →
    k = k0 ∧ dtagW tg = false ∧ (j ∈ dtsrcs s asrc ∨ j ∈ ctxProv s) := by
  simp only [dedgesR, List.mem_append, elemOfTagEdges]
  rintro (⟨rfl, rfl, hj, -⟩ | ⟨rfl, rfl, hj, -⟩)
  · exact ⟨rfl, rfl, .inl hj⟩
  · exact ⟨rfl, rfl, .inr hj⟩

/-- (Lean-only) the shape of a write item's edges. -/
theorem AxScRun.dedgesWMem (s : DstateT) (k0 : Nat) (asrc vsrc : List Dsrc) (j k : Nat)
    (tg : Dtag) :
    ((j, k), tg) ∈ dedgesW s k0 asrc vsrc →
    k = k0 ∧ (j ∈ dtsrcs s asrc ∨ j ∈ dtsrcs s vsrc ∨ j ∈ s.dtCtl ∨ j ∈ s.dtLd ∨
      j ∈ s.dtAdr ∨ j ∈ ctxProv s) := by
  simp only [dedgesW, List.mem_append, elemOfTagEdges]
  rintro (⟨rfl, rfl, hj, -⟩ | ⟨rfl, rfl, hj, -⟩ | ⟨rfl, rfl, hj, -⟩ | ⟨rfl, rfl, hj, -⟩ |
    ⟨rfl, rfl, hj, -⟩ | ⟨rfl, rfl, hj, -⟩)
  · exact ⟨rfl, .inl hj⟩
  · exact ⟨rfl, .inr (.inl hj)⟩
  · exact ⟨rfl, .inr (.inr (.inl hj))⟩
  · exact ⟨rfl, .inr (.inr (.inr (.inl hj)))⟩
  · exact ⟨rfl, .inr (.inr (.inr (.inr (.inl hj))))⟩
  · exact ⟨rfl, .inr (.inr (.inr (.inr (.inr hj))))⟩

section deps
variable (rows : List (List Lbl)) (i : Nat)

def Rd (j : Nat) : Prop := isAt rows lbIsR i j = true

def dinv (s : DstateT) : Prop :=
  (∀ r j, j ∈ dprov (dsOfT s) r → Rd rows i j) ∧ (∀ j, j ∈ s.dtLd → Rd rows i j) ∧
  (∀ j, j ∈ s.dtCtl → Rd rows i j) ∧ (∀ j, j ∈ s.dtAdr → Rd rows i j)

theorem dinvInit : dinv rows i dtInit := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;> simp_all [dprov, dsOfT, dtInit]

theorem dinvSrcs (s : DstateT) (xs : List Dsrc) (j : Nat) :
    dinv rows i s → j ∈ dtsrcs s xs → Rd rows i j := by
  rintro ⟨hp, hl, _, _⟩
  simp only [dtsrcs, dsrcsPos, elem_of_list_join]
  rintro ⟨L, hjL, hL⟩
  obtain ⟨x, rfl, _⟩ := elem_of_list_fmap.1 hL
  cases x with
  | DReg r => exact hp r j hjL
  | DLdRes => exact hl j hjL

theorem dinvCtx (s : DstateT) (j : Nat) : dinv rows i s → j ∈ ctxProv s → Rd rows i j := by
  rintro ⟨hp, _⟩
  simp only [ctxProv, elem_of_list_join]
  rintro ⟨L, hjL, hL⟩
  obtain ⟨r, rfl, _⟩ := elem_of_list_fmap.1 hL
  exact hp r j hjL

theorem dinvAcc (s : DstateT) (xs : List Dsrc) (j : Nat) :
    dinv rows i s → j ∈ dtAcc s xs → Rd rows i j := by
  intro hd
  simp only [dtAcc, nodupApp, List.mem_append, elem_of_list_filter]
  rintro (hj | ⟨_, hj⟩)
  · exact hd.2.2.2 j hj
  · exact dinvSrcs rows i s xs j hd hj

/-- (Lean-only) every source a write item draws on is a read. -/
theorem AxScRun.dinvWSrcs (s : DstateT) (asrc vsrc : List Dsrc) (j : Nat) :
    dinv rows i s →
    (j ∈ dtsrcs s asrc ∨ j ∈ dtsrcs s vsrc ∨ j ∈ s.dtCtl ∨ j ∈ s.dtLd ∨
      j ∈ s.dtAdr ∨ j ∈ ctxProv s) → Rd rows i j := by
  intro hd
  rintro (h | h | h | h | h | h)
  · exact dinvSrcs rows i s _ j hd h
  · exact dinvSrcs rows i s _ j hd h
  · exact hd.2.2.1 j h
  · exact hd.2.1 j h
  · exact hd.2.2.2 j h
  · exact dinvCtx rows i s j hd h

theorem dinvStep (s : DstateT) (it : Eitem) :
    dinv rows i s → itemOkB rows i it = true → dinv rows i (dstepT s it).1 := by
  intro hd hok
  obtain ⟨hp, hl, hc, ha⟩ := hd
  obtain ⟨l, ko⟩ := it
  have hd : dinv rows i s := ⟨hp, hl, hc, ha⟩
  -- the load-like arms: push k (a read) and accumulate the address sources
  have hload : ∀ (k : Nat) (asrc : List Dsrc), isAt rows lbIsR i k = true →
      dinv rows i ⟨s.dtProv, k :: s.dtLd, s.dtCtl, dtAcc s asrc⟩ := by
    intro k asrc hr
    refine ⟨hp, ?_, hc, fun j => dinvAcc rows i s asrc j hd⟩
    intro j hj
    rcases List.mem_cons.1 hj with rfl | hj
    · exact hr
    · exact hl j hj
  have hstore : ∀ asrc : List Dsrc,
      dinv rows i ⟨s.dtProv, s.dtLd, s.dtCtl, dtAcc s asrc⟩ :=
    fun asrc => ⟨hp, hl, hc, fun j => dinvAcc rows i s asrc j hd⟩
  cases l with
  | LSilent => exact hd
  | LDev kd =>
    -- W13 (F-dep) (2): an SC-run emission has no positioned MMIO item (`itemOkB`)
    cases ko with
    | none => cases kd <;> exact hd
    | some k =>
      cases kd
      · simp [itemOkB, elbIsIoRd] at hok
      · simp [itemOkB, elbIsIoRd, elbIsIoWr] at hok
      · exact hd
  | LFence => exact hd
  | LIFetch => exact hd
  | LInstr =>
    refine ⟨hp, ?_, hc, ha⟩
    intro j hj; exact absurd hj List.not_mem_nil
  | LRegW rd srcs =>
    refine ⟨?_, hl, hc, ha⟩
    intro r j
    simp only [dstepT, dprov, dsOfT, dprovSet]
    by_cases hr : r = rd
    · rw [if_pos hr]; exact dinvSrcs rows i s srcs j hd
    · rw [if_neg hr]; exact hp r j
  | LCtrl srcs =>
    refine ⟨hp, hl, ?_, ha⟩
    intro j hj
    simp only [dstepT, List.mem_append] at hj
    rcases hj with hj | hj
    · exact hc j hj
    · exact dinvSrcs rows i s srcs j hd hj
  | LLoad =>
    cases ko with
    | none => exact hd
    | some k =>
      simp only [itemOkB, elbIsIoRd, elbIsIoWr, Bool.not_false, Bool.true_and, elbIsR, elbIsW, Bool.not_true, Bool.false_or, Bool.not_false,
        Bool.true_or, Bool.and_true] at hok
      exact hload k _ hok
  | LExLoad =>
    cases ko with
    | none => exact hd
    | some k =>
      simp only [itemOkB, elbIsIoRd, elbIsIoWr, Bool.not_false, Bool.true_and, elbIsR, elbIsW, Bool.not_true, Bool.false_or, Bool.not_false,
        Bool.true_or, Bool.and_true] at hok
      exact hload k _ hok
  | LRmw =>
    cases ko with
    | none => exact hd
    | some k =>
      simp only [itemOkB, elbIsIoRd, elbIsIoWr, Bool.not_false, Bool.true_and, elbIsR, elbIsW, Bool.not_true, Bool.false_or, Bool.and_eq_true] at hok
      exact hload k _ hok.1
  | LStore =>
    cases ko with
    | none => exact hd
    | some k => exact hstore _
  | LExStore =>
    cases ko with
    | none => exact hd
    | some k => exact hstore _

theorem dstepEdge (s : DstateT) (it : Eitem) (j k : Nat) (tg : Dtag) :
    dinv rows i s → itemOkB rows i it = true → ((j, k), tg) ∈ (dstepT s it).2 →
    Rd rows i j ∧
      (if dtagW tg then isAt rows lbIsW i k else isAt rows lbIsMem i k) = true := by
  intro hd hok hin
  obtain ⟨l, ko⟩ := it
  cases ko with
  | none => cases l <;> simp [dstepT] at hin
  | some k' =>
    have hR : ∀ asrc, ((j, k), tg) ∈ dedgesR s k' asrc → isAt rows lbIsR i k' = true →
        Rd rows i j ∧
          (if dtagW tg then isAt rows lbIsW i k else isAt rows lbIsMem i k) = true := by
      intro asrc h hr
      obtain ⟨rfl, htg, hj⟩ := AxScRun.dedgesRMem s k' asrc j k tg h
      refine ⟨?_, ?_⟩
      · rcases hj with hj | hj
        · exact dinvSrcs rows i s asrc j hd hj
        · exact dinvCtx rows i s j hd hj
      · rw [htg]; exact isAtRMem rows i k hr
    have hW : ∀ asrc vsrc, ((j, k), tg) ∈ dedgesW s k' asrc vsrc →
        isAt rows lbIsW i k' = true →
        Rd rows i j ∧
          (if dtagW tg then isAt rows lbIsW i k else isAt rows lbIsMem i k) = true := by
      intro asrc vsrc h hw
      obtain ⟨rfl, hj⟩ := AxScRun.dedgesWMem s k' asrc vsrc j k tg h
      refine ⟨AxScRun.dinvWSrcs rows i s asrc vsrc j hd hj, ?_⟩
      split
      · exact hw
      · exact isAtWMem rows i k hw
    cases l with
    | LLoad =>
      simp only [itemOkB, elbIsIoRd, elbIsIoWr, Bool.not_false, Bool.true_and, elbIsR, elbIsW, Bool.not_true, Bool.false_or, Bool.not_false,
        Bool.true_or, Bool.and_true] at hok
      exact hR _ hin hok
    | LExLoad =>
      simp only [itemOkB, elbIsIoRd, elbIsIoWr, Bool.not_false, Bool.true_and, elbIsR, elbIsW, Bool.not_true, Bool.false_or, Bool.not_false,
        Bool.true_or, Bool.and_true] at hok
      exact hR _ hin hok
    | LStore =>
      simp only [itemOkB, elbIsIoRd, elbIsIoWr, Bool.not_false, Bool.true_and, elbIsR, elbIsW, Bool.not_true, Bool.false_or, Bool.not_false,
        Bool.true_or, Bool.true_and] at hok
      exact hW _ _ hin hok
    | LExStore =>
      simp only [itemOkB, elbIsIoRd, elbIsIoWr, Bool.not_false, Bool.true_and, elbIsR, elbIsW, Bool.not_true, Bool.false_or, Bool.not_false,
        Bool.true_or, Bool.true_and] at hok
      exact hW _ _ hin hok
    | LRmw =>
      simp only [itemOkB, elbIsIoRd, elbIsIoWr, Bool.not_false, Bool.true_and, elbIsR, elbIsW, Bool.not_true, Bool.false_or, Bool.and_eq_true] at hok
      exact hW _ _ hin hok.2
    | LDev kd =>
      cases kd
      · simp [itemOkB, elbIsIoRd] at hok
      · simp [itemOkB, elbIsIoRd, elbIsIoWr] at hok
      · simp [dstepT] at hin
    | _ => simp [dstepT] at hin

theorem rowEdges (s : DstateT) (es : List Eitem) (j k : Nat) (tg : Dtag) :
    dinv rows i s → (∀ it, it ∈ es → itemOkB rows i it = true) →
    ((j, k), tg) ∈ rowDepsTAux s es →
    Rd rows i j ∧
      (if dtagW tg then isAt rows lbIsW i k else isAt rows lbIsMem i k) = true := by
  induction es generalizing s with
  | nil => intro _ _ h; exact absurd h List.not_mem_nil
  | cons it es ih =>
    intro hd hall hin
    simp only [rowDepsTAux, List.mem_append] at hin
    rcases hin with hin | hin
    · exact dstepEdge rows i s it j k tg hd (hall it (List.mem_cons_self ..)) hin
    · exact ih _ (dinvStep rows i s it hd (hall it (List.mem_cons_self ..)))
        (fun it' h => hall it' (List.mem_cons_of_mem _ h)) hin

end deps

theorem gDepsWf (img : Int → BitVec 8) (rows : List (List Lbl)) (il : List Geid)
    (ems : List (List Eitem)) :
    emsOkB rows ems = true →
    gtdepsWf (graphOfSc img rows il ems).gtG (graphOfSc img rows il ems).gtDeps := by
  intro hems d hd
  obtain ⟨i, es, ⟨⟨j, k⟩, tg⟩, hes, hdd, rfl⟩ := (elemGdepsOf d ems).1 hd
  have hlt := rowDepsTLt es j k tg hdd
  obtain ⟨hr, ht⟩ := rowEdges rows i dtInit es j k tg (dinvInit rows i)
    (emsOkItems _ _ _ _ hems hes) hdd
  refine ⟨rfl, hlt, glblIsRTOfR _ _ ((glblIsAt img rows il ems lbIsR (i, j) kindR).2 hr), ?_⟩
  simp only
  cases htg : dtagW tg
  · simp only [htg, Bool.false_eq_true, if_false] at ht ⊢
    exact (gmemAt img rows il ems (i, k)).2 ht
  · simp only [htg, if_true] at ht ⊢
    exact glblIsWTOfW _ _ ((glblIsAt img rows il ems lbIsW (i, k) kindW).2 ht)

/-! # 8. THE CAPSTONES (i): SC, hence the tagged model -/

theorem graphOfScSc (img : Int → BitVec 8) (rows : List (List Lbl)) (il : List Geid)
    (ems : List (List Eitem)) :
    scInputsOkB rows il ems = true → scGraph (graphOfSc img rows il ems) := by
  simp only [scInputsOkB, Bool.and_eq_true]
  rintro ⟨⟨hsh, hok⟩, hems⟩
  exact ⟨gGwf img rows il ems hsh hok, gPo img rows il ems hok, gScRf img rows il ems hok,
    gDepsWf img rows il ems hems⟩

theorem graphOfScCatT (img : Int → BitVec 8) (rows : List (List Lbl)) (il : List Geid)
    (ems : List (List Eitem)) :
    scInputsOkB rows il ems = true → rvwmoCatConsistentT (graphOfSc img rows il ems) :=
  fun h => scGraphCatT _ (graphOfScSc img rows il ems h)

/-! # 9. THE CAPSTONE (ii): ctrl closure at graph level -/

theorem dstepTTgt (s : DstateT) (it : Eitem) (j k : Nat) (tg : Dtag) :
    ((j, k), tg) ∈ (dstepT s it).2 → it.2 = some k := by
  obtain ⟨l, ko⟩ := it
  cases ko with
  | none => cases l <;> simp [dstepT]
  | some k' =>
    intro h
    simp only
    cases l with
    | LLoad => rw [(AxScRun.dedgesRMem _ _ _ _ _ _ h).1]
    | LExLoad => rw [(AxScRun.dedgesRMem _ _ _ _ _ _ h).1]
    | LStore => rw [(AxScRun.dedgesWMem _ _ _ _ _ _ _ h).1]
    | LExStore => rw [(AxScRun.dedgesWMem _ _ _ _ _ _ _ h).1]
    | LRmw => rw [(AxScRun.dedgesWMem _ _ _ _ _ _ _ h).1]
    | LDev kd =>
      cases kd
      · rw [(AxScRun.dedgesRMem _ _ _ _ _ _ h).1]
      · rw [(AxScRun.dedgesWMem _ _ _ _ _ _ _ h).1]
      · simp [dstepT] at h
    | _ => simp [dstepT] at h

theorem rowTgt (s : DstateT) (es : List Eitem) (j k : Nat) (tg : Dtag) :
    ((j, k), tg) ∈ rowDepsTAux s es → ∃ it, it ∈ es ∧ it.2 = some k := by
  induction es generalizing s with
  | nil => intro h; exact absurd h List.not_mem_nil
  | cons it es ih =>
    intro h
    simp only [rowDepsTAux, List.mem_append] at h
    rcases h with h | h
    · exact ⟨it, List.mem_cons_self .., dstepTTgt s it j k tg h⟩
    · obtain ⟨it', hin, hk⟩ := ih _ h
      exact ⟨it', List.mem_cons_of_mem _ hin, hk⟩

theorem monoBGe (k : Nat) (es : List Eitem) (it : Eitem) (k' : Nat) :
    monoB k es = true → it ∈ es → it.2 = some k' → k ≤ k' := by
  induction es generalizing k with
  | nil => intro _ h; exact absurd h List.not_mem_nil
  | cons it0 es ih =>
    intro hm hin hk
    simp only [monoB] at hm
    rcases List.mem_cons.1 hin with rfl | hin
    · rw [hk, Bool.and_eq_true, decide_eq_true_eq] at hm
      exact hm.1
    · cases h0 : it0.2 with
      | some k1 =>
        rw [h0, Bool.and_eq_true, decide_eq_true_eq] at hm
        have := ih k1 hm.2 hin hk
        omega
      | none =>
        rw [h0] at hm
        exact ih k hm hin hk

theorem monoBTail (k0 : Nat) (es1 : List Eitem) (it : Eitem) (es2 : List Eitem) (k : Nat)
    (it' : Eitem) (k' : Nat) :
    monoB k0 (es1 ++ it :: es2) = true → it.2 = some k → it' ∈ es2 → it'.2 = some k' →
    k ≤ k' := by
  induction es1 generalizing k0 with
  | nil =>
    intro hm hk hin hk'
    simp only [List.nil_append, monoB, hk, Bool.and_eq_true] at hm
    exact monoBGe k es2 it' k' hm.2 hin hk'
  | cons x es1 ih =>
    intro hm hk hin hk'
    simp only [List.cons_append, monoB] at hm
    cases hx : x.2 with
    | some k1 =>
      rw [hx, Bool.and_eq_true] at hm
      exact ih k1 hm.2 hk hin hk'
    | none =>
      rw [hx] at hm
      exact ih k0 hm hk hin hk'

theorem coverBSpec (rows : List (List Lbl)) (i : Nat) (es : List Eitem) (k : Nat) :
    AxScRun.coverB rows i es = true → isAt rows lbIsW i k = true →
    ∃ it, it ∈ es ∧ it.2 = some k ∧ elbIsW it.1 = true := by
  intro H hw
  simp only [AxScRun.coverB, forallbForallTrue] at H
  have hks : k ∈ List.range' 0 (rowLen rows i) := by
    have := isAtLt _ _ _ _ hw
    exact elem_of_seq.2 ⟨Nat.zero_le _, by omega⟩
  have h := H k hks
  rw [hw, Bool.not_true, Bool.false_or, existsbExistsTrue] at h
  obtain ⟨it, hin, hit⟩ := h
  cases hk : it.2 with
  | none => rw [hk] at hit; cases hit
  | some k' =>
    rw [hk, Bool.and_eq_true, decide_eq_true_eq] at hit
    obtain ⟨hkk, hw'⟩ := hit
    subst hkk
    exact ⟨it, hin, hk, hw'⟩

theorem ctrlOkHart (rows : List (List Lbl)) (ems : List (List Eitem)) (i : Nat)
    (es : List Eitem) :
    ctrlOkB rows ems = true → ems[i]? = some es →
    monoB 0 es = true ∧ AxScRun.coverB rows i es = true := by
  intro H hes
  simp only [ctrlOkB, forallbForallTrue] at H
  have h := H (i, es) (elem_of_lookup_imap.2 ⟨i, es, rfl, hes⟩)
  rw [Bool.and_eq_true] at h
  exact h

theorem graphOfScCtrlClosed (img : Int → BitVec 8) (rows : List (List Lbl)) (il : List Geid)
    (ems : List (List Eitem)) :
    ctrlOkB rows ems = true → ctrlClosed (graphOfSc img rows il ems) := by
  intro hok r w e hin hpo hw
  obtain ⟨i, es, ⟨⟨j, k⟩, tg⟩, hes, hdd, heq⟩ := (elemGdepsOf _ ems).1 hin
  simp only [Prod.mk.injEq] at heq
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := heq
  obtain ⟨i', k'⟩ := e
  obtain ⟨hi, hlt, _, _⟩ := hpo
  simp only at hi hlt
  subst hi
  have hw' := (glblIsAt img rows il ems lbIsW (i, k') kindW).1 hw
  simp only at hw'
  obtain ⟨hmono, hcov⟩ := ctrlOkHart rows ems i es hok hes
  obtain ⟨it, hit, hk', hitw⟩ := coverBSpec rows i es k' hcov hw'
  obtain ⟨es1, es2, rfl⟩ := elem_of_list_split hit
  apply (elemGdepsOf _ ems).2
  refine ⟨i, es1 ++ it :: es2, ((j, k'), DTctrl), hes, ?_, rfl⟩
  apply rowDepsTCtrlClosed es1 it es2 j k k' _ hk' hitw hlt
  rw [rowDepsT, AxScCat.rowDepsTAuxApp, List.mem_append] at hdd
  rcases hdd with h | h
  · exact h
  · simp only [rowDepsTAux, List.mem_append] at h
    rcases h with h | h
    · have := dstepTTgt _ it j k DTctrl h
      rw [hk'] at this
      cases this
      omega
    · obtain ⟨it', hit', hk''⟩ := rowTgt _ es2 j k DTctrl h
      have := monoBTail 0 es1 it es2 k' it' k hmono hk' hit' hk''
      omega

/-! # 10. (iii) The read values: SC values, and the input-row bridge -/

/-- The graph label of a simulated event is the row label refilled from the memory after the
il-prefix before it: the graph's read values ARE the values an SC execution along `il` reads. -/
theorem graphOfScValue (img : Int → BitVec 8) (rows : List (List Lbl)) (il : List Geid)
    (ems : List (List Eitem)) (p i k : Nat) (l : Lbl) :
    ilOkB rows il = true → il[p]? = some (i, k) → lblAt rows (i, k) = some l →
    gxLbl (graphOfSc img rows il ems).gtG (i, k) =
      some (fill img (sim img rows (il.take p)).sM l) := by
  intro hok hp hl
  rw [gLbl img rows il ems, hl, Option.map_some,
    outSome img rows il p (i, k) l (ilOkNodup rows il hok) hp hl]
  rfl

theorem bvsEqbSpec (xs ys : List (BitVec 8)) : bvsEqb xs ys = true → xs = ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp [bvsEqb]
  | cons x xs ih =>
    cases ys with
    | nil => simp [bvsEqb]
    | cons y ys =>
      simp only [bvsEqb, Bool.and_eq_true, decide_eq_true_eq]
      rintro ⟨rfl, h⟩
      rw [ih ys h]

theorem lvEqbSpec (o o' : Option (List (BitVec 8))) : lvEqb o o' = true → o = o' := by
  cases o <;> cases o' <;> simp only [lvEqb, reduceCtorEq, imp_false, Bool.false_eq_true,
    not_false_eq_true, forall_const]
  intro h
  rw [bvsEqbSpec _ _ h]

theorem eraseFill (img : Int → BitVec 8) (M : MemT) (l : Lbl) :
    AxScRun.lv (fill img M l) = AxScRun.lv l → erase (fill img M l) = erase l := by
  cases l <;> simp [fill, AxScRun.lv, erase]

/-- THE BRIDGE.  If the input rows already carry the SC values, the graph's rows ARE the input
rows up to read timestamps — so a run driven on the input rows is a run on the graph's rows
(`AxScRun2.drive2Erase`). -/
theorem graphOfScErase (img : Int → BitVec 8) (rows : List (List Lbl)) (il : List Geid)
    (ems : List (List Eitem)) (i : Nat) :
    valsOkB img rows il = true →
    (rowOf (graphOfSc img rows il ems).gtG i).map erase = ((rows[i]?).getD []).map erase := by
  intro hv
  simp only [rowOf, graphOfSc, scProg, list_lookup_imap]
  cases hr : rows[i]? with
  | none => rfl
  | some r =>
    simp only [Option.map_some, Option.getD_some]
    apply list_eq
    intro k
    simp only [list_lookup_fmap, list_lookup_imap]
    cases hk : r[k]? with
    | none => rfl
    | some l =>
      simp only [Option.map_some, Option.some.injEq]
      cases ho : (sim img rows il).sOut (i, k) with
      | none => rfl
      | some l' =>
        obtain ⟨M, l0, hl0, rfl⟩ := outKind img rows il _ l' ho
        simp only [lblAt, hr, Option.bind_some, hk, Option.some.injEq] at hl0
        subst hl0
        simp only [Option.getD_some]
        apply eraseFill
        apply lvEqbSpec
        simp only [valsOkB, forallbForallTrue] at hv
        have h1 := hv (i, r) (elem_of_lookup_imap.2 ⟨i, r, rfl, hr⟩) (k, l)
          (elem_of_lookup_imap.2 ⟨k, l, rfl, hk⟩)
        simp only [ho] at h1
        exact h1

/-! # 11. Sanity: a 2-hart message-passing instance, end to end -/

namespace ScRunSanity

/-- Hart 0: W x=1; fence rw,w; W y=1.  Hart 1: R y; R x (values/ts junk: `graphOfSc` refills
them).  x = 0, y = 1. -/
def mpRows : List (List Lbl) :=
  [[Lbl.LStore false 0 [b1] .WCplain,
    Lbl.LFence true true false true,
    Lbl.LStore false 1 [b1] .WCplain],
   [Lbl.LLoad false 1 [] [b0],
    Lbl.LLoad false 0 [] [b0]]]

/-- Emissions: hart 1's second load is ADDRESS-dependent on its first (an addr edge into a
read), and a branch on it ctrl-guards nothing. -/
def r5 : Nat := 5

def mpEms : List (List Eitem) :=
  [[(LStore false 0 [b1] [] [], some 0),
    (LFence true true false true, some 1),
    (LStore false 1 [b1] [] [], some 2)],
   [(LLoad false false 1 [(0, b0)] [], some 0),
    (LRegW r5 [.DLdRes], none),
    (LCtrl [.DReg r5], none),
    (LLoad false false 0 [(0, b0)] [.DReg r5], some 1)]]

/-- Interleaving: hart 0 entirely, then hart 1 — hart 1 sees both writes. -/
def mpIl : List Geid := [(0, 0), (0, 2), (1, 0), (1, 1)]

def mp : GdexecT := graphOfSc (fun _ => b0) mpRows mpIl mpEms

theorem mpInputs : scInputsOkB mpRows mpIl mpEms = true := by decide +kernel

theorem mpCtrl : ctrlOkB mpRows mpEms = true := by decide +kernel

theorem mpCatT : rvwmoCatConsistentT mp := graphOfScCatT _ _ _ _ mpInputs

theorem mpCtrlClosed : ctrlClosed mp := graphOfScCtrlClosed _ _ _ _ mpCtrl

/-- NOT VACUOUS: the deps are nonempty (the addr edge (1,0)→(1,1)), and hart 1's reads got the
WRITTEN values with the right write indices (y from W y = write 2, x from W x = write 1). -/
theorem mpDeps : mp.gtDeps = [(((1, 0), (1, 1)), DTaddr)] := by decide +kernel

theorem mpReads :
    mp.gtG.gxProg[1]? =
      some [Lbl.LLoad false 1 [2] [b1], Lbl.LLoad false 0 [1] [b1]] := by decide +kernel

/-- The independent cubic decision procedure agrees. -/
theorem mpScB : scGraphB mp = true := by decide +kernel

/-- A po-violating interleaving is rejected by the cheap check. -/
theorem mpBadIl : ilOkB mpRows [(0, 2), (0, 0), (1, 0), (1, 1)] = false := by decide +kernel

end ScRunSanity

end Weak
