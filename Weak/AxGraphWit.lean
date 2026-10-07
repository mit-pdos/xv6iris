/-
Weak: **the G0.5 witness graphs, verdicts PROVED** (AxSL tier).

Rocq: `iris/AxGraphWit.v` @ xxvzwolszwmp.

The Rocq header, in substance (design: `claude-notes/design/weak-memory-lb-axsl.md`
§2 gate G0.5, rev 4 amendments: rule 12, the `r12` witness replacing the
deferral graph).  PURE (no Iris).

Every witness is a concrete `Gdexec` built like `WeakRvwmoGraph.lbgd` (tiny
addresses 0/1/2, values `b0`/`b1`/`b2`, the all-zero image).  A HOLDS verdict is
`AxGraphDec.catConsistentBSound` + `decide +kernel`; a FAILS verdict is one
offending edge + one gmo comparison, both computed (`notMinusOfPoloc` /
`notCatOfRule12`).  Only the fraction-flow invariants (§5) are proved by hand —
they are general theorems.

  §1 `fwd`  FWD+acq: cat-consistent, NOT RVWMO⁻-consistent — the two models are
            SEPARATED, and `ownForwardCat'` is exercised non-vacuously on it.
  §2 `rel`  release-then-read: the releasing hart's own later read takes the
            OTHER hart's write — "rfi from the last own write" is not a rule.
  §3 `cyc`  the ob ∪ poloc(W→R) cycle: cat-consistent, and
            `tc (gobCat ∪ gpolocWR)` is reflexive at the forwarded read — so a
            same-hart same-byte flow edge MUST carry the gmo condition.
  §4 `str`  the stranded-token graph W a; R a; R a with the reads gmo-inverted:
            cat-consistent (rule 2 exempts same-source pairs), NOT RVWMO⁻.
  §5        the FRACTION-FLOW PROTOTYPE: dyadic pieces, a read halves an
            eligible holder's piece, a write re-ties the whole token.  General
            theorem `trunFracNoStrand`: under rule 1 and gmo-order processing
            no read is ever stranded and the latest write's node retains a piece.
  §6 `r12`  RULE 12 is load-bearing: consistent under the SIX program-order arms
            alone, INCONSISTENT once rule 12 is in.
  §7 `lbgd` LB is cat-consistent (via `minusImpliesCat`, and by the checker).

CORRECTIONS TO THE COMMISSIONED STATEMENTS (Rocq header, kept): (1) the naive
full-token move strands a read in BOTH orders (`naivePo` strands r2, `naiveGmo`
strands r1); only the fractional flow strands nobody (`fracGmo`, `fracPo`).
(2) Rule 12 over `gdDeps` over-approximates riscv.cat (control deps are not
tagged apart); `r12` uses a genuine DATA dependency, so the verdict stands.

FETCHES (Stage C, D1 reversed: fetches are not graph events): nothing here involves
a fetch — every `LLoad` row item is a data load; no row or `decide` check changed.

**Deviations from Rocq.**

1. NAMES: lowerCamelCase; types capitalised (`tev` ↦ `Tev`, `tpol` ↦ `Tpol`,
   `tres` ↦ `Tres`).  Duplicated Rocq names (`notes/weak-port-dupnames.json`)
   are file-qualified: `AxGraphWit.imgw`, `.mkgd`, `.fwdCat`, `.rel`, `.Tev`,
   `.Tres`, `.trun`, `.tw`, `.lbCat`.
2. VOCABULARY: as `AxGraphDec` deviation 2 — `vm_compute; reflexivity` ↦
   `decide +kernel`; `existsb`/`forallb` ↦ `List.any`/`List.all`; `bool_decide`
   / `Nat.ltb` / `Nat.eqb` ↦ `decide`; `<[i := x]> l` ↦ `l.set i x`;
   `delete i l` ↦ `l.eraseIdx i`; `list_find` ↦ `listFind` (Bool predicate
   `fun p => holderOk e p.1` for Rocq's `holder_ok e p.1 = true`);
   `fold_right` ↦ `List.foldr`, `fold_left` ↦ `List.foldl`.
3. `tev_eq_dec` ↦ `deriving DecidableEq` on `Tev` (also on `Tres`/`Tpol`, so
   the closed run verdicts are `decide +kernel`).
4. `rule1Ok` (a Rocq `Fixpoint … : Prop`) is a structurally recursive `def`.

**Name map** (Rocq → Lean): `imgw` ↦ `AxGraphWit.imgw`; `mkgd` ↦
`AxGraphWit.mkgd`; `fwd`; `fwd_cat` ↦ `AxGraphWit.fwdCat`; `fwd_not_minus` ↦
`fwdNotMinus`; `fwd_own_forward` ↦ `fwdOwnForward`; `rel` ↦ `AxGraphWit.rel`;
`rel_cat` ↦ `relCat`; `rel_rf` ↦ `relRf`; `cyc`; `cyc_cat` ↦ `cycCat`;
`cyc_not_minus` ↦ `cycNotMinus`; `gpoloc_WR` ↦ `gpolocWR`; `gob_poloc` ↦
`gobPoloc`; `cyc_cycle` ↦ `cycCycle`; `cyc_ob_cat_acyclic` ↦
`cycObCatAcyclic`; `str`; `str_cat` ↦ `strCat`; `str_not_minus` ↦
`strNotMinus`; `str_shape` ↦ `strShape`; `tev` ↦ `AxGraphWit.Tev` (`TEv` ↦
`.mk`, `te_id/te_w/te_po/te_gmo` ↦ `teId/teW/tePo/teGmo`); `tev_eq_dec` ↦
derived; `tann`; `tholds`; `holder_ok` ↦ `holderOk`; `tpol` ↦ `Tpol`
(`PFrac`, `PNaive`); `tres` ↦ `AxGraphWit.Tres` (`TOk`, `TStranded`); `tread`;
`twrite`; `tstep`; `trun` ↦ `AxGraphWit.trun`; `tsum_ok` ↦ `tsumOk`; `tw` ↦
`AxGraphWit.tw`; `tr1`; `tr2`; `po_order` ↦ `poOrder`; `gmo_order` ↦
`gmoOrder`; `frac_gmo` ↦ `fracGmo`; `frac_po` ↦ `fracPo`; `naive_po` ↦
`naivePo`; `naive_gmo` ↦ `naiveGmo`; `tholds_insert` ↦ `tholdsInsert`;
`tread_frac_holds` ↦ `treadFracHolds`; `twrite_holds` ↦ `twriteHolds`;
`rule1_ok` ↦ `rule1Ok`; `last_write` ↦ `lastWrite`; `tinv`; `tstep_frac_ok` ↦
`tstepFracOk`; `trun_frac_no_strand` ↦ `trunFracNoStrand`;
`frac_never_strands` ↦ `fracNeverStrands`; `frac_writer_retains` ↦
`fracWriterRetains`; `gmo_order_rule1` ↦ `gmoOrderRule1`; `str_frac_ok` ↦
`strFracOk`; `r12`; `r12_cat6` ↦ `r12Cat6`; `r12_not_cat` ↦ `r12NotCat`;
`r12_edge` ↦ `r12Edge`; `lb_cat` ↦ `AxGraphWit.lbCat`; `lb_cat_b` ↦ `lbCatB`.

**Not ported:** nothing (the `Ltac vmr` is `decide +kernel`; the §8
`Print Assumptions` block has no Lean twin — the lint's axiom check covers it).
-/
import Weak.AxGraphDec

namespace Weak

open MachCSL MachCSL.Stdpp
open Lbl

/-- The all-zero image (every byte defined, so `t = 0` reads are legal). -/
def AxGraphWit.imgw : Image := fun _ => some b0

def AxGraphWit.mkgd (prog : List (List Lbl)) (gmo : List Geid) (deps : List (Geid × Geid)) :
    Gdexec :=
  ⟨⟨AxGraphWit.imgw, prog, gmo⟩, deps⟩

/-! # 1. FWD+acq — the two models separate

H0: W x=1 (0,0); R.aq x (0,1) reads its OWN store (forwarded); R y (0,2) reads 0.
H1: W y=1 (1,0); fence rw,rw (1,1); W x=2 (1,2).
gmo = [R0x; R0y; W1y; W1x; W0x] — writes: W1y=1, W1x=2, W0x=3. -/
def fwd : Gdexec :=
  AxGraphWit.mkgd
    [[LStore false 0 [b1] .WCplain, LLoad true 0 [3] [b1], LLoad false 1 [0] [b0]],
     [LStore false 1 [b1] .WCplain, LFence true true true true, LStore false 0 [b2] .WCplain]]
    [(0, 1), (0, 2), (1, 0), (1, 2), (0, 0)]
    []

theorem AxGraphWit.fwdCat : rvwmoCatConsistent fwd :=
  catConsistentBSound _ (by decide +kernel)

/-- RVWMO⁻ fails: `gpoloc` W0x→R0x demands W0x gmo-before its own read. -/
theorem fwdNotMinus : ¬ rvwmoMinusDepsConsistent fwd := by
  rintro ⟨h, _⟩
  exact notMinusOfPoloc _ (0, 0) (0, 1) (by decide +kernel) (by decide +kernel) h

/-- The forwarded read's source IS the own store — `ownForwardCat'` exercised
with every hypothesis discharged. -/
theorem fwdOwnForward : grfAt fwd.gdG 0 (0, 0) (0, 1) ∧ b1 = b1 := by
  refine ownForwardCat' fwd 0 (0, 0) (0, 1) b1 3 b1 AxGraphWit.fwdCat
    ((gpoBSpec _ _ _).1 (by decide +kernel))
    ((gwbBSpec _ _ _ _).1 (by decide +kernel))
    ((grbBSpec _ _ _ _ _).1 (by decide +kernel)) ?_ ?_
  · intro h
    have h' := (gmoLtBSpec _ _ _).2 h
    have hf : gmoLtB fwd.gdG (0, 0) (0, 1) = false := by decide +kernel
    rw [hf] at h'
    cases h'
  · rintro w' v' _ ⟨_, hlt, _⟩ ⟨_, hlt', _⟩
    dsimp only at hlt hlt'
    omega

/-! # 2. Release-then-read

H0: W a=1 (0,0); fence rw,w (0,1); W lock=0 (0,2); R a (0,3).
H1: RMW.aq lock 0→1 (1,0); W a=2 (1,1).
gmo = [W0a; W0lock; RMW1; W1a; R0a] — writes: W0a=1, W0lock=2, RMW1=3, W1a=4.
R0a reads W1a (t = 4). -/
def AxGraphWit.rel : Gdexec :=
  AxGraphWit.mkgd
    [[LStore false 0 [b1] .WCplain, LFence true true false true, LStore false 1 [b0] .WCplain,
      LLoad false 0 [4] [b2]],
     [LRmw true false 1 [2] [b0] [b1] .WCplain, LStore false 0 [b2] .WCplain]]
    [(0, 0), (0, 2), (1, 0), (1, 1), (0, 3)]
    []

theorem relCat : rvwmoCatConsistent AxGraphWit.rel :=
  catConsistentBSound _ (by decide +kernel)

/-- R0a's rf-source is the OTHER hart's W1a, uniquely — NOT the own po-earlier
W0a although that one is visible too. -/
theorem relRf :
    grfAt AxGraphWit.rel.gdG 0 (1, 1) (0, 3) ∧
    (∀ w, grfAt AxGraphWit.rel.gdG 0 w (0, 3) → w = (1, 1)) ∧
    ¬ grfAt AxGraphWit.rel.gdG 0 (0, 0) (0, 3) := by
  have H : grfAt AxGraphWit.rel.gdG 0 (1, 1) (0, 3) := (grfAtBSpec _ _ _ _).1 (by decide +kernel)
  refine ⟨H, fun w Hw => grfAtDet _ _ _ _ _ Hw H, fun Hown => ?_⟩
  have := grfAtDet _ _ _ _ _ Hown H
  cases this

/-! # 3. The ob ∪ poloc(W→R) cycle

H0: W x=1 (w1 = (0,0)); R x (r1 = (0,1), forwarded from w1);
    W y=1 (wy = (0,2), data-dependent on r1).
H1: R y (ry = (1,0), reads wy); fence rw,rw (1,1); W x=2 (w2 = (1,2)).
gmo = [r1; wy; ry; w2; w1] — writes: wy=1, w2=2, w1=3; co(w2, w1). -/
def cyc : Gdexec :=
  AxGraphWit.mkgd
    [[LStore false 0 [b1] .WCplain, LLoad false 0 [3] [b1], LStore false 1 [b1] .WCplain],
     [LLoad false 1 [1] [b1], LFence true true true true, LStore false 0 [b2] .WCplain]]
    [(0, 1), (0, 2), (1, 0), (1, 2), (0, 0)]
    [((0, 1), (0, 2))]

theorem cycCat : rvwmoCatConsistent cyc :=
  catConsistentBSound _ (by decide +kernel)

theorem cycNotMinus : ¬ rvwmoMinusDepsConsistent cyc := by
  rintro ⟨h, _⟩
  exact notMinusOfPoloc _ (0, 0) (0, 1) (by decide +kernel) (by decide +kernel) h

/-- `gpoloc` restricted to W→R — the edge RVWMO⁻ has and the cat model has not. -/
def gpolocWR (G : Gexec) (w r : Geid) : Prop :=
  gpoloc G w r ∧ glblIs G w lbIsW ∧ glblIs G r lbIsR

def gobPoloc (GD : Gdexec) (x y : Geid) : Prop :=
  gobrCat GD x y ∨ gpolocWR GD.gdG x y

/-- THE CYCLE  w1 →poloc→ r1 →dep→ wy →rfe→ ry →fence→ w2 →co→ w1, as
`tc (gobCat ∪ gpolocWR)` reflexive at r1.  Each edge is the NAMED arm. -/
theorem cycCycle : tc (gobPoloc cyc) (0, 1) (0, 1) := by
  -- r1 →dep→ wy
  refine tc_l (y := (0, 2)) (Or.inl (Or.inr (Or.inl (List.mem_singleton.2 rfl)))) ?_
  -- wy →rfe→ ry
  refine tc_l (y := (1, 0))
    (Or.inl (Or.inr (Or.inr (Or.inl ((grfeBSpec _ _ _).1 (by decide +kernel)))))) ?_
  -- ry →fence→ w2
  refine tc_l (y := (1, 2))
    (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl
      ((gfenceBSpec _ _ _).1 (by decide +kernel))))))))) ?_
  -- w2 →co→ w1
  refine tc_l (y := (0, 0))
    (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ((gcoBSpec _ _ _).1 (by decide +kernel))))))) ?_
  -- w1 →poloc(W→R)→ r1
  exact tc_once (Or.inr ⟨(gpolocBSpec _ _ _).1 (by decide +kernel),
    (glblBSpec _ _ _).1 (by decide +kernel), (glblBSpec _ _ _).1 (by decide +kernel)⟩)

/-- ... while `gobCat` alone is acyclic there (§3 of `AxGraphCat`). -/
theorem cycObCatAcyclic (x : Geid) : ¬ gobCat cyc x x :=
  obCatIrreflexive _ _ cycCat

/-! # 4. The stranded-token graph

One hart: W a (w = (0,0), gmo 0); R a (r1 = (0,1), gmo 2); R a (r2 = (0,2), gmo 1).
Both reads take w; r2 is gmo-BEFORE r1. -/
def str : Gdexec :=
  AxGraphWit.mkgd
    [[LStore false 0 [b1] .WCplain, LLoad false 0 [1] [b1], LLoad false 0 [1] [b1]]]
    [(0, 0), (0, 2), (0, 1)]
    []

/-- Rule 2 exempts the pair (same source), so the inversion is legal. -/
theorem strCat : rvwmoCatConsistent str :=
  catConsistentBSound _ (by decide +kernel)

theorem strNotMinus : ¬ rvwmoMinusDepsConsistent str := by
  rintro ⟨h, _⟩
  exact notMinusOfPoloc _ (0, 1) (0, 2) (by decide +kernel) (by decide +kernel) h

theorem strShape :
    gmoLt str.gdG (0, 2) (0, 1) ∧
    ¬ gppoCat str (0, 1) (0, 2) ∧
    grfAt str.gdG 0 (0, 0) (0, 1) ∧
    grfAt str.gdG 0 (0, 0) (0, 2) := by
  refine ⟨(gmoLtBSpec _ _ _).1 (by decide +kernel), fun H => ?_,
    (grfAtBSpec _ _ _ _).1 (by decide +kernel), (grfAtBSpec _ _ _ _).1 (by decide +kernel)⟩
  have h := (gppoCatBSpec _ _ _).2 H
  have hf : gppoCatB str (0, 1) (0, 2) = false := by decide +kernel
  rw [hf] at h
  cases h

/-! # 5. The fraction-flow prototype (pure; one hart, one byte)

Events carry identity, kind, po index and gmo index.  An annotation is an
association list holder ↦ `k`, meaning the DYADIC piece 2^-k of the byte's token
(a present entry IS a positive piece; Σ = 1 is a `Nat` check, `tsumOk`).  Two
policies: `PFrac` (the design's F1): a read pulls HALF of the piece of the first
eligible holder — same hart, same byte, po-earlier, gmo-earlier — and retains
it; `PNaive`: a read takes the holder's WHOLE piece.  A write pulls every piece
of a po-earlier access (rule 1) and re-ties the full token at itself.  A read
with no eligible holder is STRANDED. -/

structure AxGraphWit.Tev where
  teId : Nat
  teW : Bool
  tePo : Nat
  teGmo : Nat
  deriving DecidableEq

open AxGraphWit (Tev)

abbrev tann : Type := List (Tev × Nat)

def tholds (ann : tann) (e : Tev) : Bool :=
  ann.any (fun p : Tev × Nat => decide (p.1 = e))

def holderOk (e h : Tev) : Bool :=
  decide (h.tePo < e.tePo) && decide (h.teGmo < e.teGmo)

inductive Tpol where
  | PFrac
  | PNaive
  deriving DecidableEq

inductive AxGraphWit.Tres where
  | TOk (ann : tann)
  | TStranded (e : Tev)
  deriving DecidableEq

open AxGraphWit (Tres)

def tread (pol : Tpol) (ann : tann) (e : Tev) : Tres :=
  match listFind (fun p : Tev × Nat => holderOk e p.1) ann with
  | none => .TStranded e
  | some (i, (h, k)) =>
      match pol with
      | .PFrac => .TOk ((e, k + 1) :: ann.set i (h, k + 1))
      | .PNaive => .TOk ((e, k) :: ann.eraseIdx i)

def twrite (ann : tann) (e : Tev) : tann :=
  (e, 0) :: ann.filter (fun p : Tev × Nat => !(decide (p.1.tePo < e.tePo)))

def tstep (pol : Tpol) (ann : tann) (e : Tev) : Tres :=
  if e.teW then .TOk (twrite ann e) else tread pol ann e

def AxGraphWit.trun (pol : Tpol) (ann : tann) : List Tev → Tres
  | [] => .TOk ann
  | e :: L' =>
      match tstep pol ann e with
      | .TOk ann' => AxGraphWit.trun pol ann' L'
      | .TStranded x => .TStranded x

/-- Σ 2^-k = 1  ⇔  Σ 2^(K-k) = 2^K, K the largest exponent. -/
def tsumOk (ann : tann) : Bool :=
  let K := ann.foldr (fun p m => Nat.max p.2 m) 0
  decide (ann.foldr (fun p s => 2 ^ (K - p.2) + s) 0 = 2 ^ K)

/-! ## 5.1 The stranded-token graph, both policies, both orders -/

def AxGraphWit.tw : Tev := ⟨0, true, 0, 10⟩
def tr1 : Tev := ⟨1, false, 1, 12⟩
def tr2 : Tev := ⟨2, false, 2, 11⟩
def poOrder : List Tev := [AxGraphWit.tw, tr1, tr2]
def gmoOrder : List Tev := [AxGraphWit.tw, tr2, tr1]

/-- Fractional flow in gmo order: r2 halves w's token, r1 halves w's REMAINDER;
nobody is stranded, every node holds a piece, Σ = 1. -/
theorem fracGmo :
    AxGraphWit.trun .PFrac [] gmoOrder = .TOk [(tr1, 2), (tr2, 1), (AxGraphWit.tw, 2)] ∧
    tsumOk [(tr1, 2), (tr2, 1), (AxGraphWit.tw, 2)] = true ∧
    gmoOrder.all (tholds [(tr1, 2), (tr2, 1), (AxGraphWit.tw, 2)]) = true := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

theorem fracPo :
    AxGraphWit.trun .PFrac [] poOrder = .TOk [(tr2, 2), (tr1, 1), (AxGraphWit.tw, 2)] := by
  decide +kernel

/-- The naive move: po order strands r2 (as commissioned) — and GMO ORDER
STRANDS r1 (correction (1)). -/
theorem naivePo : AxGraphWit.trun .PNaive [] poOrder = .TStranded tr2 := by decide +kernel

theorem naiveGmo : AxGraphWit.trun .PNaive [] gmoOrder = .TStranded tr1 := by decide +kernel

/-! ## 5.2 THE GENERAL INVARIANT for the fractional flow

"The writer's node retains a positive piece until the next same-byte write."
Under `PFrac` a read never EVICTS a holder (it only halves a piece), and a write
re-ties at itself; so, processing in gmo order under rule 1 (`rule1Ok`), the
latest write always holds a piece (`tinv`) and no read is ever stranded. -/

theorem tholdsInsert (ann : tann) (i : Nat) (h : Tev) (k k' : Nat) (e : Tev) :
    ann[i]? = some (h, k) → tholds ann e = true →
    tholds (ann.set i (h, k')) e = true := by
  intro Hi He
  unfold tholds at He ⊢
  rw [List.any_eq_true] at He ⊢
  obtain ⟨p, Hp, Hpe⟩ := He
  have Hpe' : p.1 = e := of_decide_eq_true Hpe
  obtain ⟨j, Hj⟩ := elem_of_list_lookup_1 Hp
  by_cases Hij : i = j
  · subst Hij
    rw [Hi, Option.some.injEq] at Hj
    subst Hj
    exact ⟨(h, k'), elem_of_list_lookup_2 (list_lookup_insert (lookup_lt_Some Hi)),
      decide_eq_true Hpe'⟩
  · exact ⟨p, elem_of_list_lookup_2 (by rw [list_lookup_insert_ne Hij]; exact Hj), Hpe⟩

/-- A successful `PFrac` read ties a piece at the read and keeps every existing
holder. -/
theorem treadFracHolds (ann : tann) (e : Tev) (ann' : tann) :
    tread .PFrac ann e = .TOk ann' →
    tholds ann' e = true ∧ (∀ x, tholds ann x = true → tholds ann' x = true) := by
  unfold tread
  cases Hf : listFind (fun p : Tev × Nat => holderOk e p.1) ann with
  | none => intro H; cases H
  | some r =>
    obtain ⟨i, h, k⟩ := r
    intro H
    simp only [Tres.TOk.injEq] at H
    subst H
    obtain ⟨Hi, _, _⟩ := list_find_Some.1 Hf
    refine ⟨by simp [tholds], fun x Hx => ?_⟩
    simp only [tholds, List.any_cons, Bool.or_eq_true]
    exact Or.inr (tholdsInsert ann i h k (k + 1) x Hi Hx)

theorem twriteHolds (ann : tann) (e : Tev) : tholds (twrite ann e) e = true := by
  simp [tholds, twrite]

/-- Rule 1 + gmo-order processing, stated along the list with the latest
processed write `lw`: every READ has a latest preceding write that is
po-earlier and gmo-earlier. -/
def rule1Ok (lw : Option Tev) : List Tev → Prop
  | [] => True
  | e :: L' =>
      (e.teW = false → ∃ w, lw = some w ∧ w.tePo < e.tePo ∧ w.teGmo < e.teGmo) ∧
      rule1Ok (if e.teW then some e else lw) L'

def lastWrite (lw : Option Tev) (L : List Tev) : Option Tev :=
  L.foldl (fun acc e => if e.teW then some e else acc) lw

/-- THE INVARIANT: the latest write's node holds a piece. -/
def tinv (ann : tann) (lw : Option Tev) : Prop :=
  ∀ w, lw = some w → tholds ann w = true

theorem tstepFracOk (ann : tann) (lw : Option Tev) (e : Tev) :
    tinv ann lw →
    (e.teW = false → ∃ w, lw = some w ∧ w.tePo < e.tePo ∧ w.teGmo < e.teGmo) →
    ∃ ann', tstep .PFrac ann e = .TOk ann' ∧ tinv ann' (if e.teW then some e else lw) := by
  intro Hinv Hr
  unfold tstep
  cases Hw : e.teW with
  | true =>
    refine ⟨_, rfl, ?_⟩
    intro w Hw'
    simp only [if_true, Option.some.injEq] at Hw'
    subst Hw'
    exact twriteHolds ann _
  | false =>
    simp only [Bool.false_eq_true, if_false]
    obtain ⟨w, Hlw, Hpo, Hgmo⟩ := Hr Hw
    have Hhold := Hinv w Hlw
    unfold tholds at Hhold
    rw [List.any_eq_true] at Hhold
    obtain ⟨p, Hp, Hpw⟩ := Hhold
    have Hpw' : p.1 = w := of_decide_eq_true Hpw
    -- an eligible holder exists, so the search succeeds
    cases Hf : listFind (fun p : Tev × Nat => holderOk e p.1) ann with
    | none =>
      exfalso
      have Hnp := list_find_None.1 Hf p Hp
      rw [Hpw'] at Hnp
      simp [holderOk, Hpo, Hgmo] at Hnp
    | some r =>
      obtain ⟨i, h, k⟩ := r
      have Htr : tread .PFrac ann e = .TOk ((e, k + 1) :: ann.set i (h, k + 1)) := by
        unfold tread; rw [Hf]
      obtain ⟨_, Hkeep⟩ := treadFracHolds ann e _ Htr
      exact ⟨_, Htr, fun w' Hw' => Hkeep w' (Hinv w' Hw')⟩

theorem trunFracNoStrand (L : List Tev) :
    ∀ ann lw, tinv ann lw → rule1Ok lw L →
    ∃ ann', AxGraphWit.trun .PFrac ann L = .TOk ann' ∧ tinv ann' (lastWrite lw L) := by
  induction L with
  | nil => intro ann lw Hinv _; exact ⟨ann, rfl, Hinv⟩
  | cons e L IH =>
    intro ann lw Hinv Hok
    obtain ⟨Hr, Hok⟩ := Hok
    obtain ⟨ann1, Hstep, Hinv1⟩ := tstepFracOk ann lw e Hinv Hr
    obtain ⟨ann', Hrun, Hinv'⟩ := IH ann1 _ Hinv1 Hok
    refine ⟨ann', ?_, ?_⟩
    · simp only [AxGraphWit.trun, Hstep]
      exact Hrun
    · exact Hinv'

/-- The two consumable readings. -/
theorem fracNeverStrands (L : List Tev) (x : Tev) :
    rule1Ok none L → AxGraphWit.trun .PFrac [] L ≠ .TStranded x := by
  intro Hok
  obtain ⟨ann', Hrun, _⟩ := trunFracNoStrand L [] none (fun _ h => by cases h) Hok
  rw [Hrun]
  intro H
  cases H

theorem fracWriterRetains (L : List Tev) (ann' : tann) (w : Tev) :
    rule1Ok none L → AxGraphWit.trun .PFrac [] L = .TOk ann' →
    lastWrite none L = some w → tholds ann' w = true := by
  intro Hok Hrun Hlw
  obtain ⟨ann'', Hrun', Hinv⟩ := trunFracNoStrand L [] none (fun _ h => by cases h) Hok
  rw [Hrun, Tres.TOk.injEq] at Hrun'
  subst Hrun'
  exact Hinv w Hlw

/-- The stranded-token graph satisfies the hypothesis in gmo order (and,
incidentally, in po order too — the fractional flow is robust). -/
theorem gmoOrderRule1 : rule1Ok none gmoOrder := by
  show rule1Ok none [AxGraphWit.tw, tr2, tr1]
  refine ⟨fun h => (by cases h), ?_⟩
  show rule1Ok (some AxGraphWit.tw) [tr2, tr1]
  refine ⟨fun _ => ⟨AxGraphWit.tw, rfl, by decide, by decide⟩, ?_⟩
  show rule1Ok (some AxGraphWit.tw) [tr1]
  exact ⟨fun _ => ⟨AxGraphWit.tw, rfl, by decide, by decide⟩, trivial⟩

theorem strFracOk (x : Tev) : AxGraphWit.trun .PFrac [] gmoOrder ≠ .TStranded x :=
  fracNeverStrands _ _ gmoOrderRule1

/-! # 6. RULE 12 is load-bearing

H0 owns x, sp, q:  r0: ld a5,(x) (0,0) — reads H1's wx;
                   w:  sd a5,0(sp) (0,1) — DATA-dependent on r0;
                   r:  ld a6,0(sp) (0,2) — reads w by forwarding;
                   sd2: sd a6,(q) (0,3) — DATA-dependent on r.
H1:                wx: sd 2,(x) (1,0).
gmo = [r; sd2; wx; r0; w] — writes: sd2=1, wx=2, w=3.

Rule 10 gives r0 < w and r < sd2 only, so the six program-order arms accept this
order: `r` completes with `w`'s data BEFORE `r0` has read the value that data
depends on.  Rule 12 (`r0 →data→ w →rfi→ r`) demands r0 < r and refutes it. -/
def r12 : Gdexec :=
  AxGraphWit.mkgd
    [[LLoad false 0 [2] [b2], LStore false 1 [b2] .WCplain, LLoad false 1 [3] [b2],
      LStore false 2 [b2] .WCplain],
     [LStore false 0 [b2] .WCplain]]
    [(0, 2), (0, 3), (1, 0), (0, 0), (0, 1)]
    [((0, 0), (0, 1)), ((0, 2), (0, 3))]

theorem r12Cat6 : rvwmoCat6Consistent r12 :=
  cat6ConsistentBSound _ (by decide +kernel)

theorem r12NotCat : ¬ rvwmoCatConsistent r12 :=
  notCatOfRule12 _ (0, 0) (0, 2) (by decide +kernel) (by decide +kernel)

/-- The offending edge, named: rule 12 at (r0, r), and r gmo-before r0. -/
theorem r12Edge :
    gppo12 r12.gdG r12.gdDeps (0, 0) (0, 2) ∧
    gmoLt r12.gdG (0, 2) (0, 0) ∧
    grfAt r12.gdG 1 (0, 1) (0, 2) :=
  ⟨(gppo12BSpec _ _ _ _).1 (by decide +kernel), (gmoLtBSpec _ _ _).1 (by decide +kernel),
    (grfAtBSpec _ _ _ _).1 (by decide +kernel)⟩

/-! # 7. LB -/

theorem AxGraphWit.lbCat : rvwmoCatConsistent lbgd :=
  minusImpliesCat _ lbGraphDepsConsistent

/-- ... and the checker agrees (a cross-check of the checker on the tree's own
witness). -/
theorem lbCatB : catConsistentB lbgd = true := by decide +kernel

end Weak
