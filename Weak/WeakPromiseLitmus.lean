/-
Weak: **LB is REACHABLE in the full promising machine** (M6 W1's litmus sanity
check).

Rocq: `iris/WeakPromiseLitmus.v` @ xxvzwolszwmp (1cc222280).

The Rocq header, verbatim in substance: the W1 litmus sanity check of the M6
robustness effort (`claude-notes/projects/weak-memory-m6.md`, W1's last box):
the LOAD BUFFERING weak outcome `r1 = r2 = 1` is a genuine behavior of
`WeakPromise`'s FULL promising machine.  Together with `WeakLitmus`'s `lbInv`
— which proves the SAME outcome unreachable in the promise-free machine — this
is the "the new machine is really weaker" check (see the closing comment).
Import surface is deliberately minimal: the stdpp shims + `WeakMem` +
`WeakPromise`.  In particular `WeakLitmus` is NOT imported (only cited); the
handful of literal bytes and addresses it also uses are re-built locally.

**Deviations from Rocq.**

1. NAMES: as `Weak/WeakMem.lean` deviation 1.  Rocq → Lean map: `lbp` ↦
   `Lbp` (constructors `LBLoad`/`LBStore`/`LBDone` kept, `lbp_eq_dec` is a
   `deriving DecidableEq`), `lbstep` ↦ `lbstep` (a Prop-valued inductive, like
   `wpstep`; constructors `LBSLoad`/`LBSStore` kept), `lbstep'` ↦ `lbstep'`,
   `lb_p0`/`lb_p1` ↦ `lbP0`/`lbP1`, `b1_unsigned` ↦ `b1Unsigned`,
   `img0_x`/`img0_y` ↦ `img0X`/`img0Y`, `msg_byte_hit` ↦ `msgByteHit`,
   `log_byte_MY`/`log_byte_MX` ↦ `logByteMY`/`logByteMX`,
   `readable_above_floor` ↦ `readableAboveFloor`, `ws_init_floor` ↦
   `wsInitFloor`, `read_ok_h1`/`read_ok_h0` ↦ `readOkH1`/`readOkH0`,
   `ws_bounded_h1` ↦ `wsBoundedH1`, `fulfil_ok_h0` ↦ `fulfilOkH0`,
   `lb_weak_outcome_reachable` ↦ `lbWeakOutcomeReachable`,
   `lb_weak_outcome_regs` ↦ `lbWeakOutcomeRegs`.
2. NAMESPACE: the file lives in `Weak.WeakPromiseLitmus` (Rocq's module
   qualification), because its locally re-built `b0`/`b1`/`img0m`/`img0`/
   `img0X`/`img0Y` would otherwise clash with `WeakLitmus`'s in `Weak`.
3. `bv_unsigned b1 = 1` (a `Z`) is `b1.toNat = 1` (`bv_unsigned` is the
   non-negative `toNat`, as in `WeakPromise` deviation 3); the same in
   `lbWeakOutcomeRegs`.
4. THE `_d 0` CONVERSIONS (`WeakMem` deviation 3).  `WPLoad`/`WPFulfil` produce
   and consume `loadPostRunD ws aq (srcsView ws []) …`, which Rocq reads as
   `load_post_run` by conversion.  The side-condition lemmas keep their Rocq
   statements (over `loadPostRun` / `fulfilOk`); the interleaving rewrites them
   with `loadPostRunD0` at the two use sites.
5. `fulfilOkH0` is closed by `decide` on the unfolded (closed, one-byte)
   condition instead of Rocq's `load_post_run_single` + `coh_upd_ne`
   rewriting; the statement is unchanged.

**Not ported:** nothing.

**Statements checked** (by hand, against Rocq): all of them.
-/
import Weak.WeakPromise

namespace Weak.WeakPromiseLitmus

open MachCSL MachCSL.Stdpp Iris.Std Iris.Std.PartialMap Weak Wlabel

/-! ## Bytes, addresses, the era-initial image -/

def b0 : BitVec 8 := 0#8
def b1 : BitVec 8 := 1#8

theorem b1Unsigned : b1.toNat = 1 := by decide

/-- The two litmus bytes. -/
local notation "ax" => (0 : Int)
local notation "ay" => (8 : Int)

def img0m : GMapF Int (BitVec 8) := insert {[ay := b0]} ax b0
def img0 : Image := fun a => get? img0m a

theorem img0X : img0 ax = some b0 := by
  show get? (insert _ ax b0) ax = some b0
  exact lookupInsert

theorem img0Y : img0 ay = some b0 := by
  show get? (insert {[ay := b0]} ax b0) ay = some b0
  rw [lookupInsertNe (by decide)]
  exact lookupSingleton

/-- The two messages the test produces: hart 0's `y := 1` and hart 1's `x := 1`. -/
local notation "MY" => Wmsg.mk ay [b1] (some 0) WmClass.WCplain
local notation "MX" => Wmsg.mk ax [b1] (some 1) WmClass.WCplain

theorem msgByteHit (a : Int) (v : BitVec 8) (tid : Option Nat) (k : WmClass) :
    msgByte ⟨a, [v], tid, k⟩ a = some v := by
  simp [msgByte]

theorem logByteMY : logByte img0 [MY] 1 ay = some b1 := 
  (msgByteHit _ _ _ _ : msgByte MY ay = some b1)

theorem logByteMX : logByte img0 [MY, MX] 2 ax = some b1 := 
  (msgByteHit _ _ _ _ : msgByte MX ax = some b1)

/-! ## The program: `P` for the two LB harts

The LB harts need exactly three program states, and the state after the load
RECORDS the value read — that register is the `r1`/`r2` of the litmus outcome. -/

inductive Lbp where
  /-- about to load from `ald`; will then store 1 to `ast` -/
  | LBLoad (ald ast : Int)
  /-- loaded `r`; about to store 1 to `ast` -/
  | LBStore (ast : Int) (r : BitVec 8)
  /-- finished, having read `r` -/
  | LBDone (r : BitVec 8)
  deriving DecidableEq

open Lbp

/-- The LTS.  A plain single-byte load, then a plain single-byte store of `b1`.
The store's label carries no read at all, which is precisely why hart 0's store
may be PROMISED before its load has happened. -/
inductive lbstep : Lbp → Wlabel → Lbp → Prop
  | LBSLoad (ald ast : Int) (t : Nat) (r : BitVec 8) :
      lbstep (LBLoad ald ast) (LLoad false false ald [(t, r)] []) (LBStore ast r)
  | LBSStore (ast : Int) (r : BitVec 8) :
      lbstep (LBStore ast r) (LStore false ast [b1] [] []) (LBDone r)

/-- LB: hart 0 = `load x; y := 1`; hart 1 = `load y; x := 1`. -/
def lbP0 : Lbp := LBLoad ax ay
def lbP1 : Lbp := LBLoad ay ax

/-! ## Discharging the side conditions of the four memory steps -/

/-- Both LB loads read a message that sits ABOVE the reader's whole floor, so
the coherence window `readable` forbids is empty. -/
theorem readableAboveFloor (img : Image) (log : List Wmsg) (ws : Wstate) (base : Int) (t : Nat)
    (v : BitVec 8) :
    logByte img log t base = some v →
    max (loadVpre ws false) (coh ws base) ≤ t →
    readable img log ws (loadVpre ws false) base t := by
  intro hv hle
  refine ⟨by rw [hv]; rfl, ?_⟩
  rintro ⟨t', h1, h2, _⟩
  omega

theorem wsInitFloor (a : Int) (t : Nat) : max (loadVpre wsInit false) (coh wsInit a) ≤ t := by
  rw [cohInit]; simp [loadVpre, wsInit]

/-- Hart 1 reads hart 0's PROMISED (not yet fulfilled) message at ts = 1. -/
theorem readOkH1 : readOk img0 [MY] wsInit false false ay [(1, b1)] :=
  readOkSingle _ _ _ _ _ _ logByteMY
    (readableAboveFloor _ _ _ _ _ _ logByteMY (wsInitFloor _ _))

/-- Hart 0 reads hart 1's message at ts = 2 — its own view is still pristine
(a promise step does not touch `paWs`). -/
theorem readOkH0 : readOk img0 [MY, MX] wsInit false false ax [(2, b1)] :=
  readOkSingle _ _ _ _ _ _ logByteMX
    (readableAboveFloor _ _ _ _ _ _ logByteMX (wsInitFloor _ _))

/-- Hart 1's state after its load is still bounded by the one-message log. -/
theorem wsBoundedH1 : wsBounded (loadPostRun wsInit false ay [1]) 1 :=
  loadPostRunBounded _ _ _ _ _ (wsBoundedInit _) (by simp)

/-- THE KEY SIDE CONDITION — hart 0 fulfilling its ts = 1 promise of `y` AFTER
having read `x` at ts = 2:

- COH: the load touched byte `x` only, so `coh` at `y` is still 0 < 1.
- EXT: `fulfilVpre ws false = max wVcap wVwNew`, and a PLAIN load raises only
  `vrOld` and `coh` — `wVwNew` is still 0 < 1.

This is exactly the `po ∪ rf` cycle: were the load an acquire (or a fence in
between), `wVwNew` would have been raised to 2 and EXT would fail. -/
theorem fulfilOkH0 : fulfilOk (loadPostRun wsInit false ax [2]) false ay 1 1 := by
  unfold fulfilOk fulfilOkD
  decide

/-! ## The theorem: the LB weak outcome is a behavior of the full machine

The interleaving (the log starts empty, so hart 0's promise lands at ts = 1):

  1. hart 0 PROMISES `y := 1`                     (`WPPromise`, ts = 1)
  2. hart 1 LOADS y, reading the PROMISE          (`WPLoad`, t = 1 → r2 = 1)
  3. hart 1 STORES `x := 1`                       (`wpstepStoreNow`, ts = 2)
  4. hart 0 LOADS x, reading hart 1's store       (`WPLoad`, t = 2 → r1 = 1)
  5. hart 0 FULFILS its promise                   (`WPFulfil`, ts = 1)

Step 5 is what makes this a BEHAVIOR rather than a doomed run: the final
configuration has every promise set empty (`noPromises`). -/

/-- THE FABRIC SHIM: this program does not touch the device fabric, so it
instantiates the generalized machine at the CONSTANT fabric (`D := Unit`). -/
def lbstep' : Lbp → Unit → Wlabel → Lbp → Unit → Prop :=
  pstepOfPure lbstep

theorem lbWeakOutcomeReachable :
    ∃ (cfg : Wpcfg Lbp Unit) (ag0 ag1 : Wpagent Lbp),
      -- a genuine behavior of the FULL machine: reachable, all promises kept
      wpBehavior lbstep' img0 () [lbP0, lbP1] cfg ∧
      -- hart 0's final program state records r1 = 1 …
      cfg.pcAgs[0]? = some ag0 ∧ ag0.paSt = LBDone b1 ∧
      -- … and hart 1's records r2 = 1
      cfg.pcAgs[1]? = some ag1 ∧ ag1.paSt = LBDone b1 := by
  refine ⟨?cfg, ?ag0, ?ag1, ⟨?run, ?np⟩, ?o1, ?o2, ?o3, ?o4⟩
  case run =>
    -- 1. hart 0 PROMISES y := 1; the log was empty, so ts = 1
    refine rtc_l (wpstep.WPPromise (pstep := lbstep') _ 0 _ ay [b1] .WCplain rfl (by simp)) ?_
    -- 2. hart 1 LOADS y and reads that promise
    refine rtc_l (wpstep.WPLoad (pstep := lbstep') _ 1 _ false false ay [(1, b1)] [] _ _ rfl
      (pstepOfPureIntro _ _ _ _ _ (lbstep.LBSLoad _ _ _ _)) readOkH1) ?_
    -- 3. hart 1 STORES x := 1 (promise + immediate fulfil at the fresh top)
    refine rtc_transitive (wpstepStoreNow lbstep' _ 1 _ false ax [b1] [] [] .WCplain _ _ rfl
      (pstepOfPureIntro _ _ _ _ _ (lbstep.LBSStore _ _)) (by simp)
      (show wsBounded (loadPostRunD wsInit false 0 ay [1]) 1 by
        rw [loadPostRunD0]; exact wsBoundedH1)
      (by set_solver)) ?_
    -- 4. hart 0 LOADS x and reads hart 1's store
    refine rtc_l (wpstep.WPLoad (pstep := lbstep') _ 0 _ false false ax [(2, b1)] [] _ _ rfl
      (pstepOfPureIntro _ _ _ _ _ (lbstep.LBSLoad _ _ _ _)) readOkH0) ?_
    -- 5. hart 0 FULFILS its ts = 1 promise of y := 1
    refine rtc_l (wpstep.WPFulfil (pstep := lbstep') _ 0 _ false ay [b1] [] [] .WCplain 1 _ _ rfl
      (pstepOfPureIntro _ _ _ _ _ (lbstep.LBSStore _ _))
      (by simp only [wpInit, List.length_nil]; set_solver) rfl
      (show fulfilOk (loadPostRunD wsInit false 0 ax [2]) false ay 1 1 by
        rw [loadPostRunD0]; exact fulfilOkH0)) ?_
    exact rtc_refl _
  case np =>
    -- every promise discharged
    intro i ag hlk
    rcases i with _ | _ | i <;>
      simp only [wpInit, List.map_cons, List.map_nil, List.set_cons_zero, List.set_cons_succ,
        List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil, Option.some.injEq,
        reduceCtorEq] at hlk
    · subst hlk; simp only [List.length_nil]; set_solver
    · subst hlk; rfl
  -- the outcome: both harts recorded the value 1
  case o1 => rfl
  case o2 => rfl
  case o3 => rfl
  case o4 => rfl

/-- The same statement with the litmus registers spelled out numerically:
`r1 = r2 = 1`. -/
theorem lbWeakOutcomeRegs :
    ∃ (cfg : Wpcfg Lbp Unit) (ag0 ag1 : Wpagent Lbp) (r1 r2 : BitVec 8),
      wpBehavior lbstep' img0 () [lbP0, lbP1] cfg ∧
      cfg.pcAgs[0]? = some ag0 ∧ ag0.paSt = LBDone r1 ∧
      cfg.pcAgs[1]? = some ag1 ∧ ag1.paSt = LBDone r2 ∧
      r1.toNat = 1 ∧ r2.toNat = 1 := by
  obtain ⟨cfg, ag0, ag1, h1, h2, h3, h4, h5⟩ := lbWeakOutcomeReachable
  exact ⟨cfg, ag0, ag1, b1, b1, h1, h2, h3, h4, h5, b1Unsigned, b1Unsigned⟩

/-! ## The promise-free contrast (no proof here — a pointer)

`WeakLitmus`'s LB section (`lbC0` / `lbInv` / `lbForbidden`) proves that the
SAME outcome is UNREACHABLE in the promise-free machine: with no promises, a
store cannot enter the log before the program-order-earlier load has resolved,
so an `x`-message must be preceded in the log by a `y`-message and vice versa,
and that descent is impossible in a finite append-only log
(`WeakLitmus.lbDescend`).

Consequences worth recording:

- The full machine is STRICTLY weaker than the promise-free one, so the
  promise-free ⊆ full inclusion (`WeakPromise.wpstepStoreNow`, used at step 3
  above) is not an equivalence — W1's erasure bridge really does have to be
  one-directional.
- The single side condition standing between "promise-free" and this behavior
  is `fulfilOk`'s EXT (`fulfilVpre ws rl < ts`).  Step 5 goes through only
  because a PLAIN load leaves `wVwNew` at 0; an acquire load, or a
  `fence r,rw` between the load and the store, raises `wVwNew` to 2 and kills
  the fulfilment.  That is the miniature of the M6 Layer-1 argument for the
  fenced store class (D-M6-5's surviving pin is precisely `wVwNew`). -/

end Weak.WeakPromiseLitmus
