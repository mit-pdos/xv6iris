/-
Weak: **the "ctrl gate"** — stores after a gate are gmo-after the gate's sources.  PURE (no Iris).

Rocq: `iris/AxGate.v` @ xxvzwolszwmp.

## The Rocq header, in substance

Design `claude-notes/design/weak-memory-lb-axsl.md` rev 7 (the "ctrl gate" pivot, C14) and
`claude-notes/design/weak-memory-lb-axsl-review-fetch.md` Q2–Q5.  Entirely over `AxDeps`' tagged
dependency model.

THE IDEA.  RVWMO rule 11 orders EVERY po-later store after the loads a branch / jump /
trap-redirect depends on (`DTctrl`, `AxDeps.dedgesW`).  So after such a "gate", the only events
that can be gmo-EARLIER than its sources are READS (`gateStoreAfter`, `gateGmoEarlierIsRead`).

TWO LEVELS.  (A) ROW level over `DstateT`/`dstepT`/`rowDepsT`: `dtCtl` only grows along a row
(`dstepTDtctlMono`, `dstateTAfterMono`) and every write's `dedgesW` reads the CURRENT `dtCtl`, so
a gate's sources reach every po-later write (`gateCtrlEdges`, `gateStoreAfterRow`).  (B) GRAPH
level over `GdexecT`: `gateSrcs`, `gateStoreAfter`, `gateGmoEarlierIsRead`.

FINDINGS (kept from Rocq).  (F1) `dstepT` is a pure fold over an arbitrary `List Eitem`; that row
positions increase is not intrinsic to it, so the row/graph lemmas take an explicit position bound
`Hbound`.  (F2) Nothing connects `rowDepsT` to a `GdexecT`'s `gtDeps`; the embedding is the
explicit hypothesis `gtRowConformant`.  (F3) A gate has no graph event (`LCtrl` emits no edges
and ignores `it.2`), so `gateSrcs` is indexed by the row (hart, prefix state, sources).  (F4)
`dstepT`'s `LCtrl` arm APPENDS to `dtCtl` and nothing resets it, so the gate reaches every later
write (incl. AMO/SC write parts via `LRmw`).  (F5) A trap redirect emitting `LCtrl []` gives a
vacuous gate.

FETCHES (O2 Stage C): untouched here — a fetch (`LIFetch`) is an administrative label
(`elbIsR (LIFetch ..) = false`), and `dstepT`'s `LIFetch` arm is `(s, [])`, leaving `dtCtl`
unchanged like every non-`LCtrl` arm.  This file has no `decide` checks over fetch rows.

**Deviations from Rocq.**

1. NAMES: lowerCamelCase.  `row_deps_t_aux_app` is in `notes/weak-port-dupnames.json`
   (AxGate, AxScCat): declared file-qualified as `AxGate.rowDepsTAuxApp`.
2. List inclusion `⊆` is Lean's `List.Subset` (same meaning: membership implication).
3. Edges are `((j, k), tg)` (AxDeps' `Redge`/`Tdep` nesting) where Rocq writes `(j, k, tg)`.

**Name map.**  `dstep_t_dtctl_mono` `dstepTDtctlMono`, `dstate_t_after` `dstateTAfter`,
`dstate_t_after_mono` `dstateTAfterMono`, `row_deps_t_aux_app` `AxGate.rowDepsTAuxApp`,
`elb_is_w_ctrl_edge` `elbIsWCtrlEdge`, `gate_ctrl_edges` `gateCtrlEdges`, `gate_srcs` `gateSrcs`,
`dtsrcs_gate_dt_ctl` `dtsrcsGateDtCtl`, `gate_store_after_row` `gateStoreAfterRow`,
`gt_row_conformant` `gtRowConformant`, `gate_store_after` `gateStoreAfter`,
`gate_gmo_earlier_is_read` `gateGmoEarlierIsRead`.

**Not ported:** nothing (the §4 `Print Assumptions` block has no Lean twin; the lint's axiom check
covers it).
-/
import Weak.AxDeps

namespace Weak

open MachCSL MachCSL.Stdpp
open Wlabel Dtag

/-! # 1. Row level: `dtCtl` monotonicity along `dstepT` / `rowDepsTAux` -/

/-- `dtCtl` never shrinks: every arm leaves it unchanged or (the `LCtrl` arm) appends to it. -/
theorem dstepTDtctlMono (s : DstateT) (it : Eitem) : s.dtCtl ⊆ (dstepT s it).1.dtCtl := by
  obtain ⟨l, ok⟩ := it
  intro x hx
  cases l <;> cases ok <;> simp [dstepT, hx]

/-- The state reached after folding `dstepT` over a whole row. -/
def dstateTAfter (s : DstateT) (es : List Eitem) : DstateT :=
  match es with
  | [] => s
  | it :: es' => dstateTAfter (dstepT s it).1 es'

theorem dstateTAfterMono (s : DstateT) (es : List Eitem) :
    s.dtCtl ⊆ (dstateTAfter s es).dtCtl := by
  induction es generalizing s with
  | nil => exact fun _ h => h
  | cons it es' ih => exact fun x hx => ih _ (dstepTDtctlMono s it hx)

/-- `rowDepsTAux` splits over `++`, the state threaded through `dstateTAfter`. -/
theorem AxGate.rowDepsTAuxApp (s : DstateT) (es1 es2 : List Eitem) :
    rowDepsTAux s (es1 ++ es2) = rowDepsTAux s es1 ++ rowDepsTAux (dstateTAfter s es1) es2 := by
  induction es1 generalizing s with
  | nil => rfl
  | cons it es1' ih =>
    simp only [List.cons_append, rowDepsTAux, dstateTAfter, ih, List.append_assoc]

/-- THE PER-STEP FACT: a write item at row position `k` emits a `DTctrl` edge from every position
already in `dtCtl` (below `k`) — `dedgesW`'s third summand. -/
theorem elbIsWCtrlEdge (s : DstateT) (it : Eitem) (k j : Nat) :
    it.2 = some k → elbIsW it.1 = true → j ∈ s.dtCtl → j < k →
    ((j, k), DTctrl) ∈ (dstepT s it).2 := by
  obtain ⟨l, ow⟩ := it
  simp only
  rintro rfl hw hin hlt
  have he : ((j, k), DTctrl) ∈ tagEdges DTctrl k s.dtCtl :=
    (elemOfTagEdges ..).2 ⟨rfl, rfl, hin, hlt⟩
  cases l <;> simp only [elbIsW, Bool.false_eq_true] at hw <;>
    simp only [dstepT, dedgesW, List.mem_append] <;> exact Or.inr (Or.inr (Or.inl he))

/-- THE ROW-LEVEL KEY LEMMA (F4): across an ARBITRARY later suffix, under the bound (F1). -/
theorem gateCtrlEdges (S : List Nat) (s : DstateT) (es1 es2 : List Eitem) (it : Eitem) (k : Nat) :
    S ⊆ s.dtCtl →
    (∀ j, j ∈ S → j < k) →
    it.2 = some k → elbIsW it.1 = true →
    ∀ j, j ∈ S → ((j, k), DTctrl) ∈ rowDepsTAux s (es1 ++ it :: es2) := by
  intro hS hbound hpos hw j hj
  rw [AxGate.rowDepsTAuxApp]
  simp only [rowDepsTAux, List.mem_append]
  exact Or.inr (Or.inl (elbIsWCtrlEdge _ it k j hpos hw (dstateTAfterMono s es1 (hS hj))
    (hbound j hj)))

/-! # 2. Gate sources -/

/-- The load events a ctrl node depends on, via `dtCtl` provenance: `srcs` is the `LCtrl`
label's operand list and `s0` the state right before it fires, embedded into `Geid`s at hart `i`
(F3: a gate itself has no `Geid`). -/
def gateSrcs (i : Agent) (s0 : DstateT) (srcs : List Dsrc) : List Geid :=
  (dtsrcs s0 srcs).map (fun j => (i, j))

/-- A gate's sources are already inside `dtCtl` right after it fires. -/
theorem dtsrcsGateDtCtl (s0 : DstateT) (srcs : List Dsrc) :
    dtsrcs s0 srcs ⊆ (dstepT s0 (LCtrl srcs, none)).1.dtCtl := by
  intro x hx
  simp [dstepT, hx]

/-- THE ROW-LEVEL PACKAGE: a gate at the end of prefix `es1` reaches every later write. -/
theorem gateStoreAfterRow
    (es1 : List Eitem) (srcs : List Dsrc) (esA esB : List Eitem) (it : Eitem) (k : Nat)
    (Hbound : ∀ j, j ∈ dtsrcs (dstateTAfter dtInit es1) srcs → j < k)
    (Hpos : it.2 = some k) (Hw : elbIsW it.1 = true) :
    ∀ j, j ∈ dtsrcs (dstateTAfter dtInit es1) srcs →
      ((j, k), DTctrl) ∈ rowDepsT (es1 ++ (LCtrl srcs, none) :: (esA ++ it :: esB)) := by
  intro j hj
  rw [rowDepsT, AxGate.rowDepsTAuxApp]
  simp only [rowDepsTAux, List.mem_append]
  exact Or.inr (Or.inr (gateCtrlEdges _ _ esA esB it k (dtsrcsGateDtCtl _ srcs) Hbound Hpos Hw
    j hj))

/-! # 3. Graph level: the KEY LEMMA and its corollary -/

/-- F2, the graph-embedding gap, named: hart `i`'s row's tagged edges are in `gtDeps`. -/
def gtRowConformant (GT : GdexecT) (i : Agent) (row : List Eitem) : Prop :=
  ∀ j k tg, ((j, k), tg) ∈ rowDepsT row → (((i, j), (i, k)), tg) ∈ GT.gtDeps

/-- THE KEY LEMMA.  For consistent `GT`, every WRITE `(i, k)` po-after a gate is ob-after —
hence gmo-after — every gate source. -/
theorem gateStoreAfter (GT : GdexecT) (i : Agent)
    (es1 : List Eitem) (srcs : List Dsrc) (esA esB : List Eitem) (it : Eitem) (k : Nat)
    (Hconf : gtRowConformant GT i (es1 ++ (LCtrl srcs, none) :: (esA ++ it :: esB)))
    (Hcons : rvwmoCatConsistentT GT)
    (Hbound : ∀ j, j ∈ dtsrcs (dstateTAfter dtInit es1) srcs → j < k)
    (Hpos : it.2 = some k) (Hw : elbIsW it.1 = true) :
    ∀ r, r ∈ gateSrcs i (dstateTAfter dtInit es1) srcs → gmoLt GT.gtG r (i, k) := by
  intro r hr
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hr
  apply obCatTSubGmo GT _ _ Hcons
  apply gobCatTStep
  exact Or.inr ⟨DTctrl, Hconf _ _ _ (gateStoreAfterRow es1 srcs esA esB it k Hbound Hpos Hw j hj)⟩

/-- THE COROLLARY.  A memory event `(i, k)` po-after the gate that is gmo-BEFORE a gate source is
a READ. -/
theorem gateGmoEarlierIsRead (GT : GdexecT) (i : Agent)
    (es1 : List Eitem) (srcs : List Dsrc) (esA esB : List Eitem) (it : Eitem) (k : Nat)
    (Hconf : gtRowConformant GT i (es1 ++ (LCtrl srcs, none) :: (esA ++ it :: esB)))
    (Hcons : rvwmoCatConsistentT GT)
    (Hbound : ∀ j, j ∈ dtsrcs (dstateTAfter dtInit es1) srcs → j < k)
    (Hpos : it.2 = some k)
    (Hmem : elbIsR it.1 = true ∨ elbIsW it.1 = true)
    (r : Geid) (Hr : r ∈ gateSrcs i (dstateTAfter dtInit es1) srcs)
    (Hgmo : gmoLt GT.gtG (i, k) r) :
    elbIsR it.1 = true := by
  rcases Hmem with h | hw
  · exact h
  · exfalso
    have hafter := gateStoreAfter GT i es1 srcs esA esB it k Hconf Hcons Hbound Hpos hw r Hr
    exact gmoLtIrrefl GT.gtG (i, k) (gmoLtTrans _ _ _ _ Hgmo hafter)

end Weak
