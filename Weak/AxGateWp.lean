/-
Weak: **the ctrl-gate WP rule**, derived on top of `Weak.AxWp`/`Weak.AxWp2` (unchanged) and
`Weak.AxGate`'s `gateSrcs`.

Rocq: `iris/AxGateWp.v` @ xxvzwolszwmp.

## The Rocq header, in substance

Design `claude-notes/design/weak-memory-lb-axsl.md` rev 7 (the "ctrl gate" pivot), §7 items
1/2/4/6, and the design review `weak-memory-lb-axsl-review-fetch.md` Q2/Q4/Q5 (the review's
title is the only fetch mention; the gate never involves the fetch).

THE PIECES.  (1) `gateFacts`/`wpGate`/`wpGateCtrl`/`wpGateRow`: at an `LCtrl` step the
continuation may assume the PURE facts of the annotations of the gate's sources.  (2) Retired
(formerly `wp_ev_step_owned`; superseded by `AxReadAll.wpReadAll`).  (3) `Snippet` (§3, no Iris):
the "ld ra; ret" pattern in the abstract — after the gate the continuation is proved only at the
read's expected value.

FINDING (kept).  `gateFacts` cannot be DERIVED here: an event hands its annotation onward only via
`naSplittingWf`'s `lobp`-indexed split, consumed by the next event's `wpEvStep`; a gate has no
`Geid` (`AxGate` F3), so nothing in the ghost state `AxWp` exposes reconstructs the pure content of
an arbitrary past source's annotation.  `wpGate` therefore takes the extraction as an EXPLICIT
premise `Hna : ⊢ ∀ na, annotInterp na -∗ annotInterp na ∗ ⌜gateFacts na gsrcs φ⌝` — a hypothesis
about the `AxirisG` INSTANCE, supplied by whoever proves adequacy (the joint per-hart-frontier GMO
scheduler).  `wpGateRow` also inherits `AxGate` F2 (row/graph conformance): its sources are
`gateSrcs i s0 srcs`.

PURITY, NOT RESOURCES, CROSSES THE GATE: `gateFacts` is a bare `Prop`.  Handing the continuation a
full annotation (e.g. a `□P` of an open protocol) would be UNSOUND (MP+ctrl).

## Deviations from Rocq

1. NAMES: the tree's camelCase (map below).  No name of this file is in
   `notes/weak-port-dupnames.json`.
2. `invGS_gen HasNoLc Σ` ↦ `[InvGS_gen hlc GF]` for any `hlc` (as `AxWp` deviation 6), and only
   where used: `wpSkipStepGate`, `wpGate`, `wpGateRow` take just `[AxirisG GF]` (as
   `AxWp2.wpSkipStep`); `wpGateCtrl` (which mentions `wpEvStep`) also `[InvGS_gen hlc GF]`
   `[Axpol]`.
3. `gateFacts`: stdpp `Forall P l` ↦ `∀ e ∈ gsrcs, P e` (same meaning); `na !! e` ↦ `get? na e`.
4. `annotPure R φ := R ⊢ ⌜φ⌝` is `AxReadAll.annotDeposit` again; kept as its own definition (the
   Rocq file has both).
5. Statement shape: Rocq's `P ⊢ Q` kept as `P ⊢ Q`; `Hna` stays a `⊢ …` premise.

**Name map.**  `annot_pure` `annotPure`, `gate_facts` `gateFacts`, `wp_skip_step_gate`
`wpSkipStepGate`, `wp_gate` `wpGate`, `wl_wdata_ctrl` `wlWdataCtrl`, `wp_gate_ctrl` `wpGateCtrl`,
`wp_gate_row` `wpGateRow`, `tstate` `Tstate` (`TRead`/`TGate`/`TDone` `Tstate.TRead`/`TGate`/
`TDone`), `tgate_ok` `tgateOk`, `twp` `twp` (`twp_read`/`twp_gate`/`twp_done`
`twp.twpRead`/`twpGate`/`twpDone`), `snippet_ld_ra_ret` `snippetLdRaRet`.

**Not ported:** the §4 `Print Assumptions` block (the lint's axiom check covers it).
-/
import Weak.AxWp2
import Weak.AxGate

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp

/-! # 1. The gate's pure facts, and `wpGate` -/

section gate
variable {GF : BundledGFunctors}

/-- An annotation entails its PURE content `φ` (a meta-level entailment; `R` may carry arbitrary
resources besides). -/
def annotPure (R : IProp GF) (φ : Prop) : Prop := R ⊢ iprop(⌜φ⌝)

/-- The conjunction of the PURE parts of the annotations, in `na`, of the gate's sources
`gsrcs` — a bare `Prop`: only pure content ever crosses into a WP continuation. -/
def gateFacts (na : Mea GF) (gsrcs : List Geid) (φ : Geid → Prop) : Prop :=
  ∀ e ∈ gsrcs, ∃ R, get? na e = some R ∧ annotPure R (φ e)

variable [AxirisG GF]

/-- THE GATED SKIP STEP: `wpSkipStep`'s shape, the continuation getting the extra pure
hypothesis `gateFacts na gsrcs φ` on the same `na` the ambient `annotInterp` carries. -/
def wpSkipStepGate (GD : Gdexec) (i : Agent) (k' : Nat)
    (gsrcs : List Geid) (φ : Geid → Prop) (Ψ : IProp GF) : IProp GF :=
  iprop(∀ na, AxirisG.annotInterp na -∗ ⌜gateFacts na gsrcs φ⌝ -∗ |==> ▷ |==>
    ∃ ls' : AxirisG.logTsT GF, AxirisG.annotInterp na ∗ AxirisG.localInterp GD i k' ls' ∗ Ψ)

/-- THE RULE.  Given the adequacy-dependent premise `Hna` (NOT proved here), the gated
obligation entails the plain one. -/
theorem wpGate (GD : Gdexec) (i : Agent) (k' : Nat) (gsrcs : List Geid) (φ : Geid → Prop)
    (Ψ : IProp GF)
    (Hna : ⊢ ∀ na : Mea GF, AxirisG.annotInterp na -∗
       AxirisG.annotInterp na ∗ ⌜gateFacts na gsrcs φ⌝) :
    wpSkipStepGate GD i k' gsrcs φ Ψ ⊢ wpSkipStep GD i k' Ψ := by
  unfold wpSkipStepGate wpSkipStep
  iintro H %na Hn
  ihave Hnaw := Hna
  icases Hnaw $$ %na Hn with ⟨Hn, %Hgf⟩
  iapply H $$ %na Hn
  ipureintro
  exact Hgf

/-- `LCtrl` never carries a write half. -/
theorem wlWdataCtrl (srcs : List Dsrc) : wlWdata (Wlabel.LCtrl srcs) = none := rfl

/-- The concrete instantiation via `AxGate.gateSrcs` (F3: indexed by the hart, the row-state
accumulator and the `LCtrl` label's sources). -/
theorem wpGateRow (GD : Gdexec) (i : Agent) (k' : Nat) (s0 : DstateT) (srcs : List Dsrc)
    (φ : Geid → Prop) (Ψ : IProp GF)
    (Hna : ⊢ ∀ na : Mea GF, AxirisG.annotInterp na -∗
       AxirisG.annotInterp na ∗ ⌜gateFacts na (gateSrcs i s0 srcs) φ⌝) :
    wpSkipStepGate GD i k' (gateSrcs i s0 srcs) φ Ψ ⊢ wpSkipStep GD i k' Ψ :=
  wpGate GD i k' (gateSrcs i s0 srcs) φ Ψ Hna

end gate

section gateCtrl
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]

/-- `wpGate` plugged into `wpPreStepDef`'s branch (b) at an `LCtrl srcs` step, in the
`match wlWdata l with …` shape that definition uses. -/
theorem wpGateCtrl (GD : Gdexec) (i : Agent) (s s' : Athread) (srcs : List Dsrc)
    (gsrcs : List Geid) (φ : Geid → Prop) (Ψ : IProp GF)
    (Hna : ⊢ ∀ na : Mea GF, AxirisG.annotInterp na -∗
       AxirisG.annotInterp na ∗ ⌜gateFacts na gsrcs φ⌝) :
    wpSkipStepGate GD i s'.atK gsrcs φ Ψ ⊢
    (match wlWdata (Wlabel.LCtrl srcs) with
     | some data =>
         wpEvStep GD i s.atK (fun _ : Unit => True)
           (fun _ => graphData GD (i, s.atK) = some data) (fun _ => s'.atK) (fun _ => Ψ)
     | none => wpSkipStep GD i s'.atK Ψ) :=
  wpGate GD i s'.atK gsrcs φ Ψ Hna

end gateCtrl

/-! # 3. The abstract snippet (no Sail, no Iris): "ld ra; …; ret" -/

section Snippet
variable {V : Type} (x : V) (Post : V → Prop)

/-- `TRead`: about to read.  `TGate v`: just read `v`, about to cross the gate.  `TDone v`: past
the gate, running the code the loaded `v` selects. -/
inductive Tstate (V : Type) where
  | TRead
  | TGate (v : V)
  | TDone (v : V)

/-- The gate's pure fact: the sole source is valid iff the value read is the expected one. -/
def tgateOk (v : V) : Prop := v = x

/-- A minimal WP-shaped judgment: the read is ∀v; crossing the gate the continuation may assume
`tgateOk v`; `twpDone` discharges `Φ` directly. -/
inductive twp : Tstate V → (Tstate V → Prop) → Prop where
  | twpRead (Φ : Tstate V → Prop) : (∀ v, twp (.TGate v) Φ) → twp .TRead Φ
  | twpGate (v : V) (Φ : Tstate V → Prop) : (tgateOk x v → Φ (.TDone v)) → twp (.TGate v) Φ
  | twpDone (v : V) (Φ : Tstate V → Prop) : Φ (.TDone v) → twp (.TDone v) Φ

/-- THE SNIPPET: given the continuation only at the expected value `x`, the whole run — read
(any `v`), gate, done — is proved. -/
theorem snippetLdRaRet (Hx : Post x) :
    twp x .TRead (fun s => ∃ v, s = .TDone v ∧ Post v) := by
  apply twp.twpRead
  intro v
  apply twp.twpGate
  intro h
  unfold tgateOk at h
  rw [h]
  exact ⟨x, rfl, Hx⟩

end Snippet

end Weak
