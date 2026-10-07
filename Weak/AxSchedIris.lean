/-
Weak: **THE IRIS SHELL over `Weak.AxSched`'s joint gmo scheduler** (LB/AxSL ctrl-gate scheduler,
review-fetch Q4: "where does the deferred read's tie piece live at its gmo time").

Rocq: `iris/AxSchedIris.v` @ xxvzwolszwmp.

## The Rocq header, in substance

FINDING (tie-piece reachability): NOT REACHABLE as `AxToken`/`AxProt` are stated.  (a) The global
side (`protInv`, the `obStInterp` instantiation) carries only PERSISTENT per-write coverage
snapshots (`protInvPrefixCov(Mem)`), never the exclusive `histAuth` fraction that
`AxToken.ownedReadRule`'s case (i) / `AxGhost.ownedReadGhost` dereferences; `wpEvStep`/`flowEqDyn`
forbid touching an event's own slot before it steps.  (b) The hart's own WP continuation cannot
hold it either: a DEFERRED read's hart has, by construction, not run that far at the read's gmo
turn, and a cross-hart same-byte write gmo-after the read may commit before its flush, polluting
any live fraction (`AxTieProc`'s counterexample, one layer up).

THE MINIMAL FIX (`AxTieProc`'s prescription): validate the deferred read against a FROZEN history
`H_r` taken at its gmo turn.  §1 adds the snapshot-vs-snapshot comparability primitive
(`histSnapSnapPrefix`, from the mono-list's `lb_op_valid`), so two persistent snapshots of one
byte compare without a live fraction.  §2 `ownedReadGhostSnap`: given the coverage fact
`deferredReadCov` over the plain history `H_r` (taken as an explicit hypothesis: deriving it
hart-wide needs "processing order tracks gmo order for writes", future work flagged by
`AxSched`'s FINDING), the deferred read validates with NO live `histAuth` fraction — literally
`AxGhost.ownedReadGhost`'s proof body with its ghost-derived coverage replaced by the hypothesis.
§3 names the remaining wiring as unproved `Prop`s (`axpolWfProc`, `deferredSnapAvail`) and the
target `procAdequate` (an implication ending in `True`, a placeholder marking where
`AxAdequacy.ord_ea_todo`'s restated conclusion goes — NOT a claim that it holds).

**Fetches.** Nothing here depends on instruction fetches: the file speaks of ghost snapshots and of
`gwritesByte`/`greadsByte`/`gmoLt`/`gpo`/`grfAt`/`gvisible` over graph labels (`Lbl` has no fetch
constructor).

## Deviations from Rocq

1. NAMES: camelCase (map below).  No name is in `notes/weak-port-dupnames.json`; no Lean-only
   helpers.
2. VOCABULARY (`AxGhost`/`AxProt` deviation 2): `last l` ↦ `l.getLast?`; `H.*1` ↦
   `H.map Prod.fst`; `gd_g GD` ↦ `GD.gdG`; `gpo` ↦ `WeakRvwmoGraph.gpo`; `list_to_set` ↦
   `LawfulSet.ofList`; `gset geid` ↦ `GSet Geid`; `Z` ↦ `Int`; `bv 8` ↦ `BitVec 8`;
   `axlogG Σ A` ↦ `[AxlogG GF A]`; `` `prefix_of` `` ↦ `<+:`; `s_pol`/`lobp` ↦
   `Axpol.sPol`/`Axpol.lobp`.
3. STATEMENT SHAPES (`AxGhost` deviation 4): `P -∗ Q -∗ R` ↦ `P ∗ Q ⊢ R`; pure premises stay `→`.

**Rocq → Lean name map.**  `log_snap_snap_prefix` `logSnapSnapPrefix`, `hent_fst_prefix`
`hentFstPrefix`, `hist_snap_snap_prefix` `histSnapSnapPrefix`, `hist_snap_snap_elem`
`histSnapSnapElem`, `deferred_read_cov` `deferredReadCov`, `owned_read_ghost_snap`
`ownedReadGhostSnap`, `axpol_wf_proc` `axpolWfProc`, `deferred_snap_avail` `deferredSnapAvail`,
`proc_adequate` `procAdequate`.

**Not ported:** the §4 `Print Assumptions` audit (the lint's axiom check covers it).
-/
import Weak.AxProt
import Weak.AxSched
import Weak.AxTieProc
import Weak.AxGhost
import Iris.Algebra.Lib.MonoList
import Iris.BI.Lib.MonoList
import Iris.ProofMode

namespace Weak

open Iris Iris.BI Iris.Std MachCSL MachCSL.Stdpp

/-! ## 1. The new ghost primitive: two snapshots of the SAME cell compare -/

section snapCmp

variable {GF : BundledGFunctors} {A : Type} [AxlogG GF A]

/-- Two lower bounds of the same mono-list cell are comparable by prefix. -/
theorem logSnapSnapPrefix (γ : GName) (a : Int) (L1 L2 : List A) :
    logSnap (GF := GF) γ a L1 ∗ logSnap γ a L2 ⊢ ⌜L1 <+: L2 ∨ L2 <+: L1⌝ := by
  unfold logSnap
  iintro ⟨H1, H2⟩
  icases iOwn_cmraValid_op $$ [$H1 $H2] with %hv
  ipureintro
  rw [Heap.singleton_op_singleton, Heap.singleton_valid_iff] at hv
  exact ((MonoList.lb_op_valid _ _).mp hv).imp MonoList.map_mk_prefix MonoList.map_mk_prefix

end snapCmp

/-- Taking the writer half of every `Hent` preserves the prefix order. -/
theorem hentFstPrefix (H1 H2 : List Hent) (h : H1 <+: H2) :
    H1.map Prod.fst <+: H2.map Prod.fst := by
  obtain ⟨k, rfl⟩ := h
  exact ⟨k.map Prod.fst, by simp⟩

section histSnapCmp

variable {GF : BundledGFunctors} [AxlogG GF Hent]

/-- THE PRIMITIVE at `AxGhost`'s `histSnap`: two frozen histories of the same byte compare. -/
theorem histSnapSnapPrefix (γ : GName) (a : Int) (H1 H2 : List Hent) :
    histSnap (GF := GF) γ a H1 ∗ histSnap γ a H2 ⊢ ⌜H1 <+: H2 ∨ H2 <+: H1⌝ :=
  logSnapSnapPrefix γ a H1 H2

/-- Membership transfers along whichever prefix direction holds. -/
theorem histSnapSnapElem (γ : GName) (a : Int) (H1 H2 : List Hent) (w : Geid)
    (hw : w ∈ H1.map Prod.fst) :
    histSnap (GF := GF) γ a H1 ∗ histSnap γ a H2 ⊢ ⌜w ∈ H2.map Prod.fst ∨ H2 <+: H1⌝ := by
  refine (histSnapSnapPrefix γ a H1 H2).trans ?_
  iintro %h
  ipureintro
  rcases h with hp | hp
  · exact Or.inl ((hentFstPrefix H1 H2 hp).subset hw)
  · exact Or.inr hp

end histSnapCmp

/-! ## 2. The minimal fix: validate a deferred read from a FROZEN history `H_r` -/

/-- The coverage obligation over the frozen history: every gmo-before-`r` same-byte write is a
member. -/
def deferredReadCov (GD : Gdexec) (a : Int) (r : Geid) (H_r : List Hent) : Prop :=
  ∀ w v, gwritesByte GD.gdG w a v → gmoLt GD.gdG w r → w ∈ H_r.map Prod.fst

theorem ownedReadGhostSnap (GD : Gdexec) (a : Int) (r : Geid)
    (H_r : List Hent) (wl : Geid) (vl : BitVec 8) :
    rvwmoCatConsistent GD →
    (∀ p, p ∈ H_r → gwritesByte GD.gdG p.1 a p.2) →
    chainWith (gmoLt GD.gdG) (H_r.map Prod.fst) →
    (∀ w v, gwritesByte GD.gdG w a v → WeakRvwmoGraph.gpo GD.gdG w r →
      w ∈ H_r.map Prod.fst) →
    H_r.getLast? = some (wl, vl) →
    gvisible GD.gdG wl r →
    (∃ t v, greadsByte GD.gdG r a t v) →
    deferredReadCov GD a r H_r →
    grfAt GD.gdG a wl r ∧ ∀ t v, greadsByte GD.gdG r a t v → v = vl := by
  intro hcons hwr hch hown hlast hvis hrd hcov
  unfold deferredReadCov at hcov
  have ⟨hwf, _, hlv, _⟩ := hcons
  obtain ⟨H0, rfl⟩ := List.getLast?_eq_some_iff.mp hlast
  have hfst : (H0 ++ [(wl, vl)]).map Prod.fst = H0.map Prod.fst ++ [wl] := by simp
  rw [hfst] at hch hown hcov
  have hwr' : ∀ w, w ∈ H0.map Prod.fst ++ [wl] → ∃ v, gwritesByte GD.gdG w a v := by
    intro w hw
    rw [← hfst] at hw
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hw
    exact ⟨p.2, hwr p hp⟩
  have hobch : obCatChain GD (H0.map Prod.fst ++ [wl]) := by
    intro i w1 w2 hi1 hi2
    have hpos := hch i w1 w2 hi1 hi2
    obtain ⟨v1, hwb1⟩ := hwr' w1 (List.mem_of_getElem? hi1)
    obtain ⟨v2, hwb2⟩ := hwr' w2 (List.mem_of_getElem? hi2)
    apply gobCatStep
    refine Or.inr (Or.inr (Or.inr (Or.inl ⟨a, v1, v2, hwb1, hwb2, ?_⟩)))
    exact (gwixGposLt GD.gdG w1 w2 hwf.1 (gwritesByteGwrites _ _ _ _ hwf hwb1)
      (gwritesByteGwrites _ _ _ _ hwf hwb2)).2 hpos.2.2
  have hwl : gwritesByte GD.gdG wl a vl := hwr (wl, vl) (by simp)
  have hrf : grfAt GD.gdG a wl r := by
    refine ownedReadCatSnoc GD (H0.map Prod.fst) wl a r hcons hwr' hobch ?_ hvis hrd
    rintro w v hwb (hmo | hpo)
    · exact hcov w v hwb hmo
    · exact hown w v hwb hpo
  exact ⟨hrf, fun t v hrdv => grfAtValue _ _ _ _ _ _ _ hlv hrf hrdv hwl⟩

/-! ## 3. The remaining wiring (named, not proved — `AxSched`'s closing FINDING) -/

/-- The processing-order analogue of `AxAdequacy.axpol_wf_gmo`: the handout fields are bounded by
the PROCESSING prefix at each event's position. -/
def axpolWfProc [Axpol] (GD : Gdexec) (proc : List Geid) : Prop :=
  ∀ n e, proc[n]? = some e →
    Axpol.sPol GD e ⊆ (LawfulSet.ofList (proc.take n) : GSet Geid) ∧
    Axpol.lobp GD e ⊆ (LawfulSet.ofList (proc.take n) : GSet Geid)

/-- The deferred-read discharge obligation: every ever-deferred read has a frozen history whose
last entry is visible to it and which covers it (`ownedReadGhostSnap`'s hypotheses). -/
def deferredSnapAvail (GD : Gdexec) (everD : GSet Geid) (r : Geid) : Prop :=
  r ∈ everD →
    ∃ (a : Int) (H_r : List Hent) (wl : Geid) (vl : BitVec 8),
      H_r.getLast? = some (wl, vl) ∧ gvisible GD.gdG wl r ∧ deferredReadCov GD a r H_r

/-- THE TARGET (placeholder): the composition a following increment must discharge; the `True`
marks where `AxAdequacy.ord_ea_todo`'s restated conclusion goes. -/
def procAdequate [Axpol] (GD : Gdexec) (proc : List Geid) (everD : GSet Geid) : Prop :=
  isProcOrder GD.gdG (fun e => e ∈ everD) proc →
  axpolWfProc GD proc →
  (∀ r, deferredSnapAvail GD everD r) →
  True

end Weak
