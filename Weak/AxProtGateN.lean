/-
Weak: **THE n-BYTE GATE COMPOSITION** (LB/AxSL rev 7, closing `AxProtBytes`'s finding (3)):
`gateDeliversExpectedN`, the n-byte lift of `AxProtGate.gateDeliversExpectedFwd`.

Rocq: `iris/AxProtGateN.v` @ xxvzwolszwmp.

## The Rocq header, in substance

`AxProtGate.naOf'`'s read slot is hard-wired to the single-byte fact `graphValue GD e = some
[(wdat wl).2]` (one byte per write event), so an n-byte gate fact needs a FRESH annotation map,
`naOfn` (additive; no existing file touched).  Its read slot carries the n-ary purity fact
`axprotgatePhiN` with the values carried explicitly via `ownedExpectedWriteb` (no `wdat`); its
write slot is the bare `∃ data, graphData GD e = some data` (needs only `HdataTot`).  The purity
half is UNCONDITIONAL (no `Hnofwd`): `axprotgatePhiN r` is an implication — for any `Hs`/`Vs` of
the shape `AxProtBytes.readnPureFacts` produces, `graphValue GD r = some Vs` — proved directly from
`HrdatnSpec` + `greadsByteDet` (`readnValueAgreePure`'s content).  FINDING: `naOfn`'s domain is a
purely syntactic fact (`naOfnDom`, via `mapOfFunLookupSome`/`None`); no `axprotAdequateGhost'` or
`Hdomn` hypothesis is needed.  `axprotgateGateFactsn` is `AxProtGate`'s §3/§8 composition.

**Fetches.** Graph events only (Stage C); nothing here mentions fetches.

## Deviations from Rocq

1. NAMES: camelCase (map below); no name of this file is in the dup table.  Lean-only helpers are
   file-qualified `AxProtGateN.*`.
2. CONTEXTS (as `AxProtGate` deviation 4): the section context (`GD`, `Hcons`, `HdataTot`,
   `rdatn`, `HrdatnSpec`) becomes explicit arguments in that order, each declaration taking
   exactly the ones it uses.  Rocq's unused `invGS_gen`/`axirisG`/`axpol` contexts are dropped
   (nothing here mentions them); `HdataTot`/`HrdatnSpec` are used only by `axprotgatePhiNHolds`
   (as in Rocq, where no other proof mentions them).  `GF : BundledGFunctors.{0,0,0}`
   (`gateSrcsDomOfSched` is universe-0).
3. VOCABULARY (as `AxProtBytes` deviation 3): `Hs !! j` ↦ `Hs[j]?`, `Z.of_nat j` ↦ `(j : Int)`,
   `last` ↦ `List.getLast?`, `.*2` ↦ `List.map Prod.snd`, `Forall2` ↦ `List.Forall₂`,
   `list_to_map` ↦ `PartialMap.ofList`, `dom` ↦ `FiniteMap.dom_set`, `list_to_set` ↦
   `LawfulSet.ofList`, `Forall` gate facts ↦ `gateFacts`'s `∀ e ∈ gsrcs`.
4. `axprotgatePhiNHolds` is re-proved (as Rocq), not reduced to `readnValueAgreePure`: the Lean
   `readnValueAgreePure` takes the OLD `HrdatnSpec` domain (`gisW r = false`), this file the
   corrected one (`gxLbl r = some l ∧ lbIsR l`).
5. Lean-only helpers: `AxProtGateN.naOfnLookup`/`naOfnLookupNone` (the `mapOfFunLookup*` steps),
   `AxProtGateN.domOfRun` (Rocq's inline `Hperm`/`Hdom'`).

**Rocq → Lean name map.**  `axprotgate_phi_n` `axprotgatePhiN`, `axprotgate_phi_n_holds`
`axprotgatePhiNHolds`, `na_val'n` `naVal'n`, `na_ofn` `naOfn`, `na_ofn_dom` `naOfnDom`,
`axprotgate_na_pure_globaln` `axprotgateNaPureGlobaln`, `axprotgate_gate_factsn`
`axprotgateGateFactsn`, `gate_delivers_expected_n` `gateDeliversExpectedN`.

**Not ported:** the section `Let`s `Hwf`/`Hnd_gmo` (inlined as `Hcons.1`/`Hcons.1.1`) and the
`Print Assumptions` audits.

**W13 (I) (plan `notes/weak-allocproc-plan.md` §C W13 (I); [OWN.27]).** `axprotgatePhiNHolds` (and its users here) take `AxProtGate`'s `HnoIo` premise (`gwf` admits I/O events).
-/
import Weak.AxProtBytes

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp

/-! # 1. THE ASSEMBLY -/

/-! ## 1.1 `axprotgatePhiN`: the n-byte purity fact, unconditional -/

def axprotgatePhiN (GD : Gdexec) (rdatn : Geid → Int × List (Nat × BitVec 8)) (e : Geid) : Prop :=
  if gisW GD.gdG e then ∃ data, graphData GD e = some data
  else ∀ (Hs : List (List Hent)) (Vs : List (BitVec 8)),
    List.Forall₂ (fun H v => ∃ wl, H.getLast? = some (wl, v)) Hs Vs →
    (rdatn e).2.length = Hs.length →
    (∀ (j : Nat) (H : List Hent), Hs[j]? = some H → ∀ wl vl, H.getLast? = some (wl, vl) →
      ownedExpectedWriteb GD ((rdatn e).1 + (j : Int)) e wl vl ∧
      ∃ t, greadsByte GD.gdG e ((rdatn e).1 + (j : Int)) t vl) →
    graphValue GD e = some Vs

theorem axprotgatePhiNHolds (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (HnoIo : ∀ e l, gxLbl GD.gdG e = some l → lbIsIo l = false)
    (HdataTot : ∀ w, gisW GD.gdG w = true → ∃ data, graphData GD w = some data)
    (rdatn : Geid → Int × List (Nat × BitVec 8))
    (HrdatnSpec : ∀ r l, gxLbl GD.gdG r = some l → lbIsR l = true →
      graphValue GD r = some ((rdatn r).2.map Prod.snd) ∧
      ∀ (j : Nat) t v, (rdatn r).2[j]? = some (t, v) →
        greadsByte GD.gdG r ((rdatn r).1 + (j : Int)) t v)
    (e : Geid) (Hin : e ∈ GD.gdG.gxGmo) : axprotgatePhiN GD rdatn e := by
  unfold axprotgatePhiN
  cases Hisw : gisW GD.gdG e
  · simp only [Bool.false_eq_true, ↓reduceIte]
    intro Hs Vs Hvals Hlen HPall
    obtain ⟨l, Hl, Hisr⟩ := gisROfGmo GD Hcons e Hin Hisw (HnoIo e)
    obtain ⟨Hgv, Hconn⟩ := HrdatnSpec e l Hl Hisr
    have HlenV : Hs.length = Vs.length := Hvals.length_eq
    have Heq : (rdatn e).2.map Prod.snd = Vs := by
      apply List.ext_getElem?
      intro j
      by_cases Hlt : j < Hs.length
      · have Hlt' : j < (rdatn e).2.length := by omega
        have HjH : Hs[j]? = some Hs[j] := List.getElem?_eq_getElem Hlt
        obtain ⟨v, HjV, wl, Hlast⟩ := Forall2_lookup_l Hvals HjH
        have Hjrd : (rdatn e).2[j]? = some (rdatn e).2[j] := List.getElem?_eq_getElem Hlt'
        have Hgb2 := Hconn j _ _ Hjrd
        obtain ⟨_, t, Hgb1⟩ := HPall j _ HjH wl v Hlast
        have Heqv := (greadsByteDet GD.gdG e _ _ _ _ _ Hgb1 Hgb2).2
        rw [List.getElem?_map, Hjrd, HjV, Option.map_some, Heqv]
        rfl
      · have Hge1 : ((rdatn e).2.map Prod.snd).length ≤ j := by
          rw [List.length_map]; omega
        have Hge2 : Vs.length ≤ j := by omega
        rw [List.getElem?_eq_none Hge1, List.getElem?_eq_none Hge2]
    rw [Hgv, Heq]
  · simp only [↓reduceIte]
    exact HdataTot e Hisw

/-! ## 1.2 `naOfn`: the fresh annotation map -/

section annot

variable {GF : BundledGFunctors.{0,0,0}}

def naVal'n (GD : Gdexec) (rdatn : Geid → Int × List (Nat × BitVec 8)) (e : Geid) : IProp GF :=
  if gisW GD.gdG e then iprop(∃ (data : List (BitVec 8)), ⌜graphData GD e = some data⌝)
  else iprop(⌜axprotgatePhiN GD rdatn e⌝)

def naOfn (GD : Gdexec) (rdatn : Geid → Int × List (Nat × BitVec 8)) : Mea GF :=
  PartialMap.ofList (GD.gdG.gxGmo.map fun e => (e, naVal'n GD rdatn e))

theorem AxProtGateN.naOfnLookup (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (rdatn : Geid → Int × List (Nat × BitVec 8)) (e : Geid) (He : e ∈ GD.gdG.gxGmo) :
    get? (naOfn (GF := GF) GD rdatn) e = some (naVal'n GD rdatn e) := by
  unfold naOfn
  exact mapOfFunLookupSome _ _ Hcons.1.1 e He

theorem AxProtGateN.naOfnLookupNone (GD : Gdexec) (rdatn : Geid → Int × List (Nat × BitVec 8))
    (e : Geid) (He : e ∉ GD.gdG.gxGmo) :
    get? (naOfn (GF := GF) GD rdatn) e = none := by
  unfold naOfn
  exact mapOfFunLookupNone _ _ e He

theorem naOfnDom (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (rdatn : Geid → Int × List (Nat × BitVec 8)) :
    (FiniteMap.dom_set (naOfn (GF := GF) GD rdatn) : GSet Geid) =
      LawfulSet.ofList GD.gdG.gxGmo := by
  rw [setEq]
  intro e
  rw [elemOfDom, elemOfListToSet]
  constructor
  · intro Hv
    by_cases Hin : e ∈ GD.gdG.gxGmo
    · exact Hin
    · rw [AxProtGateN.naOfnLookupNone GD rdatn e Hin] at Hv
      exact absurd Hv Bool.false_ne_true
  · intro Hin
    rw [AxProtGateN.naOfnLookup GD Hcons rdatn e Hin]
    rfl

/-! ## 1.3 The purity half and the composition -/

theorem axprotgateNaPureGlobaln (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (rdatn : Geid → Int × List (Nat × BitVec 8)) :
    naPureGlobal (naOfn (GF := GF) GD rdatn) (axprotgatePhiN GD rdatn) := by
  intro e He
  have hin : e ∈ GD.gdG.gxGmo := by
    rw [naOfnDom GD Hcons rdatn, elemOfListToSet] at He
    exact He
  refine ⟨naVal'n GD rdatn e, AxProtGateN.naOfnLookup GD Hcons rdatn e hin, ?_⟩
  unfold annotPure naVal'n axprotgatePhiN
  cases gisW GD.gdG e
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact .rfl
  · simp only [↓reduceIte]
    iintro ⟨%data, %h⟩
    ipureintro
    exact ⟨data, h⟩

/-- Lean-only: a completed run puts `sProc` inside `dom naOfn`. -/
theorem AxProtGateN.domOfRun (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (rdatn : Geid → Int × List (Nat × BitVec 8))
    (st : Sstate) (Hrun : rtc (schedStep GD.gdG) sst0 st)
    (Hfull : st.sN = GD.gdG.gxGmo.length) (Hdone : st.sD = ∅) :
    (LawfulSet.ofList st.sProc : GSet Geid) ⊆ FiniteMap.dom_set (naOfn (GF := GF) GD rdatn) := by
  have HGw := schedHGwf GD Hcons
  have HC6 := schedHCat6gmo GD Hcons
  obtain ⟨Hmemiff, _⟩ := schedCorrect GD.gdG HGw HC6 st Hrun Hfull Hdone
  rw [naOfnDom GD Hcons rdatn]
  intro e' He'
  rw [elemOfListToSet] at He' ⊢
  exact (Hmemiff e').1 He'

theorem axprotgateGateFactsn (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (rdatn : Geid → Int × List (Nat × BitVec 8))
    (i : Agent) (s0 : DstateT) (srcs : List Dsrc)
    (st : Sstate) (Hrun : rtc (schedStep GD.gdG) sst0 st)
    (Hfull : st.sN = GD.gdG.gxGmo.length) (Hdone : st.sD = ∅)
    (Hmem : ∀ r, r ∈ gateSrcs i s0 srcs → r ∈ GD.gdG.gxGmo) :
    gateFacts (naOfn (GF := GF) GD rdatn) (gateSrcs i s0 srcs) (axprotgatePhiN GD rdatn) :=
  gateFactsOfDomPure _ _ _ (axprotgateNaPureGlobaln GD Hcons rdatn)
    (gateSrcsDomOfSched GD Hcons st Hrun Hfull Hdone _
      (AxProtGateN.domOfRun GD Hcons rdatn st Hrun Hfull Hdone) _ Hmem)

/-! # 2. THE TASK CONCLUSION: `gateDeliversExpectedN` -/

theorem gateDeliversExpectedN (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (rdatn : Geid → Int × List (Nat × BitVec 8))
    (i : Agent) (s0 : DstateT) (srcs : List Dsrc)
    (st : Sstate) (Hrun : rtc (schedStep GD.gdG) sst0 st)
    (Hfull : st.sN = GD.gdG.gxGmo.length) (Hdone : st.sD = ∅)
    (Hmem : ∀ r, r ∈ gateSrcs i s0 srcs → r ∈ GD.gdG.gxGmo)
    (r : Geid) (Hr_src : r ∈ gateSrcs i s0 srcs) (Hnw : gisW GD.gdG r = false)
    (Hs : List (List Hent)) (Vs : List (BitVec 8))
    (Hvals : List.Forall₂ (fun H v => ∃ wl, H.getLast? = some (wl, v)) Hs Vs)
    (Hlen : (rdatn r).2.length = Hs.length)
    (HPall : ∀ (j : Nat) (H : List Hent), Hs[j]? = some H → ∀ wl vl, H.getLast? = some (wl, vl) →
      ownedExpectedWriteb GD ((rdatn r).1 + (j : Int)) r wl vl ∧
      ∃ t, greadsByte GD.gdG r ((rdatn r).1 + (j : Int)) t vl) :
    ∃ R, get? (naOfn (GF := GF) GD rdatn) r = some R ∧
      (R ⊢ iprop(⌜graphValue GD r = some Vs⌝)) := by
  obtain ⟨R, Hlook, Hpure⟩ :=
    axprotgateGateFactsn (GF := GF) GD Hcons rdatn i s0 srcs st Hrun Hfull Hdone Hmem r Hr_src
  refine ⟨R, Hlook, ?_⟩
  unfold annotPure axprotgatePhiN at Hpure
  simp only [Hnw, Bool.false_eq_true, ↓reduceIte] at Hpure
  iintro HR
  ihave %Hφ := Hpure $$ HR
  ipureintro
  exact Hφ Hs Vs Hvals Hlen HPall

end annot

end Weak
