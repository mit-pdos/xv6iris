/-
Weak: **NON-VACUOUS GATE FACTS for the concrete `AxProtCov3` instance** (LB/AxSL rev 7, C6/C14
follow-up): `naOf'` agrees with `AxProtCov3.naOf` at every write and additionally deposits, at a
read with a real write source, the pure value fact; the ownership-side and forwarding-side
readings of that value; the token-level WP read rules and their `skelAxirisG` instances.

Rocq: `iris/AxProtGate.v` @ xxvzwolszwmp.

## The Rocq header, in substance

`AxProtCov3.naOf` gives every READ a bare `emp` slot, so `naPureGlobal`/`gateFacts` could only
extract `True` at an owned read gate source.  This file builds `naOf'`: at a write it is
`AxProtCov3.naVal` unchanged; at a read `r` whose OWN named source `rown r := gwriteAt (rdat r).t`
is a real write `wl` it deposits `⌜graphValue GD r = some [(wdat wl).2]⌝`.  SCOPE: single-byte reads
only — the read's `(byte, timestamp, value)` triple is the explicit hypothesis `rdat`/`HrdatSpec`
(as `AxProtCov3`'s `HwdatSpec`/`HdataTot`), over the CORRECTED read domain
(`gxLbl r = some l ∧ lbIsR l`; `gisROfGmo` supplies it from `r ∈ gxGmo`).

FINDING (kept): the value fact comes DIRECTLY from `rvwmoCatConsistent`'s `gloadValue`
(`greadsByteRealValue`), not from `AxSchedIris.ownedReadGhostSnap`/`Hwit`/`Hnofwd`.
§1 the assembly (`axprotAdequateGhost'`); §2 `axprotgateNaPureGlobal`; §3 `axprotgateGateFacts`
via `gateFactsOfDomPure` (not `wpGateRowAdeqOfSched`, whose `∀ na` purity premise cannot be met);
§4 the ownership-side `x_r` (`ownedLastWrite`, the gmo-maximal same-byte write gmo-before `r`) and
its agreement with `rown` under `Hnofwd`; §5 `flowEqOwnedReadOwned` (AxProt's `flowEqOwnedRead`
keeping the `grfAt` half); §6 `wpReadOwnedTok` (the WP read obligation from the thread's own
`tokTie`, with the fresh-annotation allocation as the named hypothesis `Hnalloc`); §7
`gateDeliversExpected`; §8 the FORWARDING case without `Hnofwd` (`ownedForwardedWrite`,
`ownedExpectedWrite`, unconditional `axprotgatePhiOwnedFwdHolds`, `*Fwd` twins); §9 the
`skelAxirisG` instances discharging `Hnalloc` by `annotAllocAtProgress`.

**Fetches.** Graph events only (Stage C); nothing here mentions fetches.

## Deviations from Rocq

1. NAMES: camelCase (map below).  Names duplicated in the Rocq tree (`notes/weak-port-dupnames.json`)
   are FILE-QUALIFIED `AxProtGate.*`; so are the Lean-only helpers and (one-letter / generic names,
   as `AxProtCov3` deviation 1) `F'`.
2. REUSE instead of re-derivation (Rocq's header reason — guessing section-closed argument lists
   under a rebuild budget — does not apply): the write-side machinery of Rocq §1.1-1.2 and the
   unchanged `V`/`eaVal`/`eaOf` are DEFINED as / PROVED BY their `AxProtCov3` counterparts; the
   write-case flow lemmas reduce to `AxProtCov3`'s via `AxProtGate.fEqWrite` (`F' = AxProtCov3.F`
   at a write).  The statements are Rocq's.
3. VOCABULARY (as `AxProtCov3` deviation 3): `list_to_map` ↦ `PartialMap.ofList`, `dom` ↦
   `FiniteMap.dom_set`, `last` ↦ `List.getLast?`, `.*1` ↦ `List.map Prod.fst`, `Forall` gate facts
   ↦ `gateFacts`'s `∀ e ∈ gsrcs`, `<[(i,k):=P]> na` ↦ `insert na (i, k) P`, `gpo` ↦
   `WeakRvwmoGraph.gpo`.  `rdat : Int × Nat × BitVec 8` is right-nested: Rocq `.1.1/.1.2/.2` ↦
   `.1/.2.1/.2.2` (AxInstrFacts).
4. CONTEXTS: Rocq's section context (`γ`, `Hob_eq`, `GD`, `Hcons`, `wdat`, `HwdatSpec`, `HdataTot`,
   `rdat`, `HrdatSpec`) becomes explicit arguments in that order, each declaration taking exactly
   the ones it uses; `invGS_gen HasNoLc Σ` ↦ `[InvGS_gen hlc GF]` for any `hlc`.  §1 uses the
   global `axprotPol` (as Rocq, whose §1 precedes `Context axpol`); the §2+ `Context axpol` is
   used only by `wpReadOwnedTok*`, which take their own `[Axpol]` binder (as Rocq's `{!axpol}`).
5. STATEMENT SHAPES: `P -∗ Q` lemmas are `P ⊢ Q`; wand chains `⊢ A -∗ B -∗ C`.
6. §9 `Skel`: Rocq's `T : Z → Prop` oracle parameter of `skel_axirisG` is gone in Lean (Stage C);
   the instance is passed explicitly, `(axG := skelAxirisG γg Φp)`.
7. Lean-only helpers (file-qualified): `AxProtGate.naValWriteEq`, `AxProtGate.fEqWrite`,
   `AxProtGate.naOfLookup'`/`naOfLookupNone'`/`eaOfLookup`/`eaOfLookupNone`,
   `AxProtGate.todoAtEq`, `AxProtGate.annotInsertEq`, `AxProtGate.naSplittingWfEmpty`,
   `AxProtGate.lastVal` (the three-line `Hwdat_spec` argument `vl = (wdat wl).2`),
   `AxProtGate.domOfRun` (Rocq's inline `Hdom'`: a completed run's `sProc` lies in `dom naOf'`).

**Rocq → Lean name map.**  File-qualified `AxProtGate.`: `axprot_immpred_byte'`
`axprotImmpredByte'`, `axprot_immpred_gpos_lt'` `axprotImmpredGposLt'`, `axprot_immpred_inj'`
`axprotImmpredInj'`, `H_of_fuel'` `hOfFuel'`, `H_of'` `hOf'`, `H_of_fuel_S_eq'` `hOfFuelSEq'`,
`H_of_fuel_none_eq'` `hOfFuelNoneEq'`, `H_of_fuel_stable'` `hOfFuelStable'`, `H_of_first'`
`hOfFirst'`, `H_of_chain'` `hOfChain'`, `axprot_immpred_dom` `axprotImmpredDom`, `axprot_immsucc`
`axprotImmsucc`, `axprot_immsucc_some` `axprotImmsuccSome`, `axprot_immsucc_none`
`axprotImmsuccNone`, `axprot_immsucc_none_of_nonwrite` `axprotImmsuccNoneOfNonwrite`,
`first_write_uniq` `firstWriteUniq`, `V` `V`, `na_val'` `naVal'`, `ea_val` `eaVal`, `na_of'`
`naOf'`, `ea_of` `eaOf`, `ea_val_lookup_none` `eaValLookupNone`, `ea_deposit_term_emp`
`eaDepositTermEmp`, `ea_deposit_p_eq` `eaDepositPEq`, `F'` `F'`, `flow_eq_read_trivial`
`flowEqReadTrivial`, `na_of'_dom` `naOfDom'`, `ea_of_dom` `eaOfDom`.  Unqualified: `gis_r_of_gmo`
`gisROfGmo`, `rown` `rown`, `greads_byte_real_value` `greadsByteRealValue`, `flow_eq_read'_pure`
`flowEqReadPure'`, `flow_eq_ea_of_read'` `flowEqEaOfRead'`, `flow_eq_ea_of_write_nonfirst'`
`flowEqEaOfWriteNonfirst'`, `flow_eq_ea_of_write_first'` `flowEqEaOfWriteFirst'`,
`distribute_first_writes'` `distributeFirstWrites'`, `na_of'_ea_of_dom_eq` `naOfEaOfDomEq'`,
`Hea_lob'` `heaLob'`, `axprot_adequate_ghost'` `axprotAdequateGhost'`, `axprotgate_phi`
`axprotgatePhi`, `axprotgate_na_pure_global` `axprotgateNaPureGlobal`, `axprotgate_gate_facts`
`axprotgateGateFacts`, `owned_last_write` `ownedLastWrite`, `greads_byte_owned_last_write`
`greadsByteOwnedLastWrite`, `greads_byte_no_owned_last_write` `greadsByteNoOwnedLastWrite`,
`owned_last_write_uniq` `ownedLastWriteUniq`, `rown_is_owned_last_write` `rownIsOwnedLastWrite`,
`rown_none_no_owned_last_write` `rownNoneNoOwnedLastWrite`, `axprotgate_phi_owned`
`axprotgatePhiOwned`, `axprotgate_phi_owned_entails` `axprotgatePhiOwnedEntails`,
`axprotgate_gate_facts_owned` `axprotgateGateFactsOwned`, `flow_eq_owned_read_owned`
`flowEqOwnedReadOwned`, `wp_read_owned_tok` `wpReadOwnedTok`, `gate_delivers_expected`
`gateDeliversExpected`, `owned_forwarded_write` `ownedForwardedWrite`, `owned_expected_write`
`ownedExpectedWrite`, `owned_forwarded_write_uniq` `ownedForwardedWriteUniq`,
`owned_expected_write_uniq` `ownedExpectedWriteUniq`, `greads_byte_owned_expected_write`
`greadsByteOwnedExpectedWrite`, `greads_byte_owned_expected_write_none`
`greadsByteOwnedExpectedWriteNone`, `axprotgate_phi_owned_fwd` `axprotgatePhiOwnedFwd`,
`axprotgate_phi_owned_fwd_holds` `axprotgatePhiOwnedFwdHolds`, `axprotgate_na_pure_global_fwd`
`axprotgateNaPureGlobalFwd`, `axprotgate_gate_facts_fwd` `axprotgateGateFactsFwd`,
`flow_eq_owned_read_owned_fwd` `flowEqOwnedReadOwnedFwd`, `wp_read_owned_tok_fwd`
`wpReadOwnedTokFwd`, `gate_delivers_expected_fwd` `gateDeliversExpectedFwd`,
`annot_alloc_at_progress_skel` `annotAllocAtProgressSkel`, `wp_read_owned_tok_skel`
`wpReadOwnedTokSkel`, `wp_read_owned_tok_skel_fwd` `wpReadOwnedTokSkelFwd`.

**Not ported:** the section `Let`s `Hwf`/`Hnd_gmo` (inlined as `Hcons.1`/`Hcons.1.1`) and the
`Print Assumptions` audits (the lint's axiom check covers them).
-/
import Weak.AxProtCov3

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp

/-! # 1. THE ASSEMBLY -/

/-- `r ∈ gxGmo` and not a write: `r`'s label is an actual READ (the corrected `HrdatSpec` domain). -/
theorem gisROfGmo (GD : Gdexec) (Hcons : rvwmoCatConsistent GD) (e : Geid)
    (Hin : e ∈ GD.gdG.gxGmo) (Hnw : gisW GD.gdG e = false) :
    ∃ l, gxLbl GD.gdG e = some l ∧ lbIsR l = true := by
  obtain ⟨l, Hl, Hm⟩ := (Hcons.1.2.1 e).1 Hin
  refine ⟨l, Hl, ?_⟩
  unfold gisW at Hnw
  simp only [Hl] at Hnw
  unfold lbIsMem at Hm
  rw [Hnw, Bool.or_false] at Hm
  exact Hm

/-! ## 1.1 The chain machinery (`AxProtCov3`'s, deviation 2) -/

theorem AxProtGate.axprotImmpredByte' (GD : Gdexec) (wdat : Geid → Int × BitVec 8)
    (HwdatSpec : ∀ w a v, gisW GD.gdG w = true →
      (gwritesByte GD.gdG w a v ↔ (a, v) = wdat w))
    (w w0 : Geid) :
    axprotImmpred GD w = some w0 → (wdat w0).1 = (wdat w).1 :=
  AxProtCov3.axprotImmpredByte' GD wdat HwdatSpec w w0

theorem AxProtGate.axprotImmpredGposLt' (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (w w0 : Geid) :
    axprotImmpred GD w = some w0 → gpos GD.gdG w0 < gpos GD.gdG w :=
  AxProtCov3.axprotImmpredGposLt' GD Hcons w w0

theorem AxProtGate.axprotImmpredInj' (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (wdat : Geid → Int × BitVec 8)
    (HwdatSpec : ∀ w a v, gisW GD.gdG w = true →
      (gwritesByte GD.gdG w a v ↔ (a, v) = wdat w))
    (p w1 w2 : Geid) :
    axprotImmpred GD w1 = some p → axprotImmpred GD w2 = some p → w1 = w2 :=
  AxProtCov3.axprotImmpredInj' GD Hcons wdat HwdatSpec p w1 w2

def AxProtGate.hOfFuel' (GD : Gdexec) (wdat : Geid → Int × BitVec 8) : Nat → Geid → List Hent :=
  AxProtCov3.hOfFuel' GD wdat

def AxProtGate.hOf' (GD : Gdexec) (wdat : Geid → Int × BitVec 8) (w : Geid) : List Hent :=
  AxProtGate.hOfFuel' GD wdat (gpos GD.gdG w) w

theorem AxProtGate.hOfFuelSEq' (GD : Gdexec) (wdat : Geid → Int × BitVec 8) (f : Nat)
    (w w0 : Geid) :
    axprotImmpred GD w = some w0 →
    AxProtGate.hOfFuel' GD wdat (f + 1) w = AxProtGate.hOfFuel' GD wdat f w0 ++ [(w, (wdat w).2)] :=
  AxProtCov3.hOfFuelSEq' GD wdat f w w0

theorem AxProtGate.hOfFuelNoneEq' (GD : Gdexec) (wdat : Geid → Int × BitVec 8) (f : Nat)
    (w : Geid) :
    axprotImmpred GD w = none → AxProtGate.hOfFuel' GD wdat f w = [(w, (wdat w).2)] :=
  AxProtCov3.hOfFuelNoneEq' GD wdat f w

theorem AxProtGate.hOfFuelStable' (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (wdat : Geid → Int × BitVec 8) :
    ∀ f w, gpos GD.gdG w ≤ f →
      ∀ f', gpos GD.gdG w ≤ f' → AxProtGate.hOfFuel' GD wdat f w = AxProtGate.hOfFuel' GD wdat f' w :=
  AxProtCov3.hOfFuelStable' GD Hcons wdat

theorem AxProtGate.hOfFirst' (GD : Gdexec) (wdat : Geid → Int × BitVec 8) (w : Geid) :
    axprotImmpred GD w = none → AxProtGate.hOf' GD wdat w = [(w, (wdat w).2)] :=
  AxProtCov3.hOfFirst' GD wdat w

theorem AxProtGate.hOfChain' (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (wdat : Geid → Int × BitVec 8) (w w0 : Geid) :
    axprotImmpred GD w = some w0 →
    AxProtGate.hOf' GD wdat w = AxProtGate.hOf' GD wdat w0 ++ [(w, (wdat w).2)] :=
  AxProtCov3.hOfChain' GD Hcons wdat w w0

/-! ## 1.2 `axprotImmsucc` (`AxProtCov3`'s) -/

theorem AxProtGate.axprotImmpredDom (GD : Gdexec) (Hcons : rvwmoCatConsistent GD) (w w0 : Geid) :
    axprotImmpred GD w = some w0 → w ∈ GD.gdG.gxGmo :=
  AxProtCov3.axprotImmpredDom GD Hcons w w0

def AxProtGate.axprotImmsucc (GD : Gdexec) (p : Geid) : Option Geid :=
  AxProtCov3.axprotImmsucc GD p

theorem AxProtGate.axprotImmsuccSome (GD : Gdexec) (p w' : Geid) :
    AxProtGate.axprotImmsucc GD p = some w' → axprotImmpred GD w' = some p :=
  AxProtCov3.axprotImmsuccSome GD p w'

theorem AxProtGate.axprotImmsuccNone (GD : Gdexec) (Hcons : rvwmoCatConsistent GD) (p : Geid) :
    AxProtGate.axprotImmsucc GD p = none → ∀ w', axprotImmpred GD w' = some p → False :=
  AxProtCov3.axprotImmsuccNone GD Hcons p

theorem AxProtGate.axprotImmsuccNoneOfNonwrite (GD : Gdexec) (p : Geid)
    (Hp : gisW GD.gdG p = false) : AxProtGate.axprotImmsucc GD p = none :=
  AxProtCov3.axprotImmsuccNoneOfNonwrite GD p Hp

theorem AxProtGate.firstWriteUniq (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (w1 w2 : Geid) (a : Int) (v1 v2 : BitVec 8) :
    gwritesByte GD.gdG w1 a v1 → axprotImmpred GD w1 = none →
    gwritesByte GD.gdG w2 a v2 → axprotImmpred GD w2 = none →
    w1 = w2 :=
  AxProtCov3.firstWriteUniq GD Hcons w1 w2 a v1 v2

/-! ## 1.3 `naVal'`/`eaVal`, and the `eaDeposit` collapse -/

/-- The write, if any, the read's OWN named source points at (`none`: an image read). -/
def rown (GD : Gdexec) (rdat : Geid → Int × Nat × BitVec 8) (r : Geid) : Option Geid :=
  gwriteAt GD.gdG (rdat r).2.1

section annot

variable {GF : BundledGFunctors} [AxlogG GF Hent]

def AxProtGate.V (γ : GName) (GD : Gdexec) (wdat : Geid → Int × BitVec 8) (p : Geid) : IProp GF :=
  AxProtCov3.V γ GD wdat p

/-- THE VALUE FACT per event: writes as `AxProtCov3.naVal`; an owned read the value of its source. -/
def AxProtGate.naVal' (γ : GName) (GD : Gdexec) (wdat : Geid → Int × BitVec 8)
    (rdat : Geid → Int × Nat × BitVec 8) (e : Geid) : IProp GF :=
  if gisW GD.gdG e then
    iprop(histSnap γ (wdat e).1 (AxProtGate.hOf' GD wdat e) ∗
      ∃ (data : List (BitVec 8)), ⌜graphData GD e = some data⌝)
  else
    match rown GD rdat e with
    | some wl => iprop(⌜graphValue GD e = some [(wdat wl).2]⌝)
    | none => iprop(emp)

def AxProtGate.eaVal (γ : GName) (GD : Gdexec) (wdat : Geid → Int × BitVec 8) (e : Geid) :
    Mea GF :=
  AxProtCov3.eaVal γ GD wdat e

def AxProtGate.naOf' (γ : GName) (GD : Gdexec) (wdat : Geid → Int × BitVec 8)
    (rdat : Geid → Int × Nat × BitVec 8) : Mea GF :=
  PartialMap.ofList (GD.gdG.gxGmo.map fun e => (e, AxProtGate.naVal' γ GD wdat rdat e))

def AxProtGate.eaOf (γ : GName) (GD : Gdexec) (wdat : Geid → Int × BitVec 8) : Sra GF :=
  AxProtCov3.eaOf γ GD wdat

/-- Lean-only: at a write `naVal'` is `AxProtCov3.naVal`. -/
theorem AxProtGate.naValWriteEq (γ : GName) (GD : Gdexec) (wdat : Geid → Int × BitVec 8)
    (rdat : Geid → Int × Nat × BitVec 8) (e : Geid) (Hisw : gisW GD.gdG e = true) :
    AxProtGate.naVal' (GF := GF) γ GD wdat rdat e = AxProtCov3.naVal γ GD wdat e := by
  unfold AxProtGate.naVal' AxProtCov3.naVal
  simp only [Hisw, ↓reduceIte]
  rfl

theorem AxProtGate.naOfLookup' (γ : GName) (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (wdat : Geid → Int × BitVec 8) (rdat : Geid → Int × Nat × BitVec 8) (e : Geid)
    (He : e ∈ GD.gdG.gxGmo) :
    get? (AxProtGate.naOf' (GF := GF) γ GD wdat rdat) e =
      some (AxProtGate.naVal' γ GD wdat rdat e) := by
  unfold AxProtGate.naOf'
  exact mapOfFunLookupSome _ _ Hcons.1.1 e He

theorem AxProtGate.naOfLookupNone' (γ : GName) (GD : Gdexec) (wdat : Geid → Int × BitVec 8)
    (rdat : Geid → Int × Nat × BitVec 8) (e : Geid) (He : e ∉ GD.gdG.gxGmo) :
    get? (AxProtGate.naOf' (GF := GF) γ GD wdat rdat) e = none := by
  unfold AxProtGate.naOf'
  exact mapOfFunLookupNone _ _ e He

theorem AxProtGate.eaOfLookup (γ : GName) (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (wdat : Geid → Int × BitVec 8) (e : Geid) (He : e ∈ GD.gdG.gxGmo) :
    get? (AxProtGate.eaOf (GF := GF) γ GD wdat) e = some (AxProtGate.eaVal γ GD wdat e) :=
  AxProtCov3.eaOfLookup γ GD Hcons wdat e He

theorem AxProtGate.eaOfLookupNone (γ : GName) (GD : Gdexec) (wdat : Geid → Int × BitVec 8)
    (e : Geid) (He : e ∉ GD.gdG.gxGmo) :
    get? (AxProtGate.eaOf (GF := GF) γ GD wdat) e = none :=
  AxProtCov3.eaOfLookupNone γ GD wdat e He

theorem AxProtGate.eaValLookupNone (γ : GName) (GD : Gdexec) (wdat : Geid → Int × BitVec 8)
    (eOut p : Geid) :
    axprotImmpred GD eOut ≠ some p → get? (AxProtGate.eaVal (GF := GF) γ GD wdat eOut) p = none :=
  AxProtCov3.eaValLookupNone γ GD wdat eOut p

theorem AxProtGate.eaDepositTermEmp {hlc : HasLC} [InvGS_gen hlc GF] [AxirisG GF]
    (γ : GName) (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (wdat : Geid → Int × BitVec 8) (eOut p : Geid) (Hne : axprotImmpred GD eOut ≠ some p) :
    ⊢ AxLifting.depAt (AxProtGate.eaOf (GF := GF) γ GD wdat) p eOut :=
  AxProtCov3.eaDepositTermEmp γ GD Hcons wdat eOut p Hne

theorem AxProtGate.eaDepositPEq {hlc : HasLC} [InvGS_gen hlc GF] [AxirisG GF]
    (γ : GName) (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (wdat : Geid → Int × BitVec 8)
    (HwdatSpec : ∀ w a v, gisW GD.gdG w = true →
      (gwritesByte GD.gdG w a v ↔ (a, v) = wdat w))
    (p : Geid) :
    eaDeposit (AxProtGate.eaOf (GF := GF) γ GD wdat) (lobSuccOf GD p) p ⊣⊢
      (match AxProtGate.axprotImmsucc GD p with
       | some _ => AxProtGate.V γ GD wdat p
       | none => iprop(emp)) :=
  AxProtCov3.eaDepositPEq γ GD Hcons wdat HwdatSpec p

end annot

/-! ## 1.4 The per-event flow obligations -/

section flows

variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [AxlogG GF Hent]

def AxProtGate.F' (γ : GName) (GD : Gdexec) (wdat : Geid → Int × BitVec 8)
    (rdat : Geid → Int × Nat × BitVec 8) (e0 : Geid) : IProp GF :=
  flowEqEa GD e0 (Axpol.sPol GD e0) (AxProtGate.eaVal γ GD wdat e0) (AxProtGate.eaOf γ GD wdat)
    (AxProtGate.naVal' γ GD wdat rdat e0)

/-- Lean-only: at a write `F'` is `AxProtCov3.F`. -/
theorem AxProtGate.fEqWrite (γ : GName) (GD : Gdexec) (wdat : Geid → Int × BitVec 8)
    (rdat : Geid → Int × Nat × BitVec 8) (e0 : Geid) (Hisw : gisW GD.gdG e0 = true) :
    AxProtGate.F' (GF := GF) γ GD wdat rdat e0 = AxProtCov3.F γ GD wdat e0 := by
  unfold AxProtGate.F' AxProtCov3.F
  rw [AxProtGate.naValWriteEq γ GD wdat rdat e0 Hisw]
  rfl

theorem AxProtGate.flowEqReadTrivial (γ : GName)
    (Hob_eq : ∀ (GD : Gdexec) (σ : AxirisG.obSt GF) (s : GSet Geid),
      AxirisG.obStInterp GD σ s ⊣⊢ protInv γ GD s)
    (GD : Gdexec) (r : Geid) (Hr : gisW GD.gdG r = false) :
    ⊢ flowEqDyn GD r ∅ (∅ : Mea GF) iprop(emp) :=
  AxProtCov3.flowEqReadTrivial γ Hob_eq GD r Hr

/-- THE READ-SIDE VALUE FACT: the read's own source pins its value (`gloadValue`). -/
theorem greadsByteRealValue (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (wdat : Geid → Int × BitVec 8)
    (HwdatSpec : ∀ w a v, gisW GD.gdG w = true →
      (gwritesByte GD.gdG w a v ↔ (a, v) = wdat w))
    (r : Geid) (a : Int) (t : Nat) (v : BitVec 8) (wl : Geid) :
    greadsByte GD.gdG r a t v → gwriteAt GD.gdG t = some wl → v = (wdat wl).2 := by
  intro Hgb Hwrat
  have ⟨_, _, Hgv, _⟩ := Hcons
  obtain ⟨Hsrc, _⟩ := Hgv r a t v Hgb
  cases t with
  | zero => simp [gwriteAt] at Hwrat
  | succ t' =>
    obtain ⟨w0, Hwat0, Hwb0, _⟩ := Hsrc
    have hw : w0 = wl := Option.some.inj (Hwat0.symm.trans Hwrat)
    rw [hw] at Hwb0
    exact congrArg Prod.snd ((HwdatSpec wl a v (WeakRvwmoGraph.gwritesByteGisW _ _ _ _ Hwb0)).1 Hwb0)

theorem flowEqReadPure' (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (wdat : Geid → Int × BitVec 8)
    (HwdatSpec : ∀ w a v, gisW GD.gdG w = true →
      (gwritesByte GD.gdG w a v ↔ (a, v) = wdat w))
    (rdat : Geid → Int × Nat × BitVec 8)
    (HrdatSpec : ∀ r l, gxLbl GD.gdG r = some l → lbIsR l = true →
      graphValue GD r = some [(rdat r).2.2] ∧
      greadsByte GD.gdG r (rdat r).1 (rdat r).2.1 (rdat r).2.2)
    (r : Geid) (Hin : r ∈ GD.gdG.gxGmo) (Hnw : gisW GD.gdG r = false) :
    match rown GD rdat r with
    | some wl => graphValue GD r = some [(wdat wl).2]
    | none => True := by
  obtain ⟨l, Hl, Hisr⟩ := gisROfGmo GD Hcons r Hin Hnw
  obtain ⟨Hgvv, Hgb⟩ := HrdatSpec r l Hl Hisr
  unfold rown
  cases Hro : gwriteAt GD.gdG (rdat r).2.1 with
  | none => trivial
  | some wl =>
    show graphValue GD r = some [(wdat wl).2]
    rw [Hgvv, greadsByteRealValue GD Hcons wdat HwdatSpec r _ _ _ wl Hgb Hro]

theorem flowEqEaOfRead' (γ : GName)
    (Hob_eq : ∀ (GD : Gdexec) (σ : AxirisG.obSt GF) (s : GSet Geid),
      AxirisG.obStInterp GD σ s ⊣⊢ protInv γ GD s)
    (GD : Gdexec) (Hcons : rvwmoCatConsistent GD) (wdat : Geid → Int × BitVec 8)
    (HwdatSpec : ∀ w a v, gisW GD.gdG w = true →
      (gwritesByte GD.gdG w a v ↔ (a, v) = wdat w))
    (rdat : Geid → Int × Nat × BitVec 8)
    (HrdatSpec : ∀ r l, gxLbl GD.gdG r = some l → lbIsR l = true →
      graphValue GD r = some [(rdat r).2.2] ∧
      greadsByte GD.gdG r (rdat r).1 (rdat r).2.1 (rdat r).2.2)
    (e0 : Geid) (Hin : e0 ∈ GD.gdG.gxGmo) (Hnw : gisW GD.gdG e0 = false) :
    ⊢ AxProtGate.F' (GF := GF) γ GD wdat rdat e0 := by
  have hea : AxProtGate.eaVal (GF := GF) γ GD wdat e0 = ∅ := by
    unfold AxProtGate.eaVal AxProtCov3.eaVal; simp only [Hnw, Bool.false_eq_true, ↓reduceIte]
  have hna : (iprop(emp) : IProp GF) ⊢ AxProtGate.naVal' γ GD wdat rdat e0 := by
    have hp := flowEqReadPure' GD Hcons wdat HwdatSpec rdat HrdatSpec e0 Hin Hnw
    unfold AxProtGate.naVal'
    simp only [Hnw, Bool.false_eq_true, ↓reduceIte]
    revert hp
    cases rown GD rdat e0 with
    | none => intro _; exact .rfl
    | some wl => intro hp; exact pure_intro hp
  have hdep : ⊢ eaDeposit (AxProtGate.eaOf (GF := GF) γ GD wdat) (lobSuccOf GD e0) e0 := by
    have h := (AxProtGate.eaDepositPEq (GF := GF) γ GD Hcons wdat HwdatSpec e0).2
    rw [AxProtGate.axprotImmsuccNoneOfNonwrite GD e0 Hnw] at h
    exact h
  have hbase : ⊢ flowEqDyn GD e0 (Axpol.sPol GD e0) (∅ : Mea GF) iprop(emp) :=
    (AxProtGate.flowEqReadTrivial γ Hob_eq GD e0 Hnw).trans
      (flowEqDynPolMono GD e0 ∅ _ ∅ _ emptySubseteq)
  have hpost : (iprop(emp) : IProp GF) ⊢
      iprop(AxProtGate.naVal' γ GD wdat rdat e0 ∗
        eaDeposit (AxProtGate.eaOf (GF := GF) γ GD wdat) (lobSuccOf GD e0) e0) :=
    emp_sep.2.trans (sep_mono hna hdep)
  unfold AxProtGate.F' flowEqEa
  rw [hea]
  exact hbase.trans (AxProtCov3.flowEqDynPost GD e0 _ _ _ _ hpost)

theorem flowEqEaOfWriteNonfirst' (γ : GName)
    (Hob_eq : ∀ (GD : Gdexec) (σ : AxirisG.obSt GF) (s : GSet Geid),
      AxirisG.obStInterp GD σ s ⊣⊢ protInv γ GD s)
    (GD : Gdexec) (Hcons : rvwmoCatConsistent GD) (wdat : Geid → Int × BitVec 8)
    (HwdatSpec : ∀ w a v, gisW GD.gdG w = true →
      (gwritesByte GD.gdG w a v ↔ (a, v) = wdat w))
    (HdataTot : ∀ w, gisW GD.gdG w = true → ∃ data, graphData GD w = some data)
    (rdat : Geid → Int × Nat × BitVec 8)
    (e0 w0 : Geid) (Hisw : gisW GD.gdG e0 = true) (Himm : axprotImmpred GD e0 = some w0) :
    ⊢ AxProtGate.F' (GF := GF) γ GD wdat rdat e0 := by
  rw [AxProtGate.fEqWrite γ GD wdat rdat e0 Hisw]
  exact flowEqEaOfWriteNonfirst γ Hob_eq GD Hcons wdat HwdatSpec HdataTot e0 w0 Hisw Himm

theorem flowEqEaOfWriteFirst' (γ : GName)
    (Hob_eq : ∀ (GD : Gdexec) (σ : AxirisG.obSt GF) (s : GSet Geid),
      AxirisG.obStInterp GD σ s ⊣⊢ protInv γ GD s)
    (GD : Gdexec) (Hcons : rvwmoCatConsistent GD) (wdat : Geid → Int × BitVec 8)
    (HwdatSpec : ∀ w a v, gisW GD.gdG w = true →
      (gwritesByte GD.gdG w a v ↔ (a, v) = wdat w))
    (HdataTot : ∀ w, gisW GD.gdG w = true → ∃ data, graphData GD w = some data)
    (rdat : Geid → Int × Nat × BitVec 8)
    (e0 : Geid) (Hisw : gisW GD.gdG e0 = true) (Himm : axprotImmpred GD e0 = none) :
    histAuth γ (wdat e0).1 1 [] ⊢ AxProtGate.F' (GF := GF) γ GD wdat rdat e0 := by
  rw [AxProtGate.fEqWrite γ GD wdat rdat e0 Hisw]
  exact flowEqEaOfWriteFirst γ Hob_eq GD Hcons wdat HwdatSpec HdataTot e0 Hisw Himm

/-! ## 1.5 `distributeFirstWrites'` -/

theorem distributeFirstWrites' (γ : GName)
    (Hob_eq : ∀ (GD : Gdexec) (σ : AxirisG.obSt GF) (s : GSet Geid),
      AxirisG.obStInterp GD σ s ⊣⊢ protInv γ GD s)
    (GD : Gdexec) (Hcons : rvwmoCatConsistent GD) (wdat : Geid → Int × BitVec 8)
    (HwdatSpec : ∀ w a v, gisW GD.gdG w = true →
      (gwritesByte GD.gdG w a v ↔ (a, v) = wdat w))
    (HdataTot : ∀ w, gisW GD.gdG w = true → ∃ data, graphData GD w = some data)
    (rdat : Geid → Int × Nat × BitVec 8)
    (HrdatSpec : ∀ r l, gxLbl GD.gdG r = some l → lbIsR l = true →
      graphValue GD r = some [(rdat r).2.2] ∧
      greadsByte GD.gdG r (rdat r).1 (rdat r).2.1 (rdat r).2.2)
    (K : List Geid) :
    ∀ (Xk : GSet Int), K.Nodup → (∀ w, w ∈ K → w ∈ GD.gdG.gxGmo) →
      (∀ w, w ∈ K → gisW GD.gdG w = true → axprotImmpred GD w = none → (wdat w).1 ∈ Xk) →
      iprop([∗set] a ∈ Xk, histAuth (GF := GF) γ a 1 []) ⊢
        [∗list] e0 ∈ K, AxProtGate.F' γ GD wdat rdat e0 := by
  induction K with
  | nil => intro _ _ _ _; exact BigSepL.bigSepL_nil_intro
  | cons e0 K ih =>
    intro Xk Hnd Hgmo Hcov
    obtain ⟨Hnin, Hnd'⟩ := List.nodup_cons.1 Hnd
    refine Entails.trans ?_ BigSepL.bigSepL_cons.2
    have Hgmo' : ∀ w, w ∈ K → w ∈ GD.gdG.gxGmo := fun w hw => Hgmo w (List.mem_cons.2 (Or.inr hw))
    have Hcov' : ∀ w, w ∈ K → gisW GD.gdG w = true → axprotImmpred GD w = none →
        (wdat w).1 ∈ Xk := fun w hw h1 h2 => Hcov w (List.mem_cons.2 (Or.inr hw)) h1 h2
    cases Hisw : gisW GD.gdG e0
    · exact emp_sep.2.trans (sep_mono
        (flowEqEaOfRead' γ Hob_eq GD Hcons wdat HwdatSpec rdat HrdatSpec e0
          (Hgmo e0 (List.mem_cons.2 (Or.inl rfl))) Hisw)
        (ih Xk Hnd' Hgmo' Hcov'))
    · cases Himm : axprotImmpred GD e0 with
      | some w0 =>
        exact emp_sep.2.trans (sep_mono
          (flowEqEaOfWriteNonfirst' γ Hob_eq GD Hcons wdat HwdatSpec HdataTot rdat e0 w0 Hisw Himm)
          (ih Xk Hnd' Hgmo' Hcov'))
      | none =>
        have Ha : (wdat e0).1 ∈ Xk := Hcov e0 (List.mem_cons.2 (Or.inl rfl)) Hisw Himm
        have Hcov'' : ∀ w, w ∈ K → gisW GD.gdG w = true → axprotImmpred GD w = none →
            (wdat w).1 ∈ Xk \ {(wdat e0).1} := by
          intro w hw hisw' himm'
          refine elemOfDifference.2 ⟨Hcov' w hw hisw' himm', fun heq => ?_⟩
          have heqa := elemOfSingleton.1 heq
          have hbyw : gwritesByte GD.gdG w (wdat w).1 (wdat w).2 := (HwdatSpec w _ _ hisw').2 rfl
          have hbye0 : gwritesByte GD.gdG e0 (wdat w).1 (wdat e0).2 := by
            rw [heqa]; exact (HwdatSpec e0 _ _ Hisw).2 rfl
          have hwe0 := AxProtGate.firstWriteUniq GD Hcons w e0 (wdat w).1 (wdat w).2 (wdat e0).2
            hbyw himm' hbye0 Himm
          exact Hnin (hwe0 ▸ hw)
        exact (BigSepS.bigSepS_delete Ha).1.trans (sep_mono
          (flowEqEaOfWriteFirst' γ Hob_eq GD Hcons wdat HwdatSpec HdataTot rdat e0 Hisw Himm)
          (ih _ Hnd' Hgmo' Hcov''))

end flows

/-! ## 1.6 Domain facts -/

section dom

variable {GF : BundledGFunctors} [AxlogG GF Hent]

theorem AxProtGate.naOfDom' (γ : GName) (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (wdat : Geid → Int × BitVec 8) (rdat : Geid → Int × Nat × BitVec 8) :
    (FiniteMap.dom_set (AxProtGate.naOf' (GF := GF) γ GD wdat rdat) : GSet Geid) =
      LawfulSet.ofList GD.gdG.gxGmo := by
  rw [setEq]
  intro e
  rw [elemOfDom, elemOfListToSet]
  constructor
  · intro Hv
    by_cases Hin : e ∈ GD.gdG.gxGmo
    · exact Hin
    · rw [AxProtGate.naOfLookupNone' γ GD wdat rdat e Hin] at Hv
      exact absurd Hv Bool.false_ne_true
  · intro Hin
    rw [AxProtGate.naOfLookup' γ GD Hcons wdat rdat e Hin]
    rfl

theorem AxProtGate.eaOfDom (γ : GName) (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (wdat : Geid → Int × BitVec 8) :
    (FiniteMap.dom_set (AxProtGate.eaOf (GF := GF) γ GD wdat) : GSet Geid) =
      LawfulSet.ofList GD.gdG.gxGmo :=
  AxProtCov3.eaOfDom γ GD Hcons wdat

theorem naOfEaOfDomEq' (γ : GName) (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (wdat : Geid → Int × BitVec 8) (rdat : Geid → Int × Nat × BitVec 8) :
    (FiniteMap.dom_set (AxProtGate.eaOf (GF := GF) γ GD wdat) : GSet Geid) =
      FiniteMap.dom_set (AxProtGate.naOf' (GF := GF) γ GD wdat rdat) := by
  rw [AxProtGate.eaOfDom γ GD Hcons wdat, AxProtGate.naOfDom' γ GD Hcons wdat rdat]

theorem heaLob' (γ : GName) (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (wdat : Geid → Int × BitVec 8) :
    ∀ e0 gm, get? (AxProtGate.eaOf (GF := GF) γ GD wdat) e0 = some gm →
      (FiniteMap.dom_set gm : GSet Geid) ⊆ Axpol.lobp GD e0 :=
  heaLob γ GD Hcons wdat

end dom

/-! ## 1.7 The wiring theorem -/

section wiring

variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [AxlogG GF Hent]

/-- Lean-only: the `ordEaTodoL` line at a `gxGmo` event is `F'`. -/
theorem AxProtGate.todoAtEq (γ : GName) (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (wdat : Geid → Int × BitVec 8) (rdat : Geid → Int × Nat × BitVec 8) (e : Geid)
    (He : e ∈ GD.gdG.gxGmo) :
    AxWp.fromOption (fun R0 => AxWp.fromOption
        (fun flowIn => flowEqEa GD e (Axpol.sPol GD e) flowIn (AxProtGate.eaOf (GF := GF) γ GD wdat)
          R0) iprop(emp) (get? (AxProtGate.eaOf (GF := GF) γ GD wdat) e))
      iprop(emp) (get? (AxProtGate.naOf' (GF := GF) γ GD wdat rdat) e) =
    AxProtGate.F' γ GD wdat rdat e := by
  rw [AxProtGate.naOfLookup' γ GD Hcons wdat rdat e He, AxProtGate.eaOfLookup γ GD Hcons wdat e He]
    <;> rfl

theorem axprotAdequateGhost' (γ : GName)
    (Hob_eq : ∀ (GD : Gdexec) (σ : AxirisG.obSt GF) (s : GSet Geid),
      AxirisG.obStInterp GD σ s ⊣⊢ protInv γ GD s)
    (GD : Gdexec) (Hcons : rvwmoCatConsistent GD) (wdat : Geid → Int × BitVec 8)
    (HwdatSpec : ∀ w a v, gisW GD.gdG w = true →
      (gwritesByte GD.gdG w a v ↔ (a, v) = wdat w))
    (HdataTot : ∀ w, gisW GD.gdG w = true → ∃ data, graphData GD w = some data)
    (rdat : Geid → Int × Nat × BitVec 8)
    (HrdatSpec : ∀ r l, gxLbl GD.gdG r = some l → lbIsR l = true →
      graphValue GD r = some [(rdat r).2.2] ∧
      greadsByte GD.gdG r (rdat r).1 (rdat r).2.1 (rdat r).2.2)
    (st : Sstate) (Hrun : rtc (schedStep GD.gdG) sst0 st)
    (Hfull : st.sN = GD.gdG.gxGmo.length) (Hdone : st.sD = ∅)
    (Hreal : ∀ r, r ∈ st.sEverD →
      ∃ a t vr wl, greadsByte GD.gdG r a t vr ∧ gwriteAt GD.gdG t = some wl)
    (σ0 : AxirisG.obSt GF) :
    ⊢ ([∗set] a ∈ (LawfulSet.ofList ((gwrites GD.gdG).map fun w => (wdat w).1) : GSet Int),
          histAuth (GF := GF) γ a 1 []) -∗
      AxirisG.obStInterp GD σ0 ∅ -∗
      |={⊤}[∅]▷=>^[st.sProc.length]
        ∃ (σ : AxirisG.obSt GF),
          AxirisG.obStInterp GD σ (LawfulSet.ofList st.sProc) ∗
          [∗set] e0 ∈ (LawfulSet.ofList st.sProc : GSet Geid),
            AxProtGate.naVal' γ GD wdat rdat e0 := by
  have HGw := schedHGwf GD Hcons
  have HC6 := schedHCat6gmo GD Hcons
  obtain ⟨Hmemiff, HndP, _⟩ := schedCorrect GD.gdG HGw HC6 st Hrun Hfull Hdone
  have Hperm : st.sProc.Perm GD.gdG.gxGmo := NoDup_Permutation HndP HGw.1 Hmemiff
  have Hcov0 : ∀ w, w ∈ GD.gdG.gxGmo → gisW GD.gdG w = true → axprotImmpred GD w = none →
      (wdat w).1 ∈ (LawfulSet.ofList ((gwrites GD.gdG).map fun w0 => (wdat w0).1) : GSet Int) :=
    fun w hw hisw _ => elemOfListToSet.2 (List.mem_map.2 ⟨w, (gwritesElemOf _ _).2 ⟨hw, hisw⟩, rfl⟩)
  have Htodo : ([∗set] a ∈ (LawfulSet.ofList ((gwrites GD.gdG).map fun w => (wdat w).1) :
        GSet Int), histAuth (GF := GF) γ a 1 []) ⊢
      ordEaTodoL GD (AxProtGate.eaOf γ GD wdat) (AxProtGate.naOf' γ GD wdat rdat) st.sProc 0 := by
    refine (distributeFirstWrites' γ Hob_eq GD Hcons wdat HwdatSpec HdataTot rdat HrdatSpec
      GD.gdG.gxGmo _ HGw.1 (fun _ h => h) Hcov0).trans ?_
    unfold ordEaTodoL
    simp only [List.drop_zero]
    refine Entails.trans ?_ (BigSepL.bigSepL_perm Hperm.symm).1
    exact (BiEntails.of_eq (BigSepL.bigSepL_eq fun {_ x} hk =>
      (AxProtGate.todoAtEq γ GD Hcons wdat rdat x (List.mem_of_getElem? hk)).symm)).1
  have Hdom : (LawfulSet.ofList st.sProc : GSet Geid) ⊆
      FiniteMap.dom_set (AxProtGate.naOf' (GF := GF) γ GD wdat rdat) := by
    rw [AxProtGate.naOfDom' γ GD Hcons wdat rdat]
    intro e' He'
    rw [elemOfListToSet] at He' ⊢
    exact (Hmemiff e').1 He'
  have Hbag : ([∗set] e0 ∈ (LawfulSet.ofList st.sProc : GSet Geid),
        AxWp.fromOption (fun P => P) iprop(emp)
          (get? (AxProtGate.naOf' (GF := GF) γ GD wdat rdat) e0)) ⊢
      [∗set] e0 ∈ (LawfulSet.ofList st.sProc : GSet Geid), AxProtGate.naVal' γ GD wdat rdat e0 :=
    BigSepS.bigSepS_mono fun {e0} he => by
      have hin : e0 ∈ GD.gdG.gxGmo := (Hmemiff e0).1 (elemOfListToSet.1 he)
      rw [AxProtGate.naOfLookup' γ GD Hcons wdat rdat e0 hin] <;> exact .rfl
  have Had := axprotSchedProcAdequateCov GD Hcons st Hrun Hfull Hdone
    (AxProtGate.naOf' γ GD wdat rdat) (AxProtGate.eaOf γ GD wdat)
    (naOfEaOfDomEq' γ GD Hcons wdat rdat) Hdom (heaLob' γ GD Hcons wdat) Hreal σ0
  iintro Hb Hob
  ihave Ht := Htodo $$ Hb
  ihave H := Had $$ Ht Hob
  iapply step_fupdN_wand $$ H
  iintro ⟨%σ, Hobf, Hbg⟩
  iexists σ
  isplitl [Hobf]
  · iexact Hobf
  · iapply Hbag
    iexact Hbg

end wiring

/-! # 2. THE PURITY HALF: `naPureGlobal` for `naOf'`, the owned-read arm non-trivial -/

def axprotgatePhi (GD : Gdexec) (wdat : Geid → Int × BitVec 8)
    (rdat : Geid → Int × Nat × BitVec 8) (e : Geid) : Prop :=
  if gisW GD.gdG e then ∃ data, graphData GD e = some data
  else
    match rown GD rdat e with
    | some wl => graphValue GD e = some [(wdat wl).2]
    | none => True

section gate

variable {GF : BundledGFunctors} [AxlogG GF Hent]

theorem axprotgateNaPureGlobal (γ : GName) (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (wdat : Geid → Int × BitVec 8) (rdat : Geid → Int × Nat × BitVec 8) :
    naPureGlobal (AxProtGate.naOf' (GF := GF) γ GD wdat rdat) (axprotgatePhi GD wdat rdat) := by
  intro e He
  have hin : e ∈ GD.gdG.gxGmo := by
    rw [AxProtGate.naOfDom' γ GD Hcons wdat rdat, elemOfListToSet] at He
    exact He
  refine ⟨AxProtGate.naVal' γ GD wdat rdat e, AxProtGate.naOfLookup' γ GD Hcons wdat rdat e hin, ?_⟩
  unfold annotPure AxProtGate.naVal' axprotgatePhi
  cases gisW GD.gdG e
  · simp only [Bool.false_eq_true, ↓reduceIte]
    cases rown GD rdat e with
    | some wl => exact .rfl
    | none =>
      iintro _
      ipureintro
      trivial
  · simp only [↓reduceIte]
    iintro ⟨_, %data, %h⟩
    ipureintro
    exact ⟨data, h⟩

/-! # 3. THE COMPOSITION: `gateFacts naOf' (gateSrcs i s0 srcs) axprotgatePhi` -/

/-- Lean-only: a completed run puts `sProc` inside `dom naOf'`. -/
theorem AxProtGate.domOfRun (γ : GName) (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (wdat : Geid → Int × BitVec 8) (rdat : Geid → Int × Nat × BitVec 8)
    (st : Sstate) (Hrun : rtc (schedStep GD.gdG) sst0 st)
    (Hfull : st.sN = GD.gdG.gxGmo.length) (Hdone : st.sD = ∅) :
    (LawfulSet.ofList st.sProc : GSet Geid) ⊆
      FiniteMap.dom_set (AxProtGate.naOf' (GF := GF) γ GD wdat rdat) := by
  have HGw := schedHGwf GD Hcons
  have HC6 := schedHCat6gmo GD Hcons
  obtain ⟨Hmemiff, _⟩ := schedCorrect GD.gdG HGw HC6 st Hrun Hfull Hdone
  rw [AxProtGate.naOfDom' γ GD Hcons wdat rdat]
  intro e' He'
  rw [elemOfListToSet] at He' ⊢
  exact (Hmemiff e').1 He'

theorem axprotgateGateFacts (γ : GName) (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (wdat : Geid → Int × BitVec 8) (rdat : Geid → Int × Nat × BitVec 8)
    (i : Agent) (_k' : Nat) (s0 : DstateT) (srcs : List Dsrc)
    (st : Sstate) (Hrun : rtc (schedStep GD.gdG) sst0 st)
    (Hfull : st.sN = GD.gdG.gxGmo.length) (Hdone : st.sD = ∅)
    (Hmem : ∀ r, r ∈ gateSrcs i s0 srcs → r ∈ GD.gdG.gxGmo) :
    gateFacts (AxProtGate.naOf' (GF := GF) γ GD wdat rdat) (gateSrcs i s0 srcs)
      (axprotgatePhi GD wdat rdat) :=
  gateFactsOfDomPure _ _ _ (axprotgateNaPureGlobal γ GD Hcons wdat rdat)
    (gateSrcsDomOfSched GD Hcons st Hrun Hfull Hdone _
      (AxProtGate.domOfRun γ GD Hcons wdat rdat st Hrun Hfull Hdone) _ Hmem)

end gate

/-! # 4. THE OWNERSHIP-SIDE `x_r`: the gmo-maximal same-byte write gmo-before `r` -/

def ownedLastWrite (GD : Gdexec) (wdat : Geid → Int × BitVec 8) (a : Int) (r w : Geid) : Prop :=
  gwritesByte GD.gdG w a (wdat w).2 ∧ gmoLt GD.gdG w r ∧
  (∀ w' v', gwritesByte GD.gdG w' a v' → gmoLt GD.gdG w' r → gwix GD.gdG w' ≤ gwix GD.gdG w)

theorem greadsByteOwnedLastWrite (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (wdat : Geid → Int × BitVec 8)
    (HwdatSpec : ∀ w a v, gisW GD.gdG w = true →
      (gwritesByte GD.gdG w a v ↔ (a, v) = wdat w))
    (r : Geid) (a : Int) (t : Nat) (v : BitVec 8) (wl : Geid)
    (Hnofwd : ∀ w' v', gwritesByte GD.gdG w' a v' → WeakRvwmoGraph.gpo GD.gdG w' r →
      gmoLt GD.gdG w' r)
    (Hgb : greadsByte GD.gdG r a t v) (Hwrat : gwriteAt GD.gdG t = some wl) :
    ownedLastWrite GD wdat a r wl := by
  have Hveq := greadsByteRealValue GD Hcons wdat HwdatSpec r a t v wl Hgb Hwrat
  have Hwix := (gwriteAtInv GD.gdG t wl Hcons.1.1 Hwrat).2
  have ⟨_, _, Hgv, _⟩ := Hcons
  obtain ⟨Hsrc, Hmaxg⟩ := Hgv r a t v Hgb
  cases t with
  | zero => simp [gwriteAt] at Hwrat
  | succ t' =>
    obtain ⟨w0, Hwat0, Hwb0, Hvis0⟩ := Hsrc
    have hw : w0 = wl := Option.some.inj (Hwat0.symm.trans Hwrat)
    rw [hw] at Hwb0 Hvis0
    refine ⟨?_, ?_, ?_⟩
    · rw [← Hveq]; exact Hwb0
    · rcases Hvis0 with Hmo | Hpo
      · exact Hmo
      · exact Hnofwd wl v Hwb0 Hpo
    · intro w' v' Hwb' Hmo'
      rw [Hwix]
      exact Hmaxg w' v' Hwb' (Or.inl Hmo')

theorem greadsByteNoOwnedLastWrite (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (wdat : Geid → Int × BitVec 8) (r : Geid) (a : Int) (t : Nat) (v : BitVec 8) (wl : Geid) :
    greadsByte GD.gdG r a t v → gwriteAt GD.gdG t = none → ¬ ownedLastWrite GD wdat a r wl := by
  intro Hgb Hnone ⟨Hwb, Hmo, _⟩
  have ⟨_, _, Hgv, _⟩ := Hcons
  obtain ⟨Hsrc, Hmaxg⟩ := Hgv r a t v Hgb
  cases t with
  | zero =>
    have Hpos := WeakRvwmoGraph.gwixPos _ _ (gwritesByteGwrites _ _ _ _ Hcons.1 Hwb)
    have Hle := Hmaxg wl _ Hwb (Or.inl Hmo)
    omega
  | succ t' =>
    obtain ⟨w0, Hwat0, _⟩ := Hsrc
    rw [Hnone] at Hwat0
    cases Hwat0

theorem ownedLastWriteUniq (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (wdat : Geid → Int × BitVec 8) (a : Int) (r w1 w2 : Geid) :
    ownedLastWrite GD wdat a r w1 → ownedLastWrite GD wdat a r w2 → w1 = w2 := by
  intro ⟨Hwb1, Hmo1, Hmax1⟩ ⟨Hwb2, Hmo2, Hmax2⟩
  have Hw1w := gwritesByteGwrites _ _ _ _ Hcons.1 Hwb1
  have Hw2w := gwritesByteGwrites _ _ _ _ Hcons.1 Hwb2
  have h12 := Hmax2 w1 _ Hwb1 Hmo1
  have h21 := Hmax1 w2 _ Hwb2 Hmo2
  exact gwixInj _ _ _ Hcons.1.1 Hw1w Hw2w (by omega)

theorem rownIsOwnedLastWrite (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (wdat : Geid → Int × BitVec 8)
    (HwdatSpec : ∀ w a v, gisW GD.gdG w = true →
      (gwritesByte GD.gdG w a v ↔ (a, v) = wdat w))
    (rdat : Geid → Int × Nat × BitVec 8)
    (HrdatSpec : ∀ r l, gxLbl GD.gdG r = some l → lbIsR l = true →
      graphValue GD r = some [(rdat r).2.2] ∧
      greadsByte GD.gdG r (rdat r).1 (rdat r).2.1 (rdat r).2.2)
    (r : Geid) (Hin : r ∈ GD.gdG.gxGmo) (Hnw : gisW GD.gdG r = false) (wl : Geid)
    (Hro : rown GD rdat r = some wl)
    (Hnofwd : ∀ w' v', gwritesByte GD.gdG w' (rdat r).1 v' → WeakRvwmoGraph.gpo GD.gdG w' r →
      gmoLt GD.gdG w' r) :
    ownedLastWrite GD wdat (rdat r).1 r wl := by
  obtain ⟨l, Hl, Hisr⟩ := gisROfGmo GD Hcons r Hin Hnw
  obtain ⟨_, Hgb⟩ := HrdatSpec r l Hl Hisr
  exact greadsByteOwnedLastWrite GD Hcons wdat HwdatSpec r _ _ _ wl Hnofwd Hgb Hro

theorem rownNoneNoOwnedLastWrite (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (wdat : Geid → Int × BitVec 8) (rdat : Geid → Int × Nat × BitVec 8)
    (HrdatSpec : ∀ r l, gxLbl GD.gdG r = some l → lbIsR l = true →
      graphValue GD r = some [(rdat r).2.2] ∧
      greadsByte GD.gdG r (rdat r).1 (rdat r).2.1 (rdat r).2.2)
    (r : Geid) (Hin : r ∈ GD.gdG.gxGmo) (Hnw : gisW GD.gdG r = false) (wl : Geid)
    (Hro : rown GD rdat r = none) :
    ¬ ownedLastWrite GD wdat (rdat r).1 r wl := by
  obtain ⟨l, Hl, Hisr⟩ := gisROfGmo GD Hcons r Hin Hnw
  obtain ⟨_, Hgb⟩ := HrdatSpec r l Hl Hisr
  exact greadsByteNoOwnedLastWrite GD Hcons wdat r _ _ _ wl Hgb Hro

/-- THE OWNERSHIP-SIDE PHI: universally over the (unique) `ownedLastWrite` witness. -/
def axprotgatePhiOwned (GD : Gdexec) (wdat : Geid → Int × BitVec 8)
    (rdat : Geid → Int × Nat × BitVec 8) (e : Geid) : Prop :=
  if gisW GD.gdG e then ∃ data, graphData GD e = some data
  else ∀ wl, ownedLastWrite GD wdat (rdat e).1 e wl → graphValue GD e = some [(wdat wl).2]

theorem axprotgatePhiOwnedEntails (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (wdat : Geid → Int × BitVec 8)
    (HwdatSpec : ∀ w a v, gisW GD.gdG w = true →
      (gwritesByte GD.gdG w a v ↔ (a, v) = wdat w))
    (rdat : Geid → Int × Nat × BitVec 8)
    (HrdatSpec : ∀ r l, gxLbl GD.gdG r = some l → lbIsR l = true →
      graphValue GD r = some [(rdat r).2.2] ∧
      greadsByte GD.gdG r (rdat r).1 (rdat r).2.1 (rdat r).2.2)
    (e : Geid) (Hin : e ∈ GD.gdG.gxGmo)
    (Hnofwd : ∀ w' v', gwritesByte GD.gdG w' (rdat e).1 v' → WeakRvwmoGraph.gpo GD.gdG w' e →
      gmoLt GD.gdG w' e) :
    axprotgatePhi GD wdat rdat e → axprotgatePhiOwned GD wdat rdat e := by
  unfold axprotgatePhi axprotgatePhiOwned
  cases Hisw : gisW GD.gdG e
  · simp only [Bool.false_eq_true, ↓reduceIte]
    cases Hro : rown GD rdat e with
    | some wl0 =>
      intro Hgvv wl Hown
      have Heq := ownedLastWriteUniq GD Hcons wdat _ e wl wl0 Hown
        (rownIsOwnedLastWrite GD Hcons wdat HwdatSpec rdat HrdatSpec e Hin Hisw wl0 Hro Hnofwd)
      rw [Heq]
      exact Hgvv
    | none =>
      intro _ wl Hown
      exact absurd Hown (rownNoneNoOwnedLastWrite GD Hcons wdat rdat HrdatSpec e Hin Hisw wl Hro)
  · simp only [↓reduceIte]
    exact id

section gateOwned

variable {GF : BundledGFunctors} [AxlogG GF Hent]

theorem axprotgateGateFactsOwned (γ : GName) (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (wdat : Geid → Int × BitVec 8)
    (HwdatSpec : ∀ w a v, gisW GD.gdG w = true →
      (gwritesByte GD.gdG w a v ↔ (a, v) = wdat w))
    (rdat : Geid → Int × Nat × BitVec 8)
    (HrdatSpec : ∀ r l, gxLbl GD.gdG r = some l → lbIsR l = true →
      graphValue GD r = some [(rdat r).2.2] ∧
      greadsByte GD.gdG r (rdat r).1 (rdat r).2.1 (rdat r).2.2)
    (i : Agent) (k' : Nat) (s0 : DstateT) (srcs : List Dsrc)
    (st : Sstate) (Hrun : rtc (schedStep GD.gdG) sst0 st)
    (Hfull : st.sN = GD.gdG.gxGmo.length) (Hdone : st.sD = ∅)
    (Hmem : ∀ r, r ∈ gateSrcs i s0 srcs → r ∈ GD.gdG.gxGmo)
    (Hnofwd : ∀ r a w' v', gwritesByte GD.gdG w' a v' → WeakRvwmoGraph.gpo GD.gdG w' r →
      gmoLt GD.gdG w' r) :
    gateFacts (AxProtGate.naOf' (GF := GF) γ GD wdat rdat) (gateSrcs i s0 srcs)
      (axprotgatePhiOwned GD wdat rdat) := by
  intro e He
  obtain ⟨R, Hlook, Hpure⟩ :=
    axprotgateGateFacts (GF := GF) γ GD Hcons wdat rdat i k' s0 srcs st Hrun Hfull Hdone Hmem
      e He
  refine ⟨R, Hlook, ?_⟩
  have Hin : e ∈ GD.gdG.gxGmo := Hmem e He
  unfold annotPure at Hpure ⊢
  iintro HR
  ihave %Hφ := Hpure $$ HR
  ipureintro
  exact axprotgatePhiOwnedEntails GD Hcons wdat HwdatSpec rdat HrdatSpec e Hin
    (Hnofwd e (rdat e).1) Hφ

end gateOwned

/-! # 5. THE TOKEN-LEVEL AGREEMENT: `flowEqOwnedRead` keeping the `grfAt` half -/

/-- Lean-only: the token's last value is the graph's write datum at the same write. -/
theorem AxProtGate.lastVal (GD : Gdexec) (wdat : Geid → Int × BitVec 8)
    (HwdatSpec : ∀ w a v, gisW GD.gdG w = true →
      (gwritesByte GD.gdG w a v ↔ (a, v) = wdat w))
    (a : Int) (Hl : List Hent) (wl : Geid) (vl : BitVec 8)
    (Hwr : ∀ p, p ∈ Hl → gwritesByte GD.gdG p.1 a p.2)
    (Hlast : Hl.getLast? = some (wl, vl)) :
    vl = (wdat wl).2 := by
  have Hwb : gwritesByte GD.gdG wl a vl := Hwr (wl, vl) (List.mem_of_getLast? Hlast)
  exact congrArg Prod.snd ((HwdatSpec wl a vl (WeakRvwmoGraph.gwritesByteGisW _ _ _ _ Hwb)).1 Hwb)

section tok

variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [axG : AxirisG GF]
  [AxlogG GF Hent]

theorem flowEqOwnedReadOwned (γ : GName)
    (Hob_eq : ∀ (GD : Gdexec) (σ : AxirisG.obSt GF) (s : GSet Geid),
      AxirisG.obStInterp GD σ s ⊣⊢ protInv γ GD s)
    (GD : Gdexec) (Hcons : rvwmoCatConsistent GD) (wdat : Geid → Int × BitVec 8)
    (HwdatSpec : ∀ w a v, gisW GD.gdG w = true →
      (gwritesByte GD.gdG w a v ↔ (a, v) = wdat w))
    (r : Geid) (a : Int) (Hl : List Hent) (S : GMapF Geid Qp) (wl : Geid) (vl : BitVec 8)
    (sOb0 : GSet Geid) (flowIn : Mea GF)
    (Hrgmo : r ∈ GD.gdG.gxGmo) (Hnw : gisW GD.gdG r = false)
    (Hwr : ∀ p, p ∈ Hl → gwritesByte GD.gdG p.1 a p.2)
    (Hch : chainWith (gmoLt GD.gdG) (Hl.map Prod.fst))
    (Hown : ∀ w v, gwritesByte GD.gdG w a v → WeakRvwmoGraph.gpo GD.gdG w r →
      w ∈ Hl.map Prod.fst)
    (Hlast : Hl.getLast? = some (wl, vl))
    (Hrd : ∃ t v, greadsByte GD.gdG r a t v)
    (Hcase : (∃ e, e ∈ (FiniteMap.dom_set S : GSet Geid) ∧ gmoLt GD.gdG e r)
      ∨
      (wl ∈ (FiniteMap.dom_set S : GSet Geid) ∧
       (∀ e, e ∈ (FiniteMap.dom_set S : GSet Geid) → ¬ gmoLt GD.gdG e r) ∧
       WeakRvwmoGraph.gpo GD.gdG wl r ∧
       (∀ w' v', gwritesByte GD.gdG w' a v' →
         WeakRvwmoGraph.gpo GD.gdG wl w' → WeakRvwmoGraph.gpo GD.gdG w' r → False)))
    (Hpref : (LawfulSet.ofList (gmoPrefix GD.gdG r) : GSet Geid) ⊆ sOb0)
    (Hnofwd_a : ∀ w' v', gwritesByte GD.gdG w' a v' → WeakRvwmoGraph.gpo GD.gdG w' r →
      gmoLt GD.gdG w' r) :
    iprop(([∗map] Rin ∈ flowIn, Rin) -∗ tokTie GD γ a Hl S) ⊢
      flowEqDyn GD r sOb0 flowIn
        iprop(⌜ownedLastWrite GD wdat a r wl ∧ Hl.getLast? = some (wl, (wdat wl).2)⌝) := by
  have Hveq := AxProtGate.lastVal GD wdat HwdatSpec a Hl wl vl Hwr Hlast
  unfold flowEqDyn
  iintro Hflowin %σ %sOb %Hsub %Hnin Hob Hflow
  ihave Hob := (Hob_eq GD σ sOb).1 $$ Hob
  icases Hob with #Hob
  ihave Htie := Hflowin $$ Hflow
  have hkey : tokTie (GF := GF) GD γ a Hl S ∗ protInv γ GD sOb ⊢
      ⌜grfAt GD.gdG a wl r ∧ ∀ t v, greadsByte GD.gdG r a t v → v = vl⌝ :=
    (BI.sep_mono_right (protInvPrefixCovMem γ GD sOb r a Hcons.1 Hrgmo
      (subseteqTrans Hpref Hsub))).trans
      (ownedReadRule GD a r γ Hl S wl vl Hcons Hwr Hch Hown Hlast Hrd Hcase)
  ihave %hres := hkey $$ [$Htie $Hob]
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  inext
  imod Hclose
  imodintro
  iexists σ
  isplitl []
  · iapply (Hob_eq GD σ (({r} : GSet Geid) ∪ sOb)).2
    iapply protInvReadStep γ GD sOb r Hnin Hnw
    iexact Hob
  · ipureintro
    obtain ⟨t, v, Hgb, Hwrat⟩ := hres.1
    refine ⟨greadsByteOwnedLastWrite GD Hcons wdat HwdatSpec r a t v wl Hnofwd_a Hgb Hwrat, ?_⟩
    rw [Hlast, Hveq]

/-! # 6. FROM THE THREAD'S OWN TOKEN TO THE WP OBLIGATION -/

/-- Lean-only: the annotation map after an event with empty `naUnused` is the insert. -/
theorem AxProtGate.annotInsertEq (na : Mea GF) (e : Geid) (R : IProp GF) :
    PartialMap.union (PartialMap.union {[e := R]} (∅ : Mea GF)) na = insert na e R := by
  have h1 : PartialMap.union ({[e := R]} : Mea GF) (∅ : Mea GF) = {[e := R]} :=
    mapUnionEmptyR (M := GMapF Geid)
  rw [h1]
  exact (insertUnionSingletonL (M := GMapF Geid)).symm

/-- Lean-only: the empty splitting is well formed. -/
theorem AxProtGate.naSplittingWfEmpty (sLob : GSet Geid) (na : Mea GF) :
    ⊢ naSplittingWf sLob na (∅ : Mea GF) (∅ : Mea GF) := by
  unfold naSplittingWf
  isplitr
  · ipureintro
    rw [domEmpty]
    exact LawfulSet.empty_subset
  · iapply (BigSepM2.bigSepM2_empty _).2
    itrivial

theorem wpReadOwnedTok [Axpol] (γ : GName)
    (Hob_eq : ∀ (GD : Gdexec) (σ : AxirisG.obSt GF) (s : GSet Geid),
      AxirisG.obStInterp GD σ s ⊣⊢ protInv γ GD s)
    (GD : Gdexec) (Hcons : rvwmoCatConsistent GD) (wdat : Geid → Int × BitVec 8)
    (HwdatSpec : ∀ w a v, gisW GD.gdG w = true →
      (gwritesByte GD.gdG w a v ↔ (a, v) = wdat w))
    (rdat : Geid → Int × Nat × BitVec 8)
    (HrdatSpec : ∀ r l, gxLbl GD.gdG r = some l → lbIsR l = true →
      graphValue GD r = some [(rdat r).2.2] ∧
      greadsByte GD.gdG r (rdat r).1 (rdat r).2.1 (rdat r).2.2)
    (i : Agent) (k k'0 : Nat) (ls' : AxirisG.logTsT GF)
    (Hl : List Hent) (S : GMapF Geid Qp) (wl : Geid) (vl : BitVec 8)
    (Ψ : List (BitVec 8) → IProp GF)
    (Hrgmo : (i, k) ∈ GD.gdG.gxGmo) (Hnw : gisW GD.gdG (i, k) = false)
    (Hwr : ∀ p, p ∈ Hl → gwritesByte GD.gdG p.1 (rdat (i, k)).1 p.2)
    (Hch : chainWith (gmoLt GD.gdG) (Hl.map Prod.fst))
    (Hown : ∀ w v, gwritesByte GD.gdG w (rdat (i, k)).1 v →
      WeakRvwmoGraph.gpo GD.gdG w (i, k) → w ∈ Hl.map Prod.fst)
    (Hlast : Hl.getLast? = some (wl, vl))
    (Hrd : ∃ t v, greadsByte GD.gdG (i, k) (rdat (i, k)).1 t v)
    (Hcase : (∃ e, e ∈ (FiniteMap.dom_set S : GSet Geid) ∧ gmoLt GD.gdG e (i, k))
      ∨
      (wl ∈ (FiniteMap.dom_set S : GSet Geid) ∧
       (∀ e, e ∈ (FiniteMap.dom_set S : GSet Geid) → ¬ gmoLt GD.gdG e (i, k)) ∧
       WeakRvwmoGraph.gpo GD.gdG wl (i, k) ∧
       (∀ w' v', gwritesByte GD.gdG w' (rdat (i, k)).1 v' →
         WeakRvwmoGraph.gpo GD.gdG wl w' → WeakRvwmoGraph.gpo GD.gdG w' (i, k) → False)))
    (Hpref : (LawfulSet.ofList (gmoPrefix GD.gdG (i, k)) : GSet Geid) ⊆ Axpol.sPol GD (i, k))
    (Hnofwd_a : ∀ w' v', gwritesByte GD.gdG w' (rdat (i, k)).1 v' →
      WeakRvwmoGraph.gpo GD.gdG w' (i, k) → gmoLt GD.gdG w' (i, k))
    (Hnalloc : ⊢ ∀ na : Mea GF, naAtProgress GD i k na ∗ AxirisG.annotInterp na ==∗
       AxirisG.annotInterp (insert na (i, k)
         iprop(⌜ownedLastWrite GD wdat (rdat (i, k)).1 (i, k) wl ∧
           Hl.getLast? = some (wl, (wdat wl).2)⌝))) :
    ⊢ tokTie GD γ (rdat (i, k)).1 Hl S -∗
      AxirisG.localInterp GD i k'0 ls' -∗
      (∀ v : List (BitVec 8), ⌜v.length = 1⌝ -∗ Ψ v) -∗
      wpEvStep GD i k (fun v : List (BitVec 8) => v.length = 1)
        (fun v => graphValue GD (i, k) = some v) (fun _ => k'0) Ψ := by
  have Hphi : axprotgatePhi GD wdat rdat (i, k) := by
    have h0 := flowEqReadPure' GD Hcons wdat HwdatSpec rdat HrdatSpec (i, k) Hrgmo Hnw
    unfold axprotgatePhi
    simp only [Hnw, Bool.false_eq_true, ↓reduceIte]
    exact h0
  have Hpo := axprotgatePhiOwnedEntails GD Hcons wdat HwdatSpec rdat HrdatSpec (i, k) Hrgmo
    Hnofwd_a Hphi
  unfold axprotgatePhiOwned at Hpo
  simp only [Hnw, Bool.false_eq_true, ↓reduceIte] at Hpo
  have hpost : iprop(⌜ownedLastWrite GD wdat (rdat (i, k)).1 (i, k) wl ∧
        Hl.getLast? = some (wl, (wdat wl).2)⌝ : IProp GF) ⊢
      iprop(⌜ownedLastWrite GD wdat (rdat (i, k)).1 (i, k) wl ∧
        Hl.getLast? = some (wl, (wdat wl).2)⌝ ∗ ⌜graphValue GD (i, k) = some [(wdat wl).2]⌝) := by
    iintro %hp
    isplitl []
    · ipureintro
      exact hp
    · ipureintro
      exact Hpo wl hp.1
  have hw : tokTie (GF := GF) GD γ (rdat (i, k)).1 Hl S ⊢
      iprop(([∗map] Rin ∈ (∅ : Mea GF), Rin) -∗ tokTie GD γ (rdat (i, k)).1 Hl S) := by
    iintro Ht _
    iexact Ht
  have Hfeq := (hw.trans (flowEqOwnedReadOwned γ Hob_eq GD Hcons wdat HwdatSpec (i, k)
    (rdat (i, k)).1 Hl S wl vl (Axpol.sPol GD (i, k)) ∅ Hrgmo Hnw Hwr Hch Hown Hlast Hrd Hcase
    Hpref Hnofwd_a)).trans (AxProtCov3.flowEqDynPost GD (i, k) _ _ _ _ hpost)
  have Hn' : ⊢ ∀ na : Mea GF, naAtProgress GD i k na ∗ AxirisG.annotInterp na ==∗
      AxirisG.annotInterp (PartialMap.union (PartialMap.union
        {[(i, k) := iprop(⌜ownedLastWrite GD wdat (rdat (i, k)).1 (i, k) wl ∧
          Hl.getLast? = some (wl, (wdat wl).2)⌝)]} (∅ : Mea GF)) na) := by
    simp only [AxProtGate.annotInsertEq]
    exact Hnalloc
  iintro Htie Hloc Hcont
  ihave Hfeq := Hfeq $$ Htie
  unfold wpEvStep
  iintro %na Hpg
  ihave Hn := Hn'
  imod Hn $$ %na Hpg with Hna'
  imodintro
  inext
  imodintro
  iexists [(wdat wl).2], iprop(⌜ownedLastWrite GD wdat (rdat (i, k)).1 (i, k) wl ∧
    Hl.getLast? = some (wl, (wdat wl).2)⌝), (∅ : Mea GF), (∅ : Mea GF), ls'
  isplitr
  · ipureintro
    rfl
  isplitr
  · iapply AxProtGate.naSplittingWfEmpty
  iframe Hfeq Hna' Hloc
  iapply Hcont
  ipureintro
  rfl

end tok

/-! # 7. THE END-TO-END GATE LEMMA -/

section deliver

variable {GF : BundledGFunctors} [AxlogG GF Hent]

theorem gateDeliversExpected (γ : GName) (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (wdat : Geid → Int × BitVec 8)
    (HwdatSpec : ∀ w a v, gisW GD.gdG w = true →
      (gwritesByte GD.gdG w a v ↔ (a, v) = wdat w))
    (rdat : Geid → Int × Nat × BitVec 8)
    (HrdatSpec : ∀ r l, gxLbl GD.gdG r = some l → lbIsR l = true →
      graphValue GD r = some [(rdat r).2.2] ∧
      greadsByte GD.gdG r (rdat r).1 (rdat r).2.1 (rdat r).2.2)
    (i : Agent) (s0 : DstateT) (srcs : List Dsrc)
    (st : Sstate) (Hrun : rtc (schedStep GD.gdG) sst0 st)
    (Hfull : st.sN = GD.gdG.gxGmo.length) (Hdone : st.sD = ∅)
    (Hmem : ∀ r, r ∈ gateSrcs i s0 srcs → r ∈ GD.gdG.gxGmo)
    (Hnofwd : ∀ r a w' v', gwritesByte GD.gdG w' a v' → WeakRvwmoGraph.gpo GD.gdG w' r →
      gmoLt GD.gdG w' r)
    (r : Geid) (Hr_src : r ∈ gateSrcs i s0 srcs) (Hnw : gisW GD.gdG r = false)
    (Hl : List Hent) (wl : Geid) (vl : BitVec 8)
    (Hwr : ∀ p, p ∈ Hl → gwritesByte GD.gdG p.1 (rdat r).1 p.2)
    (Hlast : Hl.getLast? = some (wl, vl))
    (Hown : ownedLastWrite GD wdat (rdat r).1 r wl) :
    ∃ R, get? (AxProtGate.naOf' (GF := GF) γ GD wdat rdat) r = some R ∧
      (R ⊢ iprop(⌜graphValue GD r = some [vl]⌝)) := by
  obtain ⟨R, Hlook, Hpure⟩ := axprotgateGateFactsOwned (GF := GF) γ GD Hcons wdat HwdatSpec rdat
    HrdatSpec i 0 s0 srcs st Hrun Hfull Hdone Hmem Hnofwd r Hr_src
  refine ⟨R, Hlook, ?_⟩
  have Hveq := AxProtGate.lastVal GD wdat HwdatSpec _ Hl wl vl Hwr Hlast
  unfold annotPure axprotgatePhiOwned at Hpure
  simp only [Hnw, Bool.false_eq_true, ↓reduceIte] at Hpure
  iintro HR
  ihave %Hφ := Hpure $$ HR
  ipureintro
  rw [Hveq]
  exact Hφ wl Hown

end deliver

/-! # 8. THE FORWARDING CASE: `Hnofwd` dropped -/

def ownedForwardedWrite (GD : Gdexec) (wdat : Geid → Int × BitVec 8) (a : Int) (r w : Geid) :
    Prop :=
  gwritesByte GD.gdG w a (wdat w).2 ∧ WeakRvwmoGraph.gpo GD.gdG w r ∧
  ¬ gmoLt GD.gdG w r ∧
  (∀ w' v', gwritesByte GD.gdG w' a v' → WeakRvwmoGraph.gpo GD.gdG w w' →
    WeakRvwmoGraph.gpo GD.gdG w' r → False)

def ownedExpectedWrite (GD : Gdexec) (wdat : Geid → Int × BitVec 8) (a : Int) (r w : Geid) :
    Prop :=
  ownedForwardedWrite GD wdat a r w ∨
  (ownedLastWrite GD wdat a r w ∧ ¬ ∃ w', ownedForwardedWrite GD wdat a r w')

theorem ownedForwardedWriteUniq (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (wdat : Geid → Int × BitVec 8) (r : Geid) (a : Int) (w1 w2 : Geid)
    (Hrd : ∃ t v, greadsByte GD.gdG r a t v) :
    ownedForwardedWrite GD wdat a r w1 → ownedForwardedWrite GD wdat a r w2 → w1 = w2 := by
  intro ⟨Hwb1, Hpo1, Hnmo1, Hni1⟩ ⟨Hwb2, Hpo2, Hnmo2, Hni2⟩
  obtain ⟨t, vr, Hrd⟩ := Hrd
  exact grfAtDet _ a w1 w2 r
    (ownForwardCat' GD a w1 r _ t vr Hcons Hpo1 Hwb1 Hrd Hnmo1 Hni1).1
    (ownForwardCat' GD a w2 r _ t vr Hcons Hpo2 Hwb2 Hrd Hnmo2 Hni2).1

theorem ownedExpectedWriteUniq (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (wdat : Geid → Int × BitVec 8) (r : Geid) (a : Int) (w1 w2 : Geid)
    (Hrd : ∃ t v, greadsByte GD.gdG r a t v) :
    ownedExpectedWrite GD wdat a r w1 → ownedExpectedWrite GD wdat a r w2 → w1 = w2 := by
  rintro (Hf1 | ⟨Ho1, Hno1⟩) (Hf2 | ⟨Ho2, Hno2⟩)
  · exact ownedForwardedWriteUniq GD Hcons wdat r a w1 w2 Hrd Hf1 Hf2
  · exact absurd ⟨w1, Hf1⟩ Hno2
  · exact absurd ⟨w2, Hf2⟩ Hno1
  · exact ownedLastWriteUniq GD Hcons wdat a r w1 w2 Ho1 Ho2

theorem greadsByteOwnedExpectedWrite (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (wdat : Geid → Int × BitVec 8)
    (HwdatSpec : ∀ w a v, gisW GD.gdG w = true →
      (gwritesByte GD.gdG w a v ↔ (a, v) = wdat w))
    (r : Geid) (a : Int) (t : Nat) (v : BitVec 8) (wl : Geid)
    (Hgb : greadsByte GD.gdG r a t v) (Hwrat : gwriteAt GD.gdG t = some wl) :
    ownedExpectedWrite GD wdat a r wl := by
  have Hveq0 := greadsByteRealValue GD Hcons wdat HwdatSpec r a t v wl Hgb Hwrat
  have Hwix := (gwriteAtInv GD.gdG t wl Hcons.1.1 Hwrat).2
  have ⟨_, Hppo, Hgv, _⟩ := Hcons
  have Hrule1 : ∀ e1 e2, gppo1 GD.gdG e1 e2 → gmoLt GD.gdG e1 e2 :=
    fun e1 e2 h => Hppo e1 e2 (Or.inl (Or.inl h))
  obtain ⟨Hsrc, Hmaxg⟩ := Hgv r a t v Hgb
  cases t with
  | zero => simp [gwriteAt] at Hwrat
  | succ t' =>
    obtain ⟨w0, Hwat0, Hwb0, Hvis0⟩ := Hsrc
    have hw : w0 = wl := Option.some.inj (Hwat0.symm.trans Hwrat)
    rw [hw] at Hwb0 Hvis0
    have Hwb0' : gwritesByte GD.gdG wl a (wdat wl).2 := by rw [← Hveq0]; exact Hwb0
    by_cases Hmo : gmoLt GD.gdG wl r
    · refine Or.inr ⟨⟨Hwb0', Hmo, fun w' v' Hwb' Hmo' => ?_⟩, ?_⟩
      · rw [Hwix]; exact Hmaxg w' v' Hwb' (Or.inl Hmo')
      · rintro ⟨w1, Hwb1, Hpo1, Hnmo1, Hnoint1⟩
        have Hrfw1 := (ownForwardCat' GD a w1 r _ (t' + 1) v Hcons Hpo1 Hwb1 Hgb Hnmo1 Hnoint1).1
        have Hrfwl : grfAt GD.gdG a wl r := ⟨t' + 1, v, Hgb, Hwrat⟩
        have Heqw := grfAtDet _ a w1 wl r Hrfw1 Hrfwl
        rw [Heqw] at Hnmo1
        exact Hnmo1 Hmo
    · refine Or.inl ?_
      rcases Hvis0 with Hmo0 | Hpo0
      · exact absurd Hmo0 Hmo
      refine ⟨Hwb0', Hpo0, Hmo, ?_⟩
      intro w' v' Hwb' Hpo1 Hpo2
      have Hmo1 : gmoLt GD.gdG wl w' :=
        Hrule1 _ _ ⟨Hpo1, a, Or.inl ⟨(wdat wl).2, Hwb0'⟩, v', Hwb'⟩
      have Hle := Hmaxg w' v' Hwb' (Or.inr Hpo2)
      rw [← Hwix] at Hle
      have Hww := gwritesByteGwrites _ _ _ _ Hcons.1 Hwb0'
      have Hw'w := gwritesByteGwrites _ _ _ _ Hcons.1 Hwb'
      obtain ⟨_, _, Hgpos⟩ := Hmo1
      have := (gwixGposLt GD.gdG wl w' Hcons.1.1 Hww Hw'w).2 Hgpos
      omega

theorem greadsByteOwnedExpectedWriteNone (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (wdat : Geid → Int × BitVec 8) (r : Geid) (a : Int) (v : BitVec 8) (wl : Geid) :
    greadsByte GD.gdG r a 0 v → ¬ ownedExpectedWrite GD wdat a r wl := by
  intro Hgb Hexp
  have ⟨_, _, Hgv, _⟩ := Hcons
  obtain ⟨_, Hmaxg⟩ := Hgv r a 0 v Hgb
  rcases Hexp with ⟨Hwb, Hpo, _, _⟩ | ⟨⟨Hwb, Hmo, _⟩, _⟩
  · have Hpos := WeakRvwmoGraph.gwixPos _ _ (gwritesByteGwrites _ _ _ _ Hcons.1 Hwb)
    have Hle := Hmaxg wl _ Hwb (Or.inr Hpo)
    omega
  · have Hpos := WeakRvwmoGraph.gwixPos _ _ (gwritesByteGwrites _ _ _ _ Hcons.1 Hwb)
    have Hle := Hmaxg wl _ Hwb (Or.inl Hmo)
    omega

def axprotgatePhiOwnedFwd (GD : Gdexec) (wdat : Geid → Int × BitVec 8)
    (rdat : Geid → Int × Nat × BitVec 8) (e : Geid) : Prop :=
  if gisW GD.gdG e then ∃ data, graphData GD e = some data
  else ∀ wl, ownedExpectedWrite GD wdat (rdat e).1 e wl → graphValue GD e = some [(wdat wl).2]

theorem axprotgatePhiOwnedFwdHolds (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (wdat : Geid → Int × BitVec 8)
    (HwdatSpec : ∀ w a v, gisW GD.gdG w = true →
      (gwritesByte GD.gdG w a v ↔ (a, v) = wdat w))
    (HdataTot : ∀ w, gisW GD.gdG w = true → ∃ data, graphData GD w = some data)
    (rdat : Geid → Int × Nat × BitVec 8)
    (HrdatSpec : ∀ r l, gxLbl GD.gdG r = some l → lbIsR l = true →
      graphValue GD r = some [(rdat r).2.2] ∧
      greadsByte GD.gdG r (rdat r).1 (rdat r).2.1 (rdat r).2.2)
    (e : Geid) (Hin : e ∈ GD.gdG.gxGmo) :
    axprotgatePhiOwnedFwd GD wdat rdat e := by
  unfold axprotgatePhiOwnedFwd
  cases Hisw : gisW GD.gdG e
  · simp only [Bool.false_eq_true, ↓reduceIte]
    intro wl Hown
    obtain ⟨l, Hl, Hisr⟩ := gisROfGmo GD Hcons e Hin Hisw
    obtain ⟨Hgvv, Hgb⟩ := HrdatSpec e l Hl Hisr
    cases Ht0 : (rdat e).2.1 with
    | zero =>
      rw [Ht0] at Hgb
      exact absurd Hown (greadsByteOwnedExpectedWriteNone GD Hcons wdat e _ _ wl Hgb)
    | succ t0' =>
      rw [Ht0] at Hgb
      cases Hwrat : gwriteAt GD.gdG (t0' + 1) with
      | some w0 =>
        have Hown0 := greadsByteOwnedExpectedWrite GD Hcons wdat HwdatSpec e _ _ _ w0 Hgb Hwrat
        have Heq := ownedExpectedWriteUniq GD Hcons wdat e _ wl w0 ⟨_, _, Hgb⟩ Hown Hown0
        have Hveq := greadsByteRealValue GD Hcons wdat HwdatSpec e _ _ _ w0 Hgb Hwrat
        rw [Hgvv, Hveq, Heq]
      | none =>
        exfalso
        have ⟨_, _, Hgv, _⟩ := Hcons
        obtain ⟨⟨w0', Hwat0', _⟩, _⟩ := Hgv e _ _ _ Hgb
        rw [Hwrat] at Hwat0'
        cases Hwat0'
  · simp only [↓reduceIte]
    exact HdataTot e Hisw

section gateFwd

variable {GF : BundledGFunctors} [AxlogG GF Hent]

theorem axprotgateNaPureGlobalFwd (γ : GName) (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (wdat : Geid → Int × BitVec 8)
    (HwdatSpec : ∀ w a v, gisW GD.gdG w = true →
      (gwritesByte GD.gdG w a v ↔ (a, v) = wdat w))
    (HdataTot : ∀ w, gisW GD.gdG w = true → ∃ data, graphData GD w = some data)
    (rdat : Geid → Int × Nat × BitVec 8)
    (HrdatSpec : ∀ r l, gxLbl GD.gdG r = some l → lbIsR l = true →
      graphValue GD r = some [(rdat r).2.2] ∧
      greadsByte GD.gdG r (rdat r).1 (rdat r).2.1 (rdat r).2.2) :
    naPureGlobal (AxProtGate.naOf' (GF := GF) γ GD wdat rdat)
      (axprotgatePhiOwnedFwd GD wdat rdat) := by
  intro e He
  have hin : e ∈ GD.gdG.gxGmo := by
    rw [AxProtGate.naOfDom' γ GD Hcons wdat rdat, elemOfListToSet] at He
    exact He
  refine ⟨AxProtGate.naVal' γ GD wdat rdat e, AxProtGate.naOfLookup' γ GD Hcons wdat rdat e hin, ?_⟩
  unfold annotPure
  exact pure_intro
    (axprotgatePhiOwnedFwdHolds GD Hcons wdat HwdatSpec HdataTot rdat HrdatSpec e hin)

theorem axprotgateGateFactsFwd (γ : GName) (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (wdat : Geid → Int × BitVec 8)
    (HwdatSpec : ∀ w a v, gisW GD.gdG w = true →
      (gwritesByte GD.gdG w a v ↔ (a, v) = wdat w))
    (HdataTot : ∀ w, gisW GD.gdG w = true → ∃ data, graphData GD w = some data)
    (rdat : Geid → Int × Nat × BitVec 8)
    (HrdatSpec : ∀ r l, gxLbl GD.gdG r = some l → lbIsR l = true →
      graphValue GD r = some [(rdat r).2.2] ∧
      greadsByte GD.gdG r (rdat r).1 (rdat r).2.1 (rdat r).2.2)
    (i : Agent) (_k' : Nat) (s0 : DstateT) (srcs : List Dsrc)
    (st : Sstate) (Hrun : rtc (schedStep GD.gdG) sst0 st)
    (Hfull : st.sN = GD.gdG.gxGmo.length) (Hdone : st.sD = ∅)
    (Hmem : ∀ r, r ∈ gateSrcs i s0 srcs → r ∈ GD.gdG.gxGmo) :
    gateFacts (AxProtGate.naOf' (GF := GF) γ GD wdat rdat) (gateSrcs i s0 srcs)
      (axprotgatePhiOwnedFwd GD wdat rdat) :=
  gateFactsOfDomPure _ _ _
    (axprotgateNaPureGlobalFwd γ GD Hcons wdat HwdatSpec HdataTot rdat HrdatSpec)
    (gateSrcsDomOfSched GD Hcons st Hrun Hfull Hdone _
      (AxProtGate.domOfRun γ GD Hcons wdat rdat st Hrun Hfull Hdone) _ Hmem)

theorem gateDeliversExpectedFwd (γ : GName) (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (wdat : Geid → Int × BitVec 8)
    (HwdatSpec : ∀ w a v, gisW GD.gdG w = true →
      (gwritesByte GD.gdG w a v ↔ (a, v) = wdat w))
    (HdataTot : ∀ w, gisW GD.gdG w = true → ∃ data, graphData GD w = some data)
    (rdat : Geid → Int × Nat × BitVec 8)
    (HrdatSpec : ∀ r l, gxLbl GD.gdG r = some l → lbIsR l = true →
      graphValue GD r = some [(rdat r).2.2] ∧
      greadsByte GD.gdG r (rdat r).1 (rdat r).2.1 (rdat r).2.2)
    (i : Agent) (s0 : DstateT) (srcs : List Dsrc)
    (st : Sstate) (Hrun : rtc (schedStep GD.gdG) sst0 st)
    (Hfull : st.sN = GD.gdG.gxGmo.length) (Hdone : st.sD = ∅)
    (Hmem : ∀ r, r ∈ gateSrcs i s0 srcs → r ∈ GD.gdG.gxGmo)
    (r : Geid) (Hr_src : r ∈ gateSrcs i s0 srcs) (Hnw : gisW GD.gdG r = false)
    (Hl : List Hent) (wl : Geid) (vl : BitVec 8)
    (Hwr : ∀ p, p ∈ Hl → gwritesByte GD.gdG p.1 (rdat r).1 p.2)
    (Hlast : Hl.getLast? = some (wl, vl))
    (Hown : ownedExpectedWrite GD wdat (rdat r).1 r wl) :
    ∃ R, get? (AxProtGate.naOf' (GF := GF) γ GD wdat rdat) r = some R ∧
      (R ⊢ iprop(⌜graphValue GD r = some [vl]⌝)) := by
  obtain ⟨R, Hlook, Hpure⟩ := axprotgateGateFactsFwd (GF := GF) γ GD Hcons wdat HwdatSpec HdataTot
    rdat HrdatSpec i 0 s0 srcs st Hrun Hfull Hdone Hmem r Hr_src
  refine ⟨R, Hlook, ?_⟩
  have Hveq := AxProtGate.lastVal GD wdat HwdatSpec _ Hl wl vl Hwr Hlast
  unfold annotPure axprotgatePhiOwnedFwd at Hpure
  simp only [Hnw, Bool.false_eq_true, ↓reduceIte] at Hpure
  iintro HR
  ihave %Hφ := Hpure $$ HR
  ipureintro
  rw [Hveq]
  exact Hφ wl Hown

end gateFwd

section tokFwd

variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [axG : AxirisG GF]
  [AxlogG GF Hent]

theorem flowEqOwnedReadOwnedFwd (γ : GName)
    (Hob_eq : ∀ (GD : Gdexec) (σ : AxirisG.obSt GF) (s : GSet Geid),
      AxirisG.obStInterp GD σ s ⊣⊢ protInv γ GD s)
    (GD : Gdexec) (Hcons : rvwmoCatConsistent GD) (wdat : Geid → Int × BitVec 8)
    (HwdatSpec : ∀ w a v, gisW GD.gdG w = true →
      (gwritesByte GD.gdG w a v ↔ (a, v) = wdat w))
    (r : Geid) (a : Int) (Hl : List Hent) (S : GMapF Geid Qp) (wl : Geid) (vl : BitVec 8)
    (sOb0 : GSet Geid) (flowIn : Mea GF)
    (Hrgmo : r ∈ GD.gdG.gxGmo) (Hnw : gisW GD.gdG r = false)
    (Hwr : ∀ p, p ∈ Hl → gwritesByte GD.gdG p.1 a p.2)
    (Hch : chainWith (gmoLt GD.gdG) (Hl.map Prod.fst))
    (Hown : ∀ w v, gwritesByte GD.gdG w a v → WeakRvwmoGraph.gpo GD.gdG w r →
      w ∈ Hl.map Prod.fst)
    (Hlast : Hl.getLast? = some (wl, vl))
    (Hrd : ∃ t v, greadsByte GD.gdG r a t v)
    (Hcase : (∃ e, e ∈ (FiniteMap.dom_set S : GSet Geid) ∧ gmoLt GD.gdG e r)
      ∨
      (wl ∈ (FiniteMap.dom_set S : GSet Geid) ∧
       (∀ e, e ∈ (FiniteMap.dom_set S : GSet Geid) → ¬ gmoLt GD.gdG e r) ∧
       WeakRvwmoGraph.gpo GD.gdG wl r ∧
       (∀ w' v', gwritesByte GD.gdG w' a v' →
         WeakRvwmoGraph.gpo GD.gdG wl w' → WeakRvwmoGraph.gpo GD.gdG w' r → False)))
    (Hpref : (LawfulSet.ofList (gmoPrefix GD.gdG r) : GSet Geid) ⊆ sOb0) :
    iprop(([∗map] Rin ∈ flowIn, Rin) -∗ tokTie GD γ a Hl S) ⊢
      flowEqDyn GD r sOb0 flowIn
        iprop(⌜ownedExpectedWrite GD wdat a r wl ∧ Hl.getLast? = some (wl, (wdat wl).2)⌝) := by
  have Hveq := AxProtGate.lastVal GD wdat HwdatSpec a Hl wl vl Hwr Hlast
  unfold flowEqDyn
  iintro Hflowin %σ %sOb %Hsub %Hnin Hob Hflow
  ihave Hob := (Hob_eq GD σ sOb).1 $$ Hob
  icases Hob with #Hob
  ihave Htie := Hflowin $$ Hflow
  have hkey : tokTie (GF := GF) GD γ a Hl S ∗ protInv γ GD sOb ⊢
      ⌜grfAt GD.gdG a wl r ∧ ∀ t v, greadsByte GD.gdG r a t v → v = vl⌝ :=
    (BI.sep_mono_right (protInvPrefixCovMem γ GD sOb r a Hcons.1 Hrgmo
      (subseteqTrans Hpref Hsub))).trans
      (ownedReadRule GD a r γ Hl S wl vl Hcons Hwr Hch Hown Hlast Hrd Hcase)
  ihave %hres := hkey $$ [$Htie $Hob]
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  inext
  imod Hclose
  imodintro
  iexists σ
  isplitl []
  · iapply (Hob_eq GD σ (({r} : GSet Geid) ∪ sOb)).2
    iapply protInvReadStep γ GD sOb r Hnin Hnw
    iexact Hob
  · ipureintro
    obtain ⟨t, v, Hgb, Hwrat⟩ := hres.1
    refine ⟨greadsByteOwnedExpectedWrite GD Hcons wdat HwdatSpec r a t v wl Hgb Hwrat, ?_⟩
    rw [Hlast, Hveq]

theorem wpReadOwnedTokFwd [Axpol] (γ : GName)
    (Hob_eq : ∀ (GD : Gdexec) (σ : AxirisG.obSt GF) (s : GSet Geid),
      AxirisG.obStInterp GD σ s ⊣⊢ protInv γ GD s)
    (GD : Gdexec) (Hcons : rvwmoCatConsistent GD) (wdat : Geid → Int × BitVec 8)
    (HwdatSpec : ∀ w a v, gisW GD.gdG w = true →
      (gwritesByte GD.gdG w a v ↔ (a, v) = wdat w))
    (HdataTot : ∀ w, gisW GD.gdG w = true → ∃ data, graphData GD w = some data)
    (rdat : Geid → Int × Nat × BitVec 8)
    (HrdatSpec : ∀ r l, gxLbl GD.gdG r = some l → lbIsR l = true →
      graphValue GD r = some [(rdat r).2.2] ∧
      greadsByte GD.gdG r (rdat r).1 (rdat r).2.1 (rdat r).2.2)
    (i : Agent) (k k'0 : Nat) (ls' : AxirisG.logTsT GF)
    (Hl : List Hent) (S : GMapF Geid Qp) (wl : Geid) (vl : BitVec 8)
    (Ψ : List (BitVec 8) → IProp GF)
    (Hrgmo : (i, k) ∈ GD.gdG.gxGmo) (Hnw : gisW GD.gdG (i, k) = false)
    (Hwr : ∀ p, p ∈ Hl → gwritesByte GD.gdG p.1 (rdat (i, k)).1 p.2)
    (Hch : chainWith (gmoLt GD.gdG) (Hl.map Prod.fst))
    (Hown : ∀ w v, gwritesByte GD.gdG w (rdat (i, k)).1 v →
      WeakRvwmoGraph.gpo GD.gdG w (i, k) → w ∈ Hl.map Prod.fst)
    (Hlast : Hl.getLast? = some (wl, vl))
    (Hrd : ∃ t v, greadsByte GD.gdG (i, k) (rdat (i, k)).1 t v)
    (Hcase : (∃ e, e ∈ (FiniteMap.dom_set S : GSet Geid) ∧ gmoLt GD.gdG e (i, k))
      ∨
      (wl ∈ (FiniteMap.dom_set S : GSet Geid) ∧
       (∀ e, e ∈ (FiniteMap.dom_set S : GSet Geid) → ¬ gmoLt GD.gdG e (i, k)) ∧
       WeakRvwmoGraph.gpo GD.gdG wl (i, k) ∧
       (∀ w' v', gwritesByte GD.gdG w' (rdat (i, k)).1 v' →
         WeakRvwmoGraph.gpo GD.gdG wl w' → WeakRvwmoGraph.gpo GD.gdG w' (i, k) → False)))
    (Hpref : (LawfulSet.ofList (gmoPrefix GD.gdG (i, k)) : GSet Geid) ⊆ Axpol.sPol GD (i, k))
    (Hnalloc : ⊢ ∀ na : Mea GF, naAtProgress GD i k na ∗ AxirisG.annotInterp na ==∗
       AxirisG.annotInterp (insert na (i, k)
         iprop(⌜ownedExpectedWrite GD wdat (rdat (i, k)).1 (i, k) wl ∧
           Hl.getLast? = some (wl, (wdat wl).2)⌝))) :
    ⊢ tokTie GD γ (rdat (i, k)).1 Hl S -∗
      AxirisG.localInterp GD i k'0 ls' -∗
      (∀ v : List (BitVec 8), ⌜v.length = 1⌝ -∗ Ψ v) -∗
      wpEvStep GD i k (fun v : List (BitVec 8) => v.length = 1)
        (fun v => graphValue GD (i, k) = some v) (fun _ => k'0) Ψ := by
  have Hpo := axprotgatePhiOwnedFwdHolds GD Hcons wdat HwdatSpec HdataTot rdat HrdatSpec (i, k)
    Hrgmo
  unfold axprotgatePhiOwnedFwd at Hpo
  simp only [Hnw, Bool.false_eq_true, ↓reduceIte] at Hpo
  have hpost : iprop(⌜ownedExpectedWrite GD wdat (rdat (i, k)).1 (i, k) wl ∧
        Hl.getLast? = some (wl, (wdat wl).2)⌝ : IProp GF) ⊢
      iprop(⌜ownedExpectedWrite GD wdat (rdat (i, k)).1 (i, k) wl ∧
        Hl.getLast? = some (wl, (wdat wl).2)⌝ ∗ ⌜graphValue GD (i, k) = some [(wdat wl).2]⌝) := by
    iintro %hp
    isplitl []
    · ipureintro
      exact hp
    · ipureintro
      exact Hpo wl hp.1
  have hw : tokTie (GF := GF) GD γ (rdat (i, k)).1 Hl S ⊢
      iprop(([∗map] Rin ∈ (∅ : Mea GF), Rin) -∗ tokTie GD γ (rdat (i, k)).1 Hl S) := by
    iintro Ht _
    iexact Ht
  have Hfeq := (hw.trans (flowEqOwnedReadOwnedFwd γ Hob_eq GD Hcons wdat HwdatSpec (i, k)
    (rdat (i, k)).1 Hl S wl vl (Axpol.sPol GD (i, k)) ∅ Hrgmo Hnw Hwr Hch Hown Hlast Hrd Hcase
    Hpref)).trans (AxProtCov3.flowEqDynPost GD (i, k) _ _ _ _ hpost)
  have Hn' : ⊢ ∀ na : Mea GF, naAtProgress GD i k na ∗ AxirisG.annotInterp na ==∗
      AxirisG.annotInterp (PartialMap.union (PartialMap.union
        {[(i, k) := iprop(⌜ownedExpectedWrite GD wdat (rdat (i, k)).1 (i, k) wl ∧
          Hl.getLast? = some (wl, (wdat wl).2)⌝)]} (∅ : Mea GF)) na) := by
    simp only [AxProtGate.annotInsertEq]
    exact Hnalloc
  iintro Htie Hloc Hcont
  ihave Hfeq := Hfeq $$ Htie
  unfold wpEvStep
  iintro %na Hpg
  ihave Hn := Hn'
  imod Hn $$ %na Hpg with Hna'
  imodintro
  inext
  imodintro
  iexists [(wdat wl).2], iprop(⌜ownedExpectedWrite GD wdat (rdat (i, k)).1 (i, k) wl ∧
    Hl.getLast? = some (wl, (wdat wl).2)⌝), (∅ : Mea GF), (∅ : Mea GF), ls'
  isplitr
  · ipureintro
    rfl
  isplitr
  · iapply AxProtGate.naSplittingWfEmpty
  iframe Hfeq Hna' Hloc
  iapply Hcont
  ipureintro
  rfl

end tokFwd

/-! # 9. `wpReadOwnedTok` AT THE CONCRETE `skelAxirisG` INSTANCE -/

section skel

variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxannotGS GF] [AxgraphG GF]
  [AxlogG GF Hent] (γg : GName) (Φp : Gdexec → Geid → IProp GF)

/-- `Hnalloc`, discharged concretely: `annotAllocAtProgress` minus its ownership fragment. -/
theorem annotAllocAtProgressSkel (GD : Gdexec) (i : Agent) (k : Nat) (P : IProp GF) :
    ⊢ ∀ na : Mea GF, naAtProgress GD i k na ∗
        AxirisG.annotInterp (self := skelAxirisG γg Φp) na ==∗
      AxirisG.annotInterp (self := skelAxirisG γg Φp) (insert na (i, k) P) := by
  iintro %na H
  ihave H2 := annotAllocAtProgress γg Φp GD i k na P $$ H
  imod H2 with ⟨Ha, -⟩
  imodintro
  iexact Ha

theorem wpReadOwnedTokSkel [Axpol] (γ : GName)
    (Hob_eq : ∀ (GD : Gdexec) (σ : @AxirisG.obSt GF (skelAxirisG γg Φp)) (s : GSet Geid),
      AxirisG.obStInterp (self := skelAxirisG γg Φp) GD σ s ⊣⊢ protInv γ GD s)
    (GD : Gdexec) (Hcons : rvwmoCatConsistent GD) (wdat : Geid → Int × BitVec 8)
    (HwdatSpec : ∀ w a v, gisW GD.gdG w = true →
      (gwritesByte GD.gdG w a v ↔ (a, v) = wdat w))
    (rdat : Geid → Int × Nat × BitVec 8)
    (HrdatSpec : ∀ r l, gxLbl GD.gdG r = some l → lbIsR l = true →
      graphValue GD r = some [(rdat r).2.2] ∧
      greadsByte GD.gdG r (rdat r).1 (rdat r).2.1 (rdat r).2.2)
    (i : Agent) (k k'0 : Nat) (ls' : @AxirisG.logTsT GF (skelAxirisG γg Φp))
    (Hl : List Hent) (S : GMapF Geid Qp) (wl : Geid) (vl : BitVec 8)
    (Ψ : List (BitVec 8) → IProp GF)
    (Hrgmo : (i, k) ∈ GD.gdG.gxGmo) (Hnw : gisW GD.gdG (i, k) = false)
    (Hwr : ∀ p, p ∈ Hl → gwritesByte GD.gdG p.1 (rdat (i, k)).1 p.2)
    (Hch : chainWith (gmoLt GD.gdG) (Hl.map Prod.fst))
    (Hown : ∀ w v, gwritesByte GD.gdG w (rdat (i, k)).1 v →
      WeakRvwmoGraph.gpo GD.gdG w (i, k) → w ∈ Hl.map Prod.fst)
    (Hlast : Hl.getLast? = some (wl, vl))
    (Hrd : ∃ t v, greadsByte GD.gdG (i, k) (rdat (i, k)).1 t v)
    (Hcase : (∃ e, e ∈ (FiniteMap.dom_set S : GSet Geid) ∧ gmoLt GD.gdG e (i, k))
      ∨
      (wl ∈ (FiniteMap.dom_set S : GSet Geid) ∧
       (∀ e, e ∈ (FiniteMap.dom_set S : GSet Geid) → ¬ gmoLt GD.gdG e (i, k)) ∧
       WeakRvwmoGraph.gpo GD.gdG wl (i, k) ∧
       (∀ w' v', gwritesByte GD.gdG w' (rdat (i, k)).1 v' →
         WeakRvwmoGraph.gpo GD.gdG wl w' → WeakRvwmoGraph.gpo GD.gdG w' (i, k) → False)))
    (Hpref : (LawfulSet.ofList (gmoPrefix GD.gdG (i, k)) : GSet Geid) ⊆ Axpol.sPol GD (i, k))
    (Hnofwd_a : ∀ w' v', gwritesByte GD.gdG w' (rdat (i, k)).1 v' →
      WeakRvwmoGraph.gpo GD.gdG w' (i, k) → gmoLt GD.gdG w' (i, k)) :
    ⊢ tokTie GD γ (rdat (i, k)).1 Hl S -∗
      AxirisG.localInterp (self := skelAxirisG γg Φp) GD i k'0 ls' -∗
      (∀ v : List (BitVec 8), ⌜v.length = 1⌝ -∗ Ψ v) -∗
      @wpEvStep hlc GF _ (skelAxirisG γg Φp) _ (List (BitVec 8)) GD i k
        (fun v : List (BitVec 8) => v.length = 1)
        (fun v => graphValue GD (i, k) = some v) (fun _ => k'0) Ψ :=
  wpReadOwnedTok (axG := skelAxirisG γg Φp) γ Hob_eq GD Hcons wdat HwdatSpec rdat HrdatSpec
    i k k'0 ls' Hl S wl vl Ψ Hrgmo Hnw Hwr Hch Hown Hlast Hrd Hcase Hpref Hnofwd_a
    (annotAllocAtProgressSkel γg Φp GD i k _)

theorem wpReadOwnedTokSkelFwd [Axpol] (γ : GName)
    (Hob_eq : ∀ (GD : Gdexec) (σ : @AxirisG.obSt GF (skelAxirisG γg Φp)) (s : GSet Geid),
      AxirisG.obStInterp (self := skelAxirisG γg Φp) GD σ s ⊣⊢ protInv γ GD s)
    (GD : Gdexec) (Hcons : rvwmoCatConsistent GD) (wdat : Geid → Int × BitVec 8)
    (HwdatSpec : ∀ w a v, gisW GD.gdG w = true →
      (gwritesByte GD.gdG w a v ↔ (a, v) = wdat w))
    (HdataTot : ∀ w, gisW GD.gdG w = true → ∃ data, graphData GD w = some data)
    (rdat : Geid → Int × Nat × BitVec 8)
    (HrdatSpec : ∀ r l, gxLbl GD.gdG r = some l → lbIsR l = true →
      graphValue GD r = some [(rdat r).2.2] ∧
      greadsByte GD.gdG r (rdat r).1 (rdat r).2.1 (rdat r).2.2)
    (i : Agent) (k k'0 : Nat) (ls' : @AxirisG.logTsT GF (skelAxirisG γg Φp))
    (Hl : List Hent) (S : GMapF Geid Qp) (wl : Geid) (vl : BitVec 8)
    (Ψ : List (BitVec 8) → IProp GF)
    (Hrgmo : (i, k) ∈ GD.gdG.gxGmo) (Hnw : gisW GD.gdG (i, k) = false)
    (Hwr : ∀ p, p ∈ Hl → gwritesByte GD.gdG p.1 (rdat (i, k)).1 p.2)
    (Hch : chainWith (gmoLt GD.gdG) (Hl.map Prod.fst))
    (Hown : ∀ w v, gwritesByte GD.gdG w (rdat (i, k)).1 v →
      WeakRvwmoGraph.gpo GD.gdG w (i, k) → w ∈ Hl.map Prod.fst)
    (Hlast : Hl.getLast? = some (wl, vl))
    (Hrd : ∃ t v, greadsByte GD.gdG (i, k) (rdat (i, k)).1 t v)
    (Hcase : (∃ e, e ∈ (FiniteMap.dom_set S : GSet Geid) ∧ gmoLt GD.gdG e (i, k))
      ∨
      (wl ∈ (FiniteMap.dom_set S : GSet Geid) ∧
       (∀ e, e ∈ (FiniteMap.dom_set S : GSet Geid) → ¬ gmoLt GD.gdG e (i, k)) ∧
       WeakRvwmoGraph.gpo GD.gdG wl (i, k) ∧
       (∀ w' v', gwritesByte GD.gdG w' (rdat (i, k)).1 v' →
         WeakRvwmoGraph.gpo GD.gdG wl w' → WeakRvwmoGraph.gpo GD.gdG w' (i, k) → False)))
    (Hpref : (LawfulSet.ofList (gmoPrefix GD.gdG (i, k)) : GSet Geid) ⊆ Axpol.sPol GD (i, k)) :
    ⊢ tokTie GD γ (rdat (i, k)).1 Hl S -∗
      AxirisG.localInterp (self := skelAxirisG γg Φp) GD i k'0 ls' -∗
      (∀ v : List (BitVec 8), ⌜v.length = 1⌝ -∗ Ψ v) -∗
      @wpEvStep hlc GF _ (skelAxirisG γg Φp) _ (List (BitVec 8)) GD i k
        (fun v : List (BitVec 8) => v.length = 1)
        (fun v => graphValue GD (i, k) = some v) (fun _ => k'0) Ψ :=
  wpReadOwnedTokFwd (axG := skelAxirisG γg Φp) γ Hob_eq GD Hcons wdat HwdatSpec HdataTot rdat
    HrdatSpec i k k'0 ls' Hl S wl vl Ψ Hrgmo Hnw Hwr Hch Hown Hlast Hrd Hcase Hpref
    (annotAllocAtProgressSkel γg Φp GD i k _)

end skel

end Weak
