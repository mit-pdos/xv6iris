/-
Weak: **THE CONCRETE `ordEaTodoL` ASSEMBLY** for `AxProtInst.axprotPol` (C6/C9, continued from
`Weak.AxProtCov2`), the wiring theorem `axprotAdequateGhost`, the read-validation corollary and
the `naPureGlobal` instance.

Rocq: `iris/AxProtCov3.v` @ xxvzwolszwmp.

## The Rocq header, in substance

Fix a single-byte write-data function `wdat` (`HwdatSpec`) and graph-data totality `HdataTot`.
For every event `e` of `gxGmo`:
* `naOf e := histSnap γ a (hOf' e) ∗ ∃ data, ⌜graphData GD e = some data⌝` at a write (byte
  `a := (wdat e).1`), `emp` at a read;
* `eaOf e := {[w0 := histAuth γ a 1 (hOf' w0)]}` at a write with gco-immediate predecessor `w0`,
  `∅` otherwise.
The per-write flow obligation is `AxProtInst.flowEqOwnedWriteChainSnap`; the `eaDeposit` collapse
to the unique gco-SUCCESSOR (`axprotImmsucc`, the computable inverse of `axprotImmpred`) is
`eaDepositPEq` (item iii, via `axprotImmpredInj'`). A byte's FIRST write needs a real
`histAuth γ a 1 []`: the theorem takes the caller's single `histAlloc` over every written byte as an
antecedent and `distributeFirstWrites` (list induction with a shrinking `GSet Int` accumulator;
first writes are unique, `firstWriteUniq`) hands one piece to each first write (item ii). Reads:
`flowEqEaOfRead` (item iv). Item (i): `mapOfFunLookupSome`/`None`. §2
`axprotOwnedReadsValidated`: composition with `AxSchedIris.ownedReadGhostSnap` (non-forwarding
case, explicit witness `Hwit` and `Hnofwd`). §3 `axprotcov3NaPureGlobal`: `naPureGlobal` for `naOf`.
Remaining open (Rocq): `HdataTot`/`HwdatSpec` are named hypotheses, owed by a concrete `GD`.

**Fetches.** Graph events only (Stage C); nothing here mentions fetches.

## Deviations from Rocq

1. NAMES: camelCase (map below). Names duplicated in the Rocq tree (`notes/weak-port-dupnames.json`)
   are FILE-QUALIFIED `AxProtCov3.*`; so are the Lean-only helpers and (to keep a one-letter name
   out of `namespace Weak`) Rocq `V`/`F`.
2. THE RE-DERIVED CHAIN MACHINERY (Rocq §1.1, `axprot_immpred_*'`, `H_of*'`) is REUSED from
   `Weak.AxProtCov2`: each primed lemma is proved by the AxProtCov2 lemma, and
   `AxProtCov3.hOfFuel'` is defined as `hOfFuel` (Rocq repeats the same Fixpoint verbatim; the
   Rocq header's reason — guessing another file's section-closed argument lists — does not apply).
3. VOCABULARY (as `AxProtInst` deviation 2): `list_to_map` ↦ `PartialMap.ofList`, `list_find` ↦
   `List.find?` (`axprotImmsucc`), `mea Σ`/`sra Σ` ↦ `Mea GF`/`Sra GF`, `dom` ↦
   `FiniteMap.dom_set`, `from_option` ↦ `AxWp.fromOption`, Rocq's `ea_deposit` summand ↦
   `AxLifting.depAt` (`eaDepositTermEmp`), `gpo` ↦ `WeakRvwmoGraph.gpo`.
4. CONTEXTS: Rocq's section `Assembly` context (`γ`, `Hob_eq`, `GD`, `Hcons`, `wdat`,
   `Hwdat_spec`, `Hdata_tot`) becomes explicit arguments, in that order, each declaration taking
   exactly the ones it uses; `invGS_gen HasNoLc Σ` ↦ `[InvGS_gen hlc GF]` for any `hlc`. The
   policy is the global `axprotPol` (`Axpol.sPol`/`lobp` = `axprotPred`). The §3 `axpol` context is
   unused (`naPureGlobal` takes no policy) and dropped.
5. STATEMENT SHAPES: `P -∗ Q` lemmas are `P ⊢ Q`; the wiring theorems are `⊢ A -∗ B -∗ C`.
6. Lean-only helpers (file-qualified): `AxProtCov3.naOfLookup`/`naOfLookupNone`/`eaOfLookup`/
   `eaOfLookupNone` (the four `map_of_fun_lookup_*` instances Rocq rewrites with inline),
   `AxProtCov3.depAtEmpEq` (the equation behind `eaDepositTermEmp`), `AxProtCov3.flowEqDynPost`
   (`flowEqDynMono` from a plain entailment), `AxProtCov3.flowEqEaOfWriteGen`
   (the common body of Rocq's two write lemmas), `AxProtCov3.todoAtEq` (the `ordEaTodoL` line at a
   `gxGmo` event).

**Rocq → Lean name map.**  `fmap_fst_pair` `fmapFstPair`, `map_of_fun_lookup_some`
`mapOfFunLookupSome`, `map_of_fun_lookup_none` `mapOfFunLookupNone`; file-qualified
`AxProtCov3.`: `axprot_immpred_byte'` `axprotImmpredByte'`, `axprot_immpred_gpos_lt'`
`axprotImmpredGposLt'`, `axprot_immpred_inj'` `axprotImmpredInj'`, `H_of_fuel'` `hOfFuel'`,
`H_of'` `hOf'`, `H_of_fuel_S_eq'` `hOfFuelSEq'`, `H_of_fuel_none_eq'` `hOfFuelNoneEq'`,
`H_of_fuel_stable'` `hOfFuelStable'`, `H_of_first'` `hOfFirst'`, `H_of_chain'` `hOfChain'`,
`axprot_immpred_dom` `axprotImmpredDom`, `axprot_immsucc` `axprotImmsucc`, `axprot_immsucc_some`
`axprotImmsuccSome`, `axprot_immsucc_none` `axprotImmsuccNone`, `axprot_immsucc_none_of_nonwrite`
`axprotImmsuccNoneOfNonwrite`, `first_write_uniq` `firstWriteUniq`, `V` `V`, `na_val` `naVal`,
`ea_val` `eaVal`, `na_of` `naOf`, `ea_of` `eaOf`, `ea_val_lookup_none` `eaValLookupNone`,
`ea_deposit_term_emp` `eaDepositTermEmp`, `ea_deposit_p_eq` `eaDepositPEq`, `F` `F`,
`flow_eq_read_trivial` `flowEqReadTrivial`, `na_of_dom` `naOfDom`, `ea_of_dom` `eaOfDom`;
unqualified: `flow_eq_ea_of_read` `flowEqEaOfRead`, `flow_eq_ea_of_write_nonfirst`
`flowEqEaOfWriteNonfirst`, `flow_eq_ea_of_write_first` `flowEqEaOfWriteFirst`,
`distribute_first_writes` `distributeFirstWrites`, `na_of_ea_of_dom_eq` `naOfEaOfDomEq`,
`Hea_lob` `heaLob`, `axprot_adequate_ghost` `axprotAdequateGhost`, `axprot_owned_reads_validated`
`axprotOwnedReadsValidated`, `axprotcov3_phi` `axprotcov3Phi`, `axprotcov3_na_pure_global`
`axprotcov3NaPureGlobal`.

**Not ported:** the §4 `Print Assumptions` audit (the lint's axiom check covers it).
-/
import Weak.AxProtCov2
import Weak.AxGateAdeq

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp

/-! # 0. THE GENERIC `list_to_map` LOOKUP LEMMA — item (i) -/

theorem fmapFstPair {A B : Type _} (f : A → B) (l : List A) :
    ((l.map fun x => (x, f x)).map Prod.fst) = l := by
  induction l with
  | nil => rfl
  | cons x l ih => simp only [List.map_cons, ih]

theorem mapOfFunLookupSome {V : Type _} (f : Geid → V) (L : List Geid) (Hnd : L.Nodup)
    (e : Geid) (He : e ∈ L) :
    get? (PartialMap.ofList (L.map fun e0 => (e0, f e0)) : GMapF Geid V) e = some (f e) := by
  apply elemOfListToMap1
  · rw [fmapFstPair]; exact Hnd
  · exact List.mem_map.2 ⟨e, He, rfl⟩

theorem mapOfFunLookupNone {V : Type _} (f : Geid → V) (L : List Geid) (e : Geid) (He : e ∉ L) :
    get? (PartialMap.ofList (L.map fun e0 => (e0, f e0)) : GMapF Geid V) e = none := by
  apply notElemOfListToMap.1
  rw [fmapFstPair]; exact He

/-! # 1.1 THE CHAIN MACHINERY (reused from `AxProtCov2`, deviation 2) -/

theorem AxProtCov3.axprotImmpredByte' (GD : Gdexec) (wdat : Geid → Int × BitVec 8)
    (HwdatSpec : ∀ w a v, gisW GD.gdG w = true →
      (gwritesByte GD.gdG w a v ↔ (a, v) = wdat w))
    (w w0 : Geid) :
    axprotImmpred GD w = some w0 → (wdat w0).1 = (wdat w).1 :=
  axprotImmpredByte GD wdat HwdatSpec w w0

theorem AxProtCov3.axprotImmpredGposLt' (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (w w0 : Geid) :
    axprotImmpred GD w = some w0 → gpos GD.gdG w0 < gpos GD.gdG w :=
  axprotImmpredGposLt GD Hcons w w0

theorem AxProtCov3.axprotImmpredInj' (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (wdat : Geid → Int × BitVec 8)
    (HwdatSpec : ∀ w a v, gisW GD.gdG w = true →
      (gwritesByte GD.gdG w a v ↔ (a, v) = wdat w))
    (p w1 w2 : Geid) :
    axprotImmpred GD w1 = some p → axprotImmpred GD w2 = some p → w1 = w2 :=
  axprotImmpredInj GD Hcons wdat HwdatSpec p w1 w2

def AxProtCov3.hOfFuel' (GD : Gdexec) (wdat : Geid → Int × BitVec 8) : Nat → Geid → List Hent :=
  hOfFuel GD wdat

def AxProtCov3.hOf' (GD : Gdexec) (wdat : Geid → Int × BitVec 8) (w : Geid) : List Hent :=
  AxProtCov3.hOfFuel' GD wdat (gpos GD.gdG w) w

theorem AxProtCov3.hOfFuelSEq' (GD : Gdexec) (wdat : Geid → Int × BitVec 8) (f : Nat)
    (w w0 : Geid) :
    axprotImmpred GD w = some w0 →
    AxProtCov3.hOfFuel' GD wdat (f + 1) w = AxProtCov3.hOfFuel' GD wdat f w0 ++ [(w, (wdat w).2)] :=
  hOfFuelSEq GD wdat f w w0

theorem AxProtCov3.hOfFuelNoneEq' (GD : Gdexec) (wdat : Geid → Int × BitVec 8) (f : Nat)
    (w : Geid) :
    axprotImmpred GD w = none → AxProtCov3.hOfFuel' GD wdat f w = [(w, (wdat w).2)] :=
  hOfFuelNoneEq GD wdat f w

theorem AxProtCov3.hOfFuelStable' (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (wdat : Geid → Int × BitVec 8) :
    ∀ f w, gpos GD.gdG w ≤ f →
      ∀ f', gpos GD.gdG w ≤ f' → AxProtCov3.hOfFuel' GD wdat f w = AxProtCov3.hOfFuel' GD wdat f' w :=
  hOfFuelStable GD Hcons wdat

theorem AxProtCov3.hOfFirst' (GD : Gdexec) (wdat : Geid → Int × BitVec 8) (w : Geid) :
    axprotImmpred GD w = none → AxProtCov3.hOf' GD wdat w = [(w, (wdat w).2)] :=
  hOfFirst GD wdat w

theorem AxProtCov3.hOfChain' (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (wdat : Geid → Int × BitVec 8) (w w0 : Geid) :
    axprotImmpred GD w = some w0 →
    AxProtCov3.hOf' GD wdat w = AxProtCov3.hOf' GD wdat w0 ++ [(w, (wdat w).2)] :=
  hOfChain GD Hcons wdat w w0

/-! # 1.2 `axprotImmsucc`, AND UNIQUENESS OF A BYTE'S FIRST WRITE -/

theorem AxProtCov3.axprotImmpredDom (GD : Gdexec) (Hcons : rvwmoCatConsistent GD) (w w0 : Geid) :
    axprotImmpred GD w = some w0 → w ∈ GD.gdG.gxGmo := by
  intro himm
  obtain ⟨_, _, _, _, hwb, _⟩ := AxProtCov2.immpredGco GD w w0 himm
  exact ((gwritesElemOf _ _).1 (gwritesByteGwrites _ _ _ _ Hcons.1 hwb)).1

/-- The write, if any, whose gco-immediate predecessor is `p`. -/
def AxProtCov3.axprotImmsucc (GD : Gdexec) (p : Geid) : Option Geid :=
  GD.gdG.gxGmo.find? (fun w' => decide (axprotImmpred GD w' = some p))

theorem AxProtCov3.axprotImmsuccSome (GD : Gdexec) (p w' : Geid) :
    AxProtCov3.axprotImmsucc GD p = some w' → axprotImmpred GD w' = some p := by
  intro h
  unfold AxProtCov3.axprotImmsucc at h
  exact of_decide_eq_true
    (List.find?_some (p := fun w' => decide (axprotImmpred GD w' = some p)) h)

theorem AxProtCov3.axprotImmsuccNone (GD : Gdexec) (Hcons : rvwmoCatConsistent GD) (p : Geid) :
    AxProtCov3.axprotImmsucc GD p = none → ∀ w', axprotImmpred GD w' = some p → False := by
  intro h w' himm
  unfold AxProtCov3.axprotImmsucc at h
  rw [List.find?_eq_none] at h
  exact h w' (AxProtCov3.axprotImmpredDom GD Hcons w' p himm) (decide_eq_true himm)

theorem AxProtCov3.axprotImmsuccNoneOfNonwrite (GD : Gdexec) (p : Geid)
    (Hp : gisW GD.gdG p = false) : AxProtCov3.axprotImmsucc GD p = none := by
  cases hs : AxProtCov3.axprotImmsucc GD p with
  | none => rfl
  | some w' =>
    exfalso
    have himm := AxProtCov3.axprotImmsuccSome GD p w' hs
    obtain ⟨_, _, _, hwb, _, _⟩ := AxProtCov2.immpredGco GD w' p himm
    rw [WeakRvwmoGraph.gwritesByteGisW _ _ _ _ hwb] at Hp
    exact Bool.noConfusion Hp

theorem AxProtCov3.firstWriteUniq (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (w1 w2 : Geid) (a : Int) (v1 v2 : BitVec 8) :
    gwritesByte GD.gdG w1 a v1 → axprotImmpred GD w1 = none →
    gwritesByte GD.gdG w2 a v2 → axprotImmpred GD w2 = none →
    w1 = w2 := by
  intro hw1 himm1 hw2 himm2
  by_cases hne : w1 = w2
  · exact hne
  exfalso
  have hwf := Hcons.1
  have hw1w := gwritesByteGwrites _ _ _ _ hwf hw1
  have hw2w := gwritesByteGwrites _ _ _ _ hwf hw2
  have hgwix : gwix GD.gdG w1 ≠ gwix GD.gdG w2 := fun h => hne (gwixInj _ _ _ hwf.1 hw1w hw2w h)
  have key : ∀ x y vx vy, gwritesByte GD.gdG x a vx → gwritesByte GD.gdG y a vy →
      x ∈ GD.gdG.gxGmo → gwix GD.gdG x < gwix GD.gdG y → axprotImmpred GD y = none → False := by
    intro x y vx vy hx hy hxm hlt hnone
    have hin : x ∈ GD.gdG.gxGmo.filter (fun w => gcoB GD.gdG w y) :=
      List.mem_filter.2 ⟨hxm, (gcoBSpec _ _ _).2 ⟨a, vx, vy, hx, hy, hlt⟩⟩
    unfold axprotImmpred at hnone
    rw [List.getLast?_eq_none_iff] at hnone
    rw [hnone] at hin
    exact List.not_mem_nil hin
  rcases Nat.lt_or_gt_of_ne hgwix with h | h
  · exact key w1 w2 v1 v2 hw1 hw2 ((gwritesElemOf _ _).1 hw1w).1 h himm2
  · exact key w2 w1 v2 v1 hw2 hw1 ((gwritesElemOf _ _).1 hw2w).1 h himm1

/-! # 1.3 `naOf`/`eaOf`, AND THE `eaDeposit` COLLAPSE — item (iii) -/

section annot

variable {GF : BundledGFunctors} [AxlogG GF Hent]

def AxProtCov3.V (γ : GName) (GD : Gdexec) (wdat : Geid → Int × BitVec 8) (p : Geid) : IProp GF :=
  histAuth γ (wdat p).1 1 (AxProtCov3.hOf' GD wdat p)

def AxProtCov3.naVal (γ : GName) (GD : Gdexec) (wdat : Geid → Int × BitVec 8) (e : Geid) :
    IProp GF :=
  if gisW GD.gdG e then
    iprop(histSnap γ (wdat e).1 (AxProtCov3.hOf' GD wdat e) ∗
      ∃ (data : List (BitVec 8)), ⌜graphData GD e = some data⌝)
  else iprop(emp)

def AxProtCov3.eaVal (γ : GName) (GD : Gdexec) (wdat : Geid → Int × BitVec 8) (e : Geid) :
    Mea GF :=
  if gisW GD.gdG e then
    match axprotImmpred GD e with
    | some w0 => {[w0 := AxProtCov3.V γ GD wdat w0]}
    | none => ∅
  else ∅

def AxProtCov3.naOf (γ : GName) (GD : Gdexec) (wdat : Geid → Int × BitVec 8) : Mea GF :=
  PartialMap.ofList (GD.gdG.gxGmo.map fun e => (e, AxProtCov3.naVal γ GD wdat e))

def AxProtCov3.eaOf (γ : GName) (GD : Gdexec) (wdat : Geid → Int × BitVec 8) : Sra GF :=
  PartialMap.ofList (GD.gdG.gxGmo.map fun e => (e, AxProtCov3.eaVal γ GD wdat e))

theorem AxProtCov3.naOfLookup (γ : GName) (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (wdat : Geid → Int × BitVec 8) (e : Geid) (He : e ∈ GD.gdG.gxGmo) :
    get? (AxProtCov3.naOf (GF := GF) γ GD wdat) e = some (AxProtCov3.naVal γ GD wdat e) := by
  unfold AxProtCov3.naOf
  exact mapOfFunLookupSome _ _ Hcons.1.1 e He

theorem AxProtCov3.naOfLookupNone (γ : GName) (GD : Gdexec) (wdat : Geid → Int × BitVec 8)
    (e : Geid) (He : e ∉ GD.gdG.gxGmo) :
    get? (AxProtCov3.naOf (GF := GF) γ GD wdat) e = none := by
  unfold AxProtCov3.naOf
  exact mapOfFunLookupNone _ _ e He

theorem AxProtCov3.eaOfLookup (γ : GName) (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (wdat : Geid → Int × BitVec 8) (e : Geid) (He : e ∈ GD.gdG.gxGmo) :
    get? (AxProtCov3.eaOf (GF := GF) γ GD wdat) e = some (AxProtCov3.eaVal γ GD wdat e) := by
  unfold AxProtCov3.eaOf
  exact mapOfFunLookupSome _ _ Hcons.1.1 e He

theorem AxProtCov3.eaOfLookupNone (γ : GName) (GD : Gdexec) (wdat : Geid → Int × BitVec 8)
    (e : Geid) (He : e ∉ GD.gdG.gxGmo) :
    get? (AxProtCov3.eaOf (GF := GF) γ GD wdat) e = none := by
  unfold AxProtCov3.eaOf
  exact mapOfFunLookupNone _ _ e He

theorem AxProtCov3.eaValLookupNone (γ : GName) (GD : Gdexec) (wdat : Geid → Int × BitVec 8)
    (eOut p : Geid) :
    axprotImmpred GD eOut ≠ some p → get? (AxProtCov3.eaVal (GF := GF) γ GD wdat eOut) p = none := by
  intro hne
  unfold AxProtCov3.eaVal
  cases gisW GD.gdG eOut
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact get?_empty p
  · simp only [↓reduceIte]
    cases himm : axprotImmpred GD eOut with
    | none => exact get?_empty p
    | some w0 =>
      have hw0 : w0 ≠ p := fun h => hne (h ▸ himm)
      exact lookupSingletonNe hw0

/-- Lean-only: the deposit summand at `eOut` vanishes unless `eOut` names `p` as predecessor. -/
theorem AxProtCov3.depAtEmpEq {hlc : HasLC} [InvGS_gen hlc GF] [AxirisG GF]
    (γ : GName) (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (wdat : Geid → Int × BitVec 8) (eOut p : Geid) (Hne : axprotImmpred GD eOut ≠ some p) :
    AxLifting.depAt (AxProtCov3.eaOf (GF := GF) γ GD wdat) p eOut = iprop(emp) := by
  by_cases hin : eOut ∈ GD.gdG.gxGmo
  · exact AxLifting.depAtSomeNone _ p eOut _ (AxProtCov3.eaOfLookup γ GD Hcons wdat eOut hin)
      (AxProtCov3.eaValLookupNone γ GD wdat eOut p Hne)
  · exact AxLifting.depAtNone _ p eOut (AxProtCov3.eaOfLookupNone γ GD wdat eOut hin)

theorem AxProtCov3.eaDepositTermEmp {hlc : HasLC} [InvGS_gen hlc GF] [AxirisG GF]
    (γ : GName) (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (wdat : Geid → Int × BitVec 8) (eOut p : Geid) (Hne : axprotImmpred GD eOut ≠ some p) :
    ⊢ AxLifting.depAt (AxProtCov3.eaOf (GF := GF) γ GD wdat) p eOut := by
  rw [AxProtCov3.depAtEmpEq γ GD Hcons wdat eOut p Hne] <;> exact .rfl

theorem AxProtCov3.eaDepositPEq {hlc : HasLC} [InvGS_gen hlc GF] [AxirisG GF]
    (γ : GName) (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (wdat : Geid → Int × BitVec 8)
    (HwdatSpec : ∀ w a v, gisW GD.gdG w = true →
      (gwritesByte GD.gdG w a v ↔ (a, v) = wdat w))
    (p : Geid) :
    eaDeposit (AxProtCov3.eaOf (GF := GF) γ GD wdat) (lobSuccOf GD p) p ⊣⊢
      (match AxProtCov3.axprotImmsucc GD p with
       | some _ => AxProtCov3.V γ GD wdat p
       | none => iprop(emp)) := by
  unfold eaDeposit
  cases hs : AxProtCov3.axprotImmsucc GD p with
  | some w' =>
    have himm := AxProtCov3.axprotImmsuccSome GD p w' hs
    have hdomw := AxProtCov3.axprotImmpredDom GD Hcons w' p himm
    have hin : w' ∈ lobSuccOf GD p :=
      (elemOfLobSuccOf GD p w').2 ⟨axprotImmpredPred GD w' p himm, hdomw⟩
    have hisw : gisW GD.gdG w' = true := by
      obtain ⟨_, _, _, _, hwb, _⟩ := AxProtCov2.immpredGco GD w' p himm
      exact WeakRvwmoGraph.gwritesByteGisW _ _ _ _ hwb
    have hev : get? (AxProtCov3.eaVal (GF := GF) γ GD wdat w') p =
        some (AxProtCov3.V γ GD wdat p) := by
      unfold AxProtCov3.eaVal
      simp only [hisw, ↓reduceIte, himm]
      exact lookupSingleton
    have hdep : AxLifting.depAt (AxProtCov3.eaOf (GF := GF) γ GD wdat) p w' =
        AxProtCov3.V γ GD wdat p :=
      AxLifting.depAtSomeSome _ p w' _ _ (AxProtCov3.eaOfLookup γ GD Hcons wdat w' hdomw) hev
    have hrest : ([∗set] y ∈ lobSuccOf GD p \ {w'},
          AxLifting.depAt (AxProtCov3.eaOf (GF := GF) γ GD wdat) p y) =
        ([∗set] _y ∈ lobSuccOf GD p \ {w'}, (iprop(emp) : IProp GF)) :=
      BigSepS.bigSepS_eq fun {y} hy => AxProtCov3.depAtEmpEq γ GD Hcons wdat y p (fun habs =>
        (elemOfDifference.1 hy).2 (elemOfSingleton.2
          (AxProtCov3.axprotImmpredInj' GD Hcons wdat HwdatSpec p y w' habs himm)))
    refine (BigSepS.bigSepS_delete hin).trans ?_
    rw [hdep, hrest]
    exact (sep_congr .rfl BigSepS.bigSepS_emp).trans sep_emp
  | none =>
    rw [BigSepS.bigSepS_eq (fun {y} _ => AxProtCov3.depAtEmpEq γ GD Hcons wdat y p
      (fun habs => AxProtCov3.axprotImmsuccNone GD Hcons p hs y habs))]
    exact BigSepS.bigSepS_emp

end annot

/-! # 1.4 THE THREE PER-EVENT FLOW OBLIGATIONS -/

section flows

variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [AxlogG GF Hent]

def AxProtCov3.F (γ : GName) (GD : Gdexec) (wdat : Geid → Int × BitVec 8) (e0 : Geid) :
    IProp GF :=
  flowEqEa GD e0 (Axpol.sPol GD e0) (AxProtCov3.eaVal γ GD wdat e0) (AxProtCov3.eaOf γ GD wdat)
    (AxProtCov3.naVal γ GD wdat e0)

/-- Lean-only: `flowEqDynMono` with a pure-entailment premise. -/
theorem AxProtCov3.flowEqDynPost (GD : Gdexec) (e : Geid) (sOb0 : GSet Geid) (flowIn : Mea GF)
    (R1 R2 : IProp GF) (h : R1 ⊢ R2) :
    flowEqDyn GD e sOb0 flowIn R1 ⊢ flowEqDyn GD e sOb0 flowIn R2 := by
  iintro H
  ihave Hw : ▷ (R1 -∗ R2) $$ []
  · inext
    iintro HR
    iapply h
    iexact HR
  iapply flowEqDynMono GD e sOb0 flowIn R1 R2 $$ Hw H

theorem AxProtCov3.flowEqReadTrivial (γ : GName)
    (Hob_eq : ∀ (GD : Gdexec) (σ : AxirisG.obSt GF) (s : GSet Geid),
      AxirisG.obStInterp GD σ s ⊣⊢ protInv γ GD s)
    (GD : Gdexec) (r : Geid) (Hr : gisW GD.gdG r = false) :
    ⊢ flowEqDyn GD r ∅ (∅ : Mea GF) iprop(emp) := by
  unfold flowEqDyn
  iintro %σ %sOb %_Hsub %Hnin Hob _
  ihave Hob := (Hob_eq GD σ sOb).1 $$ Hob
  ihave Hinv := protInvReadStep γ GD sOb r Hnin Hr $$ Hob
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  inext
  imod Hclose
  imodintro
  iexists σ
  isplitl [Hinv]
  · iapply (Hob_eq GD σ (({r} : GSet Geid) ∪ sOb)).2
    iexact Hinv
  · iempintro

theorem flowEqEaOfRead (γ : GName)
    (Hob_eq : ∀ (GD : Gdexec) (σ : AxirisG.obSt GF) (s : GSet Geid),
      AxirisG.obStInterp GD σ s ⊣⊢ protInv γ GD s)
    (GD : Gdexec) (Hcons : rvwmoCatConsistent GD) (wdat : Geid → Int × BitVec 8)
    (HwdatSpec : ∀ w a v, gisW GD.gdG w = true →
      (gwritesByte GD.gdG w a v ↔ (a, v) = wdat w))
    (e0 : Geid) (Hnw : gisW GD.gdG e0 = false) :
    ⊢ AxProtCov3.F (GF := GF) γ GD wdat e0 := by
  have hea : AxProtCov3.eaVal (GF := GF) γ GD wdat e0 = ∅ := by
    unfold AxProtCov3.eaVal; simp only [Hnw, Bool.false_eq_true, ↓reduceIte]
  have hna : AxProtCov3.naVal (GF := GF) γ GD wdat e0 = iprop(emp) := by
    unfold AxProtCov3.naVal; simp only [Hnw, Bool.false_eq_true, ↓reduceIte]
  have hdep : ⊢ eaDeposit (AxProtCov3.eaOf (GF := GF) γ GD wdat) (lobSuccOf GD e0) e0 := by
    have h := (AxProtCov3.eaDepositPEq (GF := GF) γ GD Hcons wdat HwdatSpec e0).2
    rw [AxProtCov3.axprotImmsuccNoneOfNonwrite GD e0 Hnw] at h
    exact h
  have hbase : ⊢ flowEqDyn GD e0 (Axpol.sPol GD e0) (∅ : Mea GF) iprop(emp) :=
    (AxProtCov3.flowEqReadTrivial γ Hob_eq GD e0 Hnw).trans
      (flowEqDynPolMono GD e0 ∅ _ ∅ _ emptySubseteq)
  have hpost : (iprop(emp) : IProp GF) ⊢
      iprop(emp ∗ eaDeposit (AxProtCov3.eaOf (GF := GF) γ GD wdat) (lobSuccOf GD e0) e0) :=
    emp_sep.2.trans (sep_mono .rfl hdep)
  unfold AxProtCov3.F flowEqEa
  rw [hea, hna]
  exact hbase.trans (AxProtCov3.flowEqDynPost GD e0 _ _ _ _ hpost)

/-- Lean-only: the common body of the two write lemmas, given the incoming bag's content `Hl`
and the chain equation `hOf' e0 = Hl ++ [(e0, _)]`. -/
theorem AxProtCov3.flowEqEaOfWriteGen (γ : GName)
    (Hob_eq : ∀ (GD : Gdexec) (σ : AxirisG.obSt GF) (s : GSet Geid),
      AxirisG.obStInterp GD σ s ⊣⊢ protInv γ GD s)
    (GD : Gdexec) (Hcons : rvwmoCatConsistent GD) (wdat : Geid → Int × BitVec 8)
    (HwdatSpec : ∀ w a v, gisW GD.gdG w = true →
      (gwritesByte GD.gdG w a v ↔ (a, v) = wdat w))
    (HdataTot : ∀ w, gisW GD.gdG w = true → ∃ data, graphData GD w = some data)
    (e0 : Geid) (Hisw : gisW GD.gdG e0 = true) (Hl : List Hent) (flowIn : Mea GF)
    (Hea : AxProtCov3.eaVal γ GD wdat e0 = flowIn)
    (Hch : AxProtCov3.hOf' GD wdat e0 = Hl ++ [(e0, (wdat e0).2)]) :
    iprop(([∗map] Rin ∈ flowIn, Rin) -∗ histAuth γ (wdat e0).1 1 Hl) ⊢
      AxProtCov3.F γ GD wdat e0 := by
  have Hwb : gwritesByte GD.gdG e0 (wdat e0).1 (wdat e0).2 := (HwdatSpec e0 _ _ Hisw).2 rfl
  have Hsingle : ∀ a' v', gwritesByte GD.gdG e0 a' v' → a' = (wdat e0).1 :=
    fun a' v' h => congrArg Prod.fst ((HwdatSpec e0 a' v' Hisw).1 h)
  obtain ⟨data, Hgd⟩ := HdataTot e0 Hisw
  have Hbase := flowEqOwnedWriteChainSnap γ Hob_eq GD e0 (wdat e0).1 (wdat e0).2 Hl
    (Axpol.sPol GD e0) flowIn data Hwb Hsingle Hgd
  have hA : iprop(histSnap γ (wdat e0).1 (Hl ++ [(e0, (wdat e0).2)]) ∗
      ⌜graphData GD e0 = some data⌝) ⊢ AxProtCov3.naVal (GF := GF) γ GD wdat e0 := by
    unfold AxProtCov3.naVal
    simp only [Hisw, ↓reduceIte]
    rw [Hch]
    iintro ⟨Hs, %h⟩
    isplitl [Hs]
    · iexact Hs
    · iexists data
      ipureintro
      exact h
  have hB : tokTie GD γ (wdat e0).1 (Hl ++ [(e0, (wdat e0).2)]) {[e0 := (1 : Qp)]} ⊢
      eaDeposit (AxProtCov3.eaOf (GF := GF) γ GD wdat) (lobSuccOf GD e0) e0 := by
    refine Entails.trans ?_ (AxProtCov3.eaDepositPEq (GF := GF) γ GD Hcons wdat HwdatSpec e0).2
    cases AxProtCov3.axprotImmsucc GD e0 with
    | none =>
      show _ ⊢ iprop(emp)
      iintro _
      iempintro
    | some _ =>
      show _ ⊢ AxProtCov3.V γ GD wdat e0
      unfold tokTie AxProtCov3.V
      rw [Hch]
      iintro ⟨Ht, -⟩
      iapply (tokSingleton γ _ _ e0 1).1
      iexact Ht
  have hpost := sep_comm.1.trans (sep_mono hA hB)
  unfold AxProtCov3.F flowEqEa
  rw [Hea]
  exact Hbase.trans (AxProtCov3.flowEqDynPost GD e0 _ _ _ _ hpost)

theorem flowEqEaOfWriteNonfirst (γ : GName)
    (Hob_eq : ∀ (GD : Gdexec) (σ : AxirisG.obSt GF) (s : GSet Geid),
      AxirisG.obStInterp GD σ s ⊣⊢ protInv γ GD s)
    (GD : Gdexec) (Hcons : rvwmoCatConsistent GD) (wdat : Geid → Int × BitVec 8)
    (HwdatSpec : ∀ w a v, gisW GD.gdG w = true →
      (gwritesByte GD.gdG w a v ↔ (a, v) = wdat w))
    (HdataTot : ∀ w, gisW GD.gdG w = true → ∃ data, graphData GD w = some data)
    (e0 w0 : Geid) (Hisw : gisW GD.gdG e0 = true) (Himm : axprotImmpred GD e0 = some w0) :
    ⊢ AxProtCov3.F (GF := GF) γ GD wdat e0 := by
  have hea : AxProtCov3.eaVal (GF := GF) γ GD wdat e0 = {[w0 := AxProtCov3.V γ GD wdat w0]} := by
    unfold AxProtCov3.eaVal; simp only [Hisw, ↓reduceIte, Himm]
  have Hbyte := AxProtCov3.axprotImmpredByte' GD wdat HwdatSpec e0 w0 Himm
  have hflow : ([∗map] Rin ∈ ({[w0 := AxProtCov3.V γ GD wdat w0]} : Mea GF), Rin) ⊢
      histAuth γ (wdat e0).1 1 (AxProtCov3.hOf' GD wdat w0) := by
    refine BigSepM.bigSepM_singleton.1.trans (BiEntails.of_eq ?_).1
    unfold AxProtCov3.V
    rw [Hbyte]
  exact (wand_intro (emp_sep.1.trans hflow)).trans
    (AxProtCov3.flowEqEaOfWriteGen γ Hob_eq GD Hcons wdat HwdatSpec HdataTot e0 Hisw
      (AxProtCov3.hOf' GD wdat w0) _ hea (AxProtCov3.hOfChain' GD Hcons wdat e0 w0 Himm))

theorem flowEqEaOfWriteFirst (γ : GName)
    (Hob_eq : ∀ (GD : Gdexec) (σ : AxirisG.obSt GF) (s : GSet Geid),
      AxirisG.obStInterp GD σ s ⊣⊢ protInv γ GD s)
    (GD : Gdexec) (Hcons : rvwmoCatConsistent GD) (wdat : Geid → Int × BitVec 8)
    (HwdatSpec : ∀ w a v, gisW GD.gdG w = true →
      (gwritesByte GD.gdG w a v ↔ (a, v) = wdat w))
    (HdataTot : ∀ w, gisW GD.gdG w = true → ∃ data, graphData GD w = some data)
    (e0 : Geid) (Hisw : gisW GD.gdG e0 = true) (Himm : axprotImmpred GD e0 = none) :
    histAuth γ (wdat e0).1 1 [] ⊢ AxProtCov3.F (GF := GF) γ GD wdat e0 := by
  have hea : AxProtCov3.eaVal (GF := GF) γ GD wdat e0 = ∅ := by
    unfold AxProtCov3.eaVal; simp only [Hisw, ↓reduceIte, Himm]
  have hflow : histAuth γ (wdat e0).1 1 [] ⊢
      iprop(([∗map] Rin ∈ (∅ : Mea GF), Rin) -∗ histAuth γ (wdat e0).1 1 []) := by
    iintro Ha _
    iexact Ha
  exact hflow.trans
    (AxProtCov3.flowEqEaOfWriteGen γ Hob_eq GD Hcons wdat HwdatSpec HdataTot e0 Hisw [] _ hea
      (AxProtCov3.hOfFirst' GD wdat e0 Himm))

/-! # 1.5 `distributeFirstWrites` — item (ii) -/

theorem distributeFirstWrites (γ : GName)
    (Hob_eq : ∀ (GD : Gdexec) (σ : AxirisG.obSt GF) (s : GSet Geid),
      AxirisG.obStInterp GD σ s ⊣⊢ protInv γ GD s)
    (GD : Gdexec) (Hcons : rvwmoCatConsistent GD) (wdat : Geid → Int × BitVec 8)
    (HwdatSpec : ∀ w a v, gisW GD.gdG w = true →
      (gwritesByte GD.gdG w a v ↔ (a, v) = wdat w))
    (HdataTot : ∀ w, gisW GD.gdG w = true → ∃ data, graphData GD w = some data)
    (K : List Geid) :
    ∀ (Xk : GSet Int), K.Nodup →
      (∀ w, w ∈ K → gisW GD.gdG w = true → axprotImmpred GD w = none → (wdat w).1 ∈ Xk) →
      iprop([∗set] a ∈ Xk, histAuth (GF := GF) γ a 1 []) ⊢
        [∗list] e0 ∈ K, AxProtCov3.F γ GD wdat e0 := by
  induction K with
  | nil => intro _ _ _; exact BigSepL.bigSepL_nil_intro
  | cons e0 K ih =>
    intro Xk Hnd Hcov
    obtain ⟨Hnin, Hnd'⟩ := List.nodup_cons.1 Hnd
    refine Entails.trans ?_ BigSepL.bigSepL_cons.2
    have Hcov' : ∀ w, w ∈ K → gisW GD.gdG w = true → axprotImmpred GD w = none →
        (wdat w).1 ∈ Xk := fun w hw h1 h2 => Hcov w (List.mem_cons.2 (Or.inr hw)) h1 h2
    cases Hisw : gisW GD.gdG e0
    · exact emp_sep.2.trans (sep_mono
        (flowEqEaOfRead γ Hob_eq GD Hcons wdat HwdatSpec e0 Hisw) (ih Xk Hnd' Hcov'))
    · cases Himm : axprotImmpred GD e0 with
      | some w0 =>
        exact emp_sep.2.trans (sep_mono
          (flowEqEaOfWriteNonfirst γ Hob_eq GD Hcons wdat HwdatSpec HdataTot e0 w0 Hisw Himm)
          (ih Xk Hnd' Hcov'))
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
          have hwe0 := AxProtCov3.firstWriteUniq GD Hcons w e0 (wdat w).1 (wdat w).2 (wdat e0).2
            hbyw himm' hbye0 Himm
          exact Hnin (hwe0 ▸ hw)
        exact (BigSepS.bigSepS_delete Ha).1.trans (sep_mono
          (flowEqEaOfWriteFirst γ Hob_eq GD Hcons wdat HwdatSpec HdataTot e0 Hisw Himm)
          (ih _ Hnd' Hcov''))

end flows

/-! # 1.6 DOMAIN FACTS -/

section dom

variable {GF : BundledGFunctors} [AxlogG GF Hent]

theorem AxProtCov3.naOfDom (γ : GName) (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (wdat : Geid → Int × BitVec 8) :
    (FiniteMap.dom_set (AxProtCov3.naOf (GF := GF) γ GD wdat) : GSet Geid) =
      LawfulSet.ofList GD.gdG.gxGmo := by
  rw [setEq]
  intro e
  rw [elemOfDom, elemOfListToSet]
  constructor
  · intro Hv
    by_cases Hin : e ∈ GD.gdG.gxGmo
    · exact Hin
    · rw [AxProtCov3.naOfLookupNone γ GD wdat e Hin] at Hv
      exact absurd Hv Bool.false_ne_true
  · intro Hin
    rw [AxProtCov3.naOfLookup γ GD Hcons wdat e Hin]
    rfl

theorem AxProtCov3.eaOfDom (γ : GName) (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (wdat : Geid → Int × BitVec 8) :
    (FiniteMap.dom_set (AxProtCov3.eaOf (GF := GF) γ GD wdat) : GSet Geid) =
      LawfulSet.ofList GD.gdG.gxGmo := by
  rw [setEq]
  intro e
  rw [elemOfDom, elemOfListToSet]
  constructor
  · intro Hv
    by_cases Hin : e ∈ GD.gdG.gxGmo
    · exact Hin
    · rw [AxProtCov3.eaOfLookupNone γ GD wdat e Hin] at Hv
      exact absurd Hv Bool.false_ne_true
  · intro Hin
    rw [AxProtCov3.eaOfLookup γ GD Hcons wdat e Hin]
    rfl

theorem naOfEaOfDomEq (γ : GName) (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (wdat : Geid → Int × BitVec 8) :
    (FiniteMap.dom_set (AxProtCov3.eaOf (GF := GF) γ GD wdat) : GSet Geid) =
      FiniteMap.dom_set (AxProtCov3.naOf (GF := GF) γ GD wdat) := by
  rw [AxProtCov3.eaOfDom γ GD Hcons wdat, AxProtCov3.naOfDom γ GD Hcons wdat]

theorem heaLob (γ : GName) (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (wdat : Geid → Int × BitVec 8) :
    ∀ e0 gm, get? (AxProtCov3.eaOf (GF := GF) γ GD wdat) e0 = some gm →
      (FiniteMap.dom_set gm : GSet Geid) ⊆ Axpol.lobp GD e0 := by
  intro e0 gm Hea
  by_cases Hin : e0 ∈ GD.gdG.gxGmo
  · rw [AxProtCov3.eaOfLookup γ GD Hcons wdat e0 Hin] at Hea
    cases Option.some.inj Hea
    unfold AxProtCov3.eaVal
    cases gisW GD.gdG e0
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [domEmpty] <;> exact emptySubseteq
    · simp only [↓reduceIte]
      cases Himm : axprotImmpred GD e0 with
      | none => rw [domEmpty] <;> exact emptySubseteq
      | some w0 =>
        rw [domSingleton]
        intro x hx
        rw [elemOfSingleton.1 hx]
        exact axprotImmpredPred GD e0 w0 Himm
  · rw [AxProtCov3.eaOfLookupNone γ GD wdat e0 Hin] at Hea
    cases Hea

end dom

/-! # 1.7 THE WIRING THEOREM -/

section wiring

variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [AxlogG GF Hent]

/-- Lean-only: the `ordEaTodoL` line at a `gxGmo` event is `F`. -/
theorem AxProtCov3.todoAtEq (γ : GName) (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (wdat : Geid → Int × BitVec 8) (e : Geid) (He : e ∈ GD.gdG.gxGmo) :
    AxWp.fromOption (fun R0 => AxWp.fromOption
        (fun flowIn => flowEqEa GD e (Axpol.sPol GD e) flowIn (AxProtCov3.eaOf (GF := GF) γ GD wdat)
          R0) iprop(emp) (get? (AxProtCov3.eaOf (GF := GF) γ GD wdat) e))
      iprop(emp) (get? (AxProtCov3.naOf (GF := GF) γ GD wdat) e) =
    AxProtCov3.F γ GD wdat e := by
  rw [AxProtCov3.naOfLookup γ GD Hcons wdat e He, AxProtCov3.eaOfLookup γ GD Hcons wdat e He] <;>
    rfl

theorem axprotAdequateGhost (γ : GName)
    (Hob_eq : ∀ (GD : Gdexec) (σ : AxirisG.obSt GF) (s : GSet Geid),
      AxirisG.obStInterp GD σ s ⊣⊢ protInv γ GD s)
    (GD : Gdexec) (Hcons : rvwmoCatConsistent GD) (wdat : Geid → Int × BitVec 8)
    (HwdatSpec : ∀ w a v, gisW GD.gdG w = true →
      (gwritesByte GD.gdG w a v ↔ (a, v) = wdat w))
    (HdataTot : ∀ w, gisW GD.gdG w = true → ∃ data, graphData GD w = some data)
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
          [∗set] e0 ∈ (LawfulSet.ofList st.sProc : GSet Geid), AxProtCov3.naVal γ GD wdat e0 := by
  have HGw := schedHGwf GD Hcons
  have HC6 := schedHCat6gmo GD Hcons
  obtain ⟨Hmemiff, HndP, _⟩ := schedCorrect GD.gdG HGw HC6 st Hrun Hfull Hdone
  have Hperm : st.sProc.Perm GD.gdG.gxGmo := NoDup_Permutation HndP HGw.1 Hmemiff
  have Hcov0 : ∀ w, w ∈ GD.gdG.gxGmo → gisW GD.gdG w = true → axprotImmpred GD w = none →
      (wdat w).1 ∈ (LawfulSet.ofList ((gwrites GD.gdG).map fun w0 => (wdat w0).1) : GSet Int) :=
    fun w hw hisw _ => elemOfListToSet.2 (List.mem_map.2 ⟨w, (gwritesElemOf _ _).2 ⟨hw, hisw⟩, rfl⟩)
  have Htodo : ([∗set] a ∈ (LawfulSet.ofList ((gwrites GD.gdG).map fun w => (wdat w).1) :
        GSet Int), histAuth (GF := GF) γ a 1 []) ⊢
      ordEaTodoL GD (AxProtCov3.eaOf γ GD wdat) (AxProtCov3.naOf γ GD wdat) st.sProc 0 := by
    refine (distributeFirstWrites γ Hob_eq GD Hcons wdat HwdatSpec HdataTot GD.gdG.gxGmo _
      HGw.1 Hcov0).trans ?_
    unfold ordEaTodoL
    simp only [List.drop_zero]
    refine Entails.trans ?_ (BigSepL.bigSepL_perm Hperm.symm).1
    exact (BiEntails.of_eq (BigSepL.bigSepL_eq fun {_ x} hk =>
      (AxProtCov3.todoAtEq γ GD Hcons wdat x (List.mem_of_getElem? hk)).symm)).1
  have Hdom : (LawfulSet.ofList st.sProc : GSet Geid) ⊆
      FiniteMap.dom_set (AxProtCov3.naOf (GF := GF) γ GD wdat) := by
    rw [AxProtCov3.naOfDom γ GD Hcons wdat]
    intro e' He'
    rw [elemOfListToSet] at He' ⊢
    exact (Hmemiff e').1 He'
  have Hbag : ([∗set] e0 ∈ (LawfulSet.ofList st.sProc : GSet Geid),
        AxWp.fromOption (fun P => P) iprop(emp) (get? (AxProtCov3.naOf (GF := GF) γ GD wdat) e0)) ⊢
      [∗set] e0 ∈ (LawfulSet.ofList st.sProc : GSet Geid), AxProtCov3.naVal γ GD wdat e0 :=
    BigSepS.bigSepS_mono fun {e0} he => by
      have hin : e0 ∈ GD.gdG.gxGmo := (Hmemiff e0).1 (elemOfListToSet.1 he)
      rw [AxProtCov3.naOfLookup γ GD Hcons wdat e0 hin] <;> exact .rfl
  have Had := axprotSchedProcAdequateCov GD Hcons st Hrun Hfull Hdone
    (AxProtCov3.naOf γ GD wdat) (AxProtCov3.eaOf γ GD wdat) (naOfEaOfDomEq γ GD Hcons wdat) Hdom
    (heaLob γ GD Hcons wdat) Hreal σ0
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

/-! # 2. `axprotOwnedReadsValidated` — the read-validation corollary -/

theorem axprotOwnedReadsValidated (γ : GName)
    (Hob_eq : ∀ (GD : Gdexec) (σ : AxirisG.obSt GF) (s : GSet Geid),
      AxirisG.obStInterp GD σ s ⊣⊢ protInv γ GD s)
    (GD : Gdexec) (Hcons : rvwmoCatConsistent GD) (wdat : Geid → Int × BitVec 8)
    (HwdatSpec : ∀ w a v, gisW GD.gdG w = true →
      (gwritesByte GD.gdG w a v ↔ (a, v) = wdat w))
    (HdataTot : ∀ w, gisW GD.gdG w = true → ∃ data, graphData GD w = some data)
    (st : Sstate) (Hrun : rtc (schedStep GD.gdG) sst0 st)
    (Hfull : st.sN = GD.gdG.gxGmo.length) (Hdone : st.sD = ∅)
    (Hreal : ∀ r, r ∈ st.sEverD →
      ∃ a t vr wl, greadsByte GD.gdG r a t vr ∧ gwriteAt GD.gdG t = some wl)
    (Hwit : ∀ r a t vr wl,
      greadsByte GD.gdG r a t vr → gwriteAt GD.gdG t = some wl →
      ∃ H_r : List Hent,
        (∀ p, p ∈ H_r → gwritesByte GD.gdG p.1 a p.2) ∧
        chainWith (gmoLt GD.gdG) (H_r.map Prod.fst) ∧
        H_r.getLast? = some (wl, vr) ∧
        deferredReadCov GD a r H_r)
    (Hnofwd : ∀ r a w' v', gwritesByte GD.gdG w' a v' → WeakRvwmoGraph.gpo GD.gdG w' r →
      gmoLt GD.gdG w' r)
    (σ0 : AxirisG.obSt GF) :
    ⊢ ([∗set] a ∈ (LawfulSet.ofList ((gwrites GD.gdG).map fun w => (wdat w).1) : GSet Int),
          histAuth (GF := GF) γ a 1 []) -∗
      AxirisG.obStInterp GD σ0 ∅ -∗
      |={⊤}[∅]▷=>^[st.sProc.length]
        ∃ (σ : AxirisG.obSt GF),
          AxirisG.obStInterp GD σ (LawfulSet.ofList st.sProc) ∗
          ([∗set] e0 ∈ (LawfulSet.ofList st.sProc : GSet Geid), AxProtCov3.naVal γ GD wdat e0) ∗
          ⌜∀ r a t vr wl, greadsByte GD.gdG r a t vr → gwriteAt GD.gdG t = some wl →
            grfAt GD.gdG a wl r ∧ ∀ t' v', greadsByte GD.gdG r a t' v' → v' = vr⌝ := by
  have hpure : ∀ r a t vr wl, greadsByte GD.gdG r a t vr → gwriteAt GD.gdG t = some wl →
      grfAt GD.gdG a wl r ∧ ∀ t' v', greadsByte GD.gdG r a t' v' → v' = vr := by
    intro r a t vr wl Hrd Hwrat
    obtain ⟨H_r, Hwr, Hch, Hlast, Hcov⟩ := Hwit r a t vr wl Hrd Hwrat
    have ⟨_, _, Hgv, _⟩ := Hcons
    obtain ⟨Hsrc, _⟩ := Hgv r a t vr Hrd
    cases t with
    | zero => simp [gwriteAt] at Hwrat
    | succ t' =>
      obtain ⟨w0, Hwat0, _, Hvis0⟩ := Hsrc
      rw [Hwrat, Option.some.injEq] at Hwat0
      subst Hwat0
      have Hown : ∀ w v, gwritesByte GD.gdG w a v → WeakRvwmoGraph.gpo GD.gdG w r →
          w ∈ H_r.map Prod.fst := fun w v Hwb Hgpo => Hcov w v Hwb (Hnofwd r a w v Hwb Hgpo)
      exact ownedReadGhostSnap GD a r H_r wl vr Hcons Hwr Hch Hown Hlast Hvis0
        ⟨t' + 1, vr, Hrd⟩ Hcov
  have H0 := axprotAdequateGhost γ Hob_eq GD Hcons wdat HwdatSpec HdataTot st Hrun Hfull Hdone
    Hreal σ0
  iintro Hb Hob
  ihave H := H0 $$ Hb Hob
  iapply step_fupdN_wand $$ H
  iintro ⟨%σ, Hobf, Hbg⟩
  iexists σ
  isplitl [Hobf]
  · iexact Hobf
  · isplitl [Hbg]
    · iexact Hbg
    · ipureintro
      exact hpure

end wiring

/-! # 3. `axprotcov3NaPureGlobal` — the purity half of `gateFacts` for `naOf` -/

def axprotcov3Phi (GD : Gdexec) (e : Geid) : Prop :=
  if gisW GD.gdG e then ∃ data, graphData GD e = some data else True

theorem axprotcov3NaPureGlobal {GF : BundledGFunctors} [AxlogG GF Hent]
    (γ : GName) (GD : Gdexec) (Hcons : rvwmoCatConsistent GD) (wdat : Geid → Int × BitVec 8) :
    naPureGlobal (AxProtCov3.naOf (GF := GF) γ GD wdat) (axprotcov3Phi GD) := by
  intro e He
  have hin : e ∈ GD.gdG.gxGmo := by
    rw [AxProtCov3.naOfDom γ GD Hcons wdat, elemOfListToSet] at He
    exact He
  refine ⟨AxProtCov3.naVal γ GD wdat e, AxProtCov3.naOfLookup γ GD Hcons wdat e hin, ?_⟩
  unfold annotPure AxProtCov3.naVal axprotcov3Phi
  cases gisW GD.gdG e
  · simp only [Bool.false_eq_true, ↓reduceIte]
    iintro _
    ipureintro
    trivial
  · simp only [↓reduceIte]
    iintro ⟨_, %data, %h⟩
    ipureintro
    exact ⟨data, h⟩

end Weak
