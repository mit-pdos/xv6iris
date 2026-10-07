/-
Weak: **A7-T2c capstone (reader), part 2: `wpdReaderHart`, the GENESIS-sourced per-hart `WPd`
Löb induction for the lock3s reader row** (`AxLock3Prog.l3pRRow`): the acquire `(i,0)` reads
`L`'s initial image at `t = 0` (AxSL tier).

Rocq: `iris/AxLock3Reader.v` @ xxvzwolszwmp, section `RGen` (§15–§16); §1–§14 are in
`Weak/AxLock3Reader.lean` (split for size; the name `AxLock3Reader2` is free in Rocq).

## The Rocq header, in substance

The genesis path reuses part 1's row-shape facts verbatim (none mentions the release-sourced
context).  Position 0: `r0FlowEqGen` (`lockAcq0FlowEq3A`, depositing the RAW `histAuth`).
Position 3: `r3FlowEqGen` (the release, consuming the raw `histAuth` at the empty history; the
HM conjunct's `hhTiedOrEmpty` is discharged by its `Hh = []` arm, and the per-event slot picks
`xTok`'s raw arm).  Positions 3/2/2b assembled with `Hl := []` fixed (no existential lift).
Position 1: `r1FlowEqGen`, THE OWNED READ at genesis — `x`'s history is `[]`, so there is no
`tokTie` to re-tie; `AxLockOwn.lockReadOwnGenesis` pins the read to `x`'s image off the raw
`histAuth` (an external rf-source would carry an `ΦOwn` snapshot contradicting the empty auth;
it lands in the validated set by `lockPolSIntro`).  `PreaderPureHoldsGen` (the first conjunct is
vacuous: a genesis acquire has no rf-source), `r1FlowEqWpGen`, `wpdrW1Gen`, position 0
assembled, and the capstone `wpdReaderHart`.

**Fetches.** None (hand-built monad terms; the step clause's image pin is never needed).

## Deviations from Rocq

As `Weak/AxLock3Reader.lean` deviations 1–6 (names, the named instance/policy, Stage C — no
`T`/`HTx`, section hypotheses explicit in Rocq order with `Himg Hrd0` last, statement shapes,
the capstone at an arbitrary register file `rs`).  PROOF ROUTE (not statements): `r3FlowEqGen`
is derived from `AxLock3Wp.lockRelFlowEq3A` at `Hh := []` through `xTok`'s raw arm, instead of
Rocq's self-contained copy of its script; `r1FlowEqGen` derives the pure read fact by
`persistent_entails_left` (Rocq: a persistent `iAssert`).

**Rocq → Lean name map.**  `r0_flow_eq_gen` `r0FlowEqGen`, `r3_flow_eq_gen` `r3FlowEqGen`,
`wpdr_w3_gen` `wpdrW3Gen`, `wpdr_w2_gen` `wpdrW2Gen`, `wpdr_w2b_gen` `wpdrW2bGen`,
`r1_flow_eq_gen` `r1FlowEqGen`, `Preader_pure_holds_gen` `PreaderPureHoldsGen`,
`r1_flow_eq_wp_gen` `r1FlowEqWpGen`, `wpdr_w1_gen` `wpdrW1Gen`, `wpdr_w0_write_gen`
`wpdrW0WriteGen`, `wpdr_w0_read_gen` `wpdrW0ReadGen`, `wpd_reader_hart` `wpdReaderHart`.  No
name of this part is in the duplicated-name table; no Lean-only helpers.

**Dropped:** nothing (12 Rocq lemmas, 12 Lean).  **Not ported:** the `Print Assumptions` line.
-/
import Weak.AxLock3Reader

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D
open Wlabel

section RGen

variable {GF : BundledGFunctors.{0,0,0}} [AxlogG GF Hent] [AxLockG GF] (L x : Int)
variable {hlc : HasLC} [InvGS_gen hlc GF] [AxannotGS GF] (GD : Gdexec) (nm : lock3N)
variable (Lpa xpa : PAddr) (cpu : CPU) (i : Agent) (t : Nat) (old : BitVec 8) (tx : Nat)
  (vB : BitVec 8)

/-! ## 15.1 Position 0: the genesis flow equation -/

theorem r0FlowEqGen (HLeq : L = l3pLbase Lpa)
    (Hrow : AxOpsem.grow GD i = l3pRRow Lpa xpa t old tx vB) (Hcons : rvwmoCatConsistent GD)
    (Himg : GD.gdG.gxImg L = some b0) (Hrd0 : greadsByte GD.gdG (i, 0) L 0 b0) :
    ⊢ @flowEqDyn hlc GF _ (axGA2Lock3 L x GD nm) GD (i, 0) (lockPolS GD (i, 0)) (∅ : Mea GF)
        iprop(histAuth nm.1 x 1 [] ∗ ⌜graphData GD (i, 0) = some [b1]⌝) := by
  iapply (@flowEqDynMono hlc GF _ (axGA2Lock3 L x GD nm) lockAxpol GD (i, 0) (lockPolS GD (i, 0))
    _ iprop(histAuth nm.1 x 1 [])
    iprop(histAuth nm.1 x 1 [] ∗ ⌜graphData GD (i, 0) = some [b1]⌝))
  · inext
    iintro H
    isplitl [H]
    · iexact H
    · ipureintro
      exact r0Gd L GD Lpa xpa i t old tx vB HLeq Hrow
  · iapply (lockAcq0FlowEq3A (hlc := hlc) L x GD nm GD (i, 0) ∅ Hcons Himg Hrd0
      (r0Wb L GD Lpa xpa i t old tx vB HLeq Hrow) (r0Single L GD Lpa xpa i t old tx vB HLeq Hrow))

/-! ## 15.2 Position 3: the release at the empty history -/

theorem r3FlowEqGen (hxy : x ≠ L) (HLeq : L = l3pLbase Lpa)
    (Hrow : AxOpsem.grow GD i = l3pRRow Lpa xpa t old tx vB) (Hcons : rvwmoCatConsistent GD) :
    ⊢ @flowEqDyn hlc GF _ (axGA2Lock3 L x GD nm) GD (i, 3) (lockPolS GD (i, 3))
        {[(i, 1) := histAuth nm.1 x 1 []]}
        iprop(True ∗ ⌜graphData GD (i, 3) = some [b0]⌝) := by
  have Hr := lockRelFlowEq3A (hlc := hlc) L x GD nm GD (i, 3) (i, 1) []
    {[(i, 1) := histAuth (GF := GF) nm.1 x 1 []]} Hcons
    (r3Wb L GD Lpa xpa i t old tx vB HLeq Hrow)
    (r3Single L GD Lpa xpa i t old tx vB HLeq Hrow) (r3Gob GD Lpa xpa i t old tx vB Hrow)
  iapply (@flowEqDynMono hlc GF _ (axGA2Lock3 L x GD nm) lockAxpol GD (i, 3) (lockPolS GD (i, 3))
    _ iprop(True) iprop(True ∗ ⌜graphData GD (i, 3) = some [b0]⌝))
  · inext
    iintro -
    isplitr
    · itrivial
    · ipureintro
      exact r3Gd L GD Lpa xpa i t old tx vB HLeq Hrow
  · iapply Hr
    iintro Hin
    ihave Hin := (BigSepM.bigSepM_singleton (M := GMapF Geid)).1 $$ Hin
    isplitl [Hin]
    · unfold xTok
      iright
      isplitr
      · ipureintro
        rfl
      · iexact Hin
    · ipureintro
      exact ⟨histXWfNil x GD, r3PoLatest L x GD Lpa xpa i t old tx vB hxy HLeq Hrow []⟩

/-! ## 15.3 Positions 3/2/2b assembled at `Hl := []` -/

theorem wpdrW3Gen (hxy : x ≠ L) (HLram : devAddr Lpa = false) (HLeq : L = l3pLbase Lpa)
    (Hrow : AxOpsem.grow GD i = l3pRRow Lpa xpa t old tx vB) (Hcons : rvwmoCatConsistent GD) :
    iprop(AxAnnot.annotOwn (i, 1) (histAuth (GF := GF) nm.1 x 1 []) ∗
        PpureTok (GF := GF) L x GD i vB) ⊢
      ∀ rs : RegFile,
        AxLock3Reader.twpdr GF hlc L x GD nm i vB ⟨.PHart cpu (rM4 Lpa) rs none ibNone, 3⟩ := by
  apply wpdrPosShell L x GD nm cpu i vB _ 3 (rM4 Lpa) (by rw [Hrow]; simp [l3pRRow])
  · intro lb Hlk
    rw [Hrow] at Hlk
    simp only [l3pRRow, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq]
      at Hlk
    subst Hlk
    rfl
  · intro rs l s' Hstep
    obtain ⟨rfl, rfl⟩ := astepProgPlainWriteInv GD cpu i Lpa HLram b0 (fun _ => .pure ()) rs 3
      ⟨.PHart cpu (rM4 Lpa) rs none ibNone, 3⟩ rfl rfl l s' Hstep
    simp only [wlWdata, l3pWbytes1]
    unfold wpEvStep naAtProgress
    iintro ⟨Hpt1, Hpp⟩ %na ⟨%Hprog, Hannot⟩
    have Hin1 : (i, 1) ∈ (FiniteMap.dom_set na : GSet Geid) := by
      have h : (i, 1) ∈ eidsBefore GD i 3 :=
        (elemOfEidsBefore GD i 3 _).2 ⟨rfl, by simp, by
          simp only [gmemB, l3pRLbl1 Lpa xpa GD i t old tx vB Hrow]; rfl⟩
      rw [← Hprog] at h
      exact (elemOfFilter.1 h).2
    obtain ⟨P', HP'⟩ := Option.isSome_iff_exists.1 (elemOfDom.1 Hin1)
    have Hdet : ⊢ AxAnnot.annotInterp na -∗
        AxAnnot.annotOwn (i, 1) (histAuth (GF := GF) nm.1 x 1 []) ==∗
        ∃ R, AxAnnot.annotInterp (insert na (i, 1) R) ∗
          iprop(▷ □ (P' -∗ histAuth (GF := GF) nm.1 x 1 [] ∗ R)) := by
      have h := annotDetach na (i, 1) (histAuth (GF := GF) nm.1 x 1 [])
      rw [HP'] at h
      exact h
    imod Hdet $$ Hannot Hpt1 with ⟨%R, Hannot', Hwand⟩
    ihave Hfeq := r3FlowEqGen (hlc := hlc) L x GD nm Lpa xpa i t old tx vB hxy HLeq Hrow Hcons
    have Hnin : (i, 3) ∉ (FiniteMap.dom_set (insert na (i, 1) R) : GSet Geid) := by
      rw [domInsert, elemOfUnion, elemOfSingleton]
      rintro (Heq | Hik)
      · simp at Heq
      · have Hf : (i, 3) ∈ FiniteSet.filter (fun e : Geid => decide (e.1 = i))
            (FiniteMap.dom_set na : GSet Geid) := elemOfFilter.2 ⟨by simp, Hik⟩
        rw [Hprog, elemOfEidsBefore] at Hf
        exact Nat.lt_irrefl _ Hf.2.1
    imod (annotAlloc (insert na (i, 1) R) (i, 3) iprop(True) Hnin) $$ Hannot' with ⟨Hannot'', -⟩
    imodintro
    inext
    imodintro
    iexists (), iprop(True), {[(i, 1) := histAuth (GF := GF) nm.1 x 1 []]}, {[(i, 1) := R]}, ()
    isplitr
    · ipureintro
      trivial
    isplitl [Hwand]
    · unfold naSplittingWf
      isplitr
      · ipureintro
        rw [domSingleton]
        exact singletonSubseteqL.2 (rXreadInLobpRel GD Lpa xpa i t old tx vB Hrow Hcons)
      · iapply (BigSepM2.bigSepM2_singleton _ (i, 1) (histAuth (GF := GF) nm.1 x 1 []) R).2
        simp only [HP', AxWp.fromOption]
        inext
        iexact Hwand
    isplitl [Hfeq]
    · iexact Hfeq
    isplitl [Hannot'']
    · rw [← AxLock3Writer.annotEq]
      iexact Hannot''
    isplitr
    · iapply AxLock3Writer.localTriv
    · ihave H := (wpdrRowEnd (hlc := hlc) L x GD nm i vB (3 + 1) (by rw [Hrow]; simp [l3pRRow])
        (.PHart cpu (.pure ()) rs none ibNone)) $$ Hpp
      iexact H

theorem wpdrW2Gen (hxy : x ≠ L) (HLram : devAddr Lpa = false) (HLeq : L = l3pLbase Lpa)
    (Hrow : AxOpsem.grow GD i = l3pRRow Lpa xpa t old tx vB) (Hcons : rvwmoCatConsistent GD) :
    iprop(AxAnnot.annotOwn (i, 1) (histAuth (GF := GF) nm.1 x 1 []) ∗
        PpureTok (GF := GF) L x GD i vB) ⊢
      ∀ rs : RegFile,
        AxLock3Reader.twpdr GF hlc L x GD nm i vB ⟨.PHart cpu (rM3 Lpa) rs none ibNone, 2⟩ := by
  apply wpdrPosShell L x GD nm cpu i vB _ 2 (rM3 Lpa) (by rw [Hrow]; simp [l3pRRow])
  · intro lb Hlk
    rw [Hrow] at Hlk
    simp only [l3pRRow, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq]
      at Hlk
    subst Hlk
    rfl
  · intro rs l s' Hstep
    obtain ⟨rfl, rfl⟩ := astepProgFenceInv GD cpu i (fun _ => rM4 Lpa) rs 2
      ⟨.PHart cpu (rM3 Lpa) rs none ibNone, 2⟩ rfl rfl l s' Hstep
    simp only [wlWdata]
    iintro HP
    iapply wpdSkipStepOfLater (GF := GF) L x GD nm i
    inext
    ihave H := (wpdrW3Gen (hlc := hlc) L x GD nm Lpa xpa cpu i t old tx vB hxy HLram HLeq Hrow
      Hcons) $$ HP
    iapply H

theorem wpdrW2bGen (hxy : x ≠ L) (HLram : devAddr Lpa = false) (HLeq : L = l3pLbase Lpa)
    (Hrow : AxOpsem.grow GD i = l3pRRow Lpa xpa t old tx vB) (Hcons : rvwmoCatConsistent GD)
    (vw : BitVec 8) :
    iprop(AxAnnot.annotOwn (i, 1) (histAuth (GF := GF) nm.1 x 1 []) ∗
        PpureTok (GF := GF) L x GD i vB) ⊢
      ∀ rs : RegFile,
        AxLock3Reader.twpdr GF hlc L x GD nm i vB
          ⟨.PHart cpu (rM2b Lpa vw) rs none ibNone, 2⟩ := by
  apply wpdrPosShell L x GD nm cpu i vB _ 2 (rM2b Lpa vw) (by rw [Hrow]; simp [l3pRRow])
  · intro lb Hlk
    rw [Hrow] at Hlk
    simp only [l3pRRow, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq]
      at Hlk
    subst Hlk
    rfl
  · intro rs l s' Hstep
    obtain ⟨rfl, rfl⟩ := rRegwInv GD Lpa cpu i vw rs
      ⟨.PHart cpu (rM2b Lpa vw) rs none ibNone, 2⟩ rfl l s' Hstep
    have hwd : wlWdata (erwLabel (erwOf .ORnone [] .x10)) = none := by
      cases erwOf .ORnone [] .x10 <;> rfl
    rw [hwd]
    iintro HP
    iapply wpdSkipStepOfLater (GF := GF) L x GD nm i
    inext
    ihave H := (wpdrW2Gen (hlc := hlc) L x GD nm Lpa xpa cpu i t old tx vB hxy HLram HLeq Hrow
      Hcons) $$ HP
    iapply H

/-! ## 15.4 Position 1: the owned read at genesis -/

theorem r1FlowEqGen (hxy : x ≠ L) (HLeq : L = l3pLbase Lpa) (Hxeq : x = l3pXbase xpa)
    (Hrow : AxOpsem.grow GD i = l3pRRow Lpa xpa t old tx vB) (Hcons : rvwmoCatConsistent GD) :
    ⊢ @flowEqDyn hlc GF _ (axGA2Lock3 L x GD nm) GD (i, 1) (lockPolS GD (i, 1))
        {[(i, 0) := histAuth nm.1 x 1 []]}
        iprop(histAuth nm.1 x 1 [] ∗ ⌜tx = 0 ∧ GD.gdG.gxImg x = some vB⌝) := by
  have Hnpo1 : ∀ w v', gwritesByte GD.gdG w x v' → w.1 = (i, 1).1 → False := by
    intro w v' Hwb Heq
    obtain ⟨jj, kk⟩ := w
    simp only at Heq
    subst Heq
    exact r1NoXwriteHartI L x GD Lpa xpa jj t old tx vB hxy HLeq Hrow kk v' Hwb
  unfold flowEqDyn
  iintro %σ %sOb %Hsub %Hnin Hob Hflow
  ihave Hauth := (BigSepM.bigSepM_singleton (M := GMapF Geid)).1 $$ Hflow
  obtain ⟨g, D, hm⟩ := σ
  icases ((lock3ObStInterpAr L x GD nm g D hm sOb).trans
    (protInvLock3Unfold L x nm.1 nm.2 GD sOb D hm g)).1 $$ Hob with ⟨Hlock'', Hgen⟩
  icases (AxProtLock2.protInvLockUnfold'' L x nm.1 nm.2 GD sOb D hm).1 $$ Hlock''
    with ⟨Hlock', HHL, %Hclaims, %Hhmc⟩
  icases (protInvLockUnfold' L x nm.1 nm.2 GD sOb D hm).1 $$ Hlock' with ⟨Hc, Hpo, Hlocks⟩
  have hres : histAuth (GF := GF) nm.1 x 1 [] ∗ protInv nm.1 GD sOb ⊢
      ⌜tx = 0 ∧ GD.gdG.gxImg x = some vB⌝ := by
    iintro ⟨Hauth, #Hpo⟩
    iapply lockReadOwnGenesis GD nm.1 x (i, 1) tx vB Hcons Hnpo1
      (r1RdConcrete x GD Lpa xpa i t old tx vB Hxeq Hrow)
    isplitl [Hauth]
    · iexact Hauth
    iintro %w0 %vw0 %Hwb0 %Hgrfe0
    have Hin0 : w0 ∈ sOb := Hsub _ (lockPolSIntro GD w0 (i, 1)
      (gwritesByteGxGmo GD.gdG Hcons.1 w0 x vw0 Hwb0) Hgrfe0)
    have h1 : protInv (GF := GF) nm.1 GD sOb ⊢ ΦpOwn nm.1 GD w0 :=
      BigSepS.bigSepS_elem_of (Φ := ΦpOwn nm.1 GD) Hin0
    rw [AxProt.ΦpOwnW nm.1 GD w0 (AxProt.gwritesByteGisW _ _ _ _ Hwb0)] at h1
    unfold ΦOwn at h1
    ihave Hw := h1 $$ Hpo
    ihave Hw2 := Hw $$ %x %vw0 %Hwb0
    icases Hw2 with ⟨%H', Hsnap, %Hlast⟩
    iexists H'
    isplitr
    · ipureintro
      exact histSnapLastIn H' w0 vw0 Hlast
    · iexact Hsnap
  icases persistent_entails_left hres $$ [$Hauth $Hpo] with ⟨⟨Hauth, Hpo⟩, %Hval⟩
  ihave Hpo' := protInvReadStep nm.1 GD sOb (i, 1) Hnin
    (r1GisW GD Lpa xpa i t old tx vB Hrow) $$ Hpo
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  inext
  imod Hclose
  imodintro
  iexists ((g, D, hm) : Bool × GSet Geid × GMapF Geid (List Hent))
  isplitl [Hc Hpo' Hlocks HHL Hgen]
  · iapply ((lock3ObStInterpAr L x GD nm g D hm (({(i, 1)} : GSet Geid) ∪ sOb)).trans
      (protInvLock3Unfold L x nm.1 nm.2 GD (({(i, 1)} : GSet Geid) ∪ sOb) D hm g)).2
    isplitl [Hc Hpo' Hlocks HHL]
    · iapply (AxProtLock2.protInvLockUnfold'' L x nm.1 nm.2 GD (({(i, 1)} : GSet Geid) ∪ sOb)
        D hm).2
      isplitl [Hc Hpo' Hlocks]
      · iapply (protInvLockUnfold' L x nm.1 nm.2 GD (({(i, 1)} : GSet Geid) ∪ sOb) D hm).2
        isplitl [Hc]
        · iexact Hc
        isplitl [Hpo']
        · iexact Hpo'
        iapply (AxProtLock.bigSepSUnionSingleton
          (Φ := fun e => ΦLock' L x nm.1 nm.2 GD e ((get? hm e).getD [])) Hnin).2
        isplitl []
        · iapply AxProtLock.ΦLock'Vacuous L x nm.1 nm.2 GD (i, 1) _
            (r1NoWrite GD Lpa xpa i t old tx vB Hrow L b0)
        · iexact Hlocks
      · isplitl [HHL]
        · iexact HHL
        · isplitl []
          · ipureintro
            intro r hr
            obtain ⟨e, he, hre⟩ := Hclaims r hr
            exact ⟨e, elemOfUnionR he, hre⟩
          · ipureintro
            intro w hw hwb0'
            rcases elemOfUnion.1 hw with hw | hw
            · rw [elemOfSingleton.1 hw] at hwb0'
              exact (r1NoWrite GD Lpa xpa i t old tx vB Hrow L b0 hwb0').elim
            · exact Hhmc w hw hwb0'
    · iapply lockGenesisMono L x nm.1 GD g sOb (({(i, 1)} : GSet Geid) ∪ sOb)
        (fun _ h => elemOfUnionR h)
      iexact Hgen
  · isplitl [Hauth]
    · iexact Hauth
    · ipureintro
      exact Hval

/-! ## 15.5/15.6 `PreaderPure` at genesis, and the `graphValue` obligation -/

theorem PreaderPureHoldsGen (HLeq : L = l3pLbase Lpa)
    (Hrow : AxOpsem.grow GD i = l3pRRow Lpa xpa t old tx vB)
    (Hrd0 : greadsByte GD.gdG (i, 0) L 0 b0) (_Htx0 : tx = 0)
    (Himgx : GD.gdG.gxImg x = some vB) : PreaderPure L x GD i vB := by
  refine ⟨?_, ?_⟩
  · intro j v Hgrfe _
    exfalso
    obtain ⟨⟨a, ta, va, Hrd, Hat⟩, -⟩ := Hgrfe
    have Ha := r0OnlyReadsL L GD Lpa xpa i t old tx vB HLeq Hrow a ta va Hrd
    rw [Ha] at Hrd
    obtain ⟨Hteq, -⟩ := greadsByteDet GD.gdG (i, 0) L ta va 0 b0 Hrd Hrd0
    subst Hteq
    simp [gwriteAt] at Hat
  · intro _ bx Himgeq
    rw [Himgx, Option.some.injEq] at Himgeq
    exact Himgeq

theorem r1FlowEqWpGen (hxy : x ≠ L) (HLeq : L = l3pLbase Lpa) (Hxeq : x = l3pXbase xpa)
    (Hrow : AxOpsem.grow GD i = l3pRRow Lpa xpa t old tx vB) (Hcons : rvwmoCatConsistent GD)
    (Hrd0 : greadsByte GD.gdG (i, 0) L 0 b0) (v : List (BitVec 8))
    (Hgv : graphValue GD (i, 1) = some v) :
    ⊢ @flowEqDyn hlc GF _ (axGA2Lock3 L x GD nm) GD (i, 1) (lockPolS GD (i, 1))
        {[(i, 0) := histAuth nm.1 x 1 []]}
        iprop((histAuth nm.1 x 1 [] ∗ ⌜PreaderPure L x GD i vB⌝) ∗
          ⌜graphValue GD (i, 1) = some v⌝) := by
  iapply (@flowEqDynMono hlc GF _ (axGA2Lock3 L x GD nm) lockAxpol GD (i, 1) (lockPolS GD (i, 1))
    _ iprop(histAuth nm.1 x 1 [] ∗ ⌜tx = 0 ∧ GD.gdG.gxImg x = some vB⌝)
    iprop((histAuth nm.1 x 1 [] ∗ ⌜PreaderPure L x GD i vB⌝) ∗
      ⌜graphValue GD (i, 1) = some v⌝))
  · inext
    iintro ⟨HAuth, %Hval⟩
    isplitl [HAuth]
    · isplitl [HAuth]
      · iexact HAuth
      · ipureintro
        exact PreaderPureHoldsGen L x GD Lpa xpa i t old tx vB HLeq Hrow Hrd0 Hval.1 Hval.2
    · ipureintro
      exact Hgv
  · iapply (r1FlowEqGen (hlc := hlc) L x GD nm Lpa xpa i t old tx vB hxy HLeq Hxeq Hrow Hcons)

/-! ## 15.7 Position 1 assembled, genesis -/

theorem wpdrW1Gen (hxy : x ≠ L) (HLram : devAddr Lpa = false) (Hxram : devAddr xpa = false)
    (HLeq : L = l3pLbase Lpa) (Hxeq : x = l3pXbase xpa)
    (Hrow : AxOpsem.grow GD i = l3pRRow Lpa xpa t old tx vB) (Hcons : rvwmoCatConsistent GD)
    (Hrd0 : greadsByte GD.gdG (i, 0) L 0 b0) :
    AxAnnot.annotOwn (i, 0) (histAuth (GF := GF) nm.1 x 1 []) ⊢
      ∀ rs : RegFile,
        AxLock3Reader.twpdr GF hlc L x GD nm i vB ⟨.PHart cpu (rM2 Lpa xpa) rs none ibNone, 1⟩ := by
  have H : ⊢ ∀ rs : RegFile, AxAnnot.annotOwn (i, 0) (histAuth (GF := GF) nm.1 x 1 []) -∗
      AxLock3Reader.twpdr GF hlc L x GD nm i vB ⟨.PHart cpu (rM2 Lpa xpa) rs none ibNone, 1⟩ := by
    iloeb as IH
    iintro %rs HP
    unfold AxLock3Reader.twpdr tierAWpd
    iapply (@AxWpD.wpdMUnfoldStep hlc GF _ (axGA2Lock3 L x GD nm) lockAxpol rvwmoCatConsistent
      .MaybeStuck i _ _).2
    isplit
    · iapply (@progressOblMaybestuck GF (axGA2Lock3 L x GD nm) lockAxpol i _).2
      itrivial
    unfold wpdMPreStepDef
    iintro %GD' %ls ⟨%Hc, #Hg, -⟩
    ihave %Hg := AxLock3Writer.gconstPure L x GD nm GD' $$ Hg
    subst GD'
    isplit
    · iintro %id %K %Hst
      obtain ⟨lb, Hlb, Hid, -, HK⟩ := Hst
      simp only at Hlb
      rw [Hrow] at Hlb
      simp only [l3pRRow, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq]
        at Hlb
      subst Hlb Hid
      simp only [aident, aidentAdvRd, ↓reduceIte]
      iintro %v %Hgv %Hlen
      obtain ⟨l0, d0, d0', -, -, Hpst, Hatk⟩ := HK v Hlen
      obtain ⟨vw, Hp, -⟩ := r1ReadDet Lpa xpa cpu Hxram rs d0 l0 _ d0' Hpst
      have Hk2 : (K v).atK = 2 := by rw [Hatk]; rfl
      have HKv : K v = ⟨.PHart cpu (rM2b Lpa vw) rs none ibNone, 2⟩ := by
        rcases hk : K v with ⟨p'', k''⟩
        rw [hk] at Hp Hk2
        simp only at Hp Hk2
        rw [Hp, Hk2]
      rw [HKv]
      unfold wpEvStep naAtProgress
      iintro %na ⟨%Hprog, Hannot⟩
      have Hin0 : (i, 0) ∈ (FiniteMap.dom_set na : GSet Geid) := by
        have h : (i, 0) ∈ eidsBefore GD i 1 :=
          (elemOfEidsBefore GD i 1 _).2 ⟨rfl, by simp, by
            simp only [gmemB, l3pRLbl0 Lpa xpa GD i t old tx vB Hrow]; rfl⟩
        rw [← Hprog] at h
        exact (elemOfFilter.1 h).2
      obtain ⟨P0', HP0'⟩ := Option.isSome_iff_exists.1 (elemOfDom.1 Hin0)
      have Hdet : ⊢ AxAnnot.annotInterp na -∗
          AxAnnot.annotOwn (i, 0) (histAuth (GF := GF) nm.1 x 1 []) ==∗
          ∃ R, AxAnnot.annotInterp (insert na (i, 0) R) ∗
            iprop(▷ □ (P0' -∗ histAuth (GF := GF) nm.1 x 1 [] ∗ R)) := by
        have h := annotDetach na (i, 0) (histAuth (GF := GF) nm.1 x 1 [])
        rw [HP0'] at h
        exact h
      imod Hdet $$ Hannot HP with ⟨%R, Hannot', Hwand⟩
      ihave Hfeq := r1FlowEqWpGen (hlc := hlc) L x GD nm Lpa xpa i t old tx vB hxy HLeq Hxeq Hrow
        Hcons Hrd0 v Hgv
      have Hnin : (i, 1) ∉ (FiniteMap.dom_set (insert na (i, 0) R) : GSet Geid) := by
        rw [domInsert, elemOfUnion, elemOfSingleton]
        rintro (Heq | Hik)
        · simp at Heq
        · have Hf : (i, 1) ∈ FiniteSet.filter (fun e : Geid => decide (e.1 = i))
              (FiniteMap.dom_set na : GSet Geid) := elemOfFilter.2 ⟨by simp, Hik⟩
          rw [Hprog, elemOfEidsBefore] at Hf
          exact Nat.lt_irrefl _ Hf.2.1
      imod (annotAlloc (insert na (i, 0) R) (i, 1)
        iprop(histAuth (GF := GF) nm.1 x 1 [] ∗ ⌜PreaderPure L x GD i vB⌝) Hnin)
        $$ Hannot' with ⟨Hannot'', Hpt1⟩
      imod (annotSplit (i, 1) (histAuth (GF := GF) nm.1 x 1 [])
        iprop(⌜PreaderPure L x GD i vB⌝)) $$ Hpt1 %_ Hannot'' with ⟨⟨Hpt1a, Hpt1b⟩, Hannot2⟩
      imodintro
      inext
      imodintro
      iexists (), iprop(histAuth (GF := GF) nm.1 x 1 [] ∗ ⌜PreaderPure L x GD i vB⌝),
        {[(i, 0) := histAuth (GF := GF) nm.1 x 1 []]}, {[(i, 0) := R]}, ()
      isplitr
      · ipureintro
        trivial
      isplitl [Hwand]
      · unfold naSplittingWf
        isplitr
        · ipureintro
          rw [domSingleton]
          exact singletonSubseteqL.2 (l3pRAcqInLobpXread Lpa xpa GD i t old tx vB Hrow Hcons.1)
        · iapply (BigSepM2.bigSepM2_singleton _ (i, 0) (histAuth (GF := GF) nm.1 x 1 []) R).2
          simp only [HP0', AxWp.fromOption]
          inext
          iexact Hwand
      isplitl [Hfeq]
      · iexact Hfeq
      isplitl [Hannot2]
      · rw [← AxLock3Writer.annotEq]
        iexact Hannot2
      isplitr
      · iapply AxLock3Writer.localTriv
      · have Hw2 := wpdrW2bGen (GF := GF) (hlc := hlc) L x GD nm Lpa xpa cpu i t old tx vB hxy
          HLram HLeq Hrow Hcons vw
        unfold AxLock3Reader.twpdr tierAWpd at Hw2
        ihave H := Hw2 $$ [$Hpt1a $Hpt1b]
        iapply H $$ %rs
    isplit
    · iintro %l %s' %Hst %-
      exact (r1AstepProgVacuous GD Lpa xpa cpu i Hxram rs _ rfl rfl l s' Hst).elim
    isplit
    · iintro %s' %Hw
      obtain ⟨rs', rfl⟩ := l3pAwireRsOnly cpu (rM2 Lpa xpa) rs none ibNone 1 s' Hw
      iapply wpdSkipStepOfLater (GF := GF) L x GD nm i
      inext
      iapply IH $$ %rs' HP
    · iintro %Heq
      have hf : False := by
        rw [Hrow] at Heq
        simp [l3pRRow] at Heq
      exact hf.elim
  iintro HP %rs
  iapply H $$ %rs HP

/-! ## 15.8 Position 0 assembled, genesis -/

theorem wpdrW0WriteGen (hxy : x ≠ L) (HLram : devAddr Lpa = false) (Hxram : devAddr xpa = false)
    (HLeq : L = l3pLbase Lpa) (Hxeq : x = l3pXbase xpa)
    (Hrow : AxOpsem.grow GD i = l3pRRow Lpa xpa t old tx vB) (Hcons : rvwmoCatConsistent GD)
    (Himg : GD.gdG.gxImg L = some b0) (Hrd0 : greadsByte GD.gdG (i, 0) L 0 b0)
    (s : Athread) (rs : RegFile) (Heqp : s.atP = .PHart cpu (rM1 Lpa xpa) rs none ibNone)
    (Heqk : s.atK = 0) :
    ⊢ AxLock3Reader.twpdr GF hlc L x GD nm i vB s := by
  obtain ⟨p, k⟩ := s
  simp only at Heqp Heqk
  subst Heqp Heqk
  have H : ⊢ ∀ rs : RegFile,
      AxLock3Reader.twpdr GF hlc L x GD nm i vB ⟨.PHart cpu (rM1 Lpa xpa) rs none ibNone, 0⟩ := by
    iloeb as IH
    iintro %rs
    unfold AxLock3Reader.twpdr tierAWpd
    iapply (@AxWpD.wpdMUnfoldStep hlc GF _ (axGA2Lock3 L x GD nm) lockAxpol rvwmoCatConsistent
      .MaybeStuck i _ _).2
    isplit
    · iapply (@progressOblMaybestuck GF (axGA2Lock3 L x GD nm) lockAxpol i _).2
      itrivial
    unfold wpdMPreStepDef
    iintro %GD' %ls ⟨%Hc, #Hg, -⟩
    ihave %Hg := AxLock3Writer.gconstPure L x GD nm GD' $$ Hg
    subst GD'
    isplit
    · iintro %id %K %Hst
      have hfalse : False := by
        obtain ⟨lb, Hlb, Hid, Hsome, HK⟩ := Hst
        simp only at Hlb
        rw [Hrow] at Hlb
        simp only [l3pRRow, List.getElem?_cons_zero, Option.some.injEq] at Hlb
        subst Hlb Hid
        obtain ⟨l0, d0, d0', Hwlrd, -, Hpst, -⟩ := HK [old] rfl
        rcases l3pWriteExclDet cpu Lpa HLram b1 (fun _ => rM2 Lpa xpa) rs ibNone d0 l0 _ d0'
          Hpst with ⟨rfl, -, -⟩ | ⟨rfl, -, -⟩ <;> simp [wlRd, aident, aidentRd] at Hwlrd
      exact hfalse.elim
    isplit
    · iintro %l %s' %Hst %-
      rcases astepProgWrite0RelInv GD Lpa xpa cpu i HLram rs _ rfl rfl l s' Hst with
        ⟨Hwd, rfl⟩ | ⟨rfl, rfl⟩
      · rw [Hwd, l3pWbytes1]
        dsimp only
        unfold wpEvStep naAtProgress
        iintro %na ⟨%Hprog, Hannot⟩
        have Hnin0 : (i, 0) ∉ (FiniteMap.dom_set na : GSet Geid) := by
          intro Hin
          have Hf : (i, 0) ∈ FiniteSet.filter (fun e : Geid => decide (e.1 = i))
              (FiniteMap.dom_set na : GSet Geid) := elemOfFilter.2 ⟨by simp, Hin⟩
          rw [Hprog, elemOfEidsBefore] at Hf
          exact Nat.not_lt_zero _ Hf.2.1
        imod (annotAlloc na (i, 0) (histAuth (GF := GF) nm.1 x 1 []) Hnin0) $$ Hannot
          with ⟨Hannot', Hpt0⟩
        ihave Hfeq0 := r0FlowEqGen (hlc := hlc) L x GD nm Lpa xpa i t old tx vB HLeq Hrow Hcons
          Himg Hrd0
        imodintro
        inext
        imodintro
        iexists (), histAuth (GF := GF) nm.1 x 1 [], (∅ : Mea GF), (∅ : Mea GF), ()
        isplitr
        · ipureintro
          trivial
        isplitr
        · unfold naSplittingWf
          isplitr
          · ipureintro
            rw [domEmpty]
            exact LawfulSet.empty_subset
          · iapply (BigSepM2.bigSepM2_empty _).2
            itrivial
        isplitl [Hfeq0]
        · iexact Hfeq0
        isplitl [Hannot']
        · rw [AxLockWp.annotInsertEq]
          iexact Hannot'
        isplitr
        · iapply AxLock3Writer.localTriv
        · have Hw1 := wpdrW1Gen (GF := GF) (hlc := hlc) L x GD nm Lpa xpa cpu i t old tx vB hxy
            HLram Hxram HLeq Hxeq Hrow Hcons Hrd0
          unfold AxLock3Reader.twpdr tierAWpd at Hw1
          ihave H := Hw1 $$ Hpt0
          dsimp only
          iapply H
      · simp only [wlWdata]
        iapply wpdSkipStepOfLater (GF := GF) L x GD nm i
        inext
        iapply IH $$ %rs
    isplit
    · iintro %s' %Hw
      obtain ⟨rs', rfl⟩ := l3pAwireRsOnly cpu (rM1 Lpa xpa) rs none ibNone 0 s' Hw
      iapply wpdSkipStepOfLater (GF := GF) L x GD nm i
      inext
      iapply IH $$ %rs'
    · iintro %Heq
      have hf : False := by
        rw [Hrow] at Heq
        simp [l3pRRow] at Heq
      exact hf.elim
  iapply H $$ %rs

theorem wpdrW0ReadGen (hxy : x ≠ L) (HLram : devAddr Lpa = false) (Hxram : devAddr xpa = false)
    (HLeq : L = l3pLbase Lpa) (Hxeq : x = l3pXbase xpa)
    (Hrow : AxOpsem.grow GD i = l3pRRow Lpa xpa t old tx vB) (Hcons : rvwmoCatConsistent GD)
    (Himg : GD.gdG.gxImg L = some b0) (Hrd0 : greadsByte GD.gdG (i, 0) L 0 b0) :
    ⊢ ∀ rs : RegFile,
      AxLock3Reader.twpdr GF hlc L x GD nm i vB
        ⟨.PHart cpu (AxLock3Reader.rM0 Lpa xpa) rs none ibNone, 0⟩ := by
  iloeb as IH
  iintro %rs
  unfold AxLock3Reader.twpdr tierAWpd
  iapply (@AxWpD.wpdMUnfoldStep hlc GF _ (axGA2Lock3 L x GD nm) lockAxpol rvwmoCatConsistent
    .MaybeStuck i _ _).2
  isplit
  · iapply (@progressOblMaybestuck GF (axGA2Lock3 L x GD nm) lockAxpol i _).2
    itrivial
  unfold wpdMPreStepDef
  iintro %GD' %ls ⟨%Hc, #Hg, -⟩
  ihave %Hg := AxLock3Writer.gconstPure L x GD nm GD' $$ Hg
  subst GD'
  isplit
  · iintro %id %K %Hst
    obtain ⟨lb, Hlb, Hid, -, HK⟩ := Hst
    simp only at Hlb
    rw [Hrow] at Hlb
    simp only [l3pRRow, List.getElem?_cons_zero, Option.some.injEq] at Hlb
    subst Hlb Hid
    simp only [aident, aidentAdvRd, Nat.zero_ne_one, ↓reduceIte]
    iintro %gv %Hgv %Hlen
    obtain ⟨l0, d0, d0', -, -, Hpst, Hatk⟩ := HK gv Hlen
    have Hp := (r0ReadDet Lpa xpa cpu HLram rs d0 l0 _ d0' Hpst).1
    have Hk0 : (K gv).atK = 0 := by rw [Hatk]; rfl
    iapply wpdSkipStepOfLater (GF := GF) L x GD nm i
    inext
    have Hw0 := wpdrW0WriteGen (GF := GF) (hlc := hlc) L x GD nm Lpa xpa cpu i t old tx vB hxy
      HLram Hxram HLeq Hxeq Hrow Hcons Himg Hrd0 (K gv) rs Hp Hk0
    unfold AxLock3Reader.twpdr tierAWpd at Hw0
    iapply Hw0
  isplit
  · iintro %l %s' %Hst %-
    exact (astepProgRead0RelVacuous GD Lpa xpa cpu i HLram rs _ rfl rfl l s' Hst).elim
  isplit
  · iintro %s' %Hw
    obtain ⟨rs', rfl⟩ := l3pAwireRsOnly cpu (AxLock3Reader.rM0 Lpa xpa) rs none ibNone 0 s' Hw
    iapply wpdSkipStepOfLater (GF := GF) L x GD nm i
    inext
    iapply IH $$ %rs'
  · iintro %Heq
    have hf : False := by
      rw [Hrow] at Heq
      simp [l3pRRow] at Heq
    exact hf.elim

/-- 16. THE GENESIS CAPSTONE: from `lock3Init nm i` (`emp`). -/
theorem wpdReaderHart (hxy : x ≠ L) (HLram : devAddr Lpa = false)
    (Hxram : devAddr xpa = false) (HLeq : L = l3pLbase Lpa) (Hxeq : x = l3pXbase xpa)
    (Hrow : AxOpsem.grow GD i = l3pRRow Lpa xpa t old tx vB) (Hcons : rvwmoCatConsistent GD)
    (Himg : GD.gdG.gxImg L = some b0) (Hrd0 : greadsByte GD.gdG (i, 0) L 0 b0) (rs : RegFile) :
    ⊢ lock3Init (GF := GF) nm i -∗
      AxLock3Reader.twpdr GF hlc L x GD nm i vB ⟨l3pRP0 Lpa xpa cpu rs, 0⟩ := by
  have heq : l3pRP0 Lpa xpa cpu rs = .PHart cpu (AxLock3Reader.rM0 Lpa xpa) rs none ibNone := rfl
  rw [heq]
  iintro -
  ihave H := wpdrW0ReadGen (hlc := hlc) L x GD nm Lpa xpa cpu i t old tx vB hxy HLram Hxram HLeq
    Hxeq Hrow Hcons Himg Hrd0
  iapply H $$ %rs

end RGen

end Weak
