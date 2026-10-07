/-
Weak: **the EXACT sanity twin of the refuted racing hart-1 program** (AxSL tier).

Rocq: `iris/AxEpiTwinExact.v` @ xxvzwolszwmp.

## What this file proves

`AxEpiRace2Run.race2WpdUnprovable` refutes hart 1 = Sail from `AxEpiRace2Run.regs1`
(`probeRegs pc1` with `ra := 0x80000200`): its `c.sdsp ra,8(sp)` stores `raceData` to hart 0's
slot `ldAddr`.  The twin `race2oOwnWpd` differed in BOTH slot (`sp`) and value (`ra = raVal`,
storing `sdData`) because `AxEpiOwned.storeFlowOwned` is stated for `sdData`.  Here the twin
differs ONLY in `sp`: `h1xRegs := regs1` with `sp := race2B - 8`, so the SAME value `raceData`
is stored, to hart 1's OWN slot `race2B`; its WPd from `epiInit3 _ race2B nm 1` is PROVABLE,
closed on the concrete cat-consistent graph `race2x` (hart 0's row = `AxEpiSdLdSat.row`;
hart 1's row = the store of `raceData` at `race2B`).

§1 `sdWriteOkGen` / `storeFlowOwnedGen`: `AxEpiOwned`'s spill flow at the real protocol,
generalised over the stored bytes.
§2 the twin: ledger facts, WPd, concrete graph, `race2xOwnWpd`.

## Deviations from Rocq

1. O2 STAGE C (as `AxEpiRace2Run` deviations 2 and 5): the hart-1 fetch is no row item, so
   hart 1's row `row1x` is `[LStore false race2B raceData .WCplain]` (Rocq `[fetch h1_vs4;
   store]`), and the positions shift down one: `fetchImgOk GD 1 0 pc1 h1Vs4` (Rocq
   `fetch_gd_ok GD 1 0`), `storeRowOk GD 1 0` (Rocq `1 1`), `sdWriteOkGen GD 1 0 race2B
   raceData` (Rocq `1 1`), length 1 (Rocq 2), `SdRetX` at `k = 1` (Rocq 2).  `race2x`'s gmo is
   `[eSD; eW1; eLD]` (Rocq `[eF0; eSD; eF1; eG0; eW1; eLD]`).  The `Hnw1` premise (`gis_w` of
   the fetch event) of `wpd_hart1x_own_sd(_Hwp1)` is dropped (no fetch flow), and so is
   `race2x_nw1`.
2. TEXT (`AxEpiSound2` deviation 1): no text `T` (Rocq section `T`, `race2x_own_wpd`'s `T`).
3. INSTANCES: the section lemmas are generic in `hlc` and the policy (Rocq `HasNoLc`,
   `epi_pol`); the section-local instance `epi_ga2_h1x` is not declared — `epiGa2 GD0 γ` is
   passed explicitly (AxEpiSat convention).  `storeFlowOwnedGen` takes `Hann_eq` and `Hob_eq`
   as in `AxEpiOwned.storeFlowOwned`.  `Hwp1` statements are `∀ [InvGS_gen .hasNoLC epiGF]
   [AxannotGS epiGF] (nm : GName)`.
4. Ledger: `AxEpiProbe.drNopin` (Rocq `Dr_noseip`, two-pin form), ten `AxSdModelFacts` fields
   by `decide +kernel`; `dev0_state` ↦ `testDevs`; `x2 := BitVec.ofInt 64 (race2B - 8)`.
   `sdWriteOkGenSd` is `Iff.rfl`.

**Rocq → Lean name map.**  `sd_write_ok_gen` `sdWriteOkGen`, `sd_write_ok_gen_sd`
`sdWriteOkGenSd`, `store_flow_owned_gen` `storeFlowOwnedGen`, `h1x_regs` `h1xRegs`, `h1x_t`
`h1xT`, `h1x_ledger_csdsp` `h1xLedgerCsdsp`, `h1x_state` `h1xState`, `race_data_length`
`raceDataLength`, `wpd_hart1x_own_sd` `wpdHart1xOwnSd`, `wpd_hart1x_own_sd_Hwp1`
`wpdHart1xOwnSdHwp1`, `row1x` `row1x`, `race2x` `race2x`, `race2x_cat` `race2xCat`,
`race2x_fetch1` `race2xFetch1`, `race2x_store_row1` `race2xStoreRow1`, `race2x_sd_write_ok1`
`race2xSdWriteOk1`, `race2x_len1` `race2xLen1`, `race2x_own_wpd` `race2xOwnWpd`.  None is in
the duplicated-name table; no Lean-only declarations.

**Dropped:** `race2x_nw1` (deviation 1), the local instance `epi_ga2_h1x` (deviation 3), the
`Print Assumptions` line (the lint's axiom check covers it).  Rocq 19 declarations (incl. the
local instance); Lean 17.
-/
import Weak.AxEpiRace2Run

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D
open Lbl

/-! # 1. The spill flow, generalised over the stored bytes -/

/-- `AxEpiOwned.sdWriteOk` with `sdData` replaced by `data`. -/
def sdWriteOkGen (GD : Gdexec) (i : Agent) (k : Nat) (a : Int) (data : List (BitVec 8)) :
    Prop :=
  gisW GD.gdG (i, k) = true ∧
  (∀ a' v', gwritesByte GD.gdG (i, k) a' v' →
     ∃ j : Nat, data[j]? = some v' ∧ a' = a + (j : Int)) ∧
  graphData GD (i, k) = some data

theorem sdWriteOkGenSd (GD : Gdexec) (i : Agent) (k : Nat) (a : Int) :
    sdWriteOkGen GD i k a sdData ↔ sdWriteOk GD i k a := Iff.rfl

section ownedGen
variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF] [axG : AxirisG GF]
  [Axpol] [AxlogG GF Hent] [AxannotGS GF]

/-- `AxEpiOwned.storeFlowOwned` for arbitrary stored bytes `data`. -/
theorem storeFlowOwnedGen (γ : GName)
    (Hob_eq : ∀ (GD : Gdexec) (σ : AxirisG.obSt GF) (s : GSet Geid),
      AxirisG.obStInterp GD σ s ⊣⊢ protInv γ GD s)
    (Hann_eq : ∀ m : Mea GF, AxirisG.annotInterp m ⊣⊢ AxAnnot.annotInterp m)
    (i : Agent) (k : Nat) (a : Int) (data : List (BitVec 8)) (Hs0 : List (List Hent))
    (Hlen0 : Hs0.length = data.length)
    (Hw : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜sdWriteOkGen GD i k a data⌝)
    (Hloc : ∀ GD ls, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ∗ AxirisG.localInterp GD i k ls ⊢
        |==> ∃ ls', AxirisG.localInterp GD i (k + 1) ls') :
    iprop([∗list] j ↦ H ∈ Hs0, histAuth (GF := GF) γ (a + (j : Int)) 1 H) ⊢
      ∀ (GD : Gdexec) (ls : AxirisG.logTsT GF),
        ⌜rvwmoCatConsistent GD⌝ -∗ □ AxirisG.gconstInterp GD -∗ AxirisG.localInterp GD i k ls -∗
        storeFlowRes GD i k data
          (AxAnnot.annotOwn (i, k) (sdTok γ a (writenHist (i, k) data Hs0) (i, k))) := by
  have hw : iprop([∗list] j ↦ H ∈ Hs0, histAuth (GF := GF) γ (a + (j : Int)) 1 H) ⊢
      iprop(([∗map] Rin ∈ (∅ : Mea GF), Rin) -∗
        [∗list] j ↦ H ∈ Hs0, histAuth (GF := GF) γ (a + (j : Int)) 1 H) := by
    iintro Ht _
    iexact Ht
  iintro Hauths %GD %ls %Hc #Hg Hl0
  ihave %Hwok := (Hw GD Hc) $$ Hg
  obtain ⟨Hisw, Hcompl, Hgd⟩ := Hwok
  unfold storeFlowRes
  iintro %na ⟨Hpg, Hannot⟩
  ihave %Hnin := naAtProgressNotElemOf GD i k na $$ Hpg
  ihave Hl1 : iprop(|==> ∃ ls', AxirisG.localInterp GD i (k + 1) ls') $$ [Hl0]
  · iapply (Hloc GD ls Hc)
    isplitl []
    · iexact Hg
    · iexact Hl0
  imod Hl1 with ⟨%ls', Hl1⟩
  ihave Hannot := (Hann_eq na).1 $$ Hannot
  imod (annotAlloc na (i, k) (sdTok γ a (writenHist (i, k) data Hs0) (i, k)) Hnin) $$ Hannot
    with ⟨Hannot, Hfrag⟩
  have Hfeq := hw.trans (ownFlowEqWritenSnap γ Hob_eq GD Hc (i, k) a Hs0 data
    (Axpol.sPol GD (i, k)) ∅ data Hlen0 Hisw Hcompl Hgd)
  ihave Hfe := Hfeq $$ Hauths
  imodintro
  inext
  imodintro
  iexists (sdTok γ a (writenHist (i, k) data Hs0) (i, k)), (∅ : Mea GF), (∅ : Mea GF), ls'
  isplitr
  · iapply AxProtGate.naSplittingWfEmpty
  isplitl [Hfe]
  · iapply (flowEqDynMono GD (i, k) (Axpol.sPol GD (i, k)) (∅ : Mea GF) _ _) $$ [] Hfe
    inext
    iintro ⟨⟨Ht, -⟩, Hp⟩
    isplitl [Ht]
    · iapply (toknSdTok γ GD a _ (i, k))
      iexact Ht
    · iexact Hp
  isplitl [Hannot]
  · iapply (Hann_eq _).2
    rw [AxProtGate.annotInsertEq]
    iexact Hannot
  isplitl [Hl1]
  · iexact Hl1
  · iexact Hfrag

end ownedGen

/-! # 2. The exact twin -/

/-- `regs1` (the racing hart's registers, `ra = 0x80000200`) with ONLY `sp := race2B - 8`: the
same `c.sdsp ra,8(sp)` now stores `raceData` to hart 1's own slot `race2B`. -/
def h1xRegs : RegFile := AxEpiRace2Run.regs1.set .x2 (BitVec.ofInt 64 (race2B - 8))

def h1xT : ExecSt := ⟨h1xRegs, probeMem, testDevs⟩

theorem h1xLedgerCsdsp :
    AxSdModelFacts h1xT AxEpiProbe.drNopin DwAll DPost (AxEpiRace2.pc1 : Int)
      AxEpiRace2Run.h1Vs4 race2B raceData h1oPost where
  lsSeipDr := by decide +kernel
  lsMeipDr := by decide +kernel
  lsSeipD := by decide +kernel
  lsMeipD := by decide +kernel
  lsHead := by decide +kernel
  lsToSeip := by decide +kernel
  lsBranch00 := by decide +kernel
  lsBranch01 := by decide +kernel
  lsBranch10 := by decide +kernel
  lsBranch11 := by decide +kernel

noncomputable def h1xState (cpu : CPU) (ib : Ibch) : Athread :=
  ⟨.PHart cpu (riscvStep false) h1xRegs none ib, 0⟩

theorem raceDataLength : raceData.length = 8 := rfl

section h1x
variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF] [AxannotGS GF]
  [AxlogG GF Hent] [pol : Axpol]

theorem wpdHart1xOwnSd (GD0 : Gdexec) (γ : GName) (cpu : CPU) (ib : Ibch)
    (Hgd1 : AxCjrWpd.fetchImgOk GD0 1 0 AxEpiRace2.pc1 AxEpiRace2Run.h1Vs4)
    (Hrow1 : storeRowOk GD0 1 0)
    (Hw1 : sdWriteOkGen GD0 1 0 race2B raceData)
    (Hlen1 : (AxOpsem.grow GD0 1).length = 1) :
    ⊢ ([∗list] j ↦ H ∈ epiHs0, histAuth (GF := GF) γ (race2B + (j : Int)) 1 H) -∗
      @wpd hlc GF _ (epiGa2 GD0 γ) pol .MaybeStuck 1 (h1xState cpu ib)
        (fun _ => iprop(True)) := by
  have HF := @storeFlowOwnedGen hlc GF _ (epiGa2 GD0 γ) pol _ _ γ (obEqGa2 GD0 γ)
    (annEqGa2 GD0 γ) 1 0 race2B raceData epiHs0 rfl
    (pinGa2 GD0 γ (fun GD => sdWriteOkGen GD 1 0 race2B raceData) Hw1)
    (fun GD ls _ => locGa2 GD0 γ GD 1 0 ls)
  have HE : ∀ s0, SdRetX h1xT AxEpiProbe.drNopin DwAll DPost AxEpiRace2Run.h1Vs4 cpu (0 + 1) s0 →
      s0.atK = 1 := by
    rintro s0 ⟨v', v, t3, -, ib', Hk, -⟩
    exact Hk
  have Hle : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (self := epiGa2 (GF := GF) GD0 γ) GD ⊢
        ⌜(AxOpsem.grow GD 1).length ≤ 1⌝ :=
    pinGa2 GD0 γ (fun GD => (AxOpsem.grow GD 1).length ≤ 1) (Nat.le_of_eq Hlen1)
  show ⊢ _ -∗ @wpd hlc GF _ (epiGa2 GD0 γ) pol .MaybeStuck 1
    ⟨.PHart cpu (riscvStep false) h1xT.regs none ib, 0⟩ (fun _ => iprop(True))
  iintro Hauths
  ihave F := HF $$ Hauths
  iapply (@wpdCsdspStepExactRes hlc GF _ (epiGa2 GD0 γ) pol 1 (fun _ => iprop(True)) cpu ib 0
    h1xT _ _ _ _ _ _ _ _ _ h1xLedgerCsdsp
    (pinGa2 GD0 γ (fun GD => AxCjrWpd.fetchImgOk GD 1 0 (AxEpiRace2.pc1 : Int)
      AxEpiRace2Run.h1Vs4) Hgd1)
    (pinGa2 GD0 γ (fun GD => storeRowOk GD 1 0) Hrow1)) $$ F
  isplit
  · iintro _ %s' %Hs'
    iapply (@wpdPastRowEnd hlc GF _ (epiGa2 GD0 γ) pol 1 (fun _ => iprop(True))
      (SdRetX h1xT AxEpiProbe.drNopin DwAll DPost AxEpiRace2Run.h1Vs4 cpu (0 + 1)) 1 s' Hs'
      HE Hle)
    iintro %GD %s1 %_ %_
    iapply (@postLiftingTrue GF (epiGa2 GD0 γ) pol (fun _ => iprop(True)) 1 s1 .rfl)
  · iintro %GD %s1 %_ %_
    iapply (@postLiftingTrue GF (epiGa2 GD0 γ) pol (fun _ => iprop(True)) 1 s1 .rfl)

end h1x

theorem wpdHart1xOwnSdHwp1 (GD : Gdexec) (a : Int) (cpu : CPU) (ib : Ibch)
    (Hgd1 : AxCjrWpd.fetchImgOk GD 1 0 AxEpiRace2.pc1 AxEpiRace2Run.h1Vs4)
    (Hrow1 : storeRowOk GD 1 0)
    (Hw1 : sdWriteOkGen GD 1 0 race2B raceData)
    (Hlen1 : (AxOpsem.grow GD 1).length = 1) :
    ∀ [InvGS_gen .hasNoLC epiGF] [AxannotGS epiGF] (nm : GName),
      ⊢ epiInit3 a race2B nm 1 -∗
        @tierAWpd epiGF .hasNoLC _ _ epiPol GD GName Unit epiObInterp nm (h1xState cpu ib)
          .MaybeStuck 1 (fun _ => iprop(True)) := by
  intro _ _ nm
  unfold tierAWpd
  iintro H
  ihave H := (AxEpiSound3.epiInit3One a race2B nm).1 $$ H
  iapply (@wpdHart1xOwnSd .hasNoLC epiGF _ _ _ epiPol GD nm cpu ib Hgd1 Hrow1 Hw1 Hlen1) $$ H

/-- The concrete graph: `race2o` with hart 1's store carrying `raceData` (the racing value) at
its own slot `race2B`. -/
def row1x : List Lbl :=
  [LStore false race2B raceData .WCplain]

def race2x : Gdexec :=
  ⟨⟨race2Img, [AxEpiSdLdSat.row, row1x],
    [AxEpiRace2.eSD, AxEpiRace2.eW1, AxEpiRace2.eLD]⟩, []⟩

theorem race2xCat : rvwmoCatConsistent race2x :=
  catConsistentBSound _ (by decide +kernel)

theorem race2xFetch1 : AxCjrWpd.fetchImgOk race2x 1 0 AxEpiRace2.pc1 AxEpiRace2Run.h1Vs4 := by
  refine ⟨by decide, ?_⟩
  intro j hj
  have hj' : j < 4 := hj
  match j, hj' with
  | 0, _ => decide +kernel
  | 1, _ => decide +kernel
  | 2, _ => decide +kernel
  | 3, _ => decide +kernel

theorem race2xStoreRow1 : storeRowOk race2x 1 0 := ⟨_, rfl⟩

theorem race2xSdWriteOk1 : sdWriteOkGen race2x 1 0 race2B raceData := by
  refine ⟨by decide +kernel, ?_, rfl⟩
  rintro a' v' ⟨l, base, vs, j, Hl, Hw, Hv, Ha⟩
  have Hl0 : gxLbl race2x.gdG (1, 0) = some (Lbl.LStore false race2B raceData .WCplain) := rfl
  rw [Hl0, Option.some.injEq] at Hl
  subst Hl
  simp only [lbWr, Option.some.injEq, Prod.mk.injEq] at Hw
  obtain ⟨rfl, rfl⟩ := Hw
  exact ⟨j, Hv, Ha.symm⟩

theorem race2xLen1 : (AxOpsem.grow race2x 1).length = 1 := rfl

/-- THE EXACT TWIN: differs from the refuted `race2WpdUnprovable`'s hart (`regs1`) only in `sp`;
stores the same `raceData`. -/
theorem race2xOwnWpd (a : Int) (cpu : CPU) :
    ∀ [InvGS_gen .hasNoLC epiGF] [AxannotGS epiGF] (nm : GName),
      ⊢ epiInit3 a race2B nm 1 -∗
        @tierAWpd epiGF .hasNoLC _ _ epiPol race2x GName Unit epiObInterp nm
          (h1xState cpu ibNone) .MaybeStuck 1 (fun _ => iprop(True)) :=
  wpdHart1xOwnSdHwp1 race2x a cpu ibNone race2xFetch1 race2xStoreRow1 race2xSdWriteOk1
    race2xLen1

end Weak
