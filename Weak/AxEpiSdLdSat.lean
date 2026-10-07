/-
Weak: **non-vacuity witness for the PURE premises of `AxEpiChainSdLd.wpd_epi_sd_ld`** (the J0
program `c.sdsp ; c.ldsp`), AxSL tier.

Rocq: `iris/AxEpiSdLdSat.v` @ xxvzwolszwmp.

## What this file proves

One concrete 1-hart graph `gsdld` (hart 0, `kk = 0`) whose row is EXACTLY the program's two
memory events (Lean positions, see deviation 1):
  `SD = sd sdData → sdAddr` at `(0,0)`;  `LD = ld 8 bytes @ldAddr, rf SD` at `(0,1)`,
with gmo = program order.  The image holds `sdVs` at `[pcSd, pcSd+4)` (the two fetch windows
overlap: `pcLd = pcSd + 2`, and `ldVs` = bytes 2,3 of `sdVs`) and zero elsewhere.

Discharged (pure, by `decide +kernel` / `rfl`): `rvwmoCatConsistent gsdld`, the two fetches'
`AxCjrWpd.fetchImgOk`, `storeRowOk`, `loadRowOk`, the row length `= 0 + 2`, `¬ sdldText ldAddr`,
plus the readback facts `graphData (0,0) = some sdData`, `graphValue (0,1) = some sdData` and the
internal rf edge.  §2 lifts them to the wrapped `∀ GD, consistent → gconstInterp GD ⊢ ⌜..⌝`
forms at the adequacy instance `axGA2 gsdld …` (`sdldGa2`).

NOT discharged here (as Rocq): the Iris protocol-side premises (`localInterp` advance,
`storeFlow`, `loadFlow`; Rocq's `fetch_flow` is gone under Stage C).

As usual, a concrete certificate proves nothing about the MODEL — only that this premise bundle
is jointly satisfiable.

## Deviations from Rocq

1. O2 STAGE C (fetches are not graph events; `AxEpiSat` deviation 1 / `AxEpiLedgerSd`
   deviation 3): the Rocq row `[F0; SD; F1; LD]` carried the two instruction FETCHES as text
   `LLoad`s; the Lean row is `[SD; LD]`, so `eSD = (0,0)` (Rocq `(0,1)`), `eLD = (0,1)` (Rocq
   `(0,3)`), the load's rf timestamps stay `1` (the spill is gmo-first among writes, as in
   Rocq).  Rocq's `fetch_gd_ok gsdld 0 0 pc_sd sd_vs` / `… 0 2 pc_ld ld_vs` become
   `AxCjrWpd.fetchImgOk gsdld 0 0 pcSd sdVs` / `… 0 1 pcLd AxEpiLedger.ldVs` (the fetch keeps the
   row position of the event that follows it — Rocq `S kk` ↦ `kk` — and `fetchGdOk`'s `IRead`
   item no longer exists); `store_row_ok … 0 1` ↦ `storeRowOk … 0 0`; `load_row_ok … 0 3` ↦
   `loadRowOk … 0 1`; the length `0 + 4` ↦ `0 + 2`; the readbacks at `(0,0)` / `(0,1)`.
2. `AxirisG` has no `ax_text` (AxTierA2 deviation 2): the instance is `axGA2 gsdld Unit Unit
   (fun _ _ _ _ => True) ()` (no `T`), and the ga2 conjunct `¬ ax_text ld_addr` is stated as
   `¬ sdldText ldAddr` (what it unfolded to in Rocq).  `sdldGa2` is a `@[reducible] def`, named
   explicitly (`(self := sdldGa2)`), not an instance (AxTierA2 deviation 3).  Rocq's unused
   section `axpol` is not taken.
3. DROPPED: `eF0`, `eF1` (the fetch events; no downstream Rocq file uses this file's —
   AxEpiRace2Run's `eF0`/`eF1` are AxEpiRace2's, imported later).  The `Print Assumptions`
   audits are not ported (the lint's axiom check covers them).
4. VOCABULARY (as `AxEpiSat` deviation 4): `Z` ↦ `Int`, `Z_to_bv 8 0` ↦ `0#8`, `l !! n ≫= Some`
   ↦ `l[n]?`, `Z.to_nat` ↦ `Int.toNat`, `gd_g` ↦ `.gdG`, `vm_compute` ↦ `decide +kernel`;
   `sdldText` is a conjunction (Rocq a chained `≤ <`).
5. NAMES: duplicated Rocq names are file-qualified (`AxEpiSdLdSat.row`/`eSD`/`eLD`).

**Rocq → Lean name map.**  `sdld_text` `sdldText`, `sdld_img` `sdldImg`, `row`
`AxEpiSdLdSat.row`, `eSD` `AxEpiSdLdSat.eSD`, `eLD` `AxEpiSdLdSat.eLD`, `gsdld` `gsdld`,
`gsdld_cat` `gsdldCat`, `gsdld_fetch_sd` `gsdldFetchSd`, `gsdld_store_row` `gsdldStoreRow`,
`gsdld_fetch_ld` `gsdldFetchLd`, `gsdld_load_row` `gsdldLoadRow`, `gsdld_len` `gsdldLen`,
`gsdld_ntext` `gsdldNtext`, `gsdld_data_sd` `gsdldDataSd`, `gsdld_value_ld` `gsdldValueLd`,
`gsdld_rf` `gsdldRf`, `gsdld_sat` `gsdldSat`, `sdld_ga2` `sdldGa2`, `pin_pure`
`AxEpiSdLdSat.pinPure`, `gsdld_premises_ga2` `gsdldPremisesGa2`.

**Dropped:** `eF0`, `eF1` (deviation 3).  Rocq 22 declarations; Lean 20.
-/
import Weak.AxEpiLedgerSd
import Weak.AxCjrWpd
import Weak.AxLdspWpd
import Weak.AxGraphDec
import Weak.AxTierA2

namespace Weak

open Iris Iris.Std MachCSL MachCSL.Stdpp
open Lbl

/-! # 1. The graph -/

def sdldText (a : Int) : Prop := (pcSd : Int) ≤ a ∧ a < (pcSd : Int) + 4

def sdldImg : Image := fun a =>
  if (pcSd : Int) ≤ a ∧ a < (pcSd : Int) + 4 then sdVs[(a - (pcSd : Int)).toNat]?
  else some 0#8

def AxEpiSdLdSat.row : List Lbl :=
  [LStore false sdAddr sdData .WCplain,
   LLoad false ldAddr [1, 1, 1, 1, 1, 1, 1, 1] sdData]

def AxEpiSdLdSat.eSD : Geid := (0, 0)
def AxEpiSdLdSat.eLD : Geid := (0, 1)

def gsdld : Gdexec :=
  ⟨⟨sdldImg, [AxEpiSdLdSat.row], [AxEpiSdLdSat.eSD, AxEpiSdLdSat.eLD]⟩, []⟩

theorem gsdldCat : rvwmoCatConsistent gsdld :=
  catConsistentBSound _ (by decide +kernel)

theorem gsdldFetchSd : AxCjrWpd.fetchImgOk gsdld 0 0 pcSd sdVs := by
  refine ⟨by decide, ?_⟩
  intro j hj
  have hj' : j < 4 := hj
  match j, hj' with
  | 0, _ => decide +kernel
  | 1, _ => decide +kernel
  | 2, _ => decide +kernel
  | 3, _ => decide +kernel

theorem gsdldStoreRow : storeRowOk gsdld 0 0 := ⟨_, rfl⟩

theorem gsdldFetchLd : AxCjrWpd.fetchImgOk gsdld 0 1 pcLd AxEpiLedger.ldVs := by
  refine ⟨by decide, ?_⟩
  intro j hj
  have hj' : j < 2 := hj
  match j, hj' with
  | 0, _ => decide +kernel
  | 1, _ => decide +kernel

theorem gsdldLoadRow : loadRowOk gsdld 0 1 := ⟨_, rfl, rfl⟩

theorem gsdldLen : (AxOpsem.grow gsdld 0).length = 0 + 2 := rfl

theorem gsdldNtext : ¬ sdldText ldAddr := by
  unfold sdldText ldAddr spVal pcSd
  omega

/-- Readback: the spill writes `sdData`, the reload reads it back. -/
theorem gsdldDataSd : graphData gsdld (0, 0) = some sdData := rfl

theorem gsdldValueLd : graphValue gsdld (0, 1) = some sdData := rfl

/-- The reload really is served by the spill (internal rf, byte 0). -/
theorem gsdldRf : grfAt gsdld.gdG ldAddr AxEpiSdLdSat.eSD AxEpiSdLdSat.eLD :=
  ⟨1, 0#8, (grbBSpec _ _ _ _ _).1 (by decide +kernel), by decide +kernel⟩

theorem gsdldSat :
    rvwmoCatConsistent gsdld ∧
    AxCjrWpd.fetchImgOk gsdld 0 0 pcSd sdVs ∧ storeRowOk gsdld 0 0 ∧
    AxCjrWpd.fetchImgOk gsdld 0 1 pcLd AxEpiLedger.ldVs ∧ loadRowOk gsdld 0 1 ∧
    (AxOpsem.grow gsdld 0).length = 0 + 2 ∧ ¬ sdldText ldAddr ∧
    graphData gsdld (0, 0) = some sdData ∧
    graphValue gsdld (0, 1) = some sdData :=
  ⟨gsdldCat, gsdldFetchSd, gsdldStoreRow, gsdldFetchLd, gsdldLoadRow, gsdldLen, gsdldNtext,
    gsdldDataSd, gsdldValueLd⟩

/-! # 2. The wrapped premises at the adequacy instance `axGA2` -/

section ga2
variable {GF : BundledGFunctors.{0,0,0}} [AxannotGS GF]

/-- Rocq `sdld_ga2` (a local instance there; a named def here). -/
@[reducible] def sdldGa2 : AxirisG GF :=
  axGA2 gsdld Unit Unit (fun _ _ _ _ => iprop(True)) ()

theorem AxEpiSdLdSat.pinPure (P : Gdexec → Prop) (HP : P gsdld) :
    ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (self := sdldGa2 (GF := GF)) GD ⊢ ⌜P GD⌝ := by
  intro GD _
  show iprop(⌜GD = gsdld⌝) ⊢ iprop(⌜P GD⌝)
  iintro %h
  subst h
  ipureintro
  exact HP

theorem gsdldPremisesGa2 :
    (∀ GD, rvwmoCatConsistent GD → AxirisG.gconstInterp (self := sdldGa2 (GF := GF)) GD ⊢
      ⌜AxCjrWpd.fetchImgOk GD 0 0 pcSd sdVs⌝) ∧
    (∀ GD, rvwmoCatConsistent GD → AxirisG.gconstInterp (self := sdldGa2 (GF := GF)) GD ⊢
      ⌜storeRowOk GD 0 0⌝) ∧
    (∀ GD, rvwmoCatConsistent GD → AxirisG.gconstInterp (self := sdldGa2 (GF := GF)) GD ⊢
      ⌜AxCjrWpd.fetchImgOk GD 0 1 pcLd AxEpiLedger.ldVs⌝) ∧
    ¬ sdldText ldAddr ∧
    (∀ GD, rvwmoCatConsistent GD → AxirisG.gconstInterp (self := sdldGa2 (GF := GF)) GD ⊢
      ⌜loadRowOk GD 0 1⌝) ∧
    (∀ GD, rvwmoCatConsistent GD → AxirisG.gconstInterp (self := sdldGa2 (GF := GF)) GD ⊢
      ⌜(AxOpsem.grow GD 0).length = 0 + 2⌝) :=
  ⟨AxEpiSdLdSat.pinPure (fun GD => AxCjrWpd.fetchImgOk GD 0 0 pcSd sdVs) gsdldFetchSd,
   AxEpiSdLdSat.pinPure (fun GD => storeRowOk GD 0 0) gsdldStoreRow,
   AxEpiSdLdSat.pinPure (fun GD => AxCjrWpd.fetchImgOk GD 0 1 pcLd AxEpiLedger.ldVs) gsdldFetchLd,
   gsdldNtext,
   AxEpiSdLdSat.pinPure (fun GD => loadRowOk GD 0 1) gsdldLoadRow,
   AxEpiSdLdSat.pinPure (fun GD => (AxOpsem.grow GD 0).length = 0 + 2) gsdldLen⟩

end ga2

end Weak
