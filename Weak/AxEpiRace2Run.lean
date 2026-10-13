/-
Weak: **`race2WpdUnprovable`: the CONCRETE racing hart-1 program has no WPd at the epilogue
protocol — fully closed** (AxSL tier).

Rocq: `iris/AxEpiRace2Run.v` @ xxvzwolszwmp.

## What this file proves

Hart 1 = Sail `riscvStep false` from `AxEpiRace2Run.regs1` (= `probeRegs pc1` with
`x1 := 0x80000200`, the value `raceData` encodes), whose first instruction `c.sdsp ra,8(sp)`
stores `raceData` to hart 0's slot.  Both harts' runs are discharged by kernel evaluation of the
`AxEpiRun.drive` driver (`drive0Ok`, `drive1Ok`, `race2'Run0`, `race2'Run1`), so the
refutations `race2WpdUnprovable` (via `epiReloadSound2`, hart 1 from no resources) and
`race2WpdUnprovableOwn` (via `epiReloadSound3`, hart 1 from its own slot-`race2B` auths) have
NO remaining hypotheses.  §5: the sanity twin at the same 4-byte fetch shape (`sp := race2B - 8`,
store to hart 1's own slot) IS provable (`race2oOwnWpd`), at the concrete cat-consistent graph
`race2o`.

## Deviations from Rocq

1. O2 STAGE C (fetches are not graph events; `AxEpiRace2` deviation 1): Rocq needed the widened
   graph `race2'` because hart 1's ROW fetch item (2 bytes) did not match the model's 4-byte
   fetch at the 4-aligned `pc1`.  In Lean a fetch is an admin step answered from the IMAGE
   (`AxEpiRun` deviation 1), and `race2Img` holds `0` at `pc1+2`, `pc1+3`, so the 4-byte fetch
   `h1Vs4` is served at `race2` itself.  `row1'` (Rocq `[fetch h1_vs4; W1]`) is `[W1]` =
   `AxEpiRace2.row1`, and `race2'` is definitionally `race2` (`AxEpiRace2Run.race2'Eq`, `rfl`);
   the `race2'` premises are those of `race2` at Lean positions: `fetchImgOk race2' 0 0` /
   `0 1`, `storeRowOk 0 0`, `sdWriteOk 0 0`, `loadRowOk 0 1`, `ldspOwnOk … 0 1 (0,0) …
   (writenHist (0,0) …)`, length `2` (Rocq 4), `gmoLt (0,0) (0,1)`, `race2'NotSd` at `(0,1)`.
   Drivers: `drive0` ends at row position 2 (Rocq 4), `drive1` at 1 (Rocq 2); both take the
   image `race2'.gdG.gxImg`.  gmo `[eSD; eW1; eLD]` (Rocq `[eF0; eSD; eF1; eG0; eW1; eLD]`).
2. DROPPED (Stage C): `race2_hart1_stuck` (FALSE in Lean: with image-served fetches hart 1 runs
   at `race2` — `race2'` is `race2`; no downstream use), `race2'_nw_sd`, `race2'_nw_ld`,
   `race2o_nw1` (`gis_w` of fetch events; the Lean theorems take no such premise), and the
   `Hnw1` premise of `wpdHart1oOwnSd`/`wpdHart1oOwnSdHwp1` (no fetch flow, `AxEpiSound3`
   deviation 2).
3. TEXT (`AxEpiSound2` deviation 1): `tierAWpd` and `epiReloadSound2/3` take no text `T` and no
   `¬ T ld_addr`.  So `race2'NoWpdT`/`race2'NoWpd3T` drop `T`/`HT`, and
   `race2WpdUnprovable` / `race2WpdUnprovableRace2Text` (resp. `…Own` / `…OwnRace2Text`) state
   the same proposition (kept for the name map).  `race2'Text` and `race2'Ntext` are kept.
4. INSTANCES (`AxEpiRun` deviation 4): `race2'Run0/1` quantify over `cpu` only (Rocq
   `∀ Σ (HG : axirisG Σ)`); `Hwp1` statements are `∀ [InvGS_gen .hasNoLC epiGF]
   [AxannotGS epiGF] (nm : GName)` with `epiPol` passed explicitly (`AxEpiSound2` deviation 2).
5. §5 (`AxEpiSound3` deviation 2 shapes): hart 1's row is `[SD]`, so `fetchImgOk GD 1 0 pc1
   h1Vs4`, `storeRowOk GD 1 0`, `sdWriteOk GD 1 0 race2B`, length 1 (Rocq 2), `SdRetX` at
   `k = 1`; the ledger uses `AxEpiProbe.drNopin` (Rocq `Dr_noseip`, two-pin form);
   `dev0_state` ↦ `testDevs`; `x2 := BitVec.ofInt 64 (race2B - 8)`; `row1o` is `[W1o]` and
   `race2o`'s hart-0 row is `AxEpiSdLdSat.row`.  The section lemma is generic in `hlc` and the
   policy (Rocq `HasNoLc`, `epi_pol`); Rocq's section `T` is gone.
6. NAMES: generic short names are file-qualified (`AxEpiRace2Run.h1Vs4`, `.row1'`, `.regs1`
   (also in WeakLitmus/AxEpiChain), `.driveK`, `.drive0`, `.drive1`, `.drive0Ok`, `.drive1Ok`,
   `.row1o`, `.race2'Eq`).  `vm_compute` ↦ `decide +kernel`.

**Rocq → Lean name map.**  `h1_vs4` `AxEpiRace2Run.h1Vs4`, `row1'` `AxEpiRace2Run.row1'`,
`race2'` `race2'`, `race2'_text` `race2'Text`, `race2'_cat` `race2'Cat`, `race2'_not_sd`
`race2'NotSd`, `race2'_harts` `race2'Harts`, `race2'_fetch_sd` `race2'FetchSd`,
`race2'_store_row` `race2'StoreRow`, `race2'_sd_write_ok` `race2'SdWriteOk`, `race2'_fetch_ld`
`race2'FetchLd`, `race2'_ntext` `race2'Ntext`, `race2'_load_row` `race2'LoadRow`,
`race2'_ldsp_own_ok` `race2'LdspOwnOk`, `race2'_len` `race2'Len`, `race2'_lob_gmo`
`race2'LobGmo`, `regs1` `AxEpiRace2Run.regs1`, `drive_k` `AxEpiRace2Run.driveK`, `drive0`
`AxEpiRace2Run.drive0`, `drive1` `AxEpiRace2Run.drive1`, `drive0_ok` `AxEpiRace2Run.drive0Ok`,
`drive1_ok` `AxEpiRace2Run.drive1Ok`, `race2'_run0` `race2'Run0`, `race2'_run1` `race2'Run1`,
`race2'_no_wpd_T` `race2'NoWpdT`, `race2_wpd_unprovable` `race2WpdUnprovable`,
`race2_wpd_unprovable_race2_text` `race2WpdUnprovableRace2Text`, `race2'_no_wpd3_T`
`race2'NoWpd3T`, `race2_wpd_unprovable_own` `race2WpdUnprovableOwn`,
`race2_wpd_unprovable_own_race2_text` `race2WpdUnprovableOwnRace2Text`, `h1o_regs` `h1oRegs`,
`h1o_t` `h1oT`, `h1o_post` `h1oPost`, `h1o_ledger_csdsp` `h1oLedgerCsdsp`, `h1o_state`
`h1oState`, `wpd_hart1o_own_sd` `wpdHart1oOwnSd`, `wpd_hart1o_own_sd_Hwp1`
`wpdHart1oOwnSdHwp1`, `row1o` `AxEpiRace2Run.row1o`, `race2o` `race2o`, `race2o_cat`
`race2oCat`, `race2o_fetch1` `race2oFetch1`, `race2o_store_row1` `race2oStoreRow1`,
`race2o_sd_write_ok1` `race2oSdWriteOk1`, `race2o_len1` `race2oLen1`, `race2o_own_wpd`
`race2oOwnWpd`.  None is in the duplicated-name table.  Lean-only: `AxEpiRace2Run.race2'Eq`.

**Dropped:** `race2_hart1_stuck`, `race2'_nw_sd`, `race2'_nw_ld`, `race2o_nw1` (deviation 2);
the section-local instance `epi_ga2_h1o` (Lean passes `epiGa2 GD0 γ` explicitly, AxEpiSat
convention); the `Print Assumptions` lines (the lint's axiom check covers them).  Rocq 50
declarations (incl. the local instance); Lean 45 + 1 Lean-only.  `race2oOwnWpd` drops the
text `T` (deviation 3).
-/
import Weak.AxEpiRun
import Weak.AxEpiSound3

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D
open Lbl

/-! # 1. The graph `race2'` (= `race2` under Stage C, deviation 1) -/

/-- Hart 1's 4-byte fetch at the 4-aligned `pc1`: `c.sdsp ra,8(sp)` and two zero bytes. -/
def AxEpiRace2Run.h1Vs4 : List (BitVec 8) := [0x06#8, 0xe4#8, 0x00#8, 0x00#8]

/-- Hart 1's row: the store only (the fetch is no row item). -/
def AxEpiRace2Run.row1' : List Lbl :=
  [LStore false sdAddr raceData .WCplain]

def race2' : Gdexec :=
  ⟨⟨race2Img, [AxEpiRace2.row0, AxEpiRace2Run.row1'],
    [AxEpiRace2.eSD, AxEpiRace2.eW1, AxEpiRace2.eLD]⟩, [], []⟩

/-- (Lean-only) Under Stage C the widening is the identity. -/
theorem AxEpiRace2Run.race2'Eq : race2' = race2 := rfl

def race2'Text (a : Int) : Prop :=
  ((pcSd : Int) ≤ a ∧ a < (pcSd : Int) + 4) ∨
  ((AxEpiRace2.pc1 : Int) ≤ a ∧ a < (AxEpiRace2.pc1 : Int) + 4)

theorem race2'Cat : rvwmoCatConsistent race2' := race2Cat

theorem race2'NotSd : graphValue race2' (0, 1) ≠ some sdData := race2NotSd

theorem race2'Harts : ∀ e, e ∈ race2'.gdG.gxGmo → e.1 = 0 ∨ e.1 = 1 := race2Harts

theorem race2'FetchSd : AxCjrWpd.fetchImgOk race2' 0 0 pcSd sdVs := race2FetchSd

theorem race2'StoreRow : storeRowOk race2' 0 0 := race2StoreRow

theorem race2'SdWriteOk : sdWriteOk race2' 0 0 ldAddr := race2SdWriteOk

theorem race2'FetchLd : AxCjrWpd.fetchImgOk race2' 0 1 pcLd AxEpiLedger.ldVs := race2FetchLd

theorem race2'Ntext : ¬ race2'Text ldAddr := by
  unfold race2'Text ldAddr spVal pcSd AxEpiRace2.pc1
  omega

theorem race2'LoadRow : loadRowOk race2' 0 1 := race2LoadRow

theorem race2'LdspOwnOk :
    @ldspOwnOk epiPol race2' 0 1 (0, 0) ldAddr (writenHist (0, 0) sdData epiHs0) :=
  race2LdspOwnOk

theorem race2'Len : (AxOpsem.grow race2' 0).length = 2 := rfl

theorem race2'LobGmo : gmoLt race2'.gdG (0, 0) (0, 1) := race2LobGmo

/-! # 2. The concrete runs -/

/-- Hart 1's initial registers: `probeRegs pc1` with `ra := 0x80000200`. -/
def AxEpiRace2Run.regs1 : RegFile :=
  (probeRegs AxEpiRace2.pc1).set .x1 (AxEpiProbe.w64 0x80000200)

def AxEpiRace2Run.driveK (d : Option (SailM Unit × RegFile × Ibch × Nat)) : Option Nat :=
  match d with
  | some (_, _, _, k) => some k
  | none => none

noncomputable def AxEpiRace2Run.drive0 : Option (SailM Unit × RegFile × Ibch × Nat) :=
  drive race2'.gdG.gxImg (AxOpsem.grow race2' 0) 2 runFuel (riscvStep false) (probeRegs pcSd)
    ibNone 0

noncomputable def AxEpiRace2Run.drive1 : Option (SailM Unit × RegFile × Ibch × Nat) :=
  drive race2'.gdG.gxImg (AxOpsem.grow race2' 1) 1 runFuel (riscvStep false)
    AxEpiRace2Run.regs1 ibNone 0

theorem AxEpiRace2Run.drive0Ok : AxEpiRace2Run.driveK AxEpiRace2Run.drive0 = some 2 := by
  decide +kernel

theorem AxEpiRace2Run.drive1Ok : AxEpiRace2Run.driveK AxEpiRace2Run.drive1 = some 1 := by
  decide +kernel

theorem race2'Run0 (cpu : CPU) :
    ∃ n sN, sN.atK = (AxOpsem.grow race2' 0).length ∧
      nsteps (astepAnyNfGv race2' 0) n
        ⟨.PHart cpu (riscvStep false) (probeRegs pcSd) none ibNone, 0⟩ sN := by
  have Hok := AxEpiRace2Run.drive0Ok
  unfold AxEpiRace2Run.driveK at Hok
  cases Hd : AxEpiRace2Run.drive0 with
  | none => rw [Hd] at Hok; exact absurd Hok (by simp)
  | some r =>
    obtain ⟨m, rs, ib, k⟩ := r
    obtain ⟨Hk, n, Hr⟩ := driveSound race2' 0 2 runFuel _ _ _ _ m rs ib k Hd
    subst Hk
    exact ⟨n, AxEpiRun.st cpu m rs ib 2, rfl, Hr cpu⟩

theorem race2'Run1 (cpu : CPU) :
    ∃ n sN, sN.atK = (AxOpsem.grow race2' 1).length ∧
      nsteps (astepAnyNfGv race2' 1) n
        ⟨.PHart cpu (riscvStep false) AxEpiRace2Run.regs1 none ibNone, 0⟩ sN := by
  have Hok := AxEpiRace2Run.drive1Ok
  unfold AxEpiRace2Run.driveK at Hok
  cases Hd : AxEpiRace2Run.drive1 with
  | none => rw [Hd] at Hok; exact absurd Hok (by simp)
  | some r =>
    obtain ⟨m, rs, ib, k⟩ := r
    obtain ⟨Hk, n, Hr⟩ := driveSound race2' 1 1 runFuel _ _ _ _ m rs ib k Hd
    subst Hk
    exact ⟨n, AxEpiRun.st cpu m rs ib 1, rfl, Hr cpu⟩

/-! # 3. THE CLOSED RESULT -/

theorem race2'NoWpdT (cpu : CPU) :
    ¬ (∀ [InvGS_gen .hasNoLC epiGF] [AxannotGS epiGF] (nm : GName),
      ⊢ @tierAWpd epiGF .hasNoLC _ _ epiPol race2' GName Unit epiObInterp nm
          ⟨.PHart cpu (riscvStep false) AxEpiRace2Run.regs1 none ibNone, 0⟩ .MaybeStuck 1
          (fun _ => iprop(True))) := by
  intro Hwp1
  obtain ⟨n, sN, Hend, Hrun⟩ := race2'Run0 cpu
  obtain ⟨n1, sN1, Hend1, Hrun1⟩ := race2'Run1 cpu
  exact race2'NotSd (epiReloadSound2 race2' cpu ldAddr race2'Cat race2'Harts race2'FetchSd
    race2'StoreRow race2'SdWriteOk race2'FetchLd race2'LoadRow race2'LdspOwnOk race2'Len
    race2'LobGmo sN n (fun _ _ => Hrun) Hend
    ⟨.PHart cpu (riscvStep false) AxEpiRace2Run.regs1 none ibNone, 0⟩ sN1 n1 rfl
    (fun _ _ => Hrun1) Hend1 Hwp1)

/-- THE RESULT: the concrete racing hart-1 program (from `regs1`, its `c.sdsp` storing
`raceData` into hart 0's slot) has NO WPd from no resources at the epilogue protocol. -/
theorem race2WpdUnprovable (cpu : CPU) :
    ¬ (∀ [InvGS_gen .hasNoLC epiGF] [AxannotGS epiGF] (nm : GName),
      ⊢ @tierAWpd epiGF .hasNoLC _ _ epiPol race2' GName Unit epiObInterp nm
          ⟨.PHart cpu (riscvStep false) AxEpiRace2Run.regs1 none ibNone, 0⟩ .MaybeStuck 1
          (fun _ => iprop(True))) :=
  race2'NoWpdT cpu

/-- The same at the original text `race2Text` (deviation 3: the same proposition). -/
theorem race2WpdUnprovableRace2Text (cpu : CPU) :
    ¬ (∀ [InvGS_gen .hasNoLC epiGF] [AxannotGS epiGF] (nm : GName),
      ⊢ @tierAWpd epiGF .hasNoLC _ _ epiPol race2' GName Unit epiObInterp nm
          ⟨.PHart cpu (riscvStep false) AxEpiRace2Run.regs1 none ibNone, 0⟩ .MaybeStuck 1
          (fun _ => iprop(True))) :=
  race2'NoWpdT cpu

/-! # 4. THE STRONGER (OWN-SLOT) FORM, via `epiReloadSound3`

Hart 1 now starts from ITS OWN auths for slot `race2B = ldAddr + 8`; its concrete store hits
hart 0's slot `ldAddr`, so its WPd is still refutable — with every run hypothesis discharged. -/

theorem race2'NoWpd3T (cpu : CPU) :
    ¬ (∀ [InvGS_gen .hasNoLC epiGF] [AxannotGS epiGF] (nm : GName),
      ⊢ epiInit3 ldAddr race2B nm 1 -∗
        @tierAWpd epiGF .hasNoLC _ _ epiPol race2' GName Unit epiObInterp nm
          ⟨.PHart cpu (riscvStep false) AxEpiRace2Run.regs1 none ibNone, 0⟩ .MaybeStuck 1
          (fun _ => iprop(True))) := by
  intro Hwp1
  obtain ⟨n, sN, Hend, Hrun⟩ := race2'Run0 cpu
  obtain ⟨n1, sN1, Hend1, Hrun1⟩ := race2'Run1 cpu
  have Hdisj : slotsDisjoint ldAddr race2B := by
    unfold slotsDisjoint race2B
    omega
  exact race2'NotSd (epiReloadSound3 race2' cpu ldAddr race2B Hdisj race2'Cat race2'Harts
    race2'FetchSd race2'StoreRow race2'SdWriteOk race2'FetchLd race2'LoadRow race2'LdspOwnOk
    race2'Len race2'LobGmo sN n (fun _ _ => Hrun) Hend
    ⟨.PHart cpu (riscvStep false) AxEpiRace2Run.regs1 none ibNone, 0⟩ sN1 n1 rfl
    (fun _ _ => Hrun1) Hend1 Hwp1)

/-- THE STRONGER RESULT: even from hart 1's own slot-`race2B` auths, the concrete racing hart-1
program has no WPd — fully closed. -/
theorem race2WpdUnprovableOwn (cpu : CPU) :
    ¬ (∀ [InvGS_gen .hasNoLC epiGF] [AxannotGS epiGF] (nm : GName),
      ⊢ epiInit3 ldAddr race2B nm 1 -∗
        @tierAWpd epiGF .hasNoLC _ _ epiPol race2' GName Unit epiObInterp nm
          ⟨.PHart cpu (riscvStep false) AxEpiRace2Run.regs1 none ibNone, 0⟩ .MaybeStuck 1
          (fun _ => iprop(True))) :=
  race2'NoWpd3T cpu

theorem race2WpdUnprovableOwnRace2Text (cpu : CPU) :
    ¬ (∀ [InvGS_gen .hasNoLC epiGF] [AxannotGS epiGF] (nm : GName),
      ⊢ epiInit3 ldAddr race2B nm 1 -∗
        @tierAWpd epiGF .hasNoLC _ _ epiPol race2' GName Unit epiObInterp nm
          ⟨.PHart cpu (riscvStep false) AxEpiRace2Run.regs1 none ibNone, 0⟩ .MaybeStuck 1
          (fun _ => iprop(True))) :=
  race2'NoWpd3T cpu

/-! # 5. SANITY TWIN AT THE `race2'` FETCH SHAPE: hart 1 CAN write its own slot

Hart 1 at `pc1` (4-byte fetch `h1Vs4`, the same `c.sdsp ra,8(sp)` and fetch shape as the racing
program) with `sp := race2B - 8`, so its store hits its OWN slot `race2B`.  `ra` is `raVal` here
(the store writes `sdData`) because `storeFlowOwned` is stated for `sdData`; the racing program
has `ra = 0x80000200` (`raceData`).  Its WPd from `epiInit3 _ race2B nm 1` is PROVABLE, and every
graph premise holds at the concrete `race2o`. -/

def h1oRegs : RegFile := (probeRegs AxEpiRace2.pc1).set .x2 (BitVec.ofInt 64 (race2B - 8))

def h1oT : ExecSt := ⟨h1oRegs, probeMem, testDevs⟩

def h1oPost (rs : RegFile) : Bool := decide ((rs .PC).toNat = AxEpiRace2.pc1 + 2)

theorem h1oLedgerCsdsp :
    AxSdModelFacts h1oT AxEpiProbe.drNopin DwAll DPost (AxEpiRace2.pc1 : Int)
      AxEpiRace2Run.h1Vs4 race2B sdData h1oPost where
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

noncomputable def h1oState (cpu : CPU) (ib : Ibch) : Athread :=
  ⟨.PHart cpu (riscvStep false) h1oRegs none ib, 0⟩

section h1o
variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF] [AxannotGS GF]
  [AxlogG GF Hent] [pol : Axpol]

theorem wpdHart1oOwnSd (GD0 : Gdexec) (γ : GName) (cpu : CPU) (ib : Ibch)
    (Hgd1 : AxCjrWpd.fetchImgOk GD0 1 0 AxEpiRace2.pc1 AxEpiRace2Run.h1Vs4)
    (Hrow1 : storeRowOk GD0 1 0)
    (Hw1 : sdWriteOk GD0 1 0 race2B)
    (Hlen1 : (AxOpsem.grow GD0 1).length = 1) :
    ⊢ ([∗list] j ↦ H ∈ epiHs0, histAuth (GF := GF) γ (race2B + (j : Int)) 1 H) -∗
      @wpd hlc GF _ (epiGa2 GD0 γ) pol .MaybeStuck 1 (h1oState cpu ib)
        (fun _ => iprop(True)) := by
  have HF := @storeFlowOwned hlc GF _ (epiGa2 GD0 γ) pol _ _ γ (obEqGa2 GD0 γ) (annEqGa2 GD0 γ)
    1 0 race2B epiHs0 rfl (pinGa2 GD0 γ (fun GD => sdWriteOk GD 1 0 race2B) Hw1)
    (fun GD ls _ => locGa2 GD0 γ GD 1 0 ls)
  have HE : ∀ s0, SdRetX h1oT AxEpiProbe.drNopin DwAll DPost AxEpiRace2Run.h1Vs4 cpu (0 + 1) s0 →
      s0.atK = 1 := by
    rintro s0 ⟨v', v, t3, -, ib', Hk, -⟩
    exact Hk
  have Hle : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (self := epiGa2 (GF := GF) GD0 γ) GD ⊢
        ⌜(AxOpsem.grow GD 1).length ≤ 1⌝ :=
    pinGa2 GD0 γ (fun GD => (AxOpsem.grow GD 1).length ≤ 1) (Nat.le_of_eq Hlen1)
  show ⊢ _ -∗ @wpd hlc GF _ (epiGa2 GD0 γ) pol .MaybeStuck 1
    ⟨.PHart cpu (riscvStep false) h1oT.regs none ib, 0⟩ (fun _ => iprop(True))
  iintro Hauths
  ihave F := HF $$ Hauths
  iapply (@wpdCsdspStepExactRes hlc GF _ (epiGa2 GD0 γ) pol 1 (fun _ => iprop(True)) cpu ib 0
    h1oT _ _ _ _ _ _ _ _ _ h1oLedgerCsdsp
    (pinGa2 GD0 γ (fun GD => AxCjrWpd.fetchImgOk GD 1 0 (AxEpiRace2.pc1 : Int)
      AxEpiRace2Run.h1Vs4) Hgd1)
    (pinGa2 GD0 γ (fun GD => storeRowOk GD 1 0) Hrow1)) $$ F
  isplit
  · iintro _ %s' %Hs'
    iapply (@wpdPastRowEnd hlc GF _ (epiGa2 GD0 γ) pol 1 (fun _ => iprop(True))
      (SdRetX h1oT AxEpiProbe.drNopin DwAll DPost AxEpiRace2Run.h1Vs4 cpu (0 + 1)) 1 s' Hs'
      HE Hle)
    iintro %GD %s1 %_ %_
    iapply (@postLiftingTrue GF (epiGa2 GD0 γ) pol (fun _ => iprop(True)) 1 s1 .rfl)
  · iintro %GD %s1 %_ %_
    iapply (@postLiftingTrue GF (epiGa2 GD0 γ) pol (fun _ => iprop(True)) 1 s1 .rfl)

end h1o

theorem wpdHart1oOwnSdHwp1 (GD : Gdexec) (a : Int) (cpu : CPU) (ib : Ibch)
    (Hgd1 : AxCjrWpd.fetchImgOk GD 1 0 AxEpiRace2.pc1 AxEpiRace2Run.h1Vs4)
    (Hrow1 : storeRowOk GD 1 0)
    (Hw1 : sdWriteOk GD 1 0 race2B)
    (Hlen1 : (AxOpsem.grow GD 1).length = 1) :
    ∀ [InvGS_gen .hasNoLC epiGF] [AxannotGS epiGF] (nm : GName),
      ⊢ epiInit3 a race2B nm 1 -∗
        @tierAWpd epiGF .hasNoLC _ _ epiPol GD GName Unit epiObInterp nm (h1oState cpu ib)
          .MaybeStuck 1 (fun _ => iprop(True)) := by
  intro _ _ nm
  unfold tierAWpd
  iintro H
  ihave H := (AxEpiSound3.epiInit3One a race2B nm).1 $$ H
  iapply (@wpdHart1oOwnSd .hasNoLC epiGF _ _ _ epiPol GD nm cpu ib Hgd1 Hrow1 Hw1 Hlen1) $$ H

/-- The concrete graph for the twin: `race2'` with hart 1's store moved to its own slot
`race2B` and carrying `sdData`, and hart 0's reload reading its own spill (hart 0's row =
`AxEpiSdLdSat.row`); cat-consistent. -/
def AxEpiRace2Run.row1o : List Lbl :=
  [LStore false race2B sdData .WCplain]

def race2o : Gdexec :=
  ⟨⟨race2Img, [AxEpiSdLdSat.row, AxEpiRace2Run.row1o],
    [AxEpiRace2.eSD, AxEpiRace2.eW1, AxEpiRace2.eLD]⟩, [], []⟩

theorem race2oCat : rvwmoCatConsistent race2o :=
  catConsistentBSound _ (by decide +kernel)

theorem race2oFetch1 : AxCjrWpd.fetchImgOk race2o 1 0 AxEpiRace2.pc1 AxEpiRace2Run.h1Vs4 := by
  refine ⟨by decide, ?_⟩
  intro j hj
  have hj' : j < 4 := hj
  match j, hj' with
  | 0, _ => decide +kernel
  | 1, _ => decide +kernel
  | 2, _ => decide +kernel
  | 3, _ => decide +kernel

theorem race2oStoreRow1 : storeRowOk race2o 1 0 := ⟨_, rfl⟩

theorem race2oSdWriteOk1 : sdWriteOk race2o 1 0 race2B := by
  refine ⟨by decide +kernel, ?_, rfl⟩
  rintro a' v' ⟨l, base, vs, j, Hl, Hw, Hv, Ha⟩
  have Hl0 : gxLbl race2o.gdG (1, 0) = some (Lbl.LStore false race2B sdData .WCplain) := rfl
  rw [Hl0, Option.some.injEq] at Hl
  subst Hl
  simp only [lbWr, Option.some.injEq, Prod.mk.injEq] at Hw
  obtain ⟨rfl, rfl⟩ := Hw
  exact ⟨j, Hv, Ha.symm⟩

theorem race2oLen1 : (AxOpsem.grow race2o 1).length = 1 := rfl

theorem race2oOwnWpd (a : Int) (cpu : CPU) :
    ∀ [InvGS_gen .hasNoLC epiGF] [AxannotGS epiGF] (nm : GName),
      ⊢ epiInit3 a race2B nm 1 -∗
        @tierAWpd epiGF .hasNoLC _ _ epiPol race2o GName Unit epiObInterp nm
          (h1oState cpu ibNone) .MaybeStuck 1 (fun _ => iprop(True)) :=
  wpdHart1oOwnSdHwp1 race2o a cpu ibNone race2oFetch1 race2oStoreRow1 race2oSdWriteOk1
    race2oLen1

end Weak
