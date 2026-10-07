/-
Weak: **the discriminating 2-hart race witness** for the planned 2-hart epilogue theorem
(AxSL tier).

Rocq: `iris/AxEpiRace2.v` @ xxvzwolszwmp.

## What this file proves

One concrete graph `race2` (Lean positions, deviation 1):
  hart 0 = the two events of `AxEpiSdLdSat.gsdld`
    [`SD = sd sdData → sdAddr` at `(0,0)`; `LD = ld 8 bytes @ldAddr` at `(0,1)`]
    BUT the reload `LD` reads from hart 1's write;
  hart 1 = [`W1 = sd raceData → sdAddr` (plain, 8 bytes, no deps) at `(1,0)`].
gmo = `[SD; W1; LD]`: the writes in gmo order are `SD` (ts 1) then `W1` (ts 2), so `W1` is
coherence-AFTER the spill, and `LD`'s timestamps `[2;..;2]` name `W1` (an external rf).  The
image holds `sdVs` at `[pcSd, pcSd+4)` and hart 1's text `h1Vs` (`c.sdsp ra,8(sp)` = 0xe406)
at `[pc1, pc1+2)`.

Checked: `race2Cat : rvwmoCatConsistent race2` (`decide +kernel`), `race2Value : graphValue
race2 (0,1) = some raceData` with `raceData ≠ sdData`, and EVERY PURE PREMISE of
`epiReloadSound` (AxEpiAdeq) for hart 0 at `a := ldAddr`, policy `epiPol`, EXCEPT `Hharts`,
which is replaced by its 2-hart form `∀ e ∈ gxGmo, e.1 = 0 ∨ e.1 = 1`; `race2Sat` bundles them.

CONSEQUENCE: the pure premises do NOT force `graphValue (0,1) = some sdData` once a second hart
exists, so a 2-hart theorem must use the other hart's WPd premise in a load-bearing way.  As
usual, a concrete certificate proves nothing about the MODEL.

## Deviations from Rocq

1. O2 STAGE C (fetches are not graph events; `AxEpiSdLdSat` deviation 1, `AxEpiAdeq`
   deviation 1): the Rocq rows `[F0; SD; F1; LD]` / `[G0; W1]` carried the instruction fetches
   as text `LLoad`s; the Lean rows are `[SD; LD]` / `[W1]` and gmo is `[SD; W1; LD]` (Rocq
   `[F0; SD; F1; G0; W1; LD]`).  So `eSD = (0,0)` (Rocq `(0,1)`), `eLD = (0,1)` (Rocq `(0,3)`),
   `eW1 = (1,0)` (Rocq `(1,1)`); the load's rf timestamps stay `2`.  The premises follow
   `epiReloadSound`'s Lean form: `fetch_gd_ok race2 0 0 pc_sd sd_vs` / `… 0 2 pc_ld ld_vs` ↦
   `AxCjrWpd.fetchImgOk race2 0 0 pcSd sdVs` / `… 0 1 pcLd AxEpiLedger.ldVs`;
   `store_row_ok … 0 1` ↦ `storeRowOk … 0 0`; `sd_write_ok … 0 1` ↦ `sdWriteOk … 0 0`;
   `load_row_ok … 0 3` ↦ `loadRowOk … 0 1`; `ldsp_own_ok … 0 3 (0,1) … (writen_hist (0,1) …)`
   ↦ `ldspOwnOk … 0 1 (0,0) … (writenHist (0,0) …)`; length `4` ↦ `2`; `gmo_lt (0,1) (0,3)` ↦
   `gmoLt (0,0) (0,1)`; `race2_value`/`race2_not_sd` at `(0,1)`.
2. DROPPED (Stage C): `eF0`, `eF1`, `eG0` (fetch events; downstream Rocq files use them only in
   gmo lists of fetch events, which their ports drop too) and `race2_nw_sd`, `race2_nw_ld`
   (`gis_w` of the fetch events; `epiReloadSound` dropped `Hnw_sd`/`Hnw_ld`, and Lean `(0,0)`
   is the spill, a write).  `race2Sat` drops the two `gis_w` conjuncts accordingly.
   `race2Ntext : ¬ race2Text ldAddr` is KEPT (downstream AxEpiSound2/3 state it), though
   `epiReloadSound` no longer takes a text premise.
3. POLICY: Rocq's `#[local] Existing Instance EpiSat.epi_pol` is not replicated; `ldspOwnOk` is
   stated at `@ldspOwnOk epiPol` explicitly (AxEpiSat convention).
4. VOCABULARY (as `AxEpiSdLdSat` deviation 4): `Z` ↦ `Int` (`pc1 : Nat` like `pcSd`),
   `Z_to_bv 8 0` ↦ `0#8`, `l !! n ≫= Some` ↦ `l[n]?`, `Z.to_nat` ↦ `Int.toNat`, `gd_g` ↦ `.gdG`,
   `vm_compute` ↦ `decide +kernel`; `race2Text` uses conjunctions (Rocq chained `≤ <`).
5. NAMES: duplicated Rocq names are file-qualified (`AxEpiRace2.eSD`/`eLD`); `row0`, `row1`,
   `eW1`, `t2` are also file-qualified (generic names in the shared `namespace Weak`).

**Rocq → Lean name map.**  `pc1` `AxEpiRace2.pc1`, `h1_vs` `h1Vs`, `race2_text` `race2Text`,
`race2_img` `race2Img`, `race_data` `raceData`, `t2` `AxEpiRace2.t2`, `row0` `AxEpiRace2.row0`,
`row1` `AxEpiRace2.row1`, `eSD` `AxEpiRace2.eSD`, `eLD` `AxEpiRace2.eLD`, `eW1`
`AxEpiRace2.eW1`, `race2` `race2`, `race2_cat` `race2Cat`, `race_data_ne` `raceDataNe`,
`race2_value` `race2Value`, `race2_not_sd` `race2NotSd`, `race2_rf` `race2Rf`,
`race2_gmo_sd_w1` `race2GmoSdW1`, `race2_harts` `race2Harts`, `race2_fetch_sd` `race2FetchSd`,
`race2_store_row` `race2StoreRow`, `race2_sd_write_ok` `race2SdWriteOk`, `race2_fetch_ld`
`race2FetchLd`, `race2_ntext` `race2Ntext`, `race2_load_row` `race2LoadRow`,
`race2_Hs1_lookup` `race2Hs1Lookup`, `race2_ldsp_own_ok` `race2LdspOwnOk`, `race2_len`
`race2Len`, `race2_lob_gmo` `race2LobGmo`, `race2_sat` `race2Sat`.

**Dropped:** `eF0`, `eF1`, `eG0`, `race2_nw_sd`, `race2_nw_ld` (deviation 2); the
`Print Assumptions` lines (the lint's axiom check covers them).  Rocq 35 declarations; Lean 30.
-/
import Weak.AxEpiAdeq

namespace Weak

open Iris Iris.Std MachCSL MachCSL.Stdpp
open Lbl

/-! # 1. The graph -/

/-- Hart 1's text: a `c.sdsp ra,8(sp)` (0xe406, little-endian) at `pc1`, outside hart 0's text
`[pcSd, pcSd+4)`. -/
def AxEpiRace2.pc1 : Nat := 0x80000100
def h1Vs : List (BitVec 8) := [0x06#8, 0xe4#8]

def race2Text (a : Int) : Prop :=
  ((pcSd : Int) ≤ a ∧ a < (pcSd : Int) + 4) ∨
  ((AxEpiRace2.pc1 : Int) ≤ a ∧ a < (AxEpiRace2.pc1 : Int) + 2)

def race2Img : Image := fun a =>
  if (pcSd : Int) ≤ a ∧ a < (pcSd : Int) + 4 then sdVs[(a - (pcSd : Int)).toNat]?
  else if (AxEpiRace2.pc1 : Int) ≤ a ∧ a < (AxEpiRace2.pc1 : Int) + 2 then
    h1Vs[(a - (AxEpiRace2.pc1 : Int)).toNat]?
  else some 0#8

/-- Hart 1's value: ra = 0x80000200 (≠ sdData's 0x80000100). -/
def raceData : List (BitVec 8) :=
  [0x00#8, 0x02#8, 0x00#8, 0x80#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8]

def AxEpiRace2.t2 : List Nat := [2, 2, 2, 2, 2, 2, 2, 2]

def AxEpiRace2.row0 : List Lbl :=
  [LStore false sdAddr sdData .WCplain,
   LLoad false ldAddr AxEpiRace2.t2 raceData]

def AxEpiRace2.row1 : List Lbl :=
  [LStore false sdAddr raceData .WCplain]

def AxEpiRace2.eSD : Geid := (0, 0)
def AxEpiRace2.eLD : Geid := (0, 1)
def AxEpiRace2.eW1 : Geid := (1, 0)

def race2 : Gdexec :=
  ⟨⟨race2Img, [AxEpiRace2.row0, AxEpiRace2.row1],
    [AxEpiRace2.eSD, AxEpiRace2.eW1, AxEpiRace2.eLD]⟩, []⟩

theorem race2Cat : rvwmoCatConsistent race2 :=
  catConsistentBSound _ (by decide +kernel)

/-! # 2. The race: the reload reads hart 1's value, not the spill's. -/

theorem raceDataNe : raceData ≠ sdData := by decide +kernel

theorem race2Value : graphValue race2 (0, 1) = some raceData := rfl

theorem race2NotSd : graphValue race2 (0, 1) ≠ some sdData := by
  rw [race2Value]
  intro h
  exact raceDataNe (Option.some.inj h)

/-- The reload is served by hart 1's write (external rf, byte 0). -/
theorem race2Rf : grfAt race2.gdG ldAddr AxEpiRace2.eW1 AxEpiRace2.eLD :=
  ⟨2, 0#8, (grbBSpec _ _ _ _ _).1 (by decide +kernel), by decide +kernel⟩

/-- ... and hart 1's write is gmo-after the spill. -/
theorem race2GmoSdW1 : gmoLt race2.gdG AxEpiRace2.eSD AxEpiRace2.eW1 :=
  (gmoLtBSpec _ _ _).1 (by decide +kernel)

/-! # 3. The pure premises of `epiReloadSound` (hart 0) -/

theorem race2Harts : ∀ e, e ∈ race2.gdG.gxGmo → e.1 = 0 ∨ e.1 = 1 := by
  intro e He
  have hg : race2.gdG.gxGmo = [(0, 0), (1, 0), (0, 1)] := rfl
  rw [hg] at He
  simp only [List.mem_cons, List.not_mem_nil, or_false] at He
  rcases He with rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem race2FetchSd : AxCjrWpd.fetchImgOk race2 0 0 pcSd sdVs := by
  refine ⟨by decide, ?_⟩
  intro j hj
  have hj' : j < 4 := hj
  match j, hj' with
  | 0, _ => decide +kernel
  | 1, _ => decide +kernel
  | 2, _ => decide +kernel
  | 3, _ => decide +kernel

theorem race2StoreRow : storeRowOk race2 0 0 := ⟨_, rfl⟩

theorem race2SdWriteOk : sdWriteOk race2 0 0 ldAddr := by
  refine ⟨by decide +kernel, ?_, rfl⟩
  rintro a' v' ⟨l, base, vs, j, Hl, Hw, Hv, Ha⟩
  have Hl0 : gxLbl race2.gdG (0, 0) = some (Lbl.LStore false sdAddr sdData .WCplain) := rfl
  rw [Hl0, Option.some.injEq] at Hl
  subst Hl
  simp only [lbWr, Option.some.injEq, Prod.mk.injEq] at Hw
  obtain ⟨rfl, rfl⟩ := Hw
  exact ⟨j, Hv, Ha.symm⟩

theorem race2FetchLd : AxCjrWpd.fetchImgOk race2 0 1 pcLd AxEpiLedger.ldVs := by
  refine ⟨by decide, ?_⟩
  intro j hj
  have hj' : j < 2 := hj
  match j, hj' with
  | 0, _ => decide +kernel
  | 1, _ => decide +kernel

theorem race2Ntext : ¬ race2Text ldAddr := by
  unfold race2Text ldAddr spVal pcSd AxEpiRace2.pc1
  omega

theorem race2LoadRow : loadRowOk race2 0 1 := ⟨_, rfl, rfl⟩

theorem race2Hs1Lookup (j : Nat) (H : List Hent) :
    (writenHist (0, 0) sdData epiHs0)[j]? = some H →
    ∃ v, H = [((0, 0), v)] ∧ sdData[j]? = some v :=
  gsdldHs1Lookup j H

/-- The ownership premise: its write clauses only constrain PO-EARLIER writers (hart 0's), so
hart 1's `W1` is invisible to it. -/
theorem race2LdspOwnOk :
    @ldspOwnOk epiPol race2 0 1 (0, 0) ldAddr (writenHist (0, 0) sdData epiHs0) := by
  have hbef : ((0, 0) : Geid) ∈ eidsBefore race2 0 1 :=
    (elemOfEidsBefore _ _ _ _).2 ⟨rfl, by decide, by decide +kernel⟩
  refine ⟨?_, hbef, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change ((0, 0) : Geid) ∈ epiLobp race2 (0, 1)
    unfold epiLobp
    split
    · exact elemOfIntersection.2 ⟨elemOfSingleton.2 rfl, hbef⟩
    · rename_i hne
      exact absurd rfl hne
  · decide +kernel
  · decide +kernel
  · intro x hx
    exact hx
  · exact ⟨false, AxEpiRace2.t2, raceData, rfl, rfl, rfl⟩
  · intro j H hH p hp
    obtain ⟨v, rfl, hv⟩ := race2Hs1Lookup j H hH
    rw [List.mem_singleton] at hp
    subst hp
    exact AxEpilogue.gwritesOfStore _ (0, 0) false sdAddr sdData .WCplain j v rfl hv
  · intro j H hH n w1 w2 _ hw2
    obtain ⟨v, rfl, _⟩ := race2Hs1Lookup j H hH
    cases n <;> simp at hw2
  · intro j H hH w v' _ hpo
    obtain ⟨v, rfl, _⟩ := race2Hs1Lookup j H hH
    obtain ⟨w1, w2⟩ := w
    obtain ⟨h1, h2, _, _⟩ := hpo
    simp only at h1 h2
    have hw2 : w2 = 0 := by omega
    subst h1 hw2
    exact List.mem_singleton.2 rfl
  · exact (gpoBSpec _ _ _).1 (by decide +kernel)

theorem race2Len : (AxOpsem.grow race2 0).length = 2 := rfl

theorem race2LobGmo : gmoLt race2.gdG (0, 0) (0, 1) :=
  (gmoLtBSpec _ _ _).1 (by decide +kernel)

/-! # 4. The bundle: every pure premise of `epiReloadSound` (with the 2-hart `Hharts`) holds
at `race2`, yet the reload reads `raceData`. -/

theorem race2Sat :
    rvwmoCatConsistent race2 ∧
    (∀ e, e ∈ race2.gdG.gxGmo → e.1 = 0 ∨ e.1 = 1) ∧
    AxCjrWpd.fetchImgOk race2 0 0 pcSd sdVs ∧
    storeRowOk race2 0 0 ∧
    sdWriteOk race2 0 0 ldAddr ∧
    AxCjrWpd.fetchImgOk race2 0 1 pcLd AxEpiLedger.ldVs ∧
    ¬ race2Text ldAddr ∧
    loadRowOk race2 0 1 ∧
    @ldspOwnOk epiPol race2 0 1 (0, 0) ldAddr (writenHist (0, 0) sdData epiHs0) ∧
    (AxOpsem.grow race2 0).length = 2 ∧
    gmoLt race2.gdG (0, 0) (0, 1) ∧
    -- the discriminating conclusion
    graphValue race2 (0, 1) = some raceData ∧ raceData ≠ sdData :=
  ⟨race2Cat, race2Harts, race2FetchSd, race2StoreRow, race2SdWriteOk, race2FetchLd, race2Ntext,
    race2LoadRow, race2LdspOwnOk, race2Len, race2LobGmo, race2Value, raceDataNe⟩

end Weak
