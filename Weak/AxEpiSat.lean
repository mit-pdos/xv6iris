/-
Weak: **satisfiability of the stage-5 function-epilogue premise bundle** on ONE concrete 1-hart
graph `gepi` (AxSL tier).

Rocq: `iris/AxEpiSat.v` @ xxvzwolszwmp.

## What this file proves

Shape (hart 0; Lean positions 0..1, see deviation 1): `[SD = sd Vs → slot; LD = ld slot (rf
from SD, internal)]` with `slot = 0x2000` (disjoint from the text `[0x1000, 0x100c)`) and gmo =
program order.  The image holds the real RV64 encodings `sd ra,8(sp)` = 0x00113423,
`ld ra,8(sp)` = 0x00813083, `ret` = 0x00008067 (little-endian) on the text, zero elsewhere.

The concrete policy `epiPol`: `sPol GD e := ofList (gmoPrefix GD.gdG e)` (ALL gmo-earlier);
`lobp GD e := {eSD} ∩ eidsBefore GD 0 1` at `e = eLD`, `∅` elsewhere (the `∩ eidsBefore` keeps
`axpolWf` true for EVERY graph).

Checked (`epiSat` bundles it): (1) `rvwmoCatConsistent gepi` (`catConsistentBSound` +
`decide +kernel`); (2) `axpolWf`; (3) the `tierAAdequacyAnnGmo` policy premises
(gmo-predecessors), and `lobp` also meets `flowDev2` (`epiLobpDev2`); (4) `axpolWfL gepi
gepi.gdG.gxGmo`; (5) `ldspOwnOk` at the reload with `Hs := per-byte [(SD, Vs[j])]`, plus
`HlastSpill`, the two lengths, `loadRowOk`, the slot outside the text, and the rf edge.

As AxTierA2's header warns, a concrete certificate proves nothing about the MODEL — only that
this premise bundle is jointly satisfiable.

## Deviations from Rocq

1. O2 STAGE C (fetches are not graph events; rows re-indexed as `AxEpiShape` deviation 1): the
   Rocq row `[F0; SD; F1; LD; F2]` carried the three instruction FETCHES as 4-byte text
   `LLoad`s; Lean's row is `[SD; LD]`, so `eSD = (0, 0)` (Rocq `(0,1)`), `eLD = (0, 1)` (Rocq
   `(0,3)`), `epiLobp` uses `eidsBefore GD 0 1` (Rocq `… 0 3`), and every `… gepi 0 3` premise
   (`ldspOwnOk`, `loadRowOk`) is at `… 0 1`.  Downstream (AxEpiAdeq, AxEpiSound3, AxAllHarts)
   use `epiLobp` on their own re-indexed `c.sdsp; c.ldsp` rows, where the data nodes are again
   `(0,0)`/`(0,1)`.  The image (and the encodings) are kept, though no event reads the text.
2. DROPPED for Stage C: `eF0`/`eF1`/`eF2` (the fetch events), `z4` (their timestamps) and
   `epi_not_dev2` (its witness was the fetch `F0 ∈ sPol SD`; with no fetch, `sPol eSD = ∅` and
   `sPol eLD = {eSD}` is a `flowDev2` edge, so the statement has no Lean counterpart).  None is
   used by any downstream Rocq file.  The `Print Assumptions` audits are not ported (lint).
3. POLICY: Rocq's global `Instance epi_pol` ↦ a reducible `def epiPol : Axpol`, passed
   explicitly (`(self := epiPol)` / `@axpolWf epiPol`), so it never competes with
   `AxProtInst.axprotPol` (downstream `#[local] Existing Instance EpiSat.epi_pol` ↦ pass it).
4. VOCABULARY: `gd_g` ↦ `.gdG`, `Z` ↦ `Int`, `Z_to_bv 8` ↦ `BitVec.ofInt 8`, `l !! n ≫= Some`
   ↦ `l[n]?`, `Z.to_nat` ↦ `Int.toNat`, `list_to_set` ↦ `LawfulSet.ofList`, `last` ↦
   `List.getLast?`, `vm_compute` ↦ `decide +kernel`.  `epiText` is a conjunction (Rocq a chained
   `≤ <`).  `epiLobpDev2`'s `gpoloc` comes from `gpolocBSpec` (Rocq built it by hand); the
   ownership conjunct of `epiLdspOwnOk` uses that a `gpo`-predecessor of `(0,1)` is `(0,0)`.
5. NAMES: duplicated Rocq names and generic short names are file-qualified (`AxEpiSat.*`).

**Rocq → Lean name map.**  `bz` `AxEpiSat.bz`, `enc_sd` `encSd`, `enc_ld` `encLd`, `enc_jr`
`encJr`, `text_base` `AxEpiSat.textBase`, `slot` `AxEpiSat.slot`, `epi_text` `epiText`,
`epi_img` `epiImg`, `Vs` `AxEpiSat.Vs`, `t8` `AxEpiSat.t8`, `row` `AxEpiSat.row`, `eSD`
`AxEpiSat.eSD`, `eLD` `AxEpiSat.eLD`, `gepi` `gepi`, `gepi_cat` `gepiCat`, `gepi_rf` `gepiRf`,
`epi_lobp` `epiLobp`, `epi_pol` `epiPol`, `epi_axpol_wf` `epiAxpolWf`, `gmo_prefix_gmo_lt`
`gmoPrefixGmoLt`, `epi_s_pol_gmo` `epiSPolGmo`, `epi_lobp_gmo` `epiLobpGmo`, `epi_lobp_dev2`
`epiLobpDev2`, `epi_axpol_wf_L` `epiAxpolWfL`, `Hs` `AxEpiSat.Hs`, `Hs_lookup`
`AxEpiSat.hsLookup`, `epi_Hlast_spill` `epiHlastSpill`, `epi_lens` `epiLens`,
`epi_load_row_ok` `epiLoadRowOk`, `epi_slot_not_text` `epiSlotNotText`, `epi_ldsp_own_ok`
`epiLdspOwnOk`, `epi_sat` `epiSat`.  Lean-only: `AxEpiSat.listFindNone`.

**Dropped:** `eF0`, `eF1`, `eF2`, `z4`, `epi_not_dev2` (deviation 2).  Rocq 37 declarations;
Lean 32 + 1 Lean-only.
-/
import Weak.AxTierA3
import Weak.AxLdspWpd
import Weak.AxGraphDec
import Weak.AxBridge
import Weak.AxAdequacyL

namespace Weak

open Iris Iris.Std MachCSL MachCSL.Stdpp
open Lbl

/-! # 1. The graph -/

def AxEpiSat.bz (z : Int) : BitVec 8 := BitVec.ofInt 8 z

def encSd : List (BitVec 8) :=
  [AxEpiSat.bz 0x23, AxEpiSat.bz 0x34, AxEpiSat.bz 0x11, AxEpiSat.bz 0x00]
def encLd : List (BitVec 8) :=
  [AxEpiSat.bz 0x83, AxEpiSat.bz 0x30, AxEpiSat.bz 0x81, AxEpiSat.bz 0x00]
def encJr : List (BitVec 8) :=
  [AxEpiSat.bz 0x67, AxEpiSat.bz 0x80, AxEpiSat.bz 0x00, AxEpiSat.bz 0x00]

def AxEpiSat.textBase : Int := 0x1000
def AxEpiSat.slot : Int := 0x2000

def epiText (a : Int) : Prop := AxEpiSat.textBase ≤ a ∧ a < AxEpiSat.textBase + 12

def epiImg : Image := fun a =>
  if AxEpiSat.textBase ≤ a ∧ a < AxEpiSat.textBase + 12 then
    (encSd ++ encLd ++ encJr)[(a - AxEpiSat.textBase).toNat]?
  else some (AxEpiSat.bz 0)

def AxEpiSat.Vs : List (BitVec 8) :=
  [AxEpiSat.bz 1, AxEpiSat.bz 2, AxEpiSat.bz 3, AxEpiSat.bz 4,
   AxEpiSat.bz 5, AxEpiSat.bz 6, AxEpiSat.bz 7, AxEpiSat.bz 8]

def AxEpiSat.t8 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1]

def AxEpiSat.row : List Lbl :=
  [LStore false AxEpiSat.slot AxEpiSat.Vs .WCplain,
   LLoad false AxEpiSat.slot AxEpiSat.t8 AxEpiSat.Vs]

def AxEpiSat.eSD : Geid := (0, 0)
def AxEpiSat.eLD : Geid := (0, 1)

def gepi : Gdexec :=
  ⟨⟨epiImg, [AxEpiSat.row], [AxEpiSat.eSD, AxEpiSat.eLD]⟩, [], []⟩

/-- (1) -/
theorem gepiCat : rvwmoCatConsistent gepi :=
  catConsistentBSound _ (by decide +kernel)

/-- The reload really is served by the spill (internal rf, byte 0). -/
theorem gepiRf : grfAt gepi.gdG AxEpiSat.slot AxEpiSat.eSD AxEpiSat.eLD :=
  ⟨1, AxEpiSat.bz 1, (grbBSpec _ _ _ _ _).1 (by decide +kernel), by decide +kernel⟩

/-! # 2. The policy instance -/

def epiLobp (GD : Gdexec) (e : Geid) : GSet Geid :=
  if e = AxEpiSat.eLD then ({AxEpiSat.eSD} : GSet Geid) ∩ eidsBefore GD 0 1 else ∅

@[reducible] def epiPol : Axpol :=
  ⟨fun GD e => LawfulSet.ofList (gmoPrefix GD.gdG e), epiLobp⟩

/-- (2) -/
theorem epiAxpolWf : @axpolWf epiPol := by
  intro GD i k x hx
  change x ∈ epiLobp GD (i, k) at hx
  unfold epiLobp at hx
  split at hx
  · rename_i heq
    simp only [AxEpiSat.eLD, Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    exact (elemOfIntersection.1 hx).2
  · exact absurd hx notElemOfEmpty

/-- Lean-only: `listFind` of an absent element fails. -/
theorem AxEpiSat.listFindNone (e : Geid) :
    ∀ l : List Geid, e ∉ l → listFind (fun e' => decide (e' = e)) l = none
  | [], _ => rfl
  | x :: l, h => by
    have hx : x ≠ e := fun h' => h (h' ▸ List.mem_cons_self)
    have hl : e ∉ l := fun h' => h (List.mem_cons_of_mem _ h')
    simp only [listFind, decide_eq_true_eq, hx, if_false, AxEpiSat.listFindNone e l hl,
      Option.map_none]

theorem gmoPrefixGmoLt (G : Gexec) (Hwf : gwf G) (e e' : Geid) :
    e' ∈ gmoPrefix G e → gmoLt G e' e := by
  by_cases he : e ∈ G.gxGmo
  · exact (gmoPrefixSpec G e e' Hwf he).1
  · intro hin
    have h0 : gpos G e = 0 := by
      unfold gpos
      rw [AxEpiSat.listFindNone e G.gxGmo he]
    unfold gmoPrefix at hin
    rw [h0, List.take_zero] at hin
    exact absurd hin List.not_mem_nil

/-- (3) the `tierAAdequacyAnnGmo` policy premises. -/
theorem epiSPolGmo :
    ∀ e e', e' ∈ Axpol.sPol (self := epiPol) gepi e → gmoLt gepi.gdG e' e := by
  intro e e' he'
  exact gmoPrefixGmoLt _ gepiCat.1 e e' (elemOfListToSet.1 he')

theorem epiLobpGmo :
    ∀ e e', e' ∈ Axpol.lobp (self := epiPol) gepi e → gmoLt gepi.gdG e' e := by
  intro e e' he'
  change e' ∈ epiLobp gepi e at he'
  unfold epiLobp at he'
  split at he'
  · rename_i heq
    subst heq
    have h1 := elemOfSingleton.1 (elemOfIntersection.1 he').1
    subst h1
    exact (gmoLtBSpec _ _ _).1 (by decide +kernel)
  · exact absurd he' notElemOfEmpty

/-- `lobp` also meets the stronger `flowDev2` premise (same-byte po + gmo). -/
theorem epiLobpDev2 :
    ∀ e e', e' ∈ Axpol.lobp (self := epiPol) gepi e → flowDev2 gepi e' e := by
  intro e e' he'
  have hlt := epiLobpGmo e e' he'
  change e' ∈ epiLobp gepi e at he'
  unfold epiLobp at he'
  split at he'
  · rename_i heq
    subst heq
    have h1 := elemOfSingleton.1 (elemOfIntersection.1 he').1
    subst h1
    exact .inr ⟨(gpolocBSpec _ _ _).1 (by decide +kernel), hlt⟩
  · exact absurd he' notElemOfEmpty

/-- (4) the gate-free processing order `gxGmo` satisfies `axpolWfL`. -/
theorem epiAxpolWfL : @axpolWfL epiPol gepi gepi.gdG.gxGmo := by
  intro n e hn
  have hpos : gpos gepi.gdG e = n := gposOfLookup _ n e gepiCat.1.1 hn
  refine ⟨?_, ?_⟩
  · intro x hx
    change x ∈ (LawfulSet.ofList (gmoPrefix gepi.gdG e) : GSet Geid) at hx
    unfold gmoPrefix at hx
    rw [hpos] at hx
    exact hx
  · intro e' he'
    obtain ⟨he'In, _, hlt⟩ := epiLobpGmo e e' he'
    rw [hpos] at hlt
    unfold takeL
    rw [elemOfListToSet, elem_of_take]
    exact ⟨gpos gepi.gdG e', gposElemLookup _ e' he'In, hlt⟩

/-! # 3. The reload's ownership premise -/

def AxEpiSat.Hs : List (List Hent) := AxEpiSat.Vs.map (fun v => [(AxEpiSat.eSD, v)])

theorem AxEpiSat.hsLookup (j : Nat) (H : List Hent) :
    AxEpiSat.Hs[j]? = some H → ∃ v, H = [(AxEpiSat.eSD, v)] ∧ AxEpiSat.Vs[j]? = some v := by
  unfold AxEpiSat.Hs
  rw [List.getElem?_map]
  cases hv : AxEpiSat.Vs[j]? with
  | none => intro h; cases h
  | some v => intro h; cases h; exact ⟨v, rfl, rfl⟩

theorem epiHlastSpill : ∀ (j : Nat) (H : List Hent), AxEpiSat.Hs[j]? = some H →
    ∃ v, H.getLast? = some (AxEpiSat.eSD, v) ∧ AxEpiSat.Vs[j]? = some v := by
  intro j H hH
  obtain ⟨v, rfl, hv⟩ := AxEpiSat.hsLookup j H hH
  exact ⟨v, rfl, hv⟩

theorem epiLens : AxEpiSat.Vs.length = 8 ∧ AxEpiSat.Hs.length = 8 := ⟨rfl, rfl⟩

theorem epiLoadRowOk : loadRowOk gepi 0 1 := ⟨_, rfl, rfl⟩

theorem epiSlotNotText : ¬ epiText AxEpiSat.slot := by
  unfold epiText AxEpiSat.slot AxEpiSat.textBase
  omega

theorem epiLdspOwnOk :
    @ldspOwnOk epiPol gepi 0 1 AxEpiSat.eSD AxEpiSat.slot AxEpiSat.Hs := by
  have hbef : AxEpiSat.eSD ∈ eidsBefore gepi 0 1 :=
    (elemOfEidsBefore _ _ _ _).2 ⟨rfl, by decide, by decide +kernel⟩
  refine ⟨?_, hbef, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change AxEpiSat.eSD ∈ epiLobp gepi (0, 1)
    unfold epiLobp
    split
    · exact elemOfIntersection.2 ⟨elemOfSingleton.2 rfl, hbef⟩
    · rename_i hne
      exact absurd rfl hne
  · decide +kernel
  · decide +kernel
  · intro x hx
    exact hx
  · exact ⟨false, AxEpiSat.t8, AxEpiSat.Vs, rfl, rfl, rfl⟩
  · intro j H hH p hp
    obtain ⟨v, rfl, hv⟩ := AxEpiSat.hsLookup j H hH
    rw [List.mem_singleton] at hp
    subst hp
    exact AxEpilogue.gwritesOfStore _ AxEpiSat.eSD false AxEpiSat.slot AxEpiSat.Vs .WCplain j v
      rfl hv
  · intro j H hH n w1 w2 _ hw2
    obtain ⟨v, rfl, _⟩ := AxEpiSat.hsLookup j H hH
    cases n <;> simp at hw2
  · intro j H hH w v' _ hpo
    obtain ⟨v, rfl, _⟩ := AxEpiSat.hsLookup j H hH
    obtain ⟨w1, w2⟩ := w
    obtain ⟨h1, h2, _, _⟩ := hpo
    simp only at h1 h2
    have hw2 : w2 = 0 := by omega
    subst h1 hw2
    exact List.mem_singleton.2 rfl
  · exact (gpoBSpec _ _ _).1 (by decide +kernel)

/-! # 4. The bundle -/

theorem epiSat :
    rvwmoCatConsistent gepi ∧
    @axpolWf epiPol ∧
    (∀ e e', e' ∈ Axpol.sPol (self := epiPol) gepi e → gmoLt gepi.gdG e' e) ∧
    (∀ e e', e' ∈ Axpol.lobp (self := epiPol) gepi e → gmoLt gepi.gdG e' e) ∧
    @axpolWfL epiPol gepi gepi.gdG.gxGmo ∧
    @ldspOwnOk epiPol gepi 0 1 AxEpiSat.eSD AxEpiSat.slot AxEpiSat.Hs ∧
    (∀ (j : Nat) (H : List Hent), AxEpiSat.Hs[j]? = some H →
      ∃ v, H.getLast? = some (AxEpiSat.eSD, v) ∧ AxEpiSat.Vs[j]? = some v) ∧
    AxEpiSat.Vs.length = 8 ∧ AxEpiSat.Hs.length = 8 ∧
    loadRowOk gepi 0 1 ∧ ¬ epiText AxEpiSat.slot ∧
    grfAt gepi.gdG AxEpiSat.slot AxEpiSat.eSD AxEpiSat.eLD :=
  ⟨gepiCat, epiAxpolWf, epiSPolGmo, epiLobpGmo, epiAxpolWfL, epiLdspOwnOk, epiHlastSpill,
    epiLens.1, epiLens.2, epiLoadRowOk, epiSlotNotText, gepiRf⟩

end Weak
