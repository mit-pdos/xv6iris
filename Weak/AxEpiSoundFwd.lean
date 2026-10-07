/-
Weak: **`epiReloadSound3Fwd`: `AxEpiSound3.epiReloadSound3` WITHOUT `Hlob_gmo`** (spill
gmo-before the reload), i.e. ALSO covering STORE-FORWARDING graphs (the reload performed
gmo-before its own po-earlier spill).

Rocq: `iris/AxEpiSoundFwd.v` @ xxvzwolszwmp.

## What this file proves

Statement: word for word `epiReloadSound3`'s (Lean forms), minus `Hlob_gmo` (same `ldspOwnOk`
under `epiPol`, same `Hwp1` under `epiPol`).

PROOF (§1): case split on `gmoLt (0,0) (0,1)` (decidable).
(i)  spill gmo-before reload: `epiReloadSound3` itself (ownership + adequacy through the logic).
(ii) otherwise gmo is total on the distinct `gxGmo` members `(0,0)`, `(0,1)` (`gmoLtTotal`), so
     `gmoLt (0,1) (0,0)`: the FORWARDING arm, and `AxFwdSource.epiReloadFwd` gives the
     conclusion as a PURE graph fact (ppo rule 1 + `gloadValue`); neither WPd nor run is used.
FINDING (Rocq, why a meta-level split suffices): at `axGA2` the `gconstInterp` pins the graph,
so an in-logic branch (ii) would only re-inject the same pure fact; its only real effect is to
change the policy, which changes the TYPE of `Hwp1`.  §2 nevertheless builds the design's
GD-dependent policy `fwdPol` and discharges its `axpolWf` / gmo-earlier adequacy premises
WITHOUT `Hlob_gmo`; §2b follows the design route in full: hart 0's WPd under `fwdPol` with the
reload flow case-split ((i) the owned route, (ii) `fwdLoadFlow`: no flow-in, `protInvReadStep`,
deposit `⌜v = sdData⌝`) and the adequacy theorem `epiReloadSound3FwdPol` — identical premises
except `Hwp1` is a WPd under `fwdPol`.

§3 NON-VACUITY: `AxFwdSource.gsdldFwd` (spill moved gmo-LAST) meets EVERY premise — the pure
ones, hart 0's run (the `AxEpiRun` driver: `gsdldFwd`'s image and row are `gsdld`'s, so
`driveGsdldOk` applies verbatim), and a trivial hart 1 (empty row) with its WPd — while
`Hlob_gmo` FAILS there; closed corollaries `epiReloadSound3FwdGsdldFwd` and
`epiReloadSound3FwdPolGsdldFwd`.  Caveat (as Rocq): at `gsdldFwd` hart 1 is absent.

## Deviations from Rocq

1. O2 STAGE C (AxFwdSource deviation 1, AxEpiSound3 deviation 1): the epilogue row is
   `[SD; LD]`: spill `(0,0)` (Rocq `(0,1)`), reload `(0,1)` (Rocq `(0,3)`), row length 2
   (Rocq 4); `Hlob_gmo`/the case split is on `gmoLt (0,0) (0,1)` (Rocq `(0,1) (0,3)`);
   `fwdLobp` is `{eSD} ∩ eidsBefore GD 0 1` (Rocq `eids_before GD 0 3`).  The fetch-event
   premises `Hnw_sd`/`Hnw_ld` (`gis_w` of `(0,0)`/`(0,2)`) and `Hntext`, and the text
   parameter `T`, are DROPPED everywhere (no fetch events, `axGA2`/`tierAAstep` take no `T`);
   so `epiFwdOfNotLob`/`fwdLoadFlow` take no `Hnw_ld` and call `epiReloadFwd` without it, and
   `epiReloadSound3FwdPremises`/`epiReloadSound3FwdNonvac` drop the two `gis_w` conjuncts and
   `¬ sdld_text ld_addr` (as `AxEpiAdeq.epiReloadPremisesGsdld`).  Fetch premises are
   `AxCjrWpd.fetchImgOk GD 0 0 pcSd sdVs` / `fetchImgOk GD 0 1 pcLd ldVs`, rows
   `storeRowOk GD 0 0` / `loadRowOk GD 0 1`, `sdWriteOk GD 0 0 a`,
   `ldspOwnOk GD 0 1 (0,0) a …`.  `fwdLoadFlow`'s non-write fact is `ldspOwnOk`'s
   `gisW (0,1) = false` conjunct, as Rocq.
2. POLICY/INSTANCES (AxEpiAdeq deviation 5, AxEpiSat deviation 3): Rocq's
   `#[local] Existing Instance EpiSat.epi_pol` / `fwd_pol` are not instances — `epiPol` and the
   reducible def `fwdPol` are passed explicitly.  Rocq's local instances `epi_ga2_fwdpol`,
   `epi_ga2_fwd`, `epi_ga2_fwd'` (all `AxGA2 … γ`) are not redeclared: they are
   `AxEpiAdeq.epiGa2 GD0 γ` / `epiGa2 gsdldFwd γ`, passed explicitly.  §2b/§3's section
   lemmas are generic in `hlc` (Rocq `HasNoLc`), as AxEpiAdeq's.  `gmo_lt_dec` is the local
   instance `AxEpiSoundFwd.gmoLtDec`.
3. PROOF ROUTE (not statements): `wpdEpiGa2Fwd`'s branch (i) converts `Hok_ld` to `fwdPol`
   (its `lobp` conjunct) and calls `AxEpiAdeq.wpdEpiGa2` at `fwdPol` (Lean's `wpdEpiGa2` is
   policy-generic; Rocq re-applies `wpd_epi_sd_ld_owned_rb` with `fetch_flow_fwd`).  So
   `fetchFlowFwd` (= `fetchFlowGa2` at `fwdPol`) is ported but unused, like
   `AxEpiAdeq.fetchFlowGa2`.  `vm_compute` ↦ `decide +kernel`.
4. TYPES/INSTANCES of runs (AxEpiRun deviation 4, AxEpiAdeq deviation 7): `epiRunGsdldFwd`
   concludes `nsteps (astepAnyNfGv gsdldFwd 0) …` with no `∀ Σ HG`; `Hrun`s are
   `∀ (_ : AxannotGS epiGF) (nm : GName), nsteps (tierAAstep GD nm i) …`; `Hwp1` is
   `∀ [InvGS_gen .hasNoLC epiGF] [AxannotGS epiGF] nm, ⊢ … -∗ @tierAWpd … pol …`.  `(0%fin :
   CPU)` ↦ `⟨0, by decide⟩`.  Rocq `let GD := gsdld_fwd in` / `let s0_1 := …` are inlined.

**Rocq → Lean name map.**  `gmem_of_gis_w` `gmemOfGisW`, `gmo_lt_dec`
`AxEpiSoundFwd.gmoLtDec` (local instance; dup name), `epi_fwd_of_not_lob` `epiFwdOfNotLob`,
`epi_reload_sound3_fwd` `epiReloadSound3Fwd`, `fwd_lobp` `fwdLobp`, `fwd_pol` `fwdPol`,
`fwd_axpol_wf` `fwdAxpolWf`, `fwd_s_pol_gmo` `fwdSPolGmo`, `fwd_lobp_gmo` `fwdLobpGmo`,
`fetch_flow_fwd` `fetchFlowFwd`, `fwd_load_flow` `fwdLoadFlow`, `fwd_rpost` `fwdRpost`,
`wpd_epi_ga2_fwd` `wpdEpiGa2Fwd`, `epi_reload_sound3_fwd_pol` `epiReloadSound3FwdPol`.  §3
(`Module EpiFwdSat` ↦ plain names) `gsdld_fwd_not_lob` `gsdldFwdNotLob`,
`gsdld_fwd_ldsp_own_ok` `gsdldFwdLdspOwnOk`, `gsdld_fwd_fetch_sd` `gsdldFwdFetchSd`,
`gsdld_fwd_fetch_ld` `gsdldFwdFetchLd`, `epi_reload_sound3_fwd_premises`
`epiReloadSound3FwdPremises`, `epi_run_gsdld_fwd` `epiRunGsdldFwd`, `wpd_hart1_empty`
`wpdHart1Empty`, `epi_reload_sound3_fwd_nonvac` `epiReloadSound3FwdNonvac`,
`epi_reload_sound3_fwd_gsdld_fwd` `epiReloadSound3FwdGsdldFwd`, `wpd_hart1_empty_fwd`
`wpdHart1EmptyFwd`, `epi_reload_sound3_fwd_pol_gsdld_fwd` `epiReloadSound3FwdPolGsdldFwd`.
Not redeclared (deviation 2): `epi_ga2_fwdpol`, `epi_ga2_fwd`, `epi_ga2_fwd'`.

**Dropped:** none (Rocq 25 definitions/lemmas/instances + 3 local instances; Lean 25).
**Not ported:** the `Print Assumptions` lines (the lint's axiom check covers them).
-/
import Weak.AxEpiSound3
import Weak.AxFwdSource
import Weak.AxEpiRun

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D

/-! # 1. THE THEOREM -/

theorem gmemOfGisW (G : Gexec) (e : Geid) : gisW G e = true → gmem G e := by
  unfold gisW gmem
  cases h : gxLbl G e with
  | none => intro hw; cases hw
  | some l =>
    intro hw
    refine ⟨l, rfl, ?_⟩
    simp only at hw
    simp [lbIsMem, hw]

local instance AxEpiSoundFwd.gmoLtDec (G : Gexec) (e1 e2 : Geid) :
    Decidable (gmoLt G e1 e2) := by
  unfold gmoLt; infer_instance

/-- The forwarding arm: if the spill is NOT gmo-before the reload, the reload reads the
spill's data, purely from the graph. -/
theorem epiFwdOfNotLob (GD : Gdexec) (a : Int) (Hs : List (List Hent))
    (Hcons : rvwmoCatConsistent GD)
    (Hw_sd : sdWriteOk GD 0 0 a)
    (Hok_ld : @ldspOwnOk epiPol GD 0 1 (0, 0) a Hs)
    (Hn : ¬ gmoLt GD.gdG (0, 0) (0, 1)) :
    graphValue GD (0, 1) = some sdData := by
  obtain ⟨-, -, Hin3, -, -, ⟨aq, ts0, vs0, Hlbl, -, Hvs⟩, -⟩ := Hok_ld
  have Hwf := Hcons.1
  have Hin1 : ((0, 0) : Geid) ∈ GD.gdG.gxGmo := (Hwf.2.1 _).2 (gmemOfGisW _ _ Hw_sd.1)
  rcases gmoLtTotal GD.gdG (0, 0) (0, 1) Hwf.1 Hin1 Hin3 (by decide) with Hlt | Hfwd
  · exact absurd Hlt Hn
  · exact epiReloadFwd GD a aq ts0 vs0 Hcons Hw_sd Hlbl Hvs Hfwd

theorem epiReloadSound3Fwd (GD : Gdexec) (cpu : CPU) (a b : Int)
    (Hdisj : slotsDisjoint a b)
    (Hcons : rvwmoCatConsistent GD)
    (Hharts : ∀ e, e ∈ GD.gdG.gxGmo → e.1 = 0 ∨ e.1 = 1)
    (Hgd_sd : AxCjrWpd.fetchImgOk GD 0 0 pcSd sdVs)
    (Hrow_sd : storeRowOk GD 0 0)
    (Hw_sd : sdWriteOk GD 0 0 a)
    (Hgd_ld : AxCjrWpd.fetchImgOk GD 0 1 pcLd AxEpiLedger.ldVs)
    (Hrow_ld : loadRowOk GD 0 1)
    (Hok_ld : @ldspOwnOk epiPol GD 0 1 (0, 0) a (writenHist (0, 0) sdData epiHs0))
    (Hlen : (AxOpsem.grow GD 0).length = 2)
    -- NO `Hlob_gmo`
    (sN : Athread) (n : Nat)
    (Hrun : ∀ (_ : AxannotGS epiGF) (nm : GName),
      nsteps (tierAAstep GD nm 0) n
        ⟨.PHart cpu (riscvStep false) (probeRegs pcSd) none ibNone, 0⟩ sN)
    (Hend : sN.atK = (AxOpsem.grow GD 0).length)
    (s0_1 sN1 : Athread) (n1 : Nat)
    (Hk1 : s0_1.atK = 0)
    (Hrun1 : ∀ (_ : AxannotGS epiGF) (nm : GName), nsteps (tierAAstep GD nm 1) n1 s0_1 sN1)
    (Hend1 : sN1.atK = (AxOpsem.grow GD 1).length)
    (Hwp1 : ∀ [InvGS_gen .hasNoLC epiGF] [AxannotGS epiGF] (nm : GName),
      ⊢ epiInit3 a b nm 1 -∗
        @tierAWpd epiGF .hasNoLC _ _ epiPol GD GName Unit epiObInterp nm s0_1 .MaybeStuck 1
          (fun _ => iprop(True))) :
    graphValue GD (0, 1) = some sdData := by
  by_cases Hlob_gmo : gmoLt GD.gdG (0, 0) (0, 1)
  · exact epiReloadSound3 GD cpu a b Hdisj Hcons Hharts Hgd_sd Hrow_sd Hw_sd Hgd_ld Hrow_ld
      Hok_ld Hlen Hlob_gmo sN n Hrun Hend s0_1 sN1 n1 Hk1 Hrun1 Hend1 Hwp1
  · exact epiFwdOfNotLob GD a _ Hcons Hw_sd Hok_ld Hlob_gmo

/-! # 2. THE GD-DEPENDENT POLICY `fwdPol` (the design's policy; for reuse)

`lobp GD (0,1) := {(0,0)} ∩ eidsBefore GD 0 1` if the spill is gmo-before the reload, `∅`
otherwise.  Its adequacy side conditions hold on EVERY consistent graph, with no `Hlob_gmo`. -/

def fwdLobp (GD : Gdexec) (e : Geid) : GSet Geid :=
  if e = AxEpiSat.eLD then
    if gmoLt GD.gdG AxEpiSat.eSD AxEpiSat.eLD then
      ({AxEpiSat.eSD} : GSet Geid) ∩ eidsBefore GD 0 1
    else ∅
  else ∅

@[reducible] def fwdPol : Axpol :=
  ⟨fun GD e => LawfulSet.ofList (gmoPrefix GD.gdG e), fwdLobp⟩

theorem fwdAxpolWf : @axpolWf fwdPol := by
  intro GD i k x hx
  change x ∈ fwdLobp GD (i, k) at hx
  unfold fwdLobp at hx
  split at hx
  · rename_i heq
    simp only [AxEpiSat.eLD, Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    split at hx
    · exact (elemOfIntersection.1 hx).2
    · exact absurd hx notElemOfEmpty
  · exact absurd hx notElemOfEmpty

theorem fwdSPolGmo (GD : Gdexec) (Hcons : rvwmoCatConsistent GD) :
    ∀ e e', e' ∈ Axpol.sPol (self := fwdPol) GD e → gmoLt GD.gdG e' e :=
  fun e e' he' => gmoPrefixGmoLt _ Hcons.1 e e' (elemOfListToSet.1 he')

theorem fwdLobpGmo (GD : Gdexec) :
    ∀ e e', e' ∈ Axpol.lobp (self := fwdPol) GD e → gmoLt GD.gdG e' e := by
  intro e e' he'
  change e' ∈ fwdLobp GD e at he'
  unfold fwdLobp at he'
  split at he'
  · rename_i heq
    subst heq
    split at he'
    · rename_i hlt
      have h1 := elemOfSingleton.1 (elemOfIntersection.1 he').1
      subst h1
      exact hlt
    · exact absurd he' notElemOfEmpty
  · exact absurd he' notElemOfEmpty

/-! # 2b. THE DESIGN ROUTE: hart 0's WPd under `fwdPol`, the reload flow case-split on
`gmoLt (0,0) (0,1)` INSIDE the logic -/

section fwdGa2
variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF] [AxannotGS GF]
  [AxlogG GF Hent]

/-- `AxEpiAdeq.fetchFlowGa2` at `fwdPol`. -/
theorem fetchFlowFwd (GD0 : Gdexec) (γ : GName) (i : Agent) (k : Nat)
    (Hnw : gisW GD0.gdG (i, k) = false) :
    ∀ (GD : Gdexec) (ls : @AxirisG.logTsT GF (epiGa2 GD0 γ)), rvwmoCatConsistent GD →
      AxirisG.gconstInterp (self := epiGa2 (GF := GF) GD0 γ) GD ∗
          AxirisG.localInterp (self := epiGa2 (GF := GF) GD0 γ) GD i k ls ⊢
        @fetchFlow hlc GF _ (epiGa2 GD0 γ) fwdPol GD i k :=
  @fetchFlowGa2 hlc GF _ _ _ fwdPol GD0 γ i k Hnw

/-- Branch (ii)'s reload flow: no flow-in, value from the pinned graph. -/
theorem fwdLoadFlow (GD0 : Gdexec) (γ : GName) (a : Int) (Hs : List (List Hent))
    (Hw_sd : sdWriteOk GD0 0 0 a)
    (Hok_ld : @ldspOwnOk epiPol GD0 0 1 (0, 0) a Hs)
    (Hn : ¬ gmoLt GD0.gdG (0, 0) (0, 1)) :
    ⊢ ∀ (GD : Gdexec) (ls : @AxirisG.logTsT GF (epiGa2 GD0 γ)) (w : List (BitVec 8)),
        ⌜rvwmoCatConsistent GD⌝ -∗
        □ AxirisG.gconstInterp (self := epiGa2 (GF := GF) GD0 γ) GD -∗
        AxirisG.localInterp (self := epiGa2 (GF := GF) GD0 γ) GD 0 1 ls -∗
        ⌜graphValue GD (0, 1) = some w⌝ -∗
        @loadFlowRes hlc GF _ (epiGa2 GD0 γ) fwdPol GD 0 1 iprop(⌜w = sdData⌝)
          (ldRb (axG := epiGa2 GD0 γ) 0 1 sdData) := by
  iintro %GD %ls %w %Hc #Hg _ %Hgv
  have hg : AxirisG.gconstInterp (self := epiGa2 (GF := GF) GD0 γ) GD ⊢ ⌜GD = GD0⌝ := by
    show iprop(⌜GD = GD0⌝) ⊢ iprop(⌜GD = GD0⌝)
    exact .rfl
  ihave %Heq := hg $$ Hg
  subst GD
  have Hgv0 := epiFwdOfNotLob GD0 a Hs Hc Hw_sd Hok_ld Hn
  have Hw : w = sdData := by
    rw [Hgv0] at Hgv
    exact (Option.some.inj Hgv).symm
  obtain ⟨-, -, -, Hnw3, -⟩ := Hok_ld
  have hloc : ⊢ AxirisG.localInterp (self := epiGa2 (GF := GF) GD0 γ) GD0 0 (1 + 1) () := by
    show ⊢ iprop(True)
    itrivial
  letI : AxirisG GF := epiGa2 GD0 γ
  unfold loadFlowRes
  iintro %na ⟨Hpg, Hannot⟩
  ihave %Hnin := naAtProgressNotElemOf GD0 0 1 na $$ Hpg
  imod (annotAlloc na (0, 1) iprop(⌜w = sdData⌝) Hnin) $$ Hannot with ⟨Hannot, Hfrag⟩
  imodintro
  inext
  imodintro
  iexists (∅ : Mea GF), (∅ : Mea GF), ()
  isplitr
  · iapply AxProtGate.naSplittingWfEmpty
  isplitr
  · unfold flowEqDyn
    iintro %σ %sOb %Hsub %Hnin' Hob -
    iapply fupd_mask_intro LawfulSet.empty_subset
    iintro Hclose
    inext
    imod Hclose
    imodintro
    iexists σ
    isplitl [Hob]
    · iapply protInvReadStep γ GD0 sOb (0, 1) Hnin' Hnw3
      iexact Hob
    · ipureintro
      exact Hw
  isplitl [Hannot]
  · rw [AxProtGate.annotInsertEq]
    iexact Hannot
  isplitl []
  · iapply hloc
  · unfold ldRb
    iexists GD0, w
    isplitl [Hfrag]
    · iexact Hfrag
    isplitr
    · ipureintro
      exact Hgv
    · iexact Hg

/-- The readback of `wpdEpiGa2`, verbatim. -/
theorem fwdRpost (GD0 : Gdexec) (γ : GName) :
    ⊢ ldRb (axG := epiGa2 (GF := GF) GD0 γ) 0 1 sdData -∗
      ∀ (GD : Gdexec) (s1 : Athread), ⌜s1.atK = (AxOpsem.grow GD 0).length⌝ -∗
        @postLifting GF (epiGa2 GD0 γ) (fun s => iprop(⌜epiPost GD0 0 s⌝)) 0 s1 := by
  have hg : ∀ GD', AxirisG.gconstInterp (self := epiGa2 (GF := GF) GD0 γ) GD' ⊢ ⌜GD' = GD0⌝ := by
    intro GD'
    show iprop(⌜GD' = GD0⌝) ⊢ iprop(⌜GD' = GD0⌝)
    iintro %h
    ipureintro
    exact h
  unfold ldRb
  iintro ⟨%GD', %v, Hfrag, %Hgv, #Hg⟩ %GD %s1 %_
  ihave %HGD := hg GD' $$ Hg
  rw [HGD] at Hgv
  unfold postLifting
  iintro %na Hna
  have hag : AxirisG.annotInterp (self := epiGa2 (GF := GF) GD0 γ) na ∗
      AxAnnot.annotOwn (0, 1) iprop(⌜v = sdData⌝) ⊢
      iprop(⌜(0, 1) ∈ (FiniteMap.dom_set na : GSet Geid)⌝ ∗
        AxWp.fromOption (fun P' => iprop(▷ □ (P' -∗ ⌜v = sdData⌝))) iprop(emp)
          (get? na (0, 1))) := by
    iintro ⟨Hna, Hp⟩
    iapply annotAgree na (0, 1) iprop(⌜v = sdData⌝) $$ Hna Hp
  cases hget : get? na (0, 1) with
  | none =>
    rw [hget] at hag
    simp only [AxWp.fromOption] at hag
    icases persistent_entails_left hag $$ [$Hna $Hfrag] with ⟨-, %Hdom, -⟩
    have h := elemOfDom.1 Hdom
    rw [hget] at h
    cases h
  | some P0 =>
    rw [hget] at hag
    simp only [AxWp.fromOption] at hag
    icases persistent_entails_left hag $$ [$Hna $Hfrag] with ⟨⟨Hna, -⟩, %Hdom, #Hw⟩
    imodintro
    isplitl [Hna]
    · iexact Hna
    iintro Hbig
    have Hlk : ([∗map] e ↦ R ∈ na, if e.1 = 0 then R else iprop(True)) ⊢ P0 :=
      (BigSepM.bigSepM_lookup (Φ := fun e R => if e.1 = 0 then R else iprop(True)) hget).trans
        (by dsimp only; rw [if_pos rfl])
    ihave HP0 := Hlk $$ Hbig
    inext
    ihave Hpp := Hw $$ HP0
    icases Hpp with %Hv
    imodintro
    ipureintro
    intro _
    rw [← Hv]
    exact Hgv

/-- Hart 0's WPd under `fwdPol`, NO `Hlob_gmo`. -/
theorem wpdEpiGa2Fwd (GD0 : Gdexec) (γ : GName) (cpu : CPU) (ib : Ibch) (a : Int)
    (Hgd_sd : AxCjrWpd.fetchImgOk GD0 0 0 pcSd sdVs)
    (Hrow_sd : storeRowOk GD0 0 0)
    (Hw_sd : sdWriteOk GD0 0 0 a)
    (Hgd_ld : AxCjrWpd.fetchImgOk GD0 0 1 pcLd AxEpiLedger.ldVs)
    (Hrow_ld : loadRowOk GD0 0 1)
    (Hok_ld : @ldspOwnOk epiPol GD0 0 1 (0, 0) a (writenHist (0, 0) sdData epiHs0))
    (Hlen : (AxOpsem.grow GD0 0).length = 2) :
    ⊢ ([∗list] j ↦ H ∈ epiHs0, histAuth (GF := GF) γ (a + (j : Int)) 1 H) -∗
      @wpd hlc GF _ (epiGa2 GD0 γ) fwdPol .MaybeStuck 0
        ⟨.PHart cpu (riscvStep false) (probeRegs pcSd) none ib, 0⟩
        (fun s => iprop(⌜epiPost GD0 0 s⌝)) := by
  by_cases Hlt : gmoLt GD0.gdG (0, 0) (0, 1)
  · -- (i) the spill is gmo-before the reload: the ownership route
    have Hok' : @ldspOwnOk fwdPol GD0 0 1 (0, 0) a (writenHist (0, 0) sdData epiHs0) := by
      obtain ⟨H1, Hrest⟩ := Hok_ld
      refine ⟨?_, Hrest⟩
      change ((0, 0) : Geid) ∈ fwdLobp GD0 (0, 1)
      change ((0, 0) : Geid) ∈ epiLobp GD0 (0, 1) at H1
      have he : ((0, 1) : Geid) = AxEpiSat.eLD := rfl
      unfold fwdLobp
      unfold epiLobp at H1
      rw [if_pos he] at H1
      rw [if_pos he]
      split
      · exact H1
      · rename_i hn
        exact absurd Hlt hn
    exact @wpdEpiGa2 hlc GF _ _ _ fwdPol GD0 γ cpu ib a Hgd_sd Hrow_sd Hw_sd Hgd_ld Hrow_ld Hok'
      Hlen
  · -- (ii) forwarding: the reload flow needs no token
    have Hpre : ⊢ ∀ (GD : Gdexec) (s1 : Athread), ⌜s1.atK ≤ 0 + 1⌝ -∗
        ⌜s1.atK = (AxOpsem.grow GD 0).length⌝ -∗
        @postLifting GF (epiGa2 GD0 γ) (fun s => iprop(⌜epiPost GD0 0 s⌝)) 0 s1 := by
      iintro %GD %s1 %Hle %_
      iapply (@postLiftingTrue GF (epiGa2 GD0 γ) fwdPol (fun s => iprop(⌜epiPost GD0 0 s⌝)) 0
        s1)
      iintro _
      ipureintro
      intro h
      omega
    have Hpost : ⊢ ldRb (axG := epiGa2 GD0 γ) 0 (0 + 1) sdData -∗
        ∀ (GD : Gdexec) (s1 : Athread), ⌜s1.atK = (AxOpsem.grow GD 0).length⌝ -∗
          @postLifting GF (epiGa2 GD0 γ) (fun s => iprop(⌜epiPost GD0 0 s⌝)) 0 s1 :=
      fwdRpost GD0 γ
    have HL : ⊢ ∀ (GD : Gdexec) (ls : @AxirisG.logTsT GF (epiGa2 GD0 γ)) (w : List (BitVec 8)),
        ⌜rvwmoCatConsistent GD⌝ -∗
        □ AxirisG.gconstInterp (self := epiGa2 (GF := GF) GD0 γ) GD -∗
        AxirisG.localInterp (self := epiGa2 (GF := GF) GD0 γ) GD 0 (0 + 1) ls -∗
        ⌜graphValue GD (0, 0 + 1) = some w⌝ -∗
        @loadFlowRes hlc GF _ (epiGa2 GD0 γ) fwdPol GD 0 (0 + 1) iprop(⌜w = sdData⌝)
          (ldRb (axG := epiGa2 GD0 γ) 0 (0 + 1) sdData) :=
      fwdLoadFlow GD0 γ a _ Hw_sd Hok_ld Hlt
    have HF := @storeFlowOwned hlc GF _ (epiGa2 GD0 γ) fwdPol _ _ γ (obEqGa2 GD0 γ)
      (annEqGa2 GD0 γ) 0 0 a epiHs0 rfl (pinGa2 GD0 γ (fun GD => sdWriteOk GD 0 0 a) Hw_sd)
      (fun GD ls _ => locGa2 GD0 γ GD 0 0 ls)
    iintro Hauths
    iapply (@wpdEpiSdLdRes2 hlc GF _ (epiGa2 GD0 γ) fwdPol 0
      (fun s => iprop(⌜epiPost GD0 0 s⌝)) cpu ib 0 (fun _ w => iprop(⌜w = sdData⌝))
      (AxAnnot.annotOwn (0, 0) (sdTok γ a (writenHist (0, 0) sdData epiHs0) (0, 0)))
      (ldRb (axG := epiGa2 GD0 γ) 0 (0 + 1) sdData)
      (pinGa2 GD0 γ (fun GD => AxCjrWpd.fetchImgOk GD 0 0 pcSd sdVs) Hgd_sd)
      (pinGa2 GD0 γ (fun GD => storeRowOk GD 0 0) Hrow_sd)
      (pinGa2 GD0 γ (fun GD => AxCjrWpd.fetchImgOk GD 0 (0 + 1) pcLd AxEpiLedger.ldVs) Hgd_ld)
      (pinGa2 GD0 γ (fun GD => loadRowOk GD 0 (0 + 1)) Hrow_ld)
      (pinGa2 GD0 γ (fun GD => (AxOpsem.grow GD 0).length = 0 + 2) Hlen)) $$ [Hauths] [] [] []
    · iapply HF
      iexact Hauths
    · iintro _
      iapply HL
    · iapply Hpre
    · iapply Hpost

end fwdGa2

/-- Adequacy at `fwdPol`: `epiReloadSound3` minus `Hlob_gmo`, with `Hwp1` a WPd under
`fwdPol` (hart-1 events have `lobp = ∅` under both policies). -/
theorem epiReloadSound3FwdPol (GD : Gdexec) (cpu : CPU) (a b : Int)
    (Hdisj : slotsDisjoint a b)
    (Hcons : rvwmoCatConsistent GD)
    (Hharts : ∀ e, e ∈ GD.gdG.gxGmo → e.1 = 0 ∨ e.1 = 1)
    (Hgd_sd : AxCjrWpd.fetchImgOk GD 0 0 pcSd sdVs)
    (Hrow_sd : storeRowOk GD 0 0)
    (Hw_sd : sdWriteOk GD 0 0 a)
    (Hgd_ld : AxCjrWpd.fetchImgOk GD 0 1 pcLd AxEpiLedger.ldVs)
    (Hrow_ld : loadRowOk GD 0 1)
    (Hok_ld : @ldspOwnOk epiPol GD 0 1 (0, 0) a (writenHist (0, 0) sdData epiHs0))
    (Hlen : (AxOpsem.grow GD 0).length = 2)
    (sN : Athread) (n : Nat)
    (Hrun : ∀ (_ : AxannotGS epiGF) (nm : GName),
      nsteps (tierAAstep GD nm 0) n
        ⟨.PHart cpu (riscvStep false) (probeRegs pcSd) none ibNone, 0⟩ sN)
    (Hend : sN.atK = (AxOpsem.grow GD 0).length)
    (s0_1 sN1 : Athread) (n1 : Nat)
    (Hk1 : s0_1.atK = 0)
    (Hrun1 : ∀ (_ : AxannotGS epiGF) (nm : GName), nsteps (tierAAstep GD nm 1) n1 s0_1 sN1)
    (Hend1 : sN1.atK = (AxOpsem.grow GD 1).length)
    (Hwp1 : ∀ [InvGS_gen .hasNoLC epiGF] [AxannotGS epiGF] (nm : GName),
      ⊢ epiInit3 a b nm 1 -∗
        @tierAWpd epiGF .hasNoLC _ _ fwdPol GD GName Unit epiObInterp nm s0_1 .MaybeStuck 1
          (fun _ => iprop(True))) :
    graphValue GD (0, 1) = some sdData := by
  let s00 : Athread := ⟨.PHart cpu (riscvStep false) (probeRegs pcSd) none ibNone, 0⟩
  let s0 : Agent → Athread := fun i => if i = 0 then s00 else s0_1
  let sNf : Agent → Athread := fun i => if i = 0 then sN else sN1
  let nf : Agent → Nat := fun i => if i = 0 then n else n1
  have Hin01 : ∀ i : Agent, i ∈ [0, 1] → i = 0 ∨ i = 1 := by
    intro i Hi
    simp only [List.mem_cons, List.not_mem_nil, _root_.or_false] at Hi
    exact Hi
  have Hharts' : ∀ e, e ∈ GD.gdG.gxGmo → e.1 ∈ [0, 1] := by
    intro e He
    rcases Hharts e He with h | h <;> rw [h] <;> simp
  have HrunA : ∀ (Hann : AxannotGS epiGF) (nm : GName) i, i ∈ [0, 1] →
      nsteps (tierAAstep GD nm i) (nf i) (s0 i) (sNf i) := by
    intro Hann nm i Hi
    rcases Hin01 i Hi with rfl | rfl
    · exact Hrun Hann nm
    · exact Hrun1 Hann nm
  have Hk0 : ∀ i, i ∈ [0, 1] → (s0 i).atK = 0 := by
    intro i Hi
    rcases Hin01 i Hi with rfl | rfl
    · rfl
    · exact Hk1
  have HendA : ∀ i, i ∈ [0, 1] → (sNf i).atK = (AxOpsem.grow GD i).length := by
    intro i Hi
    rcases Hin01 i Hi with rfl | rfl
    · exact Hend
    · exact Hend1
  have Hwp : ∀ [InvGS_gen .hasNoLC epiGF] [AxannotGS epiGF] (nm : GName),
      ⊢ ([∗list] i ∈ [0, 1], epiInit3 a b nm i) -∗
        [∗list] i ∈ [0, 1],
          @tierAWpd epiGF .hasNoLC _ _ fwdPol GD GName Unit epiObInterp nm (s0 i) .MaybeStuck i
            (fun s => iprop(⌜epiPost2 GD i s⌝)) := by
    intro _ _ nm
    have HA : ⊢ ([∗list] j ↦ H ∈ epiHs0, histAuth (GF := epiGF) nm (a + (j : Int)) 1 H) -∗
        @tierAWpd epiGF .hasNoLC _ _ fwdPol GD GName Unit epiObInterp nm (s0 0) .MaybeStuck 0
          (fun s => iprop(⌜epiPost2 GD 0 s⌝)) := by
      have h := wpdEpiGa2Fwd (hlc := .hasNoLC) (GF := epiGF) GD nm cpu ibNone a
        Hgd_sd Hrow_sd Hw_sd Hgd_ld Hrow_ld Hok_ld Hlen
      unfold tierAWpd
      refine h.trans (wand_mono .rfl ?_)
      exact @wpdMono .hasNoLC epiGF _ (axGA2 GD GName Unit epiObInterp nm) fwdPol _ _ _ _ _
        (fun _ => pure_mono (fun hp _ => hp))
    have HB : ⊢ epiInit3 a b nm 1 -∗
        @tierAWpd epiGF .hasNoLC _ _ fwdPol GD GName Unit epiObInterp nm (s0 1)
        .MaybeStuck 1 (fun s => iprop(⌜epiPost2 GD 1 s⌝)) := by
      have h := Hwp1 nm
      unfold tierAWpd at h
      unfold tierAWpd
      exact h.trans (wand_mono .rfl (@wpdMono .hasNoLC epiGF _
        (axGA2 GD GName Unit epiObInterp nm) fwdPol _ _ _
        _ _ (fun _ => pure_intro (fun h => absurd h (by decide)))))
    iintro Hi
    ihave Hi := BigSepL.bigSepL_cons.1 $$ Hi
    icases Hi with ⟨Hi0, Hi1⟩
    ihave Hi1 := BigSepL.bigSepL_singleton.1 $$ Hi1
    ihave Hi0 := (AxEpiSound3.epiInit3Zero a b nm).1 $$ Hi0
    iapply BigSepL.bigSepL_cons.2
    isplitl [Hi0]
    · iapply HA $$ Hi0
    iapply BigSepL.bigSepL_singleton.2
    iapply HB $$ Hi1
  have Hfin := @tierAAdequacyAnnGmo epiGF _ _ fwdPol GD GName Unit epiObInterp (epiInit3 a b)
    fwdAxpolWf Hcons [0, 1] (by decide) Hharts' s0 sNf nf HrunA Hk0 HendA
    (epiPost2 GD) Hwp (epiHobAlloc3 a b Hdisj GD) (fwdSPolGmo GD Hcons) (fwdLobpGmo GD) 0
    (by simp)
  exact Hfin rfl (by show sN.atK = 2; rw [Hend, Hlen])

/-! # 3. NON-VACUITY at `AxFwdSource.gsdldFwd` -/

theorem gsdldFwdNotLob : ¬ gmoLt gsdldFwd.gdG (0, 0) (0, 1) := by
  intro h
  have h' := (gmoLtBSpec _ _ _).2 h
  revert h'
  decide +kernel

theorem gsdldFwdLdspOwnOk :
    @ldspOwnOk epiPol gsdldFwd 0 1 (0, 0) ldAddr (writenHist (0, 0) sdData epiHs0) := by
  have hbef : ((0, 0) : Geid) ∈ eidsBefore gsdldFwd 0 1 :=
    (elemOfEidsBefore _ _ _ _).2 ⟨rfl, by decide, by decide +kernel⟩
  refine ⟨?_, hbef, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change ((0, 0) : Geid) ∈ epiLobp gsdldFwd (0, 1)
    unfold epiLobp
    split
    · exact elemOfIntersection.2 ⟨elemOfSingleton.2 rfl, hbef⟩
    · rename_i hne
      exact absurd rfl hne
  · decide +kernel
  · decide +kernel
  · intro x hx
    exact hx
  · exact ⟨false, [1, 1, 1, 1, 1, 1, 1, 1], sdData, rfl, rfl, rfl⟩
  · intro j H hH p hp
    obtain ⟨v, rfl, hv⟩ := gsdldHs1Lookup j H hH
    rw [List.mem_singleton] at hp
    subst hp
    exact AxEpilogue.gwritesOfStore _ (0, 0) false sdAddr sdData .WCplain j v rfl hv
  · intro j H hH n w1 w2 _ hw2
    obtain ⟨v, rfl, _⟩ := gsdldHs1Lookup j H hH
    cases n <;> simp at hw2
  · intro j H hH w v' _ hpo
    obtain ⟨v, rfl, _⟩ := gsdldHs1Lookup j H hH
    obtain ⟨w1, w2⟩ := w
    obtain ⟨h1, h2, _, _⟩ := hpo
    simp only at h1 h2
    have hw2 : w2 = 0 := by omega
    subst h1 hw2
    exact List.mem_singleton.2 rfl
  · exact (gpoBSpec _ _ _).1 (by decide +kernel)

theorem gsdldFwdFetchSd : AxCjrWpd.fetchImgOk gsdldFwd 0 0 pcSd sdVs := by
  refine ⟨by decide, ?_⟩
  intro j hj
  have hj' : j < 4 := hj
  match j, hj' with
  | 0, _ => decide +kernel
  | 1, _ => decide +kernel
  | 2, _ => decide +kernel
  | 3, _ => decide +kernel

theorem gsdldFwdFetchLd : AxCjrWpd.fetchImgOk gsdldFwd 0 1 pcLd AxEpiLedger.ldVs := by
  refine ⟨by decide, ?_⟩
  intro j hj
  have hj' : j < 2 := hj
  match j, hj' with
  | 0, _ => decide +kernel
  | 1, _ => decide +kernel

/-- Every PURE premise of `epiReloadSound3Fwd` (with `a := ldAddr`, `b := race2B`), and
`Hlob_gmo` FAILS. -/
theorem epiReloadSound3FwdPremises :
    slotsDisjoint ldAddr race2B ∧
    rvwmoCatConsistent gsdldFwd ∧
    (∀ e, e ∈ gsdldFwd.gdG.gxGmo → e.1 = 0 ∨ e.1 = 1) ∧
    AxCjrWpd.fetchImgOk gsdldFwd 0 0 pcSd sdVs ∧
    storeRowOk gsdldFwd 0 0 ∧
    sdWriteOk gsdldFwd 0 0 ldAddr ∧
    AxCjrWpd.fetchImgOk gsdldFwd 0 1 pcLd AxEpiLedger.ldVs ∧
    loadRowOk gsdldFwd 0 1 ∧
    @ldspOwnOk epiPol gsdldFwd 0 1 (0, 0) ldAddr (writenHist (0, 0) sdData epiHs0) ∧
    (AxOpsem.grow gsdldFwd 0).length = 2 ∧
    -- the dropped premise fails: a genuine forwarding graph
    ¬ gmoLt gsdldFwd.gdG (0, 0) (0, 1) := by
  refine ⟨?_, gsdldFwdCat, ?_, gsdldFwdFetchSd, ⟨_, rfl⟩, gsdldFwdSdWriteOk, gsdldFwdFetchLd,
    ⟨_, rfl, rfl⟩, gsdldFwdLdspOwnOk, rfl, gsdldFwdNotLob⟩
  · unfold slotsDisjoint race2B
    omega
  · intro e He
    have hg : gsdldFwd.gdG.gxGmo = [(0, 1), (0, 0)] := rfl
    rw [hg] at He
    simp only [List.mem_cons, List.not_mem_nil, _root_.or_false] at He
    rcases He with rfl | rfl <;> exact .inl rfl

/-- Hart 0's run: `gsdldFwd`'s image and row are `gsdld`'s, so the driver run is the same
computation. -/
theorem epiRunGsdldFwd (cpu : CPU) :
    ∃ n sN, sN.atK = (AxOpsem.grow gsdldFwd 0).length ∧
      nsteps (astepAnyNfGv gsdldFwd 0) n
        ⟨.PHart cpu (riscvStep false) (probeRegs pcSd) none ibNone, 0⟩ sN := by
  have Hok := driveGsdldOk
  unfold driveGsdldB at Hok
  cases Hd : driveGsdld with
  | none => rw [Hd] at Hok; exact absurd Hok Bool.false_ne_true
  | some r =>
    obtain ⟨m, rs, ib, k⟩ := r
    have Hd' : drive gsdldFwd.gdG.gxImg (AxOpsem.grow gsdldFwd 0) 2 runFuel (riscvStep false)
        (probeRegs pcSd) ibNone 0 = some (m, rs, ib, k) := Hd
    obtain ⟨Hk, n, Hr⟩ := driveSound gsdldFwd 0 2 runFuel _ _ _ _ m rs ib k Hd'
    subst Hk
    exact ⟨n, AxEpiRun.st cpu m rs ib 2, rfl, Hr cpu⟩

section h1
variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF] [AxannotGS GF]
  [AxlogG GF Hent]

/-- Hart 1: an empty row; any thread at position 0 is at its row end. -/
theorem wpdHart1Empty (γ : GName) (s : Athread) (Hk : s.atK = 0) :
    ⊢ @wpd hlc GF _ (epiGa2 gsdldFwd γ) epiPol .MaybeStuck 1 s (fun _ => iprop(True)) := by
  have Hle : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (self := epiGa2 (GF := GF) gsdldFwd γ) GD ⊢
        ⌜(AxOpsem.grow GD 1).length ≤ 0⌝ :=
    pinGa2 gsdldFwd γ (fun GD => (AxOpsem.grow GD 1).length ≤ 0) (Nat.le_refl 0)
  iapply (@wpdPastRowEnd hlc GF _ (epiGa2 gsdldFwd γ) epiPol 1 (fun _ => iprop(True))
    (fun s0 => s0.atK = 0) 0 s Hk (fun _ h => h) Hle)
  iintro %GD %s1 %_ %_
  iapply (@postLiftingTrue GF (epiGa2 gsdldFwd γ) epiPol (fun _ => iprop(True)) 1 s1 .rfl)

/-- The same at `fwdPol`. -/
theorem wpdHart1EmptyFwd (γ : GName) (s : Athread) (Hk : s.atK = 0) :
    ⊢ @wpd hlc GF _ (epiGa2 gsdldFwd γ) fwdPol .MaybeStuck 1 s (fun _ => iprop(True)) := by
  have Hle : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (self := epiGa2 (GF := GF) gsdldFwd γ) GD ⊢
        ⌜(AxOpsem.grow GD 1).length ≤ 0⌝ :=
    pinGa2 gsdldFwd γ (fun GD => (AxOpsem.grow GD 1).length ≤ 0) (Nat.le_refl 0)
  iapply (@wpdPastRowEnd hlc GF _ (epiGa2 gsdldFwd γ) fwdPol 1 (fun _ => iprop(True))
    (fun s0 => s0.atK = 0) 0 s Hk (fun _ h => h) Hle)
  iintro %GD %s1 %_ %_
  iapply (@postLiftingTrue GF (epiGa2 gsdldFwd γ) fwdPol (fun _ => iprop(True)) 1 s1 .rfl)

end h1

/-- EVERY premise of `epiReloadSound3Fwd` at `gsdldFwd`, runs and WPd included (hart 1 =
`h1State cpu ibNone`, empty row, zero steps). -/
theorem epiReloadSound3FwdNonvac (cpu : CPU) :
    -- the pure premises, with the dropped one failing
    (slotsDisjoint ldAddr race2B ∧
     rvwmoCatConsistent gsdldFwd ∧
     (∀ e, e ∈ gsdldFwd.gdG.gxGmo → e.1 = 0 ∨ e.1 = 1) ∧
     AxCjrWpd.fetchImgOk gsdldFwd 0 0 pcSd sdVs ∧
     storeRowOk gsdldFwd 0 0 ∧
     sdWriteOk gsdldFwd 0 0 ldAddr ∧
     AxCjrWpd.fetchImgOk gsdldFwd 0 1 pcLd AxEpiLedger.ldVs ∧
     loadRowOk gsdldFwd 0 1 ∧
     @ldspOwnOk epiPol gsdldFwd 0 1 (0, 0) ldAddr (writenHist (0, 0) sdData epiHs0) ∧
     (AxOpsem.grow gsdldFwd 0).length = 2 ∧
     ¬ gmoLt gsdldFwd.gdG (0, 0) (0, 1)) ∧
    -- hart 0's run
    (∃ (sN : Athread) (n : Nat),
      (∀ (_ : AxannotGS epiGF) (nm : GName),
        nsteps (tierAAstep gsdldFwd nm 0) n
          ⟨.PHart cpu (riscvStep false) (probeRegs pcSd) none ibNone, 0⟩ sN) ∧
      sN.atK = (AxOpsem.grow gsdldFwd 0).length) ∧
    -- hart 1: its run, row end and WPd
    ((h1State cpu ibNone).atK = 0 ∧
     (∀ (_ : AxannotGS epiGF) (nm : GName),
       nsteps (tierAAstep gsdldFwd nm 1) 0 (h1State cpu ibNone) (h1State cpu ibNone)) ∧
     (h1State cpu ibNone).atK = (AxOpsem.grow gsdldFwd 1).length ∧
     (∀ [InvGS_gen .hasNoLC epiGF] [AxannotGS epiGF] (nm : GName),
       ⊢ epiInit3 ldAddr race2B nm 1 -∗
         @tierAWpd epiGF .hasNoLC _ _ epiPol gsdldFwd GName Unit epiObInterp nm
           (h1State cpu ibNone) .MaybeStuck 1 (fun _ => iprop(True)))) := by
  refine ⟨epiReloadSound3FwdPremises, ?_, rfl, fun _ _ => nsteps_O _, rfl, ?_⟩
  · obtain ⟨n, sN, Hend, Hr⟩ := epiRunGsdldFwd cpu
    exact ⟨sN, n, fun _ _ => Hr, Hend⟩
  · intro _ _ nm
    unfold tierAWpd
    iintro _
    iapply (wpdHart1Empty (hlc := .hasNoLC) (GF := epiGF) nm (h1State cpu ibNone) rfl)

/-- The fully closed corollary at the forwarding witness. -/
theorem epiReloadSound3FwdGsdldFwd : graphValue gsdldFwd (0, 1) = some sdData := by
  obtain ⟨⟨Hdisj, Hcons, Hharts, Hgd_sd, Hrow_sd, Hw_sd, Hgd_ld, Hrow_ld, Hok_ld, Hlen, -⟩,
    ⟨sN, n, Hrun, Hend⟩, Hk1, Hrun1, Hend1, Hwp1⟩ :=
    epiReloadSound3FwdNonvac (⟨0, by decide⟩ : CPU)
  exact epiReloadSound3Fwd gsdldFwd ⟨0, by decide⟩ ldAddr race2B Hdisj Hcons Hharts Hgd_sd
    Hrow_sd Hw_sd Hgd_ld Hrow_ld Hok_ld Hlen sN n Hrun Hend _ _ 0 Hk1 Hrun1 Hend1 Hwp1

/-- The same for the design route `epiReloadSound3FwdPol` (hart 1's WPd under `fwdPol`). -/
theorem epiReloadSound3FwdPolGsdldFwd : graphValue gsdldFwd (0, 1) = some sdData := by
  obtain ⟨⟨Hdisj, Hcons, Hharts, Hgd_sd, Hrow_sd, Hw_sd, Hgd_ld, Hrow_ld, Hok_ld, Hlen, -⟩,
    ⟨sN, n, Hrun, Hend⟩, Hk1, Hrun1, Hend1, -⟩ :=
    epiReloadSound3FwdNonvac (⟨0, by decide⟩ : CPU)
  refine epiReloadSound3FwdPol gsdldFwd ⟨0, by decide⟩ ldAddr race2B Hdisj Hcons Hharts Hgd_sd
    Hrow_sd Hw_sd Hgd_ld Hrow_ld Hok_ld Hlen sN n Hrun Hend _ _ 0 Hk1 Hrun1 Hend1 ?_
  intro _ _ nm
  unfold tierAWpd
  iintro _
  iapply (wpdHart1EmptyFwd (hlc := .hasNoLC) (GF := epiGF) nm (h1State _ ibNone) rfl)

end Weak
