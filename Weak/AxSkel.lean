/-
Weak: **THE TOP-LEVEL THEOREM SKELETON** for the LB/AxSL target `xv6_rvwmo_safe_ax`.

Rocq: `iris/AxSkel.v` @ xxvzwolszwmp.

## The Rocq header, in substance

The SHAPE of the final theorem, with every conclusion that exists today derived and every
conclusion that does not exist yet named as an explicit OWED Prop:

    awpPackage AP pol (+ K1 supply) (+ K2Owed, K3Owed)
      → ∀ GD, rvwmoCatConsistent GD → pkGraphs GD →
        ∀ completed run (sN, n),
          ¬ gdviolationHart nh GD                       (K1, per-graph form)
        ∧ ∀ c : CPU, post GD c (sN c) ∧ chkp c (sN c)   (per-hart posts + checkpoints)
        ∧ pkQ GD                                        (final phase-2 read-back)
        ∧ K2Owed pk GD                                  (OWED: device reducibility)
        ∧ K3Owed pk eraBoot crashInv                    (OWED: multi-era crash story)

§1 `Aprot` — the protocol instance (ghost-name type, phase-2 state type, state interpretation,
per-hart initial resources).  §2 `AwpPackage` — ONE record, parametric in the protocol instance
`AP` and the policy `pol` (the two existing end-to-end instances — the epilogue at
`AxEpiAdeq.epiObInterp`/`epiPol`, the MP ledger at `obStInterpL`/`mpPol` — live at different
instances, so no fixed instance hosts both).  K1 is only available at a ledger-carrying
instance (§3 `awpK1`).  `pkRun` (PLACEHOLDER for `hart_conf`): every hart's `tierAAstep` run
from `pkS0` reaches its row end; `pkReach`: the states a hart passes through.
§3 the K1 supply (`plainCover`, `awpK1`, `ledgerPkQ`, `ledgerReadback`, `awpK1Ledger`) and the
OWED K2 (`K2Owed`, device reducibility of every pre-row-end hart state, C11) / K3 (`Era`,
`eraCut`, `K3Owed`, the era sequence, C12/D4) statements.  K2/K3 are PASS-THROUGH hypotheses;
VACUITY WARNING (Rocq): `K3Owed` is parametric in the placeholders `eraBoot`/`crashInv` and is
trivially provable at `eraBoot := fun _ _ => False`.
§4 THE SKELETON: `pkWpJoint` (framing), `xv6RvwmoSafeAxCore` (posts + checkpoints via
`wpcAdequacyAnnGmo`, read-back via `tierAAdequacyFinalGmo`), `xv6RvwmoSafeAxK1` (K1 via
`ownedNoViolationCat`), `xv6RvwmoSafeAxSkel` (the final shape).
§5 the sRVWMO subsumption link `xv6RvwmoSafeAxSrvwmoK1` (via `gviolationSubsumesSrvwmo`): on a
graph that IS the graph of an sRVWMO candidate, every matching pf configuration is free of
the SC-side `violationHart`.

## Deviations from Rocq

1. O2 STAGE C: the fetch-oracle text field `pk_T` is DROPPED (fetches are not graph events;
   `tierAWpdc`/`tierAAstep`/`AxDevGraph.devReducible` take no `T`), and `K2Owed` calls
   `AxDevGraph.devReducible GV i s` (Rocq `dev_reducible GV (pk_T pk) (gx_img …) i s`).
2. INSTANCES: Rocq's `invGS_gen HasNoLc Σ → axannotGS Σ → …` families (`pk_ck`, `pk_Hchkp`,
   `pk_wp`) take the two instances as EXPLICIT arguments (`InvGS_gen .hasNoLC GF`,
   `AxannotGS GF`); the policy `pol : Axpol` is an explicit structure parameter passed by `@`.
   The package does not take Rocq's `axannotG Σ` (unused: `AxannotGS` carries its own
   `AxannotG`); the skeleton sections take `[InvGpreS GF] [AxannotG GF]` as Rocq.  `GF` is
   `BundledGFunctors.{0,0,0}` (as `AxWpcAdeq` §4).
3. `pkRun`'s run premise quantifies `∀ (_ : AxannotGS GF) (nm : AP.apN) i`, i.e. exactly
   `wpcAdequacyAnnGmo`'s `Hrun` (`tierAAstep` is independent of the instance and of `nm`).
   Sets are `LawfulSet.ofList`; `eras !! g` ↦ `eras[g]?`; `fin_to_nat c` ↦ `c.val`.
4. §5's type parameters `Pc Dc` are named `P D` (as `gviolationSubsumesSrvwmo`).
5. `Print Assumptions` lines not ported (the lint's axiom check covers them).

**Rocq → Lean name map.**  `aprot`/`AProt` `Aprot`/`Aprot.mk`, `ap_N` `apN`, `ap_st` `apSt`,
`ap_interp` `apInterp`, `ap_init` `apInit`; `awp_package`/`AwpPackage` `AwpPackage`/`.mk`,
fields `pk_graphs` `pkGraphs`, `pk_s0` `pkS0`, `pk_post` `pkPost`, `pk_ck` `pkCk`, `pk_chkp`
`pkChkp`, `pk_Q` `pkQ`, `pk_pol_wf` `pkPolWf`, `pk_agents` `pkAgents`, `pk_k0` `pkK0`,
`pk_Hchkp` `pkHchkp`, `pk_wp` `pkWp`, `pk_alloc` `pkAlloc`, `pk_s_pol_gmo` `pkSPolGmo`,
`pk_lobp_gmo` `pkLobpGmo`, `pk_readback` `pkReadback`; `pk_run` `pkRun`, `pk_reach` `pkReach`;
`plain_cover` `plainCover`, `awp_k1` `awpK1`, `ledger_pkQ` `ledgerPkQ`, `ledger_readback`
`ledgerReadback`, `awp_k1_ledger` `awpK1Ledger`, `K2_owed` `K2Owed`, `era`/`Era` `Era`/`.mk`
(`era_gd` `eraGd`, `era_cs` `eraCs`, `era_n` `eraN`), `era_cut` `eraCut`, `K3_owed` `K3Owed`;
`pk_wp_joint` `pkWpJoint`, `xv6_rvwmo_safe_ax_core` `xv6RvwmoSafeAxCore`,
`xv6_rvwmo_safe_ax_k1` `xv6RvwmoSafeAxK1`, `xv6_rvwmo_safe_ax_skel` `xv6RvwmoSafeAxSkel`,
`xv6_rvwmo_safe_ax_srvwmo_k1` `xv6RvwmoSafeAxSrvwmoK1`.  None is in the duplicated-name table.

**Dropped:** the field `pk_T` (deviation 1).  Rocq 18 definitions/lemmas, Lean 18.
-/
import Weak.AxWpcAdeq
import Weak.AxTokLedgerWp
import Weak.AxAllHarts
import Weak.AxViolSubsume
import Weak.AxDevGraph
import Weak.WeakRvwmoRestr

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D

/-! # 1. The protocol instance (parameter of the package) -/

/-- Rocq `aprot`: ghost names, phase-2 state, state interpretation, per-hart init. -/
structure Aprot (GF : BundledGFunctors.{0,0,0}) where
  apN : Type
  apSt : Type
  apInterp : apN → Gdexec → apSt → GSet Geid → IProp GF
  apInit : apN → Agent → IProp GF

/-! # 2. `AwpPackage` -/

section package
variable {GF : BundledGFunctors.{0,0,0}}

/-- Rocq `awp_package` (Stage C: no `pk_T`). -/
structure AwpPackage (AP : Aprot GF) (pol : Axpol) where
  pkGraphs : Gdexec → Prop
  pkS0 : Agent → Athread
  pkPost : Gdexec → Agent → Athread → Prop
  pkCk : InvGS_gen .hasNoLC GF → AxannotGS GF → AP.apN → Agent → Athread → IProp GF
  pkChkp : Agent → Athread → Prop
  pkQ : Gdexec → Prop
  pkPolWf : @axpolWf pol
  pkAgents : ∀ GD, pkGraphs GD → ∀ e, e ∈ GD.gdG.gxGmo → e.1 ∈ allHarts
  pkK0 : ∀ i, i ∈ allHarts → (pkS0 i).atK = 0
  pkHchkp : ∀ (Hinv : InvGS_gen .hasNoLC GF) (Hann : AxannotGS GF) nm i s,
    pkCk Hinv Hann nm i s ⊢ iprop(⌜pkChkp i s⌝)
  pkWp : ∀ GD, pkGraphs GD →
    ∀ (Hinv : InvGS_gen .hasNoLC GF) (Hann : AxannotGS GF) (nm : AP.apN) (i : Agent),
      i ∈ allHarts →
      ⊢ AP.apInit nm i -∗
        @tierAWpdc GF .hasNoLC Hinv Hann pol GD AP.apN AP.apSt AP.apInterp nm
          (pkCk Hinv Hann nm) (pkS0 i) .MaybeStuck i (fun s => iprop(⌜pkPost GD i s⌝))
  pkAlloc : ∀ GD, pkGraphs GD →
    ⊢ |==> ∃ (nm : AP.apN) (σ0 : AP.apSt),
        AP.apInterp nm GD σ0 ∅ ∗ [∗list] i ∈ allHarts, AP.apInit nm i
  pkSPolGmo : ∀ GD, rvwmoCatConsistent GD → pkGraphs GD →
    ∀ e e', e' ∈ @Axpol.sPol pol GD e → gmoLt GD.gdG e' e
  pkLobpGmo : ∀ GD, rvwmoCatConsistent GD → pkGraphs GD →
    ∀ e e', e' ∈ @Axpol.lobp pol GD e → gmoLt GD.gdG e' e
  pkReadback : ∀ GD, rvwmoCatConsistent GD → pkGraphs GD →
    ∀ nm σ, AP.apInterp nm GD σ (LawfulSet.ofList GD.gdG.gxGmo) ⊢ iprop(⌜pkQ GD⌝)

/-- Rocq `pk_run` (PLACEHOLDER for `hart_conf`): every hart runs, at graph values, from `pkS0`
to its row end. -/
def pkRun {AP : Aprot GF} {pol : Axpol} (pk : AwpPackage AP pol) (GD : Gdexec)
    (sN : Agent → Athread) (n : Agent → Nat) : Prop :=
  (∀ (_ : AxannotGS GF) (nm : AP.apN) i, i ∈ allHarts →
     nsteps (tierAAstep GD nm i) (n i) (pk.pkS0 i) (sN i)) ∧
  (∀ i, i ∈ allHarts → (sN i).atK = (AxOpsem.grow GD i).length)

/-- Rocq `pk_reach`: states hart `c` passes through on its run (for K2). -/
def pkReach {AP : Aprot GF} {pol : Axpol} (pk : AwpPackage AP pol) (GD : Gdexec) (c : Agent)
    (s : Athread) : Prop :=
  ∀ (_ : AxannotGS GF) (nm : AP.apN), ∃ m, nsteps (tierAAstep GD nm c) m (pk.pkS0 c) s

end package

/-! # 3. The K1 supply, and the OWED K2 / K3 statements -/

/-- Plain hart writes land in the Own class `OC` (AxViol's `Hplain`). -/
def plainCover (OC : Int → Prop) (nh : Nat) (GD : Gdexec) : Prop :=
  ∀ w a v, w ∈ GD.gdG.gxGmo → tidHart nh (some w.1) →
    glblIs GD.gdG w lbPlain → gwritesByte GD.gdG w a v → OC a

/-- THE K1 SUPPLY (per-graph form): the package's final read-back yields an ownership
timeline covering every plain hart write. -/
def awpK1 {GF : BundledGFunctors.{0,0,0}} {AP : Aprot GF} {pol : Axpol}
    (nh : Nat) (pk : AwpPackage AP pol) : Prop :=
  ∀ GD, rvwmoCatConsistent GD → pk.pkGraphs GD → pk.pkQ GD →
    ∃ OC own, gtlOk OC nh GD.gdG own ∧ plainCover OC nh GD

/-- The ledger read-back (`AxTokLedgerWp.ledgerInvFull`). -/
def ledgerPkQ (OC : Int → Prop) (nh : Nat) (GD : Gdexec) : Prop :=
  ∃ LH, ledgerHistOkList OC nh GD LH

theorem ledgerReadback {GF : BundledGFunctors} [LedgerG GF] (OC : Int → Prop) (nh : Nat)
    {N0 st0 : Type} (base0 : N0 → Gdexec → st0 → GSet Geid → IProp GF) (GD : Gdexec)
    (Hcons : rvwmoCatConsistent GD) (nm : N0 × GName) (σ : st0) :
    obStInterpL OC nh base0 nm GD σ (LawfulSet.ofList GD.gdG.gxGmo) ⊢
      iprop(⌜ledgerPkQ OC nh GD⌝) := by
  unfold obStInterpL ledgerPkQ
  iintro ⟨-, Hl⟩
  iapply (ledgerInvFull (GF := GF) OC nh nm.2 GD (schedHGwf GD Hcons))
  iexact Hl

/-- A ledger-read-back package supplies K1 given the plain-write cover. -/
theorem awpK1Ledger {GF : BundledGFunctors.{0,0,0}} {AP : Aprot GF} {pol : Axpol}
    (nh : Nat) (pk : AwpPackage AP pol) (OC : Int → Prop)
    (HQ : ∀ GD, pk.pkQ GD → ledgerPkQ OC nh GD)
    (Hpl : ∀ GD, rvwmoCatConsistent GD → pk.pkGraphs GD → plainCover OC nh GD) :
    awpK1 nh pk := by
  intro GD Hcons Hg HQGD
  obtain ⟨LH, HLH⟩ := HQ GD HQGD
  exact ⟨OC, _, ledgerTimelineList OC nh GD LH (schedHGwf GD Hcons) HLH, Hpl GD Hcons Hg⟩

/-- K2 — OWED (C11, `AxDevGraph`).  For every device-graph wrapper of `GD` that is
device-consistent, every state a hart passes through before its row end is DEVICE-reducible.
The final theorem additionally owes the device agent among `pkAgents` and its own
reducibility. -/
def K2Owed {GF : BundledGFunctors.{0,0,0}} {AP : Aprot GF} {pol : Axpol}
    (pk : AwpPackage AP pol) (GD : Gdexec) : Prop :=
  ∀ GV : GdexecDev, GV.gvGd = GD → gdvConsistent GV →
  ∀ (c : CPU) s, pkReach pk GD c.val s →
    s.atK < (AxOpsem.grow GD c.val).length →
    AxDevGraph.devReducible GV c.val s

/-- Rocq `era`: a consistent graph and a cut. -/
structure Era where
  eraGd : Gdexec
  eraCs : List Nat
  eraN : Nat

def eraCut (e : Era) : Gdexec := gdRestrict e.eraGd e.eraCs e.eraN

/-- K3 — OWED (C12, decision D4).  An ERA SEQUENCE: era `g` is a consistent graph cut by a
`restrOk` cut; era 0 is a graph of the package; era `g+1`'s graph boots from era `g`'s cut
(`eraBoot`, PLACEHOLDER).  Owed: every era's graph is a graph of the package, and the
crash-spanning disk invariant `crashInv` (PLACEHOLDER) holds at every cut. -/
def K3Owed {GF : BundledGFunctors.{0,0,0}} {AP : Aprot GF} {pol : Axpol}
    (pk : AwpPackage AP pol) (eraBoot : Gdexec → Gdexec → Prop)
    (crashInv : Gdexec → Prop) : Prop :=
  ∀ eras : List Era,
    (∀ (g : Nat) (e : Era), eras[g]? = some e →
       rvwmoCatConsistent e.eraGd ∧ restrOk e.eraGd.gdG e.eraCs e.eraN) →
    (∀ (e : Era), eras[0]? = some e → pk.pkGraphs e.eraGd) →
    (∀ (g : Nat) (e e' : Era), eras[g]? = some e → eras[g + 1]? = some e' → eraBoot (eraCut e) e'.eraGd) →
    ∀ (g : Nat) (e : Era), eras[g]? = some e → pk.pkGraphs e.eraGd ∧ crashInv (eraCut e)

/-! # 4. THE SKELETON -/

section skeleton
variable {GF : BundledGFunctors.{0,0,0}} [InvGpreS GF] [AxannotG GF]
variable (AP : Aprot GF) (pol : Axpol) (pk : AwpPackage AP pol)

/-- Framing: the per-hart obligations assemble into the joint wand. -/
theorem pkWpJoint (GD : Gdexec) (Hg : pk.pkGraphs GD) :
    ∀ (Hinv : InvGS_gen .hasNoLC GF) (Hann : AxannotGS GF) (nm : AP.apN),
      ⊢ ([∗list] i ∈ allHarts, AP.apInit nm i) -∗
        [∗list] i ∈ allHarts,
          @tierAWpdc GF .hasNoLC Hinv Hann pol GD AP.apN AP.apSt AP.apInterp nm
            (pk.pkCk Hinv Hann nm) (pk.pkS0 i) .MaybeStuck i
            (fun s => iprop(⌜pk.pkPost GD i s⌝)) := by
  intro Hinv Hann nm
  refine entails_wand (BigSepL.bigSepL_mono fun {_ i} Hk => ?_)
  exact wand_entails (pk.pkWp GD Hg Hinv Hann nm i (List.mem_of_getElem? Hk))

/-- THE CORE: everything that exists today. -/
theorem xv6RvwmoSafeAxCore (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (Hg : pk.pkGraphs GD) (sN : Agent → Athread) (n : Agent → Nat)
    (Hrun : pkRun pk GD sN n) :
    (∀ c : CPU, pk.pkPost GD c.val (sN c.val) ∧ pk.pkChkp c.val (sN c.val)) ∧
    pk.pkQ GD := by
  obtain ⟨Hrun, Hend⟩ := Hrun
  refine ⟨fun c => ?_, ?_⟩
  · exact @wpcAdequacyAnnGmo GF _ _ pol GD AP.apN AP.apSt AP.apInterp AP.apInit pk.pkPolWf
      Hcons allHarts nodupAllHarts (pk.pkAgents GD Hg) pk.pkS0 sN n Hrun pk.pkK0 Hend
      (pk.pkPost GD) (@fun Hinv Hann => pk.pkCk Hinv Hann) pk.pkChkp
      (@fun Hinv Hann => pk.pkHchkp Hinv Hann)
      (@fun Hinv Hann nm => pkWpJoint AP pol pk GD Hg Hinv Hann nm) (pk.pkAlloc GD Hg)
      (pk.pkSPolGmo GD Hcons Hg) (pk.pkLobpGmo GD Hcons Hg) c.val (cpuInAllHarts c)
  · refine @tierAAdequacyFinalGmo GF _ _ pol GD AP.apN AP.apSt AP.apInterp AP.apInit
      pk.pkPolWf Hcons allHarts nodupAllHarts (pk.pkAgents GD Hg) pk.pkS0 sN n Hrun pk.pkK0
      Hend (pk.pkPost GD) ?_ (pk.pkAlloc GD Hg) (pk.pkSPolGmo GD Hcons Hg)
      (pk.pkLobpGmo GD Hcons Hg) (pk.pkQ GD) (pk.pkReadback GD Hcons Hg)
    intro Hinv Hann nm
    exact hartsPremiseMono allHarts _ _ _
      (fun j => @tierAWpdcWpd GF .hasNoLC Hinv Hann pol GD AP.apN AP.apSt AP.apInterp nm
        (pk.pkCk Hinv Hann nm) (pk.pkS0 j) .MaybeStuck j
        (fun s => iprop(⌜pk.pkPost GD j s⌝)))
      (pkWpJoint AP pol pk GD Hg Hinv Hann nm)

/-- K1 from the supply (per-graph form). -/
theorem xv6RvwmoSafeAxK1 (nh : Nat) (HK1 : awpK1 nh pk)
    (GD : Gdexec) (Hcons : rvwmoCatConsistent GD) (Hg : pk.pkGraphs GD)
    (sN : Agent → Athread) (n : Agent → Nat) (Hrun : pkRun pk GD sN n) :
    ¬ gdviolationHart nh GD := by
  obtain ⟨_, HQ⟩ := xv6RvwmoSafeAxCore AP pol pk GD Hcons Hg sN n Hrun
  obtain ⟨OC, own, Htl, Hpl⟩ := HK1 GD Hcons Hg HQ
  exact ownedNoViolationCat OC nh GD own Hcons Htl Hpl

/-- THE SKELETON — the final shape.  K2 / K3 are PASS-THROUGH (owed). -/
theorem xv6RvwmoSafeAxSkel (nh : Nat) (HK1 : awpK1 nh pk)
    (eraBoot : Gdexec → Gdexec → Prop) (crashInv : Gdexec → Prop)
    (HK2 : ∀ GD, rvwmoCatConsistent GD → pk.pkGraphs GD → K2Owed pk GD)
    (HK3 : K3Owed pk eraBoot crashInv) :
    ∀ GD, rvwmoCatConsistent GD → pk.pkGraphs GD →
    ∀ (sN : Agent → Athread) (n : Agent → Nat), pkRun pk GD sN n →
      ¬ gdviolationHart nh GD ∧
      (∀ c : CPU, pk.pkPost GD c.val (sN c.val) ∧ pk.pkChkp c.val (sN c.val)) ∧
      pk.pkQ GD ∧
      K2Owed pk GD ∧
      K3Owed pk eraBoot crashInv := by
  intro GD Hcons Hg sN n Hrun
  obtain ⟨Hpost, HQ⟩ := xv6RvwmoSafeAxCore AP pol pk GD Hcons Hg sN n Hrun
  exact ⟨xv6RvwmoSafeAxK1 AP pol pk nh HK1 GD Hcons Hg sN n Hrun, Hpost, HQ,
    HK2 GD Hcons Hg, HK3⟩

end skeleton

/-! # 5. The sRVWMO subsumption link (K1 vs the SC-side `violationHart`) -/

section srvwmoLink
variable {GF : BundledGFunctors.{0,0,0}} [InvGpreS GF] [AxannotG GF]
variable (AP : Aprot GF) (pol : Axpol) (pk : AwpPackage AP pol)

/-- On a graph that IS the graph of an sRVWMO candidate (cat-consistent, a graph of the
package), every pf configuration matching a prefix of the candidate's replay is free of the
SC-side `violationHart` (`xv6_srvwmo_safe`'s conjunct (ii), restricted to realized configs). -/
theorem xv6RvwmoSafeAxSrvwmoK1 {P D : Type} (nh : Nat) (HK1 : awpK1 nh pk)
    (GD : Gdexec) (Hcons : rvwmoCatConsistent GD) (Hg : pk.pkGraphs GD)
    (sN : Agent → Athread) (n : Agent → Nat) (Hrun : pkRun pk GD sN n)
    (cd : Cand) (Hsr : srvwmoConsistent cd) (HGT : GD.gdG = graphOfCand cd)
    (m : Nat) (Hm : m ≤ cd.cdTr.length) (c : Wpcfg P D)
    (Hmatch : cfgMatchd c (stt (candExec cd) m)) :
    ¬ violationHart clsOf pubOf nh c := fun Hv =>
  xv6RvwmoSafeAxK1 AP pol pk nh HK1 GD Hcons Hg sN n Hrun
    (gviolationSubsumesSrvwmo cd GD m nh c Hsr HGT Hm Hmatch Hv)

end srvwmoLink

end Weak
