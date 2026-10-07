/-
Weak: **DISCHARGING `AxSchedIris.deferredReadCov`** (C6 coverage; LB/AxSL rev 7, challenge C6).

Rocq: `iris/AxCov.v` @ xxvzwolszwmp.

## The Rocq header, in substance

`AxSchedIris.ownedReadGhostSnap` validates a deferred owned read `r` against a FROZEN snapshot
`H_r` GIVEN `deferredReadCov GD a r H_r` ("every write to byte `a` gmo-before `r` is a member of
`H_r`").  This file derives that coverage fact from THREE ingredients: (1) `AxProt.protInv`'s
per-write coverage (`protInvPrefixCov`) — every gmo-before-`r` write to `a` has SOME persistent
deposit; (2) co-maximality (from `gloadValue`) pinning `wl` — the write `r`'s `ts` entry names — as
the gmo-LARGEST such write; (3) ONE NAMED PREMISE, `classEpochGmoMono`: two same-byte writes'
deposits are ordered the way their writes are (`gmoLt w w' → H_w <+: H_w'`).  (3) is exactly C6's
class/epoch discipline and is NOT proved here: it is the proof obligation of the (future)
per-event adequacy induction that calls `protInvWriteStep` at each write in processing order
(which `AxSched.Inv`'s `inv_ord_fresh` shows agrees with gmo order for writes).

§1 `classEpochGmoMono` (the named premise); §2 `deferredReadCovOfMono` (the coverage lemma);
§3 `deferredSnapAvailOfMono` (the corollary instantiating `AxSchedIris.deferredSnapAvail`).

**Fetches.** Nothing here depends on instruction fetches: the file speaks of ghost snapshots and
of `gwritesByte`/`greadsByte`/`gwriteAt`/`gmoLt` over graph labels (`Lbl` has no fetch
constructor).

## Deviations from Rocq

1. NAMES: camelCase (map below).  No name is in `notes/weak-port-dupnames.json`; no Lean-only
   helpers.
2. VOCABULARY (as `AxSchedIris` deviation 2): `last l` ↦ `l.getLast?`; `H.*1` ↦ `H.map Prod.fst`;
   `gd_g GD` ↦ `GD.gdG`; `list_to_set` ↦ `LawfulSet.ofList`; `gset geid` ↦ `GSet Geid`;
   `Z` ↦ `Int`; `bv 8` ↦ `BitVec 8`; `axlogG Σ hent` ↦ `[AxlogG GF Hent]`;
   `` `prefix_of` `` ↦ `<+:`.
3. STATEMENT SHAPES (as `AxSchedIris` deviation 3): `P -∗ Q -∗ R` ↦ `P ∗ Q ⊢ R`; pure premises
   stay `→`.

**Rocq → Lean name map.**  `class_epoch_gmo_mono` `classEpochGmoMono`,
`deferred_read_cov_of_mono` `deferredReadCovOfMono`, `deferred_snap_avail_of_mono`
`deferredSnapAvailOfMono`.

**Not ported:** the §4 `Print Assumptions` audit (the lint's axiom check covers it).
-/
import Weak.AxSchedIris
import Iris.ProofMode

namespace Weak

open Iris Iris.BI Iris.Std MachCSL MachCSL.Stdpp

section cov

variable {GF : BundledGFunctors} [AxlogG GF Hent]

/-! ## 1. The named premise (= C6's class/epoch discipline) -/

/-- Two writes to the same byte `a`, each with a `ΦOwn`-deposited snapshot (`last H_w = (w, v)`),
have their deposits ordered the way the writes are gmo-ordered. -/
def classEpochGmoMono (γ : GName) (GD : Gdexec) (a : Int) : Prop :=
  ∀ (w w' : Geid) (v v' : BitVec 8) (H_w H_w' : List Hent),
    gwritesByte GD.gdG w a v → gwritesByte GD.gdG w' a v' →
    gmoLt GD.gdG w w' →
    H_w.getLast? = some (w, v) → H_w'.getLast? = some (w', v') →
    (histSnap (GF := GF) γ a H_w ∗ histSnap γ a H_w' ⊢ ⌜H_w <+: H_w'⌝)

/-! ## 2. The coverage lemma -/

/-- `wl` is the write `r`'s own `ts` entry `t` names, known gmo-before `r`;
`classEpochGmoMono` is the one un-discharged premise. -/
theorem deferredReadCovOfMono (γ : GName) (GD : Gdexec) (s : GSet Geid)
    (r wl : Geid) (a : Int) (t : Nat) (vr : BitVec 8) :
    rvwmoCatConsistent GD →
    r ∈ GD.gdG.gxGmo →
    (LawfulSet.ofList (gmoPrefix GD.gdG r) : GSet Geid) ⊆ s →
    greadsByte GD.gdG r a t vr →
    gwriteAt GD.gdG t = some wl →
    gmoLt GD.gdG wl r →
    classEpochGmoMono (GF := GF) γ GD a →
    protInv (GF := GF) γ GD s ⊢
      ∃ H_wl : List Hent, ⌜H_wl.getLast? = some (wl, vr)⌝ ∗ ⌜deferredReadCov GD a r H_wl⌝ := by
  intro hcons hrgmo hsub hrd hwrat _hmowl hmono
  have ⟨hwf, _, hgv, _⟩ := hcons
  have hwlwb : gwritesByte GD.gdG wl a vr := greadSourceByte GD.gdG r a t vr wl hgv hrd hwrat
  iintro #Hinv
  ihave Hcovwl := protInvPrefixCov γ GD s r a hwf hrgmo hsub $$ Hinv
  icases Hcovwl $$ %wl %vr %hwlwb %_hmowl with ⟨%H_wl, #Hswl, %hlwl⟩
  iexists H_wl
  isplitl []
  · ipureintro; exact hlwl
  -- the pure coverage, from the per-write deposits and the named premise
  have hcovAll : ∀ w v, gwritesByte GD.gdG w a v → gmoLt GD.gdG w r →
      protInv (GF := GF) γ GD s ∗ histSnap (GF := GF) γ a H_wl ⊢
        ⌜w ∈ H_wl.map Prod.fst⌝ := by
    intro w v hwb hmo'
    by_cases hne : w = wl
    · subst hne
      exact BI.pure_intro (histSnapLastIn H_wl w vr hlwl)
    · have hmax := (hgv r a t vr hrd).2
      obtain ⟨hwlin, hwixwl⟩ := gwriteAtInv GD.gdG t wl hwf.1 hwrat
      have hwin : w ∈ gwrites GD.gdG := gwritesByteGwrites GD.gdG w a v hwf hwb
      have hle : gwix GD.gdG w ≤ t := hmax w v hwb (Or.inl hmo')
      rw [← hwixwl] at hle
      have hltwix : gwix GD.gdG w < gwix GD.gdG wl := by
        by_cases heqx : gwix GD.gdG w = gwix GD.gdG wl
        · exact absurd (gwixInj GD.gdG w wl hwf.1 hwin hwlin heqx) hne
        · omega
      have hgpolt : gpos GD.gdG w < gpos GD.gdG wl :=
        (gwixGposLt GD.gdG w wl hwf.1 hwin hwlin).1 hltwix
      have hwgmo : w ∈ GD.gdG.gxGmo := ((gwritesElemOf GD.gdG w).1 hwin).1
      have hwlgmo : wl ∈ GD.gdG.gxGmo := ((gwritesElemOf GD.gdG wl).1 hwlin).1
      have hgmoww : gmoLt GD.gdG w wl := ⟨hwgmo, hwlgmo, hgpolt⟩
      iintro ⟨#Hinv, #Hswl⟩
      ihave Hcovw := protInvPrefixCov γ GD s r a hwf hrgmo hsub $$ Hinv
      icases Hcovw $$ %w %v %hwb %hmo' with ⟨%H_w, #Hsw, %hlw⟩
      ihave %hpre := hmono w wl v vr H_w H_wl hwb hwlwb hgmoww hlw hlwl $$ [Hsw Hswl]
      · isplitl [Hsw]
        · iexact Hsw
        · iexact Hswl
      ipureintro
      exact (hentFstPrefix H_w H_wl hpre).subset (histSnapLastIn H_w w v hlw)
  -- collect the per-write pure facts into the `∀`
  have hstep : protInv (GF := GF) γ GD s ∗ histSnap (GF := GF) γ a H_wl ⊢
      ⌜deferredReadCov GD a r H_wl⌝ := by
    unfold deferredReadCov
    refine (BI.forall_intro fun w => ?_).trans BI.pure_forall.2
    refine (BI.forall_intro fun v => ?_).trans BI.pure_forall.2
    refine (BI.forall_intro fun hwb => ?_).trans BI.pure_forall.2
    refine (BI.forall_intro fun hmo => ?_).trans BI.pure_forall.2
    exact hcovAll w v hwb hmo
  iapply hstep
  isplitl []
  · iexact Hinv
  · iexact Hswl

/-! ## 3. The corollary: `deferredSnapAvail`, instantiated -/

/-- Of the shape `AxSchedGD.sched_proc_adequate`'s `Hdefer` wants, for one concrete deferred read
`r` (the existential byte instantiated at `a`). -/
theorem deferredSnapAvailOfMono (γ : GName) (GD : Gdexec) (s everD : GSet Geid)
    (r wl : Geid) (a : Int) (t : Nat) (vr : BitVec 8) :
    rvwmoCatConsistent GD →
    r ∈ GD.gdG.gxGmo →
    (LawfulSet.ofList (gmoPrefix GD.gdG r) : GSet Geid) ⊆ s →
    greadsByte GD.gdG r a t vr →
    gwriteAt GD.gdG t = some wl →
    gmoLt GD.gdG wl r →
    classEpochGmoMono (GF := GF) γ GD a →
    protInv (GF := GF) γ GD s ⊢ ⌜deferredSnapAvail GD everD r⌝ := by
  intro hcons hrgmo hsub hrd hwrat hmowl hmono
  iintro Hinv
  ihave Hc := deferredReadCovOfMono γ GD s r wl a t vr hcons hrgmo hsub hrd hwrat hmowl hmono
    $$ Hinv
  icases Hc with ⟨%H_wl, %hlwl, %hcov⟩
  ipureintro
  intro _
  exact ⟨a, H_wl, wl, vr, hlwl, Or.inl hmowl, hcov⟩

end cov

end Weak
