/-
Weak: **the GATED program-level notion `progLedgerVerifiedG` SPECIALIZES to the gate-free
examples of `AxClsStep2`.**

Rocq: `iris/AxLedgerG3.v` @ xxvzwolszwmp.

## The Rocq header, in substance

`PMpbVerifiedG : progLedgerVerifiedG 2 PMpb` — `AxClsStep2`'s positive branchy-mp program,
re-verified at the FROZEN-SLOT ledger instance `obStInterpLG` with the EMPTY gate structure
(`gs0 := fun _ _ => ∅`: no deferred events; `polSafeS` is then the gmo prefix,
`AxLedgerG.polSafeSEmpty`).  The proof is `AxClsStep2` §5's with exactly two changes: the
instance, and the event rule (`wpEvStepLedgerG` in place of
`AxTokLedgerWp.wpEvStepLedgerJoint`), whose obligation is obtained from the UNCHANGED
`AxTokLedgerWp.ledgerJoint` obligation by `AxLedgerG.ledgerJointGOfJoint`.  `LJAnyG` is
`AxClsStep2.LJAny` at this instance.  The NEGATIVE examples need no WPd: `PPlNotVerifiedG` /
`PMprNotVerifiedG` from `progNotVerifiedGOfViol`.  (Rocq: no general "old ⇒ new" theorem, since
transporting a `wpd` across instances needs a wpd-level refinement lemma AxWp/AxWpD lack.)

## Deviations from Rocq

1. CONTEXTS (as `AxClsStep2b` deviation 7): the `wpdG` section context ↦ `{hlc}
   {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF] [AxannotGS GF] [LedgerG GF]`; the
   section parameters `γ cpu GD Hreal Hcons` are explicit leading arguments (only those the
   Rocq `Proof using` names).  `Local Instance ImpGG` is the reducible def `impGG γ GD`;
   `mp_pol` is passed explicitly as `mpPol`; the notations `TW`/`LJ` are the Lean-only abbrevs
   `AxLedgerG3.TW`/`AxLedgerG3.LJ`.  Wand chains `A -∗ B` ↦ `⊢ A -∗ B`.
2. O2 STAGE C: no text oracle `Tf` (the instance is `axGA2 GD …`); `readShellG`/`wpdRG` take
   `(classify ak).akIfetch = false` (as `AxClsStep2b.readShell`/`wpdR`).
3. PROOF ROUTE: `LJAnyG` is `LJAny` by `exact` — `ledgerJoint` sees the instance only through
   `obSt = Unit`, so the two obligations are the same term (Rocq re-runs the script).  The shells
   unfold `AxWpD.wpdMUnfoldStep` (as `AxClsStep2b`).
4. `progLedgerVerifiedG.mk`'s post is `fun _ _ => True`.

**Rocq → Lean name map.**  `gs0` `gs0`, `L0x` `L0x`, `gs0_ok` `gs0Ok`, `gs0_nodef` `gs0Nodef`,
`gs0_pol` `gs0Pol`, `ImpGG` `impGG`, `ImpGG_ext` `impGGExt`, `LJ_anyG` `LJAnyG`,
`wp_ev_step_closedG` `wpEvStepClosedG`, `wpd_skip2G` `wpdSkip2G`, `pos_shellG` `posShellG`,
`hlt_shellG` `hltShellG`, `read_shellG` `readShellG`, `wpd_wG` `wpdWG`, `wpd_h0hG` `wpdH0hG`,
`wpd_rG` `wpdRG`, `wpd_h1bG` `wpdH1bG`, `P_mpb_verified_G` `PMpbVerifiedG`, `P_mpb_viol_free_G`
`PMpbViolFreeG`, `P_pl_not_verified_G` `PPlNotVerifiedG`, `P_mpr_not_verified_G`
`PMprNotVerifiedG`.  No name of this file is in `notes/weak-port-dupnames.json`.  Lean-only
(file-qualified): `AxLedgerG3.TW`, `AxLedgerG3.LJ`, `AxLedgerG3.gconstEq`,
`AxLedgerG3.localTrue`, `AxLedgerG3.twUnfold`.

**Dropped:** only the `Print Assumptions` lines (the lint's axiom check covers them).
-/
import Weak.AxLedgerG
import Weak.AxClsStep2b

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D

/-- The empty gate structure. -/
def gs0 (_GD : Gdexec) (_e : Geid) : GSet Geid := ∅

/-- The initial ledger of `PMpb`. -/
def L0x : Ledger := {[xa := Holder.held 0]}

theorem gs0Ok (GD : Gdexec) : gsrcOk GD.gdG (gs0 GD) :=
  fun _ _ Hr => absurd Hr notElemOfEmpty

theorem gs0Nodef (GD : Gdexec) (e : Geid) : ¬ gdeferred GD.gdG (gs0 GD) e := by
  rintro ⟨r, Hr, -⟩
  exact notElemOfEmpty Hr

theorem gs0Pol (GD : Gdexec) (e : Geid) :
    polSafeS (gs0 GD) GD e ⊆ @Axpol.sPol mpPol GD e := by
  show polSafeS (fun _ => ∅) GD e ⊆ _
  rw [polSafeSEmpty]
  exact fun _ h => h

section wpdG
variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF] [AxannotGS GF]
  [LedgerG GF]

/-- Rocq `Local Instance ImpGG` (a named reducible def). -/
@[reducible] def impGG (γ : GName) (GD : Gdexec) : AxirisG GF :=
  axGA2 GD (GName × GName) Unit (obStInterpLG AxClsStep2.OCX 2 L0x gs0 baseX) (γ, γ)

theorem impGGExt (γ : GName) (GD : Gdexec) :
    ∀ (GD' : Gdexec) (σ : @AxirisG.obSt GF (impGG γ GD)) (s : GSet Geid),
      @AxirisG.obStInterp GF (impGG γ GD) GD' σ s ⊣⊢
        baseX γ GD' σ s ∗ ledgerInvG AxClsStep2.OCX 2 L0x gs0 γ GD' s :=
  fun _ _ _ => .rfl

/-- Lean-only (Rocq `Local Notation TW`). -/
abbrev AxLedgerG3.TW (γ : GName) (GD : Gdexec) (s : Athread) (i : Agent) : IProp GF :=
  @tierAWpd GF hlc _ _ mpPol GD (GName × GName) Unit
    (obStInterpLG AxClsStep2.OCX 2 L0x gs0 baseX) (γ, γ) s .MaybeStuck i (fun _ => iprop(⌜True⌝))

/-- Lean-only (Rocq `Local Notation LJ`). -/
abbrev AxLedgerG3.LJ (γ : GName) (GD : Gdexec) (e : Geid) (fin : Mea GF) (R : IProp GF) :
    IProp GF :=
  @ledgerJoint hlc GF _ (impGG γ GD) _ AxClsStep2.OCX 2 γ (baseX γ) GD e fin R

/-- Lean-only: the graph pin of the instance. -/
theorem AxLedgerG3.gconstEq (γ : GName) (GD GD' : Gdexec) :
    @AxirisG.gconstInterp GF (impGG γ GD) GD' ⊢ ⌜GD' = GD⌝ := .rfl

/-- Lean-only: the local state of the instance is trivial. -/
theorem AxLedgerG3.localTrue (γ : GName) (GD GD' : Gdexec) (i : Agent) (k : Nat) (ls : Unit) :
    ⊢ @AxirisG.localInterp GF (impGG γ GD) GD' i k ls := by
  show ⊢ iprop(True)
  itrivial

/-- Lean-only: one unfolding of `TW` at a hart state. -/
theorem AxLedgerG3.twUnfold (γ : GName) (GD : Gdexec) (s : Athread) (i : Agent) :
    AxLedgerG3.TW (hlc := hlc) (GF := GF) γ GD s i ⊣⊢
      iprop(@progressObl GF (impGG γ GD) .MaybeStuck i s ∧
        @wpdMPreStepDef hlc GF _ (impGG γ GD) mpPol rvwmoCatConsistent i
          (fun s' Φ' => @tierAWpd GF hlc _ _ mpPol GD (GName × GName) Unit
            (obStInterpLG AxClsStep2.OCX 2 L0x gs0 baseX) (γ, γ) s' .MaybeStuck i Φ') s
          (fun _ => iprop(⌜True⌝))) :=
  @AxWpD.wpdMUnfoldStep hlc GF _ (impGG γ GD) mpPol rvwmoCatConsistent .MaybeStuck i s _

/-- `AxClsStep2.LJAny` at this instance. -/
theorem LJAnyG (γ : GName) (GD : Gdexec) (Hreal : progRealizes PMpb GD)
    (Hcons : rvwmoCatConsistent GD) (e : Geid) (P : Prop) :
    P → ⊢ AxLedgerG3.LJ (hlc := hlc) (GF := GF) γ GD e ∅ iprop(True ∗ ⌜P⌝) :=
  LJAny (hlc := hlc) (GF := GF) γ GD Hreal Hcons e P

/-- THE ONLY CHANGED RULE: the gated commit rule, fed by the bridge. -/
theorem wpEvStepClosedG (γ : GName) (GD : Gdexec) (Hcons : rvwmoCatConsistent GD) (i k : Nat)
    (val : Unit → Prop) (k' : Unit → Nat) (Ψ : Unit → IProp GF)
    (He : (i, k) ∈ GD.gdG.gxGmo) :
    ⊢ AxLedgerG3.LJ (hlc := hlc) γ GD (i, k) ∅ iprop(True ∗ ⌜val ()⌝) -∗ Ψ () -∗
      @wpEvStep hlc GF _ (impGG γ GD) mpPol Unit GD i k (fun _ => True) val k' Ψ := by
  iintro Hj HΨ
  iapply (@wpEvStepLedgerG hlc GF _ (impGG γ GD) _ mpPol AxClsStep2.OCX 2 L0x gs0 γ (baseX γ)
    (impGGExt γ GD) Unit GD i k (fun _ => True) val k' Ψ () trivial (HwfG GD Hcons) (gs0Ok GD) He
    (gs0Nodef GD (i, k)) (gs0Pol GD (i, k))) $$ [Hj] HΨ
  iintro %na ⟨Hpg, Hna⟩
  ihave Hnin := naAtProgressNotElemOf GD i k na $$ Hpg
  icases Hnin with %Hnin
  imod annotAlloc na (i, k) iprop(True) Hnin $$ Hna with ⟨Hna, -⟩
  imodintro
  iexists iprop(True), (∅ : Mea GF), (∅ : Mea GF), ()
  isplitr
  · iapply (@AxTokLedgerWp.naSplittingWfEmpty GF (impGG γ GD) _ mpPol)
  isplitl [Hj]
  · iapply (@ledgerJointGOfJoint hlc GF _ (impGG γ GD) _ AxClsStep2.OCX 2 L0x gs0 γ (baseX γ)
      GD (i, k) _ _ _ (HwfG GD Hcons) rfl He (fun _ h => h)) $$ Hj
  rw [@AxTokLedgerWp.annotInsertEq GF (impGG γ GD) _ mpPol na (i, k) iprop(True)]
  isplitl [Hna]
  · iexact Hna
  · iapply AxLedgerG3.localTrue

theorem wpdSkip2G (γ : GName) (GD : Gdexec) (i : Agent) (k' : Nat) (Ψ : IProp GF) :
    ⊢ ▷ Ψ -∗ @wpSkipStep GF (impGG γ GD) GD i k' Ψ := by
  iintro HΨ
  unfold wpSkipStep
  iintro %na Hna
  imodintro
  inext
  imodintro
  iexists ()
  isplitl [Hna]
  · iexact Hna
  isplitr
  · iapply AxLedgerG3.localTrue
  · iexact HΨ

/-- The shell for a non-read node (write / fence / halt). -/
theorem posShellG (γ : GName) (GD : Gdexec) (cpu : CPU) (i : Agent) (P : IProp GF) (k : Nat)
    (m : SailM Unit)
    (Hnord : ∀ (rs : RegFile) id K, ¬ areadStep (AxOpsem.grow GD i) ⟨hp cpu m rs, k⟩ id K)
    (Hb : ∀ (rs : RegFile) (l : Wlabel) (s' : Athread),
      AxOpsem.astepProg (AxOpsem.grow GD i) ⟨hp cpu m rs, k⟩ l s' →
      ⊢ P -∗ match wlWdata l with
        | some data =>
            @wpEvStep hlc GF _ (impGG γ GD) mpPol Unit GD i k (fun _ => True)
              (fun _ => graphData GD (i, k) = some data) (fun _ => s'.atK)
              (fun _ => AxLedgerG3.TW (hlc := hlc) γ GD s' i)
        | none =>
            @wpSkipStep GF (impGG γ GD) GD i s'.atK (AxLedgerG3.TW (hlc := hlc) γ GD s' i)) :
    ⊢ P -∗ ∀ rs : RegFile, AxLedgerG3.TW (hlc := hlc) γ GD ⟨hp cpu m rs, k⟩ i := by
  have H : ⊢ ∀ rs : RegFile, P -∗ AxLedgerG3.TW (hlc := hlc) γ GD ⟨hp cpu m rs, k⟩ i := by
    iloeb as IH
    iintro %rs HP
    iapply (AxLedgerG3.twUnfold (hlc := hlc) γ GD _ i).2
    isplit
    · simp only [progressObl]
      itrivial
    unfold wpdMPreStepDef
    iintro %GD' %ls ⟨%Hc, #Hg, Hloc⟩
    ihave Hok := AxLedgerG3.gconstEq γ GD GD' $$ Hg
    icases Hok with %HGD
    subst GD'
    isplit
    · iintro %id %K %Hst
      exact (Hnord rs id K Hst).elim
    isplit
    · iintro %l %s' %Hst %_
      iapply (Hb rs l s' Hst) $$ HP
    isplit
    · iintro %s' %Hw
      obtain ⟨rs', rfl⟩ := awireRsOnly2 cpu m rs k s' Hw
      iapply wpdSkip2G
      inext
      iapply IH $$ %rs' HP
    · iintro %_
      iapply (@postLiftingTrue GF (impGG γ GD) mpPol (fun _ => iprop(⌜True⌝)) i _
        (by iintro _; ipureintro; trivial))
  iintro HP %rs
  iapply H $$ %rs HP

theorem hltShellG (γ : GName) (GD : Gdexec) (cpu : CPU) (i : Agent) (k : Nat) :
    ⊢ ∀ rs : RegFile, AxLedgerG3.TW (hlc := hlc) (GF := GF) γ GD ⟨hp cpu hlt rs, k⟩ i := by
  have H := posShellG (hlc := hlc) (GF := GF) γ GD cpu i iprop(True) k hlt
    (fun rs id K => hltNoRead cpu _ rs k id K)
    (fun rs l s' Hst => (hltNoAstep cpu _ rs k l s' Hst).elim)
  iintro %rs
  ihave H' := H $$ []
  · itrivial
  iapply H' $$ %rs

/-- The shell for a hart-1 read node, ANY continuation. -/
theorem readShellG (γ : GName) (GD : Gdexec) (cpu : CPU) (ak : AK) (pa : PAddr)
    (Hdev : devAddr pa = false) (Hlat : (classify ak).akLatest = false)
    (Hfe : (classify ak).akIfetch = false)
    (KK : Result (BitVec (8 * 1) × Option Bool) Arch.abort → SailM Unit) (k : Nat)
    (Hrow : ∀ lb, (AxOpsem.grow GD 1)[k]? = some lb → aidentAdvRd (aident lb) = 1)
    (P : IProp GF)
    (Hcont : ∀ (v : List (BitVec 8)) (b : BitVec 8) (rs : RegFile),
      graphValue GD (1, k) = some v → v = [b] →
      ⊢ P -∗ @wpEvStep hlc GF _ (impGG γ GD) mpPol Unit GD 1 k (fun _ => True)
        (fun _ => graphValue GD (1, k) = some v) (fun _ => k + 1)
        (fun _ => AxLedgerG3.TW (hlc := hlc) γ GD ⟨hp cpu (KK (.Ok (b, none))) rs, k + 1⟩ 1)) :
    ⊢ P -∗ ∀ rs : RegFile, AxLedgerG3.TW (hlc := hlc) γ GD
      ⟨hp cpu (.impure (.ok (.memRead 1 64 (l3pRreq ak pa))) KK) rs, k⟩ 1 := by
  have H : ⊢ ∀ rs : RegFile, P -∗ AxLedgerG3.TW (hlc := hlc) γ GD
      ⟨hp cpu (.impure (.ok (.memRead 1 64 (l3pRreq ak pa))) KK) rs, k⟩ 1 := by
    iloeb as IH
    iintro %rs HP
    iapply (AxLedgerG3.twUnfold (hlc := hlc) γ GD _ 1).2
    isplit
    · simp only [progressObl]
      itrivial
    unfold wpdMPreStepDef
    iintro %GD' %ls ⟨%Hc, #Hg, Hloc⟩
    ihave Hok := AxLedgerG3.gconstEq γ GD GD' $$ Hg
    icases Hok with %HGD
    subst GD'
    isplit
    · iintro %id %K %Hst
      have Hst' := Hst
      obtain ⟨lb, Hlk, Hidlb, _, -⟩ := Hst
      have Hadv1 : aidentAdvRd id = 1 := by rw [← Hidlb]; exact Hrow lb Hlk
      rw [if_pos Hadv1]
      iintro %v %Hgv %Hlen
      obtain ⟨lb', b, -, -, -, rfl, HK⟩ := readInvGen cpu _ ak pa Hdev Hlat KK rs k id K v Hst' Hlen
      rw [HK, Hadv1]
      iapply (Hcont [b] b rs Hgv rfl) $$ HP
    isplit
    · iintro %l %s' %Hst %_
      exact (readAstepVacuous2 GD cpu ak pa Hdev Hfe KK rs k l s' Hst).elim
    isplit
    · iintro %s' %Hw
      obtain ⟨rs', rfl⟩ := awireRsOnly2 cpu _ rs k s' Hw
      iapply wpdSkip2G
      inext
      iapply IH $$ %rs' HP
    · iintro %_
      iapply (@postLiftingTrue GF (impGG γ GD) mpPol (fun _ => iprop(⌜True⌝)) 1 _
        (by iintro _; ipureintro; trivial))
  iintro HP %rs
  iapply H $$ %rs HP

theorem wpdWG (γ : GName) (GD : Gdexec) (Hreal : progRealizes PMpb GD)
    (Hcons : rvwmoCatConsistent GD) (cpu : CPU) (pa : PAddr)
    (Hdev : devAddr pa = false) (k : Nat) (m' : SailM Unit)
    (Hnext : ⊢ ∀ rs : RegFile, AxLedgerG3.TW (hlc := hlc) (GF := GF) γ GD ⟨hp cpu m' rs, k + 1⟩ 0) :
    ⊢ ∀ rs : RegFile, AxLedgerG3.TW (hlc := hlc) (GF := GF) γ GD
      ⟨hp cpu (.impure (.ok (.memWrite 1 64 (l3pWreq l3pAkP pa b1))) (fun _ => m')) rs, k⟩ 0 := by
  have H := posShellG (hlc := hlc) (GF := GF) γ GD cpu 0 iprop(True) k _
    (fun rs id K => noReadAtWrite cpu _ pa Hdev b1 m' rs k id K)
    (fun rs l s' Hst => by
      obtain ⟨rfl, rfl, lb, Hlb, Hwr, Hd⟩ := writeInv2 cpu _ pa Hdev b1 m' rs k l s' Hst
      simp only [wlWdata, l3pWbytes1]
      iintro _
      iapply (wpEvStepClosedG (hlc := hlc) γ GD Hcons 0 k _ _ _
        (rowInGmo GD 0 k lb (HwfG GD Hcons) Hlb (aidentWrMem lb _ Hwr))) $$ [] []
      · iapply (LJAnyG (hlc := hlc) γ GD Hreal Hcons (0, k) _ ?_)
        unfold graphData
        rw [gxLblGrow, Hlb]
        exact Hd
      · iapply Hnext $$ %rs)
  iintro %rs
  ihave H' := H $$ []
  · itrivial
  iapply H' $$ %rs

theorem wpdH0hG (γ : GName) (GD : Gdexec) (Hreal : progRealizes PMpb GD)
    (Hcons : rvwmoCatConsistent GD) (cpu : CPU) :
    ⊢ ∀ rs : RegFile, AxLedgerG3.TW (hlc := hlc) (GF := GF) γ GD ⟨hp cpu h0hM0 rs, 0⟩ 0 := by
  refine wpdWG γ GD Hreal Hcons cpu xpaM xpaMRam 0 h0hM1 ?_
  have H := posShellG (hlc := hlc) (GF := GF) γ GD cpu 0 iprop(True) 1 h0hM1
    (fun rs id K => noReadAtFence cpu _ h0hM2 rs 1 id K)
    (fun rs l s' Hst => by
      obtain ⟨rfl, rfl, -⟩ := fenceInv2 cpu _ h0hM2 rs 1 l s' Hst
      simp only [wlWdata]
      iintro _
      iapply wpdSkip2G
      inext
      iapply (wpdWG (hlc := hlc) γ GD Hreal Hcons cpu ypaM ypaMRam 2 hlt
        (hltShellG (hlc := hlc) γ GD cpu 0 3)) $$ %rs)
  iintro %rs
  ihave H' := H $$ []
  · itrivial
  iapply H' $$ %rs

theorem wpdRG (γ : GName) (GD : Gdexec) (Hreal : progRealizes PMpb GD)
    (Hcons : rvwmoCatConsistent GD) (cpu : CPU) (ak : AK) (pa : PAddr)
    (Hdev : devAddr pa = false) (Hlat : (classify ak).akLatest = false)
    (Hfe : (classify ak).akIfetch = false)
    (KK : Result (BitVec (8 * 1) × Option Bool) Arch.abort → SailM Unit) (k : Nat)
    (Hnext : ∀ b : BitVec 8,
      ⊢ ∀ rs : RegFile, AxLedgerG3.TW (hlc := hlc) (GF := GF) γ GD
        ⟨hp cpu (KK (.Ok (b, none))) rs, k + 1⟩ 1) :
    ⊢ ∀ rs : RegFile, AxLedgerG3.TW (hlc := hlc) (GF := GF) γ GD
      ⟨hp cpu (.impure (.ok (.memRead 1 64 (l3pRreq ak pa))) KK) rs, k⟩ 1 := by
  have H := readShellG (hlc := hlc) (GF := GF) γ GD cpu ak pa Hdev Hlat Hfe KK k
    (row1Adv GD Hreal k) iprop(True) (fun v b rs Hgv Hv => by
      subst Hv
      have Hmem : ((1, k) : Geid) ∈ GD.gdG.gxGmo := by
        have Hgv' := Hgv
        unfold graphValue at Hgv'
        rw [gxLblGrow] at Hgv'
        cases Hl : (AxOpsem.grow GD 1)[k]? with
        | none => rw [Hl] at Hgv'; cases Hgv'
        | some lb =>
          apply rowInGmo GD 1 k lb (HwfG GD Hcons) Hl
          rcases row1Shape GD Hreal k lb Hl with ⟨-, ts, b', rfl⟩ | ⟨-, ⟨ts, b', rfl⟩, -⟩ <;> rfl
      iintro _
      iapply (wpEvStepClosedG (hlc := hlc) γ GD Hcons 1 k _ _ _ Hmem) $$ [] []
      · iapply (LJAnyG (hlc := hlc) γ GD Hreal Hcons (1, k) _ Hgv)
      · iapply (Hnext b) $$ %rs)
  iintro %rs
  ihave H' := H $$ []
  · itrivial
  iapply H' $$ %rs

theorem wpdH1bG (γ : GName) (GD : Gdexec) (Hreal : progRealizes PMpb GD)
    (Hcons : rvwmoCatConsistent GD) (cpu : CPU) :
    ⊢ ∀ rs : RegFile, AxLedgerG3.TW (hlc := hlc) (GF := GF) γ GD ⟨hp cpu h1bM0 rs, 0⟩ 1 := by
  refine wpdRG γ GD Hreal Hcons cpu akAq ypaM ypaMRam rfl rfl h1bK 0 (fun b => ?_)
  rw [AxClsStep2.h1bKOk]
  by_cases hb : b = b1
  · rw [if_pos hb]
    exact wpdRG γ GD Hreal Hcons cpu l3pAkP xpaM xpaMRam rfl rfl (fun _ => hlt) 1
      (fun _ => hltShellG γ GD cpu 1 2)
  · rw [if_neg hb]
    exact hltShellG γ GD cpu 1 1

end wpdG

/-! ## `PMpb` at the gated notion -/

theorem PMpbVerifiedG : progLedgerVerifiedG 2 PMpb := by
  refine @progLedgerVerifiedG.mk 2 PMpb mpbGF _ _ _ mpPol AxClsStep2.OCX L0x gs0 GName Unit baseX
    initX (fun _ _ => True) ?_ ?_
  · intro GD i k e h
    exact absurd h notElemOfEmpty
  · intro GD Hreal Hcons
    have e1 : PMpb.apHarts = [0, 1] := rfl
    have e2 : PMpb.apS0 = mpbS0 := rfl
    rw [e1, e2]
    refine ⟨fun w a v Hw _ Hpl Hwb => schedPlain GD Hreal Hcons w a v Hw Hpl Hwb, ?_, ?_, ?_, ?_,
      ?_⟩
    · intro _ _ nm
      obtain ⟨γ1, γ2⟩ := nm
      iintro H
      icases (AxTokLedgerMp.bigSepLPair 0 1 _).1 $$ H with ⟨H0, -⟩
      icases (AxClsStep2.initXEq _ _).1 $$ H0 with %Heq
      simp only at Heq
      subst Heq
      iapply (AxTokLedgerMp.bigSepLPair 0 1 _).2
      rw [AxClsStep2.mpbS0At0, AxClsStep2.mpbS0At1]
      isplitl []
      · iapply (wpdH0hG (hlc := .hasNoLC) γ1 GD Hreal Hcons cpu0) $$ %zeroRegs
      · iapply (wpdH1bG (hlc := .hasNoLC) γ1 GD Hreal Hcons cpu0) $$ %zeroRegs
    · istart
      have HA := ledgerAlloc (GF := mpbGF) ({[xa := Holder.held 0]} : Ledger)
      imod HA with ⟨%γ, Ha, Hf⟩
      ihave Hx := BigSepM.bigSepM_singleton.1 $$ Hf
      imodintro
      iexists (γ, γ), ()
      isplitl [Ha Hx]
      · unfold obStInterpLG
        rw [AxClsStep2.baseXEmpty]
        isplitl [Hx]
        · iexact Hx
        · iapply ledgerInvGInit AxClsStep2.OCX 2 L0x gs0 γ GD
          unfold L0x
          iexact Ha
      · iapply (AxTokLedgerMp.bigSepLPair 0 1 _).2
        isplitl []
        · iapply (AxClsStep2.initXEq _ _).2
          ipureintro
          rfl
        · iapply (AxClsStep2.initXEq _ _).2
          ipureintro
          rfl
    · intro e r Hr
      exact absurd Hr notElemOfEmpty
    · intro e1 e2 _
      exact fun _ h => h
    · intro e e' He'
      left
      refine ⟨?_, fun s Hs => absurd Hs notElemOfEmpty⟩
      rcases elemOfUnion.1 He' with He' | He'
      · exact gmoPrefixGmoLt' _ Hcons.1 e e' ((elemOfListToSet (S := GSet Geid)).1 He')
      · exact absurd He' notElemOfEmpty

theorem PMpbViolFreeG (GD : Gdexec) :
    progRealizes PMpb GD → rvwmoCatConsistent GD → ¬ gdviolationHart 2 GD :=
  progViolFreeG 2 PMpb PMpbVerifiedG GD

/-! ## The negative examples, at the gated notion -/

theorem PPlNotVerifiedG : ¬ progLedgerVerifiedG 2 PPl :=
  progNotVerifiedGOfViol 2 PPl plG PPlRealizesPlG plGCat plGViol

theorem PMprNotVerifiedG : ¬ progLedgerVerifiedG 2 PMpr :=
  progNotVerifiedGOfViol 2 PMpr mprRace PMprRealizesRace mprRaceCat mprRaceViol

end Weak
