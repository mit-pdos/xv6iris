/-
Weak: **`AxClsStep2`, PART 2 (§5.5–§5.7): the per-hart WPds of the positive program `PMpb` at an
ARBITRARY realized consistent graph, `PMpbVerified : progLedgerVerified 2 PMpb`, `PMpbViolFree`,
and non-vacuity (`PMpbRealizesMpr`, `mprNoViolationProg`).**

Rocq: `iris/AxClsStep2.v` @ xxvzwolszwmp, §5.5–§5.7 (lines 1075–1427).  Part 1 (§1–§5.4, the
Rocq header, deviations 1–6 and the rest of the name map) is `Weak/AxClsStep2.lean`.

## Deviations from Rocq (in addition to part 1's)

7. CONTEXTS (as `AxTokLedgerMp` deviation 5): the `wpd` section context (`invGS_gen HasNoLc Σ`,
   `axannotG`, `ledgerG`, `axannotGS`) ↦ `{hlc} {GF : BundledGFunctors.{0,0,0}}
   [InvGS_gen hlc GF] [AxannotGS GF] [LedgerG GF]` (`PMpbVerified` instantiates `.hasNoLC`);
   the section parameters `γ cpu GD Hreal Hcons` are explicit leading arguments (only those the
   Rocq `Proof using` names; `wpdW` takes `Hreal`, which its proof uses).  Rocq's
   `Local Instance ImpG` is the reducible def `impG γ GD` (not an instance); Rocq's
   `Local Existing Instance mp_pol` is passed explicitly as `mpPol`.  The Rocq notations
   `TW`/`LJ` are the Lean-only abbrevs `AxClsStep2.TW`/`AxClsStep2.LJ`.  Wand chains
   `A -∗ B` ↦ `⊢ A -∗ B`.
8. `readAstepVacuous2` (Rocq: no step at a read node under the EMPTY text oracle `Tf`), and
   hence `readShell`/`wpdR`, take `(classify ak).akIfetch = false` (part 1 deviation 2).
9. `mpbΣ` ↦ `mpbGF`, an `abbrev` for `AxTokLedgerMp.mprGF` (the same slot table
   `invΣ; ledgerΣ; axannotΣ`, with its instances).  `progLedgerVerified`'s `post` is
   `fun _ _ => True`.
10. PROOF ROUTE (not statements): the WPd shells unfold `AxWpD.wpdMUnfoldStep` (as
   `AxTokLedgerMp`); `wpdSkip2` is proved from `wpSkipStep`'s definition (Rocq: via
   `wp_skip_step_mono`); `LJAny` reads the ledger with `AxTokLedgerWp.ledgerAgreeKeep`.

**Rocq → Lean name map.**  `base_x` `baseX`, `size_take_gmo` `sizeTakeGmo`, `aident_rd_mem`
`aidentRdMem`, `aident_wr_mem` `aidentWrMem`, `row_in_gmo` `rowInGmo`, `ImpG` `impG`,
`ImpG_ext` `impGExt`, `LJ_any` `LJAny`, `wp_ev_step_closed'` `wpEvStepClosed'`, `wpd_skip2`
`wpdSkip2`, `pos_shell` `posShell`, `hlt_shell` `hltShell`, `read_astep_vacuous2`
`readAstepVacuous2`, `read_shell` `readShell`, `wpd_w` `wpdW`, `wpd_h0h` `wpdH0h`, `row1_adv`
`row1Adv`, `wpd_r` `wpdR`, `wpd_h1b` `wpdH1b`, `init_x` `initX`, `mpbΣ` `mpbGF`,
`P_mpb_verified` `PMpbVerified`, `P_mpb_viol_free` `PMpbViolFree`, `h_aread_gen` `hAreadGen`,
`word_of_bytes_B1` `wordOfBytesB1`, `h1b_k_B1` `h1bKB1`, `P_mpb_realizes_mpr`
`PMpbRealizesMpr`, `mpr_no_violation_prog` `mprNoViolationProg`.  Lean-only (file-qualified):
`AxClsStep2.baseXTake`, `AxClsStep2.baseXEmpty`, `AxClsStep2.TW`, `AxClsStep2.LJ`,
`AxClsStep2.gconstEq`, `AxClsStep2.localTrue`, `AxClsStep2.twUnfold`, `AxClsStep2.initXEq`,
`AxClsStep2.mpbS0At0/1`.

**Dropped:** nothing (the §6 `Print Assumptions` audit: the lint's axiom check covers it).
-/
import Weak.AxClsStep2

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D

/-! ## 5.5 THE PER-HART WPds at an ARBITRARY realized consistent graph

Base protocol `baseX γ GD σ s` := the ledger fragment of byte x at `hold GD |s|` — ONE definition
for the whole program (a function of the graph).  Every event's joint obligation is discharged by
`LJAny` from `holdStep`. -/

def baseX {GF : BundledGFunctors} [LedgerG GF] (γ : GName) (GD : Gdexec) (_σ : Unit)
    (s : GSet Geid) : IProp GF :=
  tokFrag γ xa (AxClsStep2.hold GD (FiniteSet.size s))

theorem sizeTakeGmo (l : List Geid) (n : Nat) :
    l.Nodup → n ≤ l.length → FiniteSet.size (LawfulSet.ofList (l.take n) : GSet Geid) = n := by
  intro Hnd Hn
  rw [sizeListToSet ((List.take_sublist n l).nodup Hnd), List.length_take]
  omega

theorem aidentRdMem (lb : Lbl) (x : Bool × Int × Nat) :
    aidentRd (aident lb) = some x → lbIsMem lb = true := by
  cases lb <;> simp [aident, aidentRd, lbIsMem, lbIsR, lbIsW, lbIsIo]

theorem aidentWrMem (lb : Lbl) (x : Bool × Int × Nat) :
    aidentWr (aident lb) = some x → lbIsMem lb = true := by
  cases lb <;> simp [aident, aidentWr, lbIsMem, lbIsR, lbIsW, lbIsIo]

theorem rowInGmo (GD : Gdexec) (i k : Nat) (lb : Lbl) :
    gwf GD.gdG → (AxOpsem.grow GD i)[k]? = some lb → lbIsMem lb = true →
    (i, k) ∈ GD.gdG.gxGmo := by
  rintro ⟨-, Hmem, -⟩ Hl Hm
  exact (Hmem _).2 ⟨lb, by rw [gxLblGrow]; exact Hl, Hm⟩

/-- Lean-only: the base at a gmo prefix. -/
theorem AxClsStep2.baseXTake {GF : BundledGFunctors} [LedgerG GF] (γ : GName) (GD : Gdexec)
    (σ : Unit) (n : Nat) (Hnd : GD.gdG.gxGmo.Nodup) (Hn : n ≤ GD.gdG.gxGmo.length) :
    baseX (GF := GF) γ GD σ (LawfulSet.ofList (GD.gdG.gxGmo.take n)) =
      tokFrag γ xa (AxClsStep2.hold GD n) := by
  unfold baseX
  rw [sizeTakeGmo _ n Hnd Hn]

/-- Lean-only: the base at the empty validated set. -/
theorem AxClsStep2.baseXEmpty {GF : BundledGFunctors} [LedgerG GF] (γ : GName) (GD : Gdexec)
    (σ : Unit) : baseX (GF := GF) γ GD σ ∅ = tokFrag γ xa (.held 0) := by
  unfold baseX
  rw [sizeEmpty]
  unfold AxClsStep2.hold
  rw [if_neg]
  rintro ⟨-, h⟩
  omega

section wpd
variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF] [AxannotGS GF]
  [LedgerG GF]

/-- Rocq `Local Instance ImpG` (a named reducible def). -/
@[reducible] def impG (γ : GName) (GD : Gdexec) : AxirisG GF :=
  axGA2 GD (GName × GName) Unit (obStInterpL AxClsStep2.OCX 2 baseX) (γ, γ)

theorem impGExt (γ : GName) (GD : Gdexec) :
    ∀ (GD' : Gdexec) (σ : @AxirisG.obSt GF (impG γ GD)) (s : GSet Geid),
      @AxirisG.obStInterp GF (impG γ GD) GD' σ s ⊣⊢
        baseX γ GD' σ s ∗ AxTokLedgerWp.ledgerInv AxClsStep2.OCX 2 γ GD' s :=
  fun _ _ _ => .rfl

/-- Lean-only (Rocq `Local Notation TW`). -/
abbrev AxClsStep2.TW (γ : GName) (GD : Gdexec) (s : Athread) (i : Agent) : IProp GF :=
  @tierAWpd GF hlc _ _ mpPol GD (GName × GName) Unit (obStInterpL AxClsStep2.OCX 2 baseX)
    (γ, γ) s .MaybeStuck i (fun _ => iprop(⌜True⌝))

/-- Lean-only (Rocq `Local Notation LJ`). -/
abbrev AxClsStep2.LJ (γ : GName) (GD : Gdexec) (e : Geid) (fin : Mea GF) (R : IProp GF) :
    IProp GF :=
  @ledgerJoint hlc GF _ (impG γ GD) _ AxClsStep2.OCX 2 γ (baseX γ) GD e fin R

/-- Lean-only: the graph pin of the instance. -/
theorem AxClsStep2.gconstEq (γ : GName) (GD GD' : Gdexec) :
    @AxirisG.gconstInterp GF (impG γ GD) GD' ⊢ ⌜GD' = GD⌝ := .rfl

/-- Lean-only: the local state of the instance is trivial. -/
theorem AxClsStep2.localTrue (γ : GName) (GD GD' : Gdexec) (i : Agent) (k : Nat) (ls : Unit) :
    ⊢ @AxirisG.localInterp GF (impG γ GD) GD' i k ls := by
  show ⊢ iprop(True)
  itrivial

/-- Lean-only: one unfolding of `TW` at a hart state. -/
theorem AxClsStep2.twUnfold (γ : GName) (GD : Gdexec) (s : Athread) (i : Agent) :
    AxClsStep2.TW (hlc := hlc) (GF := GF) γ GD s i ⊣⊢
      iprop(@progressObl GF (impG γ GD) .MaybeStuck i s ∧
        @wpdMPreStepDef hlc GF _ (impG γ GD) mpPol rvwmoCatConsistent i
          (fun s' Φ' => @tierAWpd GF hlc _ _ mpPol GD (GName × GName) Unit
            (obStInterpL AxClsStep2.OCX 2 baseX) (γ, γ) s' .MaybeStuck i Φ') s
          (fun _ => iprop(⌜True⌝))) :=
  @AxWpD.wpdMUnfoldStep hlc GF _ (impG γ GD) mpPol rvwmoCatConsistent .MaybeStuck i s _

/-- EVERY event's joint obligation, from the pure schedule. -/
theorem LJAny (γ : GName) (GD : Gdexec) (Hreal : progRealizes PMpb GD)
    (Hcons : rvwmoCatConsistent GD) (e : Geid) (P : Prop) :
    P → ⊢ AxClsStep2.LJ (hlc := hlc) (GF := GF) γ GD e ∅ iprop(True ∗ ⌜P⌝) := by
  intro HP
  unfold AxClsStep2.LJ ledgerJoint
  iintro %σ %n %L %Hn
  have Hnd := (HwfG GD Hcons).1
  have Hlt : n < GD.gdG.gxGmo.length := lookup_lt_Some Hn
  rw [AxClsStep2.baseXTake γ GD σ n Hnd (by omega)]
  iintro Hb Ha _
  icases AxTokLedgerWp.ledgerAgreeKeep γ L xa _ $$ Ha Hb with ⟨%HL, Ha, Hb⟩
  obtain ⟨Hmv, Hacc⟩ := holdStep GD Hreal Hcons n e Hn
  imod ledgerUpdate γ L xa _ (AxClsStep2.hold GD (n + 1)) $$ Ha Hb with ⟨Ha, Hb⟩
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  inext
  imod Hclose
  imodintro
  iexists σ, insert L xa (AxClsStep2.hold GD (n + 1))
  rw [AxClsStep2.baseXTake γ GD σ (n + 1) Hnd (by omega)]
  isplitl [Hb]
  · iexact Hb
  isplitl [Ha]
  · iexact Ha
  isplitr
  · ipureintro
    refine ⟨?_, ?_⟩
    · intro a
      by_cases Hne : a = xa
      · subst Hne
        rw [get?_insert_eq rfl, HL]
        exact Hmv
      · rw [get?_insert_ne (Ne.symm Hne)]
        exact .lmSame _
    · intro a Ha _ Hga
      unfold AxClsStep2.OCX at Ha
      subst Ha
      rw [get?_insert_eq rfl, HL]
      exact Hacc Hga
  isplitr
  · itrivial
  · ipureintro
    exact HP

theorem wpEvStepClosed' (γ : GName) (GD : Gdexec) (Hcons : rvwmoCatConsistent GD) (i k : Nat)
    (val : Unit → Prop) (k' : Unit → Nat) (Ψ : Unit → IProp GF)
    (He : (i, k) ∈ GD.gdG.gxGmo) :
    ⊢ AxClsStep2.LJ (hlc := hlc) γ GD (i, k) ∅ iprop(True ∗ ⌜val ()⌝) -∗ Ψ () -∗
      @wpEvStep hlc GF _ (impG γ GD) mpPol Unit GD i k (fun _ => True) val k' Ψ := by
  iintro Hj HΨ
  iapply (@wpEvStepLedgerJoint hlc GF _ (impG γ GD) _ mpPol AxClsStep2.OCX 2 γ (baseX γ)
    (impGExt γ GD) Unit GD i k (fun _ => True) val k' Ψ () trivial (HwfG GD Hcons) He
    (fun _ h => h)) $$ [Hj] HΨ
  iintro %na ⟨Hpg, Hna⟩
  ihave Hnin := naAtProgressNotElemOf GD i k na $$ Hpg
  icases Hnin with %Hnin
  imod annotAlloc na (i, k) iprop(True) Hnin $$ Hna with ⟨Hna, -⟩
  imodintro
  iexists iprop(True), (∅ : Mea GF), (∅ : Mea GF), ()
  isplitr
  · iapply (@AxTokLedgerWp.naSplittingWfEmpty GF (impG γ GD) _ mpPol)
  isplitl [Hj]
  · iexact Hj
  rw [@AxTokLedgerWp.annotInsertEq GF (impG γ GD) _ mpPol na (i, k) iprop(True)]
  isplitl [Hna]
  · iexact Hna
  · iapply AxClsStep2.localTrue

theorem wpdSkip2 (γ : GName) (GD : Gdexec) (i : Agent) (k' : Nat) (Ψ : IProp GF) :
    ⊢ ▷ Ψ -∗ @wpSkipStep GF (impG γ GD) GD i k' Ψ := by
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
  · iapply AxClsStep2.localTrue
  · iexact HΨ

/-- The shell for a non-read node (write / fence / halt). -/
theorem posShell (γ : GName) (GD : Gdexec) (cpu : CPU) (i : Agent) (P : IProp GF) (k : Nat)
    (m : SailM Unit)
    (Hnord : ∀ (rs : RegFile) id K, ¬ areadStep (AxOpsem.grow GD i) ⟨hp cpu m rs, k⟩ id K)
    (Hb : ∀ (rs : RegFile) (l : Wlabel) (s' : Athread),
      AxOpsem.astepProg (AxOpsem.grow GD i) ⟨hp cpu m rs, k⟩ l s' →
      ⊢ P -∗ match wlWdata l with
        | some data =>
            @wpEvStep hlc GF _ (impG γ GD) mpPol Unit GD i k (fun _ => True)
              (fun _ => graphData GD (i, k) = some data) (fun _ => s'.atK)
              (fun _ => AxClsStep2.TW (hlc := hlc) γ GD s' i)
        | none =>
            @wpSkipStep GF (impG γ GD) GD i s'.atK (AxClsStep2.TW (hlc := hlc) γ GD s' i)) :
    ⊢ P -∗ ∀ rs : RegFile, AxClsStep2.TW (hlc := hlc) γ GD ⟨hp cpu m rs, k⟩ i := by
  have H : ⊢ ∀ rs : RegFile, P -∗ AxClsStep2.TW (hlc := hlc) γ GD ⟨hp cpu m rs, k⟩ i := by
    iloeb as IH
    iintro %rs HP
    iapply (AxClsStep2.twUnfold (hlc := hlc) γ GD _ i).2
    isplit
    · simp only [progressObl]
      itrivial
    unfold wpdMPreStepDef
    iintro %GD' %ls ⟨%Hc, #Hg, Hloc⟩
    ihave Hok := AxClsStep2.gconstEq γ GD GD' $$ Hg
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
      iapply wpdSkip2
      inext
      iapply IH $$ %rs' HP
    · iintro %_
      iapply (@postLiftingTrue GF (impG γ GD) mpPol (fun _ => iprop(⌜True⌝)) i _
        (by iintro _; ipureintro; trivial))
  iintro HP %rs
  iapply H $$ %rs HP

theorem hltShell (γ : GName) (GD : Gdexec) (cpu : CPU) (i : Agent) (k : Nat) :
    ⊢ ∀ rs : RegFile, AxClsStep2.TW (hlc := hlc) (GF := GF) γ GD ⟨hp cpu hlt rs, k⟩ i := by
  have H := posShell (hlc := hlc) (GF := GF) γ GD cpu i iprop(True) k hlt
    (fun rs id K => hltNoRead cpu _ rs k id K)
    (fun rs l s' Hst => (hltNoAstep cpu _ rs k l s' Hst).elim)
  iintro %rs
  ihave H' := H $$ []
  · itrivial
  iapply H' $$ %rs

/-- No program step at a RAM read node (Stage C: an i-fetch access kind is excluded). -/
theorem readAstepVacuous2 (GD : Gdexec) (cpu : CPU) (ak : AK) (pa : PAddr)
    (Hdev : devAddr pa = false) (Hfe : (classify ak).akIfetch = false)
    (KK : Result (BitVec (8 * 1) × Option Bool) Arch.abort → SailM Unit) (rs : RegFile) (k : Nat)
    (l : Wlabel) (s' : Athread) :
    AxOpsem.astepProg (AxOpsem.grow GD 1)
      ⟨hp cpu (.impure (.ok (.memRead 1 64 (l3pRreq ak pa))) KK) rs, k⟩ l s' → False :=
  readNodeNoAstep cpu _ ak pa Hdev Hfe KK rs k l s'

/-- The shell for a hart-1 read node, ANY continuation. -/
theorem readShell (γ : GName) (GD : Gdexec) (cpu : CPU) (ak : AK) (pa : PAddr)
    (Hdev : devAddr pa = false) (Hlat : (classify ak).akLatest = false)
    (Hfe : (classify ak).akIfetch = false)
    (KK : Result (BitVec (8 * 1) × Option Bool) Arch.abort → SailM Unit) (k : Nat)
    (Hrow : ∀ lb, (AxOpsem.grow GD 1)[k]? = some lb → aidentAdvRd (aident lb) = 1)
    (P : IProp GF)
    (Hcont : ∀ (v : List (BitVec 8)) (b : BitVec 8) (rs : RegFile),
      graphValue GD (1, k) = some v → v = [b] →
      ⊢ P -∗ @wpEvStep hlc GF _ (impG γ GD) mpPol Unit GD 1 k (fun _ => True)
        (fun _ => graphValue GD (1, k) = some v) (fun _ => k + 1)
        (fun _ => AxClsStep2.TW (hlc := hlc) γ GD ⟨hp cpu (KK (.Ok (b, none))) rs, k + 1⟩ 1)) :
    ⊢ P -∗ ∀ rs : RegFile, AxClsStep2.TW (hlc := hlc) γ GD
      ⟨hp cpu (.impure (.ok (.memRead 1 64 (l3pRreq ak pa))) KK) rs, k⟩ 1 := by
  have H : ⊢ ∀ rs : RegFile, P -∗ AxClsStep2.TW (hlc := hlc) γ GD
      ⟨hp cpu (.impure (.ok (.memRead 1 64 (l3pRreq ak pa))) KK) rs, k⟩ 1 := by
    iloeb as IH
    iintro %rs HP
    iapply (AxClsStep2.twUnfold (hlc := hlc) γ GD _ 1).2
    isplit
    · simp only [progressObl]
      itrivial
    unfold wpdMPreStepDef
    iintro %GD' %ls ⟨%Hc, #Hg, Hloc⟩
    ihave Hok := AxClsStep2.gconstEq γ GD GD' $$ Hg
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
      iapply wpdSkip2
      inext
      iapply IH $$ %rs' HP
    · iintro %_
      iapply (@postLiftingTrue GF (impG γ GD) mpPol (fun _ => iprop(⌜True⌝)) 1 _
        (by iintro _; ipureintro; trivial))
  iintro HP %rs
  iapply H $$ %rs HP

/-! ### Hart 0 -/

theorem wpdW (γ : GName) (GD : Gdexec) (Hreal : progRealizes PMpb GD)
    (Hcons : rvwmoCatConsistent GD) (cpu : CPU) (pa : PAddr)
    (Hdev : devAddr pa = false) (k : Nat) (m' : SailM Unit)
    (Hnext : ⊢ ∀ rs : RegFile, AxClsStep2.TW (hlc := hlc) (GF := GF) γ GD ⟨hp cpu m' rs, k + 1⟩ 0) :
    ⊢ ∀ rs : RegFile, AxClsStep2.TW (hlc := hlc) (GF := GF) γ GD
      ⟨hp cpu (.impure (.ok (.memWrite 1 64 (l3pWreq l3pAkP pa b1))) (fun _ => m')) rs, k⟩ 0 := by
  have H := posShell (hlc := hlc) (GF := GF) γ GD cpu 0 iprop(True) k _
    (fun rs id K => noReadAtWrite cpu _ pa Hdev b1 m' rs k id K)
    (fun rs l s' Hst => by
      obtain ⟨rfl, rfl, lb, Hlb, Hwr, Hd⟩ := writeInv2 cpu _ pa Hdev b1 m' rs k l s' Hst
      simp only [wlWdata, l3pWbytes1]
      iintro _
      iapply (wpEvStepClosed' (hlc := hlc) γ GD Hcons 0 k _ _ _
        (rowInGmo GD 0 k lb (HwfG GD Hcons) Hlb (aidentWrMem lb _ Hwr))) $$ [] []
      · iapply (LJAny (hlc := hlc) γ GD Hreal Hcons (0, k) _ ?_)
        unfold graphData
        rw [gxLblGrow, Hlb]
        exact Hd
      · iapply Hnext $$ %rs)
  iintro %rs
  ihave H' := H $$ []
  · itrivial
  iapply H' $$ %rs

theorem wpdH0h (γ : GName) (GD : Gdexec) (Hreal : progRealizes PMpb GD)
    (Hcons : rvwmoCatConsistent GD) (cpu : CPU) :
    ⊢ ∀ rs : RegFile, AxClsStep2.TW (hlc := hlc) (GF := GF) γ GD ⟨hp cpu h0hM0 rs, 0⟩ 0 := by
  refine wpdW γ GD Hreal Hcons cpu xpaM xpaMRam 0 h0hM1 ?_
  have H := posShell (hlc := hlc) (GF := GF) γ GD cpu 0 iprop(True) 1 h0hM1
    (fun rs id K => noReadAtFence cpu _ h0hM2 rs 1 id K)
    (fun rs l s' Hst => by
      obtain ⟨rfl, rfl, -⟩ := fenceInv2 cpu _ h0hM2 rs 1 l s' Hst
      simp only [wlWdata]
      iintro _
      iapply wpdSkip2
      inext
      iapply (wpdW (hlc := hlc) γ GD Hreal Hcons cpu ypaM ypaMRam 2 hlt
        (hltShell (hlc := hlc) γ GD cpu 0 3)) $$ %rs)
  iintro %rs
  ihave H' := H $$ []
  · itrivial
  iapply H' $$ %rs

/-! ### Hart 1 -/

theorem row1Adv (GD : Gdexec) (Hreal : progRealizes PMpb GD) (k : Nat) (lb : Lbl) :
    (AxOpsem.grow GD 1)[k]? = some lb → aidentAdvRd (aident lb) = 1 := by
  intro Hl
  rcases row1Shape GD Hreal k lb Hl with ⟨-, ts, b, rfl⟩ | ⟨-, ⟨ts, b, rfl⟩, -⟩ <;> rfl

theorem wpdR (γ : GName) (GD : Gdexec) (Hreal : progRealizes PMpb GD)
    (Hcons : rvwmoCatConsistent GD) (cpu : CPU) (ak : AK) (pa : PAddr)
    (Hdev : devAddr pa = false) (Hlat : (classify ak).akLatest = false)
    (Hfe : (classify ak).akIfetch = false)
    (KK : Result (BitVec (8 * 1) × Option Bool) Arch.abort → SailM Unit) (k : Nat)
    (Hnext : ∀ b : BitVec 8,
      ⊢ ∀ rs : RegFile, AxClsStep2.TW (hlc := hlc) (GF := GF) γ GD
        ⟨hp cpu (KK (.Ok (b, none))) rs, k + 1⟩ 1) :
    ⊢ ∀ rs : RegFile, AxClsStep2.TW (hlc := hlc) (GF := GF) γ GD
      ⟨hp cpu (.impure (.ok (.memRead 1 64 (l3pRreq ak pa))) KK) rs, k⟩ 1 := by
  have H := readShell (hlc := hlc) (GF := GF) γ GD cpu ak pa Hdev Hlat Hfe KK k
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
      iapply (wpEvStepClosed' (hlc := hlc) γ GD Hcons 1 k _ _ _ Hmem) $$ [] []
      · iapply (LJAny (hlc := hlc) γ GD Hreal Hcons (1, k) _ Hgv)
      · iapply (Hnext b) $$ %rs)
  iintro %rs
  ihave H' := H $$ []
  · itrivial
  iapply H' $$ %rs

theorem wpdH1b (γ : GName) (GD : Gdexec) (Hreal : progRealizes PMpb GD)
    (Hcons : rvwmoCatConsistent GD) (cpu : CPU) :
    ⊢ ∀ rs : RegFile, AxClsStep2.TW (hlc := hlc) (GF := GF) γ GD ⟨hp cpu h1bM0 rs, 0⟩ 1 := by
  refine wpdR γ GD Hreal Hcons cpu akAq ypaM ypaMRam rfl rfl h1bK 0 (fun b => ?_)
  rw [AxClsStep2.h1bKOk]
  by_cases hb : b = b1
  · rw [if_pos hb]
    exact wpdR γ GD Hreal Hcons cpu l3pAkP xpaM xpaMRam rfl rfl (fun _ => hlt) 1
      (fun _ => hltShell γ GD cpu 1 2)
  · rw [if_neg hb]
    exact hltShell γ GD cpu 1 1

end wpd

/-! ## 5.6 PROGRAM-LEVEL K1 FOR THE BRANCHY MP PROGRAM, END TO END -/

def initX {GF : BundledGFunctors} [LedgerG GF] (nm : GName × GName) (_i : Agent) : IProp GF :=
  iprop(⌜nm.1 = nm.2⌝)

/-- Lean-only: `initX` is its pure conjunct. -/
theorem AxClsStep2.initXEq {GF : BundledGFunctors} [LedgerG GF] (nm : GName × GName) (i : Agent) :
    initX (GF := GF) nm i ⊣⊢ iprop(⌜nm.1 = nm.2⌝) := .rfl

/-- Rocq `mpbΣ := #[invΣ; ledgerΣ; axannotΣ]`: the same slot table as `mprGF`. -/
abbrev mpbGF : BundledGFunctors := mprGF

/-- Lean-only: the start states, by computation. -/
theorem AxClsStep2.mpbS0At0 : mpbS0 0 = ⟨hp cpu0 h0hM0 zeroRegs, 0⟩ := rfl
theorem AxClsStep2.mpbS0At1 : mpbS0 1 = ⟨hp cpu0 h1bM0 zeroRegs, 0⟩ := rfl

theorem PMpbVerified : progLedgerVerified 2 PMpb := by
  refine @progLedgerVerified.mk 2 PMpb mpbGF _ _ _ mpPol AxClsStep2.OCX GName Unit baseX initX
    (fun _ _ => True) ?_ ?_
  · intro GD i k e h
    exact absurd h notElemOfEmpty
  · intro GD Hreal Hcons
    have e1 : PMpb.apHarts = [0, 1] := rfl
    have e2 : PMpb.apS0 = mpbS0 := rfl
    rw [e1, e2]
    refine ⟨fun w a v Hw _ Hpl Hwb => schedPlain GD Hreal Hcons w a v Hw Hpl Hwb, ?_, ?_, ?_, ?_⟩
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
      · iapply (wpdH0h (hlc := .hasNoLC) γ1 GD Hreal Hcons cpu0) $$ %zeroRegs
      · iapply (wpdH1b (hlc := .hasNoLC) γ1 GD Hreal Hcons cpu0) $$ %zeroRegs
    · istart
      have HA := ledgerAlloc (GF := mpbGF) ({[xa := Holder.held 0]} : Ledger)
      imod HA with ⟨%γ, Ha, Hf⟩
      ihave Hx := BigSepM.bigSepM_singleton.1 $$ Hf
      imodintro
      iexists (γ, γ), ()
      isplitl [Ha Hx]
      · unfold obStInterpL
        rw [AxClsStep2.baseXEmpty]
        isplitl [Hx]
        · iexact Hx
        · iapply ledgerInvInit AxClsStep2.OCX 2 γ GD
          iexact Ha
      · iapply (AxTokLedgerMp.bigSepLPair 0 1 _).2
        isplitl []
        · iapply (AxClsStep2.initXEq _ _).2
          ipureintro
          rfl
        · iapply (AxClsStep2.initXEq _ _).2
          ipureintro
          rfl
    · intro e e' He'
      exact gmoPrefixGmoLt' _ Hcons.1 e e' ((elemOfListToSet (S := GSet Geid)).1 He')
    · intro e e' He'
      exact absurd He' notElemOfEmpty

/-- … hence violation-free on EVERY graph it realizes. -/
theorem PMpbViolFree (GD : Gdexec) :
    progRealizes PMpb GD → rvwmoCatConsistent GD → ¬ gdviolationHart 2 GD :=
  progViolFree 2 PMpb PMpbVerified GD

/-! ## 5.7 NON-VACUITY: `PMpb` realizes `mpr` (y = 1 read from the release, ld x = 1: the token
crosses harts), so `PMpbVerified` covers a graph with a real release/acquire handoff. -/

theorem hAreadGen (cpu : CPU) (row : List Lbl) (k : Nat) (aq : Bool) (ak : AK) (pa : PAddr)
    (Hdev : devAddr pa = false) (Hcoh : (classify ak).akIfetch = false)
    (Hsync : (classify ak).akSync = aq) (Hlat : (classify ak).akLatest = false)
    (ts : List Nat) (b : BitVec 8)
    (KK : Result (BitVec (8 * 1) × Option Bool) Arch.abort → SailM Unit) (rs : RegFile) :
    row[k]? = some (.LLoad aq (paZ pa) ts [b]) →
    areadStep row ⟨hp cpu (.impure (.ok (.memRead 1 64 (l3pRreq ak pa))) KK) rs, k⟩
      (.IRead aq (paZ pa) 1) (fun vs => ⟨hp cpu (KK (.Ok (wordOfBytes 1 vs, none))) rs, k + 1⟩) := by
  intro hrow
  refine ⟨_, hrow, rfl, rfl, ?_⟩
  intro vs hvs
  refine ⟨rdLabel false (classify ak).akLatest (classify ak).akSync (paZ pa) (tagVals vs)
      (rdAsrc (classify ak).akLatest ibNone), OpaxWit.wtD0, OpaxWit.wtD0, ?_, ?_,
    l3pReadStep cpu ak pa Hdev Hcoh KK rs ibNone OpaxWit.wtD0 vs hvs, rfl⟩
  · rw [Hlat, Hsync]
    simp only [rdLabel, wlRd, aidentRd, tagValsLength, Bool.false_eq_true, ↓reduceIte]
    rw [hvs]
    rfl
  · rw [rdLabelRvals _ _ _ _ _ _ rfl, tagValsSnd]

theorem wordOfBytesB1 : wordOfBytes 1 [b1] = b1 := by
  have H := wordOfBytesByte 1 [b1] 0 rfl (by omega)
  rw [nthByteBv8] at H
  exact H

theorem h1bKB1 : h1bK (.Ok (wordOfBytes 1 [b1], none)) = h1bM1 := by
  show (if wordOfBytes 1 [b1] = b1 then h1bM1 else hlt) = h1bM1
  rw [if_pos wordOfBytesB1]

theorem PMpbRealizesMpr : progRealizes PMpb AxTokLedgerMp.mpr := by
  refine ⟨by decide, rfl, AxClsStep2.harts01 _ (by decide +kernel), ?_,
    fun i => match i with | 0 => 3 | _ => 2,
    fun i => match i with
      | 0 => (⟨hp cpu0 hlt zeroRegs, 3⟩ : Athread)
      | _ => (⟨hp cpu0 hlt zeroRegs, 2⟩ : Athread), fun _ => false, ?_⟩
  · intro i Hi
    simp only [PMpb, List.mem_cons, List.not_mem_nil, or_false] at Hi
    rcases Hi with rfl | rfl <;> rfl
  · intro i Hi
    simp only [PMpb, List.mem_cons, List.not_mem_nil, or_false] at Hi
    rcases Hi with rfl | rfl
    · refine ⟨?_, rfl⟩
      refine nsteps_l (clsStep.CSProg _ _ _ _
        (hAstepWrite cpu0 (AxOpsem.grow AxTokLedgerMp.mpr 0) 0 xpaM xpaMRam b1 .WCplain h0hM1
          zeroRegs rfl) trivial ?_) ?_
      · intro lb _ Hlb
        have h : some lb = some (Lbl.LStore false xa [b1] .WCplain) := Hlb.symm
        cases h
        rfl
      refine nsteps_l (clsStep.CSProg _ _ _ _
        (hAstepFence cpu0 (AxOpsem.grow AxTokLedgerMp.mpr 0) 1 h0hM2 zeroRegs rfl) trivial ?_) ?_
      · intro lb Hx
        simp [wlWr] at Hx
      refine nsteps_l (clsStep.CSProg _ _ _ _
        (hAstepWrite cpu0 (AxOpsem.grow AxTokLedgerMp.mpr 0) 2 ypaM ypaMRam b1 .WCrel hlt
          zeroRegs rfl) trivial ?_) ?_
      · intro lb _ Hlb
        have h : some lb = some (Lbl.LStore false ya [b1] .WCrel) := Hlb.symm
        cases h
        rfl
      exact nsteps_O _
    · refine ⟨?_, rfl⟩
      refine nsteps_l (clsStep.CSRead _ (.IRead true ya 1) _ [b1] false
        (hAreadGen cpu0 (AxOpsem.grow AxTokLedgerMp.mpr 1) 0 true akAq ypaM ypaMRam rfl rfl rfl
          [2] b1 h1bK zeroRegs rfl) rfl rfl) ?_
      show nsteps (clsStep AxTokLedgerMp.mpr 1) 1
        ((⟨hp cpu0 (h1bK (.Ok (wordOfBytes 1 [b1], none))) zeroRegs, 0 + 1⟩ : Athread), false) _
      rw [h1bKB1]
      refine nsteps_l (clsStep.CSRead _ (.IRead false xa 1) _ [b1] false
        (hAread cpu0 (AxOpsem.grow AxTokLedgerMp.mpr 1) 1 false l3pAkP xpaM xpaMRam rfl rfl rfl
          [1] b1 hlt zeroRegs rfl) rfl rfl) ?_
      exact nsteps_O _

/-- The release/acquire graph, now as a consequence of PROGRAM-level K1. -/
theorem mprNoViolationProg : ¬ gdviolationHart 2 AxTokLedgerMp.mpr :=
  PMpbViolFree AxTokLedgerMp.mpr PMpbRealizesMpr AxTokLedgerMp.mprCat

end Weak
