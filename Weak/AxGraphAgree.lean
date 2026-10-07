/-
Weak: **`wpEvLift` for the ld8 data-read node, under the CONCRETE graph-agreement instance**
`skelAxirisG` (AxSL tier).

Rocq: `iris/AxGraphAgree.v` @ xxvzwolszwmp.

## The Rocq header, in substance

Closes the wall `AxSymLd`'s FINDING 1 records (the step case quantifies over an ARBITRARY graph
`GD'` and a generic `AxirisG` gives no law tying it to the real `GD`): the instance is fixed to
`skelAxirisG γg Φp` (whose `gconstInterp` is `graphAgree`, an agreement resource), `graphAgree γg
GD` is an explicit premise, and inside the step case `graphAgreeAgree` pins `GD' = GD`.
Scope: the ld8 DATA-READ event only — a hart sitting at a plain RAM `memRead 8` node (AxFetch's
ld8 landing shape).  The three `wpPreStepDef` conjuncts:
(a) THE READ.  `areadStep`'s row lookup is a function of the position, so any witness at the same
    position has identity `afLd8DataIdent ea0`; its continuation agrees with `ld8Cont` on the
    valid-length domain (`ld8ReadStepDet`, from the node-local determinism `ld8PstepProgInv`).
    The `wpEvStep` is built from the caller's `∀ v` continuation by `wpReadStepAllWand` and
    re-targeted to the arbitrary `K'` by `wpEvStepExt`.
(b) EVERY OTHER PROGRAM STEP: every program step at the node is read-labelled, so `AStepAdmin`
    (`lbAdmin` is `False` on a load), `AStepWrite`/`AStepFence` (`wlWr`/`wlFence` are `none`) are
    impossible.  (Rocq also has `AStepFetch`, absorbed into the `∀ v` continuation; see
    deviation 2.)
(c) THE PLIC WIRE: from the caller's "wire already handled" premise.
Not attempted (as Rocq): the acert→fetch/decode→execute bridge (C3), reg_bridge (C7).

## Deviations from Rocq

1. NAMES: the tree's camelCase (map below).  Lean-only helpers, file-qualified:
   `AxGraphAgree.ld8NoFetch` (the node is not an i-cache read, derived from `Hread0`),
   `AxGraphAgree.ld8NoProgStep` (clause (b) as a pure fact).  `Interface.ReadReq.t 8` ↦
   `Mem_read_request 8 va …` (`va` a new parameter, AxOpsem deviation 1); `oib32` ↦ `Ibch`;
   `regstate` ↦ `RegFile`; `inl (w, None)` ↦ `.Ok (w, none)`; `S k` ↦ `k + 1`; `tvs.*2` ↦
   `tvs.map Prod.snd`.
2. O2 STAGE C (`notes/weak-port-o2-stageC.md`): the fetch is an ADMINISTRATIVE label, so Rocq's
   `AStepFetch` arm of clause (b) does not exist (AxOpsem deviation 2) and clause (b) is the
   pure `AxGraphAgree.ld8NoProgStep` (the `∀ v` continuation is used only by clause (a)).  The
   oracle parameter `Tax` (Rocq `skel_axirisG γg Φp Tax`) is deleted (AxWp deviation 10).
   The step clause is handled in ONE place (the `isplit` of the main proof plus
   `ld8NoProgStep`), so a later change to the WP step clause touches only it.  Q8: clause (b)
   now also receives the boot-image pin `⌜WeakAxRealize.fetchPin GD.gdG.gxImg l⌝`; the bullet
   introduces and discards it (`ld8NoProgStep` refutes the step without it, so it stays
   pin-free).
3. ACCESS KIND: Rocq's RAM-read arm is guarded by `ak_coh … = false`; the Lean `pnodeStep` read
   arm also has an i-cache (fetch) disjunct, so `ld8PstepProgInv` takes `akIfetch = false`
   (Rocq's section `Hcoh`, unused by Rocq's proof).  The main theorem does NOT take it: it is
   derived from `Hread0` (`AxGraphAgree.ld8NoFetch`).  As Rocq's section closing, the main
   theorem takes `Hdev`, `Hlat`, `Hsync` but neither `Hcoh` nor `Hea0` (both unused).
4. INSTANCES: Rocq's `Local Instance ax_graph_agree_axirisG := skel_axirisG …` ↦ statements
   name the instance (`@AxWp.wp hlc GF _ (skelAxirisG γg Φp) _ …`, AxWp deviation 8);
   `invGS_gen HasNoLc Σ` ↦ `[InvGS_gen hlc GF]` for any `hlc` (AxWp deviation 6).
   `wpEvStepExt` is stated for an arbitrary `AxirisG` (Rocq: at the section's skeleton
   instance; strictly more general).
5. `ld8State`/`ld8Cont`/`ld8PstepProgInv`/`ld8ReadStepDet` take the node's data explicitly
   (Rocq section variables); `ld8ReadStepDet` and `ld8PstepProgInv` take only the premises they
   use.

**Rocq → Lean name map.**  `ld8_state` `ld8State`, `ld8_cont` `ld8Cont`, `athread_eq`
`athreadEq`, `ld8_pstep_prog_inv` `ld8PstepProgInv`, `ld8_read_step_det` `ld8ReadStepDet`,
`wp_ev_step_ext` `wpEvStepExt`, `wp_skip_step_of_psi` `wpSkipStepOfPsi`,
`wp_ld8_forallv_of_graph_agree` `wpLd8ForallvOfGraphAgree`.

**Dropped:** nothing.
-/
import Weak.AxReadAll
import Weak.AxFetch1

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D
open Wlabel

/-! ## 1. The node and its node-local determinism -/

section node
variable (cpu : CPU) (va : Nat) (req : Mem_read_request 8 va Arch.pa Arch.translation Arch.arch_ak)
  (KK : Result (BitVec (8 * 8) × Option Bool) Arch.abort → SailM Unit) (rs : RegFile)
  (ib : Ibch) (k : Nat)

/-- The hart sitting at the row's ld8 data-read event. -/
def ld8State : Athread :=
  ⟨.PHart cpu (.impure (.ok (.memRead 8 va req)) KK) rs none ib, k⟩

/-- The state after receiving the bytes `vs`. -/
def ld8Cont (vs : List (BitVec 8)) : Athread :=
  ⟨.PHart cpu (KK (.Ok (wordOfBytes 8 vs, none))) rs none ib, k + 1⟩

theorem athreadEq (x y : Athread) : x.atP = y.atP → x.atK = y.atK → x = y := by
  cases x; cases y; intro h1 h2; simp only at h1 h2; subst h1 h2; rfl

/-- THE STRUCTURAL DETERMINISM FACT: any program step from the node is the plain read of
`(false, paZ req.pa, 8)`, landing at `ld8Cont` of the label's own bytes. -/
theorem ld8PstepProgInv (d : Efab) (l : Wlabel) (p' : Pexv6) (d' : Efab) :
    devAddr req.pa = false → (classify req.access_kind).akIfetch = false →
    (classify req.access_kind).akLatest = false → (classify req.access_kind).akSync = false →
    pstepProg (ld8State cpu va req KK rs ib k).atP d l p' d' →
    ∃ tvs, l = LLoad false false (paZ req.pa) tvs [] ∧ tvs.length = 8 ∧
      p' = .PHart cpu (KK (.Ok (wordOfBytes 8 (tvs.map Prod.snd), none))) rs none ib ∧
      d' = d := by
  intro hdev hfe hlat hsync h
  cases p' with
  | PDisk _ => exact h.elim
  | PHart cpu' m' rs' fn' ib' =>
    obtain ⟨rfl, ors, oib, obar, rfl, rfl, hn, hd⟩ := h
    simp only [pstepNode, pnodeStep, hdev, Bool.false_eq_true, ↓reduceIte] at hn
    rcases hn with ⟨hif, _⟩ | ⟨_, ⟨_, w, tvs, hlen, hby, rfl, rfl, rfl, rfl, hdd, rfl, rfl⟩ |
      ⟨hl, _⟩⟩
    · rw [hfe] at hif; exact absurd hif Bool.false_ne_true
    · have hw : wordOfBytes 8 (tvs.map Prod.snd) = w := by
        rw [AxOpsem.sndEqWbytes 8 w tvs hlen hby, wordOfBytesWbytes]
      refine ⟨tvs, by rw [hsync], hlen, by rw [hw]; rfl, ?_⟩
      rw [hd, hdd]
    · rw [hlat] at hl; exact absurd hl Bool.false_ne_true

/-- (Lean-only) every program step from the node is a load: clause (b) has no case. -/
theorem AxGraphAgree.ld8NoProgStep (row : List Lbl) (l : Wlabel) (s' : Athread) :
    devAddr req.pa = false → (classify req.access_kind).akIfetch = false →
    (classify req.access_kind).akLatest = false → (classify req.access_kind).akSync = false →
    ¬ AxOpsem.astepProg row (ld8State cpu va req KK rs ib k) l s' := by
  intro hdev hfe hlat hsync h
  generalize hs0 : ld8State cpu va req KK rs ib k = s0 at h
  cases h with
  | AStepAdmin p k0 d l p' d' ha hs =>
    have hp : p = (ld8State cpu va req KK rs ib k).atP := by rw [hs0]
    subst hp
    obtain ⟨tvs, rfl, _⟩ := ld8PstepProgInv cpu va req KK rs ib k d l p' d' hdev hfe hlat hsync hs
    exact ha
  | AStepWrite p k0 d l lb p' d' _ hwr _ _ hs =>
    have hp : p = (ld8State cpu va req KK rs ib k).atP := by rw [hs0]
    subst hp
    obtain ⟨tvs, rfl, _⟩ := ld8PstepProgInv cpu va req KK rs ib k d l p' d' hdev hfe hlat hsync hs
    simp [wlWr] at hwr
  | AStepFence p k0 d l lb p' d' _ hfn _ hs =>
    have hp : p = (ld8State cpu va req KK rs ib k).atP := by rw [hs0]
    subst hp
    obtain ⟨tvs, rfl, _⟩ := ld8PstepProgInv cpu va req KK rs ib k d l p' d' hdev hfe hlat hsync hs
    simp [wlFence] at hfn

/-- (Lean-only) a node with a read step of the ld8 identity is not an i-cache read. -/
theorem AxGraphAgree.ld8NoFetch (row : List Lbl) (ea0 : Int) :
    devAddr req.pa = false →
    areadStep row (ld8State cpu va req KK rs ib k) (afLd8DataIdent ea0)
      (ld8Cont cpu KK rs ib k) →
    (classify req.access_kind).akIfetch = false := by
  intro hdev ⟨_, _, _, _, HK⟩
  obtain ⟨l, d, d', hrd, _, hp, _⟩ := HK (List.replicate 8 0#8) (by simp [afLd8DataIdent, aidentN])
  cases hf : (classify req.access_kind).akIfetch
  · rfl
  · exfalso
    obtain ⟨_, ors, oib, obar, _, _, hn, _⟩ := hp
    simp only [pstepNode, pnodeStep, hdev, Bool.false_eq_true, ↓reduceIte] at hn
    rcases hn with ⟨_, w, tvs, _, _, rfl, _⟩ | ⟨hif, _⟩
    · simp [wlRd, afLd8DataIdent, aidentRd] at hrd
    · rw [hf] at hif; exact absurd hif (by decide)

/-- Any `areadStep` witness at the node, of the ld8 identity, agrees with `ld8Cont` pointwise on
the valid-length domain. -/
theorem ld8ReadStepDet (row : List Lbl) (ea0 : Int) (id' : AidentT)
    (K' : List (BitVec 8) → Athread) (vs : List (BitVec 8)) :
    devAddr req.pa = false → (classify req.access_kind).akIfetch = false →
    (classify req.access_kind).akLatest = false → (classify req.access_kind).akSync = false →
    areadStep row (ld8State cpu va req KK rs ib k) id' K' →
    id' = afLd8DataIdent ea0 → vs.length = aidentN id' →
    K' vs = ld8Cont cpu KK rs ib k vs := by
  intro hdev hfe hlat hsync ⟨_, _, _, _, HK'⟩ hid hvs
  subst hid
  obtain ⟨l, d, d', _, hrv, hp, hk⟩ := HK' vs hvs
  obtain ⟨tvs, rfl, _, hpeq, _⟩ :=
    ld8PstepProgInv cpu va req KK rs ib k d _ (K' vs).atP d' hdev hfe hlat hsync hp
  simp only [wlRvals] at hrv
  apply athreadEq
  · rw [hpeq, hrv]; rfl
  · rw [hk]; rfl

end node

/-! ## 2. Two structural `wpEvStep` / `wpSkipStep` facts -/

section steps
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]

/-- Re-targeting `wpEvStep`'s successor position and continuation along a pointwise equality on
the `ok` domain. -/
theorem wpEvStepExt {A : Type} (GD0 : Gdexec) (i0 : Agent) (k0 : Nat) (ok val : A → Prop)
    (k'1 k'2 : A → Nat) (Ψ1 Ψ2 : A → IProp GF) :
    (∀ a, ok a → k'1 a = k'2 a) →
    (∀ a, ok a → Ψ1 a ⊢ Ψ2 a) →
    wpEvStep GD0 i0 k0 ok val k'1 Ψ1 ⊢ wpEvStep GD0 i0 k0 ok val k'2 Ψ2 := by
  intro hk hΨ
  unfold wpEvStep
  iintro H %na Hna
  imod H $$ %na Hna with H
  imodintro
  inext
  imod H with ⟨%a, %R, %nu, %nuu, %ls', %Hok, Hsplit, Hfe, Hna, Hloc, HΨa⟩
  imodintro
  iexists a, R, nu, nuu, ls'
  rw [← hk a Hok]
  isplitr
  · ipureintro; exact Hok
  iframe Hsplit Hfe Hna Hloc
  iapply (hΨ a Hok)
  iexact HΨa

end steps

section skel
variable {GF : BundledGFunctors.{0,0,0}} [AxannotGS GF] [AxgraphG GF] (γg : GName)
  (Φp : Gdexec → Geid → IProp GF)

/-- `wpSkipStep` closes from `Ψ` alone under the concrete instance. -/
theorem wpSkipStepOfPsi (GD : Gdexec) (i : Agent) (k' : Nat) (Ψ : IProp GF) :
    Ψ ⊢ @wpSkipStep GF (skelAxirisG γg Φp) GD i k' Ψ :=
  skelWpSkipStepOfPsi γg Φp GD i k' Ψ

end skel

/-! ## 3. The main result -/

section main
variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF] [AxannotGS GF]
  [AxgraphG GF] [Axpol] (γg : GName) (Φp : Gdexec → Geid → IProp GF)

/-- THE MAIN RESULT: `wpEvLift` for the ld8 data-read node, under the concrete graph-agreement
instance. -/
theorem wpLd8ForallvOfGraphAgree (GD : Gdexec) (i : Agent) (st : Stuckness)
    (Φ : Athread → IProp GF) (cpu : CPU) (va : Nat)
    (req : Mem_read_request 8 va Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (BitVec (8 * 8) × Option Bool) Arch.abort → SailM Unit) (rs : RegFile)
    (ib : Ibch) (k : Nat)
    (Hdev : devAddr req.pa = false) (Hlat : (classify req.access_kind).akLatest = false)
    (Hsync : (classify req.access_kind).akSync = false) (ea0 : Int)
    (Hread0 : areadStep (AxOpsem.grow GD i) (ld8State cpu va req KK rs ib k) (afLd8DataIdent ea0)
      (ld8Cont cpu KK rs ib k))
    (x0 : List (BitVec 8)) (Hlen0 : x0.length = aidentN (afLd8DataIdent ea0))
    (Hflow0 : ⊢ ∀ na, naAtProgress GD i (ld8State cpu va req KK rs ib k).atK na ∗
        AxirisG.annotInterp (self := skelAxirisG γg Φp) na -∗ |==> ▷ |==>
       ∃ (R : IProp GF) (naUsed naUnused : Mea GF)
         (ls' : @AxirisG.logTsT GF (skelAxirisG γg Φp)),
         naSplittingWf (Axpol.lobp GD (i, (ld8State cpu va req KK rs ib k).atK)) na naUsed
           naUnused ∗
         @flowEqDyn hlc GF _ (skelAxirisG γg Φp) GD (i, (ld8State cpu va req KK rs ib k).atK)
           (Axpol.sPol GD (i, (ld8State cpu va req KK rs ib k).atK)) naUsed
           iprop(R ∗ ⌜graphValue GD (i, (ld8State cpu va req KK rs ib k).atK) = some x0⌝) ∗
         AxirisG.annotInterp (self := skelAxirisG γg Φp)
           (PartialMap.union (PartialMap.union
             {[(i, (ld8State cpu va req KK rs ib k).atK) := R]} naUnused) na) ∗
         AxirisG.localInterp (self := skelAxirisG γg Φp) GD i
           (ld8Cont cpu KK rs ib k x0).atK ls') :
    ⊢ graphAgree γg GD -∗
      (□ ∀ s', ⌜awire (ld8State cpu va req KK rs ib k) s'⌝ -∗
        @AxWp.wp hlc GF _ (skelAxirisG γg Φp) _ st i s' Φ) -∗
      (∀ v, ⌜v.length = aidentN (afLd8DataIdent ea0)⌝ -∗
        @AxWp.wp hlc GF _ (skelAxirisG γg Φp) _ st i (ld8Cont cpu KK rs ib k v) Φ) -∗
      @AxWp.wp hlc GF _ (skelAxirisG γg Φp) _ st i (ld8State cpu va req KK rs ib k) Φ := by
  have Hfe := AxGraphAgree.ld8NoFetch cpu va req KK rs ib k _ ea0 Hdev Hread0
  iintro #Hgc #Hwire Hcont0
  iapply (@wpUnfoldStep hlc GF _ (skelAxirisG γg Φp) _ st i _ Φ).2
  isplit
  · -- the progress obligation
    cases st with
    | MaybeStuck =>
      unfold progressObl
      itrivial
    | NotStuck =>
      unfold progressObl
      iintro %GD' %ls ⟨%Hcons', #Hgc', Hloc⟩
      ihave %Heq := graphAgreeAgree γg GD GD' $$ Hgc Hgc'
      subst Heq
      iapply (@interpModIntro GF (skelAxirisG γg Φp))
      ipureintro
      refine ⟨[], ld8Cont cpu KK rs ib k (List.replicate 8 0#8), .inr
        ⟨afLd8DataIdent ea0, ld8Cont cpu KK rs ib k, List.replicate 8 0#8, ?_,
          by simp [afLd8DataIdent, aidentN], rfl⟩⟩
      rw [List.append_nil]
      exact Hread0
  · -- the step case
    unfold wpPreStepDef
    iintro %GD' %ls ⟨%Hcons', #Hgc', Hloc⟩
    ihave %Heq := graphAgreeAgree γg GD GD' $$ Hgc Hgc'
    subst Heq
    isplit
    · -- (a) THE READ
      iintro %id' %K' %Hstep'
      have Hideq : id' = afLd8DataIdent ea0 := by
        obtain ⟨lb1, hrow1, hid1, _⟩ := Hread0
        obtain ⟨lb2, hrow2, hid2, _⟩ := Hstep'
        have hlb : lb1 = lb2 := Option.some.inj (hrow1.symm.trans hrow2)
        rw [← hid2, ← hlb, hid1]
      subst Hideq
      have hadv : aidentAdvRd (afLd8DataIdent ea0) = 1 := rfl
      simp only [hadv, ↓reduceIte]
      ihave Hevbase := (@wpReadStepAllWand hlc GF _ (skelAxirisG γg Φp) _ st GD i
        (ld8State cpu va req KK rs ib k) (afLd8DataIdent ea0) (ld8Cont cpu KK rs ib k) Φ
        x0 Hlen0 Hflow0) $$ Hcont0
      have Hdet : ∀ a : List (BitVec 8), a.length = aidentN (afLd8DataIdent ea0) →
          K' a = ld8Cont cpu KK rs ib k a := fun a ha =>
        ld8ReadStepDet cpu va req KK rs ib k _ ea0 _ K' a Hdev Hfe Hlat Hsync Hstep' rfl ha
      iapply (@wpEvStepExt hlc GF _ (skelAxirisG γg Φp) _ _ GD i _ _ _
        (fun v => (ld8Cont cpu KK rs ib k v).atK) (fun v => (K' v).atK)
        (fun v => @AxWp.wp hlc GF _ (skelAxirisG γg Φp) _ st i (ld8Cont cpu KK rs ib k v) Φ)
        (fun v => @AxWp.wp hlc GF _ (skelAxirisG γg Φp) _ st i (K' v) Φ)
        (fun a ha => by rw [Hdet a ha]) (fun a ha => by rw [Hdet a ha]))
      iexact Hevbase
    isplit
    · -- (b) every other program step: none (Stage C: no fetch arm; Q8 pin unused)
      iintro %l %s' %Hstep' %_
      exact (AxGraphAgree.ld8NoProgStep cpu va req KK rs ib k _ l s' Hdev Hfe Hlat Hsync
        Hstep').elim
    · -- (c) the PLIC wire
      iintro %s' %Hw'
      iapply wpSkipStepOfPsi γg Φp
      iapply Hwire $$ %s' %Hw'

end main

end Weak
