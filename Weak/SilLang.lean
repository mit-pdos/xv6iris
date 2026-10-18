/-
Weak: **(c) [OWN.100], increment 3 — the twin WP-verified language `EExprS` and its adequacy**
(`PROGRESS-W10N2p.md`).  Lean-only, no Rocq twin.  A PRIMED TWIN of `Weak.WeakEvLang`'s language and
`Weak.WeakEvAdequacy`'s exports; the registered ones are untouched.

The registered weak language runs an AMO as an exclusive read (`readOk`, possibly stale) and a
CONDITIONAL write — the window from the reservation's timestamps to the end of the log must be free of
other harts' writes — with a retry self-loop.  The twin adds ONE disjunct at that write node
(**`SilLang.silentWrite`**): the write completes WITHOUT a message when its bytes equal the bytes read
(at the reservation's timestamps), the window is clean up to a position `q` (`exclOkTs … (q + 1)`), and
`q` passes the write's ordering bounds (coherence, the dependency bound `SilCand.depView` — PARM's
exclusive-store fulfil pre-view over the node's dependency sources — the hart's own latest exclusive message
`SilCand.ownExcl`) — the candidate-level `SilCand.silentOk` at the WP-verified machine; afterwards the views
are those of a store at `q` with the read/write-ordering views raised to `q` (`SilCand.aqRaise`).

  §1  `SilLang.silentWrite`, `ecycleStepS`, `eprimStepS`, the wrapper **`SilLang.EExprS`** and its
      `Language` / `IrisGS_gen` instances, `ewpTrivS`, `epowerForkS`;
  §2  **`SilLang.adequacyCoreS`** (the one allocation, copied) and the exports **`SilLang.adequacyPhiS`**,
      **`SilLang.adequacyProtS`**.

Spec: FAITHFUL (the silent disjunct is the faithful silent AMO; the adequacy is Iris's, unchanged).
-/
import Weak.SilMember
import Weak.WeakEvAdequacy

namespace Weak

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Iris.Std
open Language.Notation PrimStep
open MachCSL MachCSL.Stdpp
open LeanRV64D

/-! # 1. The twin language -/

/-- **THE SILENT WRITE** of an exclusive RAM write node. -/
def SilLang.silentWrite (gen : Nat) (σ : WGState) (c : CPU) (m : SailM Unit)
    (fn : Option (Bool × Bool × Bool × Bool)) (e' : EExpr) (σ' : WGState) : Prop :=
  fn = none ∧
  ∃ n va req k, m = .impure (.ok (.memWrite n va req)) k ∧
  ∃ (v : BitVec (8 * n)) (q : Nat) (R : Wresv), devAddr req.pa = false ∧ req.value = some v ∧ n ≠ 0 ∧
    (classify req.access_kind).akLatest = true ∧ (classify req.access_kind).akSync = false ∧
    (σ.wgws c).wRes = some R ∧ R.rvBase = paZ req.pa ∧ R.rvTs.length = n ∧
    (∀ (j t : Nat), R.rvTs[j]? = some t →
      t ≤ q ∧ logByte (imgZ σ.wgimg) σ.wglog t (paZ req.pa + (j : Int)) =
        (WeakInterpProj.wbytes n v)[j]?) ∧
    exclOkTs σ.wglog c.val (paZ req.pa) R.rvTs (q + 1) ∧
    q ≤ σ.wglog.length ∧
    (∀ j, j < n → coh (σ.wgws c) (paZ req.pa + (j : Int)) ≤ q) ∧
    SilCand.depView (σ.wgws c) (depsAsrc (edeps σ c)) (depsVsrc (edeps σ c)) ≤ q ∧
    SilCand.ownExcl σ.wglog c.val ≤ q ∧
    e' = ECycle gen c (k (.Ok (some true))) none ∧
    σ' = ewgWs σ c
      (storePostRunD (SilCand.aqRaise (σ.wgws c) q) false
        (srcsView (σ.wgws c) (depsAsrc (edeps σ c))) (srcsView (σ.wgws c) (depsVsrc (edeps σ c)))
        (paZ req.pa) n q)

/-- The twin cycle step: the registered one, or a silent write. -/
def SilLang.ecycleStepS (gen : Nat) (σ : WGState) (c : CPU) (m : SailM Unit)
    (fn : Option (Bool × Bool × Bool × Bool)) (e' : EExpr) (σ' : WGState) : Prop :=
  ecycleStep gen σ c m fn e' σ' ∨ SilLang.silentWrite gen σ c m fn e' σ'

/-- The twin primitive step (`eprimStep` with the twin cycle step). -/
def SilLang.eprimStepS : EExpr → WGState → List Empty → EExpr → WGState → List EExpr → Prop
  | .Sail gen cpu m fn, σ, κ, e', σ', efs =>
    κ = [] ∧ efs = [] ∧
    ((ethreadLive σ gen ∧ SilLang.ecycleStepS gen σ cpu m fn e' σ') ∨
     (¬ ethreadLive σ gen ∧ e' = .Sail gen cpu m fn ∧ σ' = σ))
  | e, σ, κ, e', σ', efs => eprimStep e σ κ e' σ' efs

/-- The wrapper expression type carrying the twin language. -/
structure SilLang.EExprS where
  e : EExpr

instance SilLang.langS : Language SilLang.EExprS WGState Empty Empty where
  primStep c κ c' := SilLang.eprimStepS c.1.e c.2 κ c'.1.e c'.2.1 (c'.2.2.map SilLang.EExprS.e)
  toVal _ := none
  ofVal v := nomatch v
  coe_of_toVal_eq_some h := nomatch h
  toVal_coe v := nomatch v
  val_stuck _ := rfl

/-- The twin power-on fork. -/
def SilLang.epowerForkS (gen : Nat) : List SilLang.EExprS := (epowerFork gen).map SilLang.EExprS.mk

section inst

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [WeakGS GF]

instance SilLang.irisGSS : IrisGS_gen hlc SilLang.EExprS GF where
  invGS := MachFixedGS.invGS
  numLatersPerStep _ := 0
  forkPost _ := iprop(True)
  stateInterp_mono σ ns obs nt := by
    let := @MachFixedGS.invGS hlc GF _
    iintro $

/-- The Φ-free WP of the twin language. -/
def SilLang.ewpTrivS (E : CoPset) (e : SilLang.EExprS) : IProp GF :=
  WP e @ Stuckness.NotStuck ; E {{ fun _ => iprop(True) }}

theorem SilLang.bigSepL2ReplicateEwpS (es : List SilLang.EExprS) :
    ([∗list] e ∈ es, SilLang.ewpTrivS (hlc := hlc) (GF := GF) ⊤ e) ⊢
      [∗list] e;Φ ∈ es;List.replicate es.length (fun _ : Empty => iprop(True)),
        WP e @ Stuckness.NotStuck ; ⊤ {{ Φ }} := by
  refine Entails.trans ?_ BigSepL2.bigSepL2_replicate_right.2
  exact .rfl

end inst

/-! # 2. The adequacy, copied -/

section adequacy

variable {hlc : HasLC} {GF : BundledGFunctors}

/-- **THE ONE ALLOCATION, at the twin language** (`weakEvAdequacyCore`'s proof, verbatim). -/
theorem SilLang.adequacyCoreS [MachGpreS hlc GF] [WeakGpreS GF]
    (gen : Nat) (g : WGState) (D : CPU → List Register)
    (hD : ∀ c, (D c).Nodup)
    (Hpow : g.wgpow = true) (Hgen0 : g.wggen = 0) (Hlog : g.wglog = [])
    (Hws : ∀ c : CPU, g.wgws c = wsInit)
    (R : MachGS hlc GF → WeakGS GF → IProp GF)
    (Hwp : ∀ [HR : MachGS hlc GF] [HW : WeakGS GF],
      (([∗list] c ∈ cpus, [∗list] r ∈ D c, regPointsTo c r (DFrac.own 1) (g.wgregs c r)) ∗
        bigSepM (M := GMapF PAddr) (fun a b => wlatPointsto (paZ a) (DFrac.own 1) 0 b) g.wgimg ∗
        ([∗list] c ∈ cpus, hartView c) ∗
        wlogLb [] ∗
        ([∗list] d ∈ DevId.all, devFragAt (MachGS.era (hlc := hlc) (GF := GF)) d (g.wgdev.st d)))
      ⊢@{IProp GF} |={⊤}=>
        (R HR HW ∗ [∗list] e ∈ SilLang.epowerForkS gen, SilLang.ewpTrivS (hlc := hlc) (GF := GF) ⊤ e))
    (t2 : List SilLang.EExprS) (g2 : WGState) (φ : Prop)
    (Hex : ∀ [HR : MachGS hlc GF] [HW : WeakGS GF],
      (∀ e2, e2 ∈ t2 → NotStuck (Val := Empty) (e2, g2)) →
      (weakStateInterp (hlc := hlc) (GF := GF) g2 ∗ R HR HW) ⊢@{IProp GF} |={⊤}=> ⌜φ⌝)
    (hrtc : (SilLang.epowerForkS gen, g) -·->ₜₚ* (t2, g2)) : φ := by
  obtain ⟨n, κs, hsteps⟩ := (Language.erasedStep_nSteps _ _).mp hrtc
  refine wp_strong_adequacy_gen (hlc := hlc) (GF := GF) Stuckness.NotStuck (SilLang.epowerForkS gen)
    g n κs t2 g2 _ (fun _ => 0) ?_ hsteps
  intro Hinv
  letI F : MachFixedGS hlc GF := weakAdeqFixedGS Hinv
  imod (regs_alloc (hlc := hlc) (GF := GF) g.wgregs) with ⟨%rn, Hri, Hrc⟩
  imod (devs_alloc (hlc := hlc) (GF := GF) g.wgdev) with ⟨%dn, Hda, Hdf⟩
  imod (MonoList.own_alloc (GF := GF) ([] : List Wmsg)) with ⟨%γlog, Hla, Hlb⟩
  imod (ghost_map_alloc (GF := GF) (wlatInit g.wgimg)) with ⟨%γlat, Hlat, Hlatel⟩
  imod (ghost_map_alloc (GF := GF) (wcdsInit g.wgimg)) with ⟨%γcds, Hcds, Hcdsel⟩
  imod (names_alloc (GF := GF)
    (fun γ _ => iprop((γ ↪VAR{.own (1 : Qp).half} wsInit) ∗ (γ ↪VAR{.own (1 : Qp).half} wsInit)))
    (fun _ => wsHalvesAlloc)) with ⟨%wsn, Hwss⟩
  icases BigSepL.bigSepL_sep_eqv.1 $$ Hwss with ⟨HwsA, HwsF⟩
  letI HR : MachGS hlc GF := weakAdeqMachGS Hinv rn dn gen
  letI HW : WeakGS GF := weakAdeqWeakGS γlog γlat γcds wsn
  have hregs : ([∗list] cpu ∈ cpus, regCells (GF := GF) (rn cpu) (g.wgregs cpu)) ⊢
      [∗list] c ∈ cpus, [∗list] r ∈ D c, regPointsTo (hlc := hlc) (GF := GF) c r (DFrac.own 1)
        (g.wgregs c r) :=
    BigSepL.bigSepL_mono (fun {_ c} _ =>
      regCellsList (rn c) (g.wgregs c) (D c) (regMapOf (g.wgregs c)) (hD c)
        (fun r _ => regAgree_regMapOf (g.wgregs c) r))
  have hviews : ([∗list] c ∈ cpus, (wsn c ↪VAR{.own (1 : Qp).half} wsInit)) ⊢@{IProp GF}
      [∗list] c ∈ cpus, hartView c :=
    BigSepL.bigSepL_mono (fun {_ c} _ => hartViewIntro (GF := GF) c wsInit)
  have hlb : MonoList.lb_own (GF := GF) γlog ([] : List Wmsg) ⊢ wlogLb [] := .rfl
  have hdf : ([∗list] d ∈ DevId.all, devFragN (GF := GF) dn d (g.wgdev.st d)) ⊢
      [∗list] d ∈ DevId.all, devFragAt (MachGS.era (hlc := hlc) (GF := GF)) d (g.wgdev.st d) :=
    .rfl
  have hri : ([∗list] cpu ∈ cpus, regInterpAt (GF := GF) (rn cpu) (g.wgregs cpu)) ⊢
      [∗list] c ∈ cpus, regInterp (hlc := hlc) (GF := GF) c (g.wgregs c) := .rfl
  have hda : ([∗list] d ∈ DevId.all, devAuthN (GF := GF) dn d (g.wgdev.st d)) ⊢
      devInterpAt (MachGS.era (hlc := hlc) (GF := GF)) g.wgdev := .rfl
  have hla : MonoList.auth_own (GF := GF) γlog (DFrac.own 1) ([] : List Wmsg) ⊢ wlogAuth [] := .rfl
  imod (@Hwp HR HW) $$ [Hrc Hlatel Hcdsel HwsF Hlb Hdf] with ⟨HRr, Hwps⟩
  · isplitl [Hrc]
    · iapply hregs $$ Hrc
    isplitl [Hlatel Hcdsel]
    · unfold wlatPointsto wlatElem wclean wcdsEl
      rw [BigSepM.bigSepM_sep_eq]
      isplitl [Hlatel]
      · iapply (bigSepM_wlatInit
          (fun z tv => ghost_map_elem (GF := GF) γlat (DFrac.own 1) z tv) g.wgimg).1 $$ Hlatel
      · iapply (bigSepM_wcdsInit
          (fun z s => ghost_map_elem (GF := GF) γcds (DFrac.own 1) z s) g.wgimg).1 $$ Hcdsel
    isplitl [HwsF]
    · iapply hviews $$ HwsF
    isplitl [Hlb]
    · iapply hlb $$ Hlb
    · iapply hdf $$ Hdf
  imodintro
  iexists (fun σ ns κs' nt =>
      @stateInterp WGState Empty GF (@SilLang.irisGSS hlc GF HR HW).toStateInterp σ ns κs' nt),
    (List.replicate (SilLang.epowerForkS gen).length (fun _ : Empty => iprop(True))),
    (fun _ => iprop(True)),
    (@SilLang.irisGSS hlc GF HR HW).stateInterp_mono
  dsimp only
  simp only [@weakStateInterpEq hlc GF HR HW]
  isplitl [Hri Hda Hla Hlat Hcds HwsA]
  · unfold weakStateInterp
    isplitr
    · ipureintro; exact ⟨Hpow, Hgen0⟩
    isplitr
    · ipureintro; intro c; rw [Hws c, Hlog]; exact wsBoundedInit 0
    isplitr
    · ipureintro; rw [Hlog]; exact noViolationNil _
    isplitr
    · ipureintro; rw [Hlog]; intro m hm; cases hm
    isplitl [Hri]
    · iapply hri $$ Hri
    isplitl [Hda]
    · iapply hda $$ Hda
    isplitl [Hla]
    · rw [Hlog]; iapply hla $$ Hla
    isplitl [Hlat Hcds]
    · unfold wlatInterp
      iexists (wlatInit g.wgimg), (wcdsInit g.wgimg)
      iframe Hlat Hcds
      rw [Hlog]
      isplit
      · ipureintro; exact wlatInitAgree g.wgimg
      · ipureintro; exact wcdsInitAgree g.wgimg
    · unfold wwsInterp wwsAuth
      have hws : g.wgws = fun _ => wsInit := funext Hws
      rw [hws]
      iexact HwsA
  isplitl [Hwps]
  · iapply SilLang.bigSepL2ReplicateEwpS (hlc := hlc) (GF := GF) (SilLang.epowerForkS gen)
    iexact Hwps
  iintro %es' %t2' %Heq %Hlen %Hns Hsi _ _
  imod (@Hex HR HW (fun e2 he => Hns e2 trivial he)) $$ [Hsi HRr] with %hφ
  · iframe Hsi HRr
  iapply fupd_mask_intro_discard LawfulSet.empty_subset
  ipureintro
  exact hφ

/-- The φ export at the twin language. -/
theorem SilLang.adequacyPhiS [MachGpreS hlc GF] [WeakGpreS GF]
    (gen : Nat) (g : WGState) (D : CPU → List Register)
    (hD : ∀ c, (D c).Nodup)
    (Hpow : g.wgpow = true) (Hgen0 : g.wggen = 0) (Hlog : g.wglog = [])
    (Hws : ∀ c : CPU, g.wgws c = wsInit)
    (Hwp : ∀ [MachGS hlc GF] [WeakGS GF],
      (([∗list] c ∈ cpus, [∗list] r ∈ D c, regPointsTo c r (DFrac.own 1) (g.wgregs c r)) ∗
        bigSepM (M := GMapF PAddr) (fun a b => wlatPointsto (paZ a) (DFrac.own 1) 0 b) g.wgimg ∗
        ([∗list] c ∈ cpus, hartView c) ∗
        wlogLb [] ∗
        ([∗list] d ∈ DevId.all, devFragAt (MachGS.era (hlc := hlc) (GF := GF)) d (g.wgdev.st d)))
      ⊢@{IProp GF} |={⊤}=>
        ([∗list] e ∈ SilLang.epowerForkS gen, SilLang.ewpTrivS (hlc := hlc) (GF := GF) ⊤ e))
    (t2 : List SilLang.EExprS) (g2 : WGState)
    (hrtc : (SilLang.epowerForkS gen, g) -·->ₜₚ* (t2, g2)) :
    noViolation g2.wglog g2.wgws := by
  refine SilLang.adequacyCoreS (hlc := hlc) (GF := GF) gen g D hD Hpow Hgen0 Hlog Hws
    (fun _ _ => iprop(True)) ?_ t2 g2 _ ?_ hrtc
  · intro HR HW
    iintro H
    imod Hwp $$ H with H
    imodintro
    isplitr
    · ipureintro; trivial
    · iexact H
  · intro HR HW _
    iintro ⟨Hsi, -⟩
    ihave %hnv := weakStateInterpExport (hlc := hlc) (GF := GF) g2 $$ Hsi
    imodintro
    ipureintro
    exact hnv

/-- The protected-byte footprint export at the twin language. -/
theorem SilLang.adequacyProtS [MachGpreS hlc GF] [WeakGpreS GF]
    (gen : Nat) (g : WGState) (D : CPU → List Register)
    (hD : ∀ c, (D c).Nodup)
    (N : Namespace) (a base : Int)
    (Hpow : g.wgpow = true) (Hgen0 : g.wggen = 0) (Hlog : g.wglog = [])
    (Hws : ∀ c : CPU, g.wgws c = wsInit)
    (Hwp : ∀ [MachGS hlc GF] [WeakGS GF],
      (([∗list] c ∈ cpus, [∗list] r ∈ D c, regPointsTo c r (DFrac.own 1) (g.wgregs c r)) ∗
        bigSepM (M := GMapF PAddr) (fun a0 b => wlatPointsto (paZ a0) (DFrac.own 1) 0 b)
          g.wgimg ∗
        ([∗list] c ∈ cpus, hartView c) ∗
        wlogLb [] ∗
        ([∗list] d ∈ DevId.all, devFragAt (MachGS.era (hlc := hlc) (GF := GF)) d (g.wgdev.st d)))
      ⊢@{IProp GF} |={⊤}=>
        (wprotRegd (hlc := hlc) N a base ∗
          [∗list] e ∈ SilLang.epowerForkS gen, SilLang.ewpTrivS (hlc := hlc) (GF := GF) ⊤ e))
    (t2 : List SilLang.EExprS) (g2 : WGState)
    (hrtc : (SilLang.epowerForkS gen, g) -·->ₜₚ* (t2, g2)) :
    ∃ (γ : GName) (n0 r0 : Nat) (h : Option Nat),
      wprotAt g2.wglog a base n0 r0 ∧
      wlpAt g2.wglog base base n0 ∧ wlpAlt g2.wglog base n0 h := by
  refine SilLang.adequacyCoreS (hlc := hlc) (GF := GF) gen g D hD Hpow Hgen0 Hlog Hws
    (fun _ _ => wprotRegd (hlc := hlc) N a base) Hwp t2 g2 _ ?_ hrtc
  intro HR HW _
  exact wprotRegdExport N ⊤ g2 a base CoPset.subseteq_top

end adequacy

end Weak
