/-
Weak: **the interpretation and the φ export at the event language** (spike S3, revised).

Rocq: `iris/WeakEvAdequacy.v` @ xxvzwolszwmp (1cc222280).

## The Rocq header, in substance

`WeakAdequacy.weakSystemAdequacyPhi` restated over `WeakEvLang`'s event-granular language, and
then the SUCCESS CRITERION derived from it and from `WeakEvPf`'s correspondence with ZERO GLUE
PREMISES.  With the placement rule (control state in the EXPRESSION where control flow is
model-defined), σ is `WeakLang.WGState` verbatim and the state interpretation is
`WeakGhost.weakStateInterp` VERBATIM, so `weakStateInterpExport` (and the lock/footprint seam
exports) are reused with no wrapper.  This file owns the `IrisGS` instance at the new language,
the adequacy theorems and the success criterion.

SCOPE (deliberate, `WeakAdequacy`'s cuts): single era, no power thread in the pool's WPs'
obligations beyond `epowerFork`, no boot carve, placeholder names for the unused SC ghosts.  THE
POOL'S WPs ARE A HYPOTHESIS (the leaves abstract): what is delivered is the
invariant-extraction shape — the interpretation established at the initial state, threaded by
the WP, and READ OFF at every reachable state.

The lock-protocol exports (§2b–2b‴) add one thing to the WP package: the REGISTRATION SEAM
(`wlockRegd` / `wprotRegd` / `wprotRdRegd` plus a `protRead` record) for the byte of interest;
the conclusion is the pure log predicate read off through the seam at `⊤`.

## Deviations from Rocq

1. NAMES: the tree's camelCase (map below).  The generation is explicit (`gen : Nat`, Rocq's
   `Hgen : gen = 0` kept), as `WeakAdequacy` deviation 1.
2. CAMERAS / STATEMENT SHAPES: as `WeakAdequacy` deviations 2, 4, 5 — `[MachGpreS hlc GF]
   [WeakGpreS GF]` (and `[WprotG GF]` for `weakEvAdequacyProtread`), the client premise
   `∀ [MachGS hlc GF] [WeakGS GF], bundle ⊢ |={⊤}=> …`, `D : CPU → List Register` with
   `hD : ∀ c, (D c).Nodup`, `[∗ set] c ∈ fin_to_set CPU` ↦ `[∗list] c ∈ cpus`, `rtc erased_step`
   ↦ `-·->ₜₚ*`, `reducible e2 σ2` ↦ `Reducible (e2, g2)`.
3. THE DEVICE FRAGMENTS: Rocq's `uart_frag ∗ plic_frag ∗ virtio_frag` is `[∗list] d ∈ DevId.all,
   devFragAt MachGS.era d (g.wgdev.st d)` (`WeakAdequacy` deviation 3).  The devices themselves
   are threads of `epowerFork` (two UARTs, the disk agent at pool index `NCPU+2`, the PLIC at
   `NCPU+3`; WeakEvLang deviation 2), so their WPs are part of `[∗list] e ∈ epowerFork gen`.
4. THE RECORDS: the SC and weak records are `WeakAdequacy`'s `weakAdeqFixedGS` /
   `weakAdeqMachGS` / `weakAdeqWeakGS`; its helpers `regCellsList`, `wsHalvesAlloc` are reused.
5. PROOF FACTORING: Rocq repeats the whole allocation in each of the five adequacy theorems; Lean
   proves it ONCE, `weakEvAdequacyCore` (Lean-only): the WP package hands out an extra resource
   `R` beside the WPs, and the caller's export `Hex` reads `φ` off `weakStateInterp g2 ∗ R` (and
   the not-stuck fact) at `⊤`.  Each Rocq theorem is an instance of it with its own `R`/`Hex`;
   the statements are Rocq's.  Lean-only too: `bigSepL2ReplicateEwp`.
6. `weak_ev_irisGS` ↦ the instance `weakEvIrisGS : IrisGS_gen hlc EExpr GF` (its `StateInterp` is
   WeakGhost's `weakStateInterpInst`, shared with `weakIrisGS`); `ewp_triv` ↦ `ewpTriv`, notation
   `EWP e @ E` (declared; the statements spell `ewpTriv (hlc := hlc) (GF := GF) ⊤ e`, as
   `WeakAdequacy` spells `wwpTriv`, because the notation does not parse as a `[∗list]` body).
7. In `weakEvPfViolationFree`, Rocq's `rewrite /= epool_list_init` is `epoolListInit` (an `rfl`).

**File-qualified names:** none (no name of this file is in `notes/weak-port-dupnames.json`).

**Rocq → Lean name map.**  `weak_ev_irisGS` `weakEvIrisGS`, `ewp_triv` `ewpTriv`,
`weak_ev_adequacy_phi` `weakEvAdequacyPhi`, `weak_ev_adequacy_lockproto`
`weakEvAdequacyLockproto`, `weak_ev_adequacy_lockalt` `weakEvAdequacyLockalt`,
`weak_ev_adequacy_prot` `weakEvAdequacyProt`, `weak_ev_adequacy_protread`
`weakEvAdequacyProtread`, `weak_ev_adequacy_reducible` `weakEvAdequacyReducible`,
`epf_violation_free_hart` `epfViolationFreeHart`, `weak_ev_pf_violation_free`
`weakEvPfViolationFree`.  Lean-only: `weakEvAdequacyCore`, `bigSepL2ReplicateEwp`.

**Not ported:** nothing.

**Statements checked** (by hand, against Rocq): all; the changed spellings are the deviations
above.
-/
import Weak.WeakAdequacy
import Weak.WeakEvPf

namespace Weak

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Iris.Std
open Language.Notation PrimStep
open MachCSL MachCSL.Stdpp
open LeanRV64D

/-! ## 1. The `IrisGS` instance and the Φ-free WP -/

section inst

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [WeakGS GF]

/-- Rocq `weak_ev_irisGS`: `WeakGhost.weakIrisGS`'s twin at the event language. -/
instance weakEvIrisGS : IrisGS_gen hlc EExpr GF where
  invGS := MachFixedGS.invGS
  numLatersPerStep _ := 0
  forkPost _ := iprop(True)
  stateInterp_mono σ ns obs nt := by
    let := @MachFixedGS.invGS hlc GF _
    iintro $

/-- Rocq `ewp_triv`. -/
def ewpTriv (E : CoPset) (e : EExpr) : IProp GF :=
  WP e @ Stuckness.NotStuck ; E {{ fun _ => iprop(True) }}

/-- The pool's Φ-free WPs as the adequacy's `[∗list] e;Φ` (Lean-only). -/
theorem bigSepL2ReplicateEwp (es : List EExpr) :
    ([∗list] e ∈ es, ewpTriv (hlc := hlc) (GF := GF) ⊤ e) ⊢
      [∗list] e;Φ ∈ es;List.replicate es.length (fun _ : Empty => iprop(True)),
        WP e @ Stuckness.NotStuck ; ⊤ {{ Φ }} := by
  refine Entails.trans ?_ BigSepL2.bigSepL2_replicate_right.2
  exact .rfl

end inst

notation:20 "EWP " e:20 " @ " E:20 => ewpTriv E e

/-! ## 2. The adequacy core (deviation 5) -/

section adequacy

variable {hlc : HasLC} {GF : BundledGFunctors}

/-- THE ONE ALLOCATION: from the fresh-era clauses and a WP package handing out `R` beside the
pool's WPs, any `φ` readable off the reachable state's interpretation and `R` holds. -/
theorem weakEvAdequacyCore [MachGpreS hlc GF] [WeakGpreS GF]
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
        (R HR HW ∗ [∗list] e ∈ epowerFork gen, ewpTriv (hlc := hlc) (GF := GF) ⊤ e))
    (t2 : List EExpr) (g2 : WGState) (φ : Prop)
    (Hex : ∀ [HR : MachGS hlc GF] [HW : WeakGS GF],
      (∀ e2, e2 ∈ t2 → NotStuck (Val := Empty) (e2, g2)) →
      (weakStateInterp (hlc := hlc) (GF := GF) g2 ∗ R HR HW) ⊢@{IProp GF} |={⊤}=> ⌜φ⌝)
    (hrtc : (epowerFork gen, g) -·->ₜₚ* (t2, g2)) : φ := by
  obtain ⟨n, κs, hsteps⟩ := (Language.erasedStep_nSteps _ _).mp hrtc
  refine wp_strong_adequacy_gen (hlc := hlc) (GF := GF) Stuckness.NotStuck (epowerFork gen) g n
    κs t2 g2 _ (fun _ => 0) ?_ hsteps
  intro Hinv
  letI F : MachFixedGS hlc GF := weakAdeqFixedGS Hinv
  -- ---- allocate the ghost state ----
  imod (regs_alloc (hlc := hlc) (GF := GF) g.wgregs) with ⟨%rn, Hri, Hrc⟩
  imod (devs_alloc (hlc := hlc) (GF := GF) g.wgdev) with ⟨%dn, Hda, Hdf⟩
  imod (MonoList.own_alloc (GF := GF) ([] : List Wmsg)) with ⟨%γlog, Hla, Hlb⟩
  imod (ghost_map_alloc (GF := GF) (wlatInit g.wgimg)) with ⟨%γlat, Hlat, Hlatel⟩
  imod (ghost_map_alloc (GF := GF) (wcdsInit g.wgimg)) with ⟨%γcds, Hcds, Hcdsel⟩
  imod (names_alloc (GF := GF)
    (fun γ _ => iprop((γ ↪VAR{.own (1 : Qp).half} wsInit) ∗ (γ ↪VAR{.own (1 : Qp).half} wsInit)))
    (fun _ => wsHalvesAlloc)) with ⟨%wsn, Hwss⟩
  icases BigSepL.bigSepL_sep_eqv.1 $$ Hwss with ⟨HwsA, HwsF⟩
  -- ---- the two instances ----
  letI HR : MachGS hlc GF := weakAdeqMachGS Hinv rn dn gen
  letI HW : WeakGS GF := weakAdeqWeakGS γlog γlat γcds wsn
  -- ---- the conversions ----
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
  -- ---- run the caller's proof to obtain the seam resource and the WPs ----
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
      @stateInterp WGState Empty GF (@weakEvIrisGS hlc GF HR HW).toStateInterp σ ns κs' nt),
    (List.replicate (epowerFork gen).length (fun _ : Empty => iprop(True))),
    (fun _ => iprop(True)),
    (@weakEvIrisGS hlc GF HR HW).stateInterp_mono
  dsimp only
  simp only [@weakStateInterpEq hlc GF HR HW]
  isplitl [Hri Hda Hla Hlat Hcds HwsA]
  · -- the initial state interpretation
    unfold weakStateInterp
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
  · iapply bigSepL2ReplicateEwp (hlc := hlc) (GF := GF) (epowerFork gen)
    iexact Hwps
  iintro %es' %t2' %Heq %Hlen %Hns Hsi _ _
  -- THE EXPORT, the caller's
  imod (@Hex HR HW (fun e2 he => Hns e2 trivial he)) $$ [Hsi HRr] with %hφ
  · iframe Hsi HRr
  iapply fupd_mask_intro_discard LawfulSet.empty_subset
  ipureintro
  exact hφ

/-! ## 2a. The φ export at the language level -/

/-- Rocq `weak_ev_adequacy_phi`. -/
theorem weakEvAdequacyPhi [MachGpreS hlc GF] [WeakGpreS GF]
    (gen : Nat) (g : WGState) (D : CPU → List Register)
    (hD : ∀ c, (D c).Nodup)
    (Hgen : gen = 0)
    -- THE FRESH ERA
    (Hpow : g.wgpow = true) (Hgen0 : g.wggen = 0) (Hlog : g.wglog = [])
    (Hws : ∀ c : CPU, g.wgws c = wsInit)
    (Hwp : ∀ [MachGS hlc GF] [WeakGS GF],
      (([∗list] c ∈ cpus, [∗list] r ∈ D c, regPointsTo c r (DFrac.own 1) (g.wgregs c r)) ∗
        bigSepM (M := GMapF PAddr) (fun a b => wlatPointsto (paZ a) (DFrac.own 1) 0 b) g.wgimg ∗
        ([∗list] c ∈ cpus, hartView c) ∗
        wlogLb [] ∗
        ([∗list] d ∈ DevId.all, devFragAt (MachGS.era (hlc := hlc) (GF := GF)) d (g.wgdev.st d)))
      ⊢@{IProp GF} |={⊤}=> ([∗list] e ∈ epowerFork gen, ewpTriv (hlc := hlc) (GF := GF) ⊤ e))
    (t2 : List EExpr) (g2 : WGState)
    (hrtc : (epowerFork gen, g) -·->ₜₚ* (t2, g2)) :
    noViolation g2.wglog g2.wgws ∧ ∀ e2, e2 ∈ t2 → Reducible (e2, g2) := by
  have _ := Hgen
  refine weakEvAdequacyCore (hlc := hlc) (GF := GF) gen g D hD Hpow Hgen0 Hlog Hws
    (fun _ _ => iprop(True)) ?_ t2 g2 _ ?_ hrtc
  · intro HR HW
    iintro H
    imod Hwp $$ H with H
    imodintro
    isplitr
    · ipureintro; trivial
    · iexact H
  · intro HR HW hns
    iintro ⟨Hsi, -⟩
    ihave %hnv := weakStateInterpExport (hlc := hlc) (GF := GF) g2 $$ Hsi
    imodintro
    ipureintro
    refine ⟨hnv, fun e2 he => ?_⟩
    -- `toVal` is constantly `none`: not-stuck IS reducibility
    rcases hns e2 he with hv | hr
    · exact absurd hv (by simp [ToVal.toVal])
    · exact hr

/-! ## 2b. The lock-protocol export (T2-0) -/

/-- Rocq `weak_ev_adequacy_lockproto`. -/
theorem weakEvAdequacyLockproto [MachGpreS hlc GF] [WeakGpreS GF]
    (gen : Nat) (g : WGState) (D : CPU → List Register)
    (hD : ∀ c, (D c).Nodup)
    (N : Namespace) (a base : Int)
    (Hgen : gen = 0)
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
        (wlockRegd (hlc := hlc) N a base ∗ [∗list] e ∈ epowerFork gen, ewpTriv (hlc := hlc) (GF := GF) ⊤ e))
    (t2 : List EExpr) (g2 : WGState)
    (hrtc : (epowerFork gen, g) -·->ₜₚ* (t2, g2)) :
    ∃ n0 : Nat, wlpAt g2.wglog a base n0 := by
  have _ := Hgen
  refine weakEvAdequacyCore (hlc := hlc) (GF := GF) gen g D hD Hpow Hgen0 Hlog Hws
    (fun _ _ => wlockRegd (hlc := hlc) N a base) Hwp t2 g2 _ ?_ hrtc
  intro HR HW _
  exact wlockRegdExport N ⊤ g2 a base CoPset.subseteq_top

/-! ## 2b′. The alternation export (T2-0′ / F3′) -/

/-- Rocq `weak_ev_adequacy_lockalt`. -/
theorem weakEvAdequacyLockalt [MachGpreS hlc GF] [WeakGpreS GF]
    (gen : Nat) (g : WGState) (D : CPU → List Register)
    (hD : ∀ c, (D c).Nodup)
    (N : Namespace) (a base : Int)
    (Hgen : gen = 0)
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
        (wlockRegd (hlc := hlc) N a base ∗ [∗list] e ∈ epowerFork gen, ewpTriv (hlc := hlc) (GF := GF) ⊤ e))
    (t2 : List EExpr) (g2 : WGState)
    (hrtc : (epowerFork gen, g) -·->ₜₚ* (t2, g2)) :
    ∃ (n0 : Nat) (h : Option Nat), wlpAt g2.wglog a base n0 ∧ wlpAlt g2.wglog a n0 h := by
  have _ := Hgen
  refine weakEvAdequacyCore (hlc := hlc) (GF := GF) gen g D hD Hpow Hgen0 Hlog Hws
    (fun _ _ => wlockRegd (hlc := hlc) N a base) Hwp t2 g2 _ ?_ hrtc
  intro HR HW _
  exact wlockRegdExportAlt N ⊤ g2 a base CoPset.subseteq_top

/-! ## 2b″. The protected-byte footprint export (T2-0′ / F3″) -/

/-- Rocq `weak_ev_adequacy_prot`. -/
theorem weakEvAdequacyProt [MachGpreS hlc GF] [WeakGpreS GF]
    (gen : Nat) (g : WGState) (D : CPU → List Register)
    (hD : ∀ c, (D c).Nodup)
    (N : Namespace) (a base : Int)
    (Hgen : gen = 0)
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
        (wprotRegd (hlc := hlc) N a base ∗ [∗list] e ∈ epowerFork gen, ewpTriv (hlc := hlc) (GF := GF) ⊤ e))
    (t2 : List EExpr) (g2 : WGState)
    (hrtc : (epowerFork gen, g) -·->ₜₚ* (t2, g2)) :
    ∃ (γ : GName) (n0 r0 : Nat) (h : Option Nat),
      wprotAt g2.wglog a base n0 r0 ∧
      wlpAt g2.wglog base base n0 ∧ wlpAlt g2.wglog base n0 h := by
  have _ := Hgen
  refine weakEvAdequacyCore (hlc := hlc) (GF := GF) gen g D hD Hpow Hgen0 Hlog Hws
    (fun _ _ => wprotRegd (hlc := hlc) N a base) Hwp t2 g2 _ ?_ hrtc
  intro HR HW _
  exact wprotRegdExport N ⊤ g2 a base CoPset.subseteq_top

/-! ## 2b‴. The read-record export (T2-0′ / F3″) -/

/-- Rocq `weak_ev_adequacy_protread`. -/
theorem weakEvAdequacyProtread [MachGpreS hlc GF] [WeakGpreS GF] [WprotG GF]
    (gen : Nat) (g : WGState) (D : CPU → List Register)
    (hD : ∀ c, (D c).Nodup)
    (N : Namespace) (γr : GName) (a base : Int) (p : Nat)
    (Hgen : gen = 0)
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
        ((wprotRdRegd (hlc := hlc) N γr a base ∗ protRead γr a p) ∗
          [∗list] e ∈ epowerFork gen, ewpTriv (hlc := hlc) (GF := GF) ⊤ e))
    (t2 : List EExpr) (g2 : WGState)
    (hrtc : (epowerFork gen, g) -·->ₜₚ* (t2, g2)) :
    ∃ (γ : GName) (n0 r0 : Nat) (h : Option Nat),
      r0 ≤ p ∧ wprotAt g2.wglog a base n0 r0 ∧
      wlpAt g2.wglog base base n0 ∧ wlpAlt g2.wglog base n0 h := by
  have _ := Hgen
  refine weakEvAdequacyCore (hlc := hlc) (GF := GF) gen g D hD Hpow Hgen0 Hlog Hws
    (fun _ _ => iprop(wprotRdRegd (hlc := hlc) N γr a base ∗ protRead γr a p))
    Hwp t2 g2 _ ?_ hrtc
  intro HR HW _
  exact wprotRdRegdExport N ⊤ g2 γr a base p CoPset.subseteq_top

/-! ## 2c. The safety form, projected -/

/-- Rocq `weak_ev_adequacy_reducible`: every thread of every reachable configuration can step. -/
theorem weakEvAdequacyReducible [MachGpreS hlc GF] [WeakGpreS GF]
    (gen : Nat) (g : WGState) (D : CPU → List Register)
    (hD : ∀ c, (D c).Nodup)
    (Hgen : gen = 0)
    (Hpow : g.wgpow = true) (Hgen0 : g.wggen = 0) (Hlog : g.wglog = [])
    (Hws : ∀ c : CPU, g.wgws c = wsInit)
    (Hwp : ∀ [MachGS hlc GF] [WeakGS GF],
      (([∗list] c ∈ cpus, [∗list] r ∈ D c, regPointsTo c r (DFrac.own 1) (g.wgregs c r)) ∗
        bigSepM (M := GMapF PAddr) (fun a b => wlatPointsto (paZ a) (DFrac.own 1) 0 b) g.wgimg ∗
        ([∗list] c ∈ cpus, hartView c) ∗
        wlogLb [] ∗
        ([∗list] d ∈ DevId.all, devFragAt (MachGS.era (hlc := hlc) (GF := GF)) d (g.wgdev.st d)))
      ⊢@{IProp GF} |={⊤}=> ([∗list] e ∈ epowerFork gen, ewpTriv (hlc := hlc) (GF := GF) ⊤ e))
    (t2 : List EExpr) (g2 : WGState) (e2 : EExpr)
    (hrtc : (epowerFork gen, g) -·->ₜₚ* (t2, g2)) (he2 : e2 ∈ t2) :
    Reducible (e2, g2) :=
  (weakEvAdequacyPhi (hlc := hlc) (GF := GF) gen g D hD Hgen Hpow Hgen0 Hlog Hws Hwp t2 g2
    hrtc).2 e2 he2

/-! ## 3. THE SUCCESS CRITERION

`WeakRobust.violationHart clsOf pubOf nDisk` for the fabric-shared promise-free machine
(`WeakEvPf.epfStep`), derived from the φ export and S2's correspondence with ZERO GLUE PREMISES:
the premises are the fresh-era clauses and the WP package. -/

def epfViolationFreeHart (ρ0 : Epool × WGState) : Prop :=
  ∀ ρ, rtc epfRun ρ0 ρ → ¬ violationHart clsOf pubOf nDisk (ecfgOf ρ.1 ρ.2)

/-- Rocq `weak_ev_pf_violation_free`. -/
theorem weakEvPfViolationFree [MachGpreS hlc GF] [WeakGpreS GF]
    (gen : Nat) (g : WGState) (D : CPU → List Register)
    (hD : ∀ c, (D c).Nodup)
    (Hgen : gen = 0)
    (Hpow : g.wgpow = true) (Hgen0 : g.wggen = 0) (Hlog : g.wglog = [])
    (Hws : ∀ c : CPU, g.wgws c = wsInit)
    (Hwp : ∀ [MachGS hlc GF] [WeakGS GF],
      (([∗list] c ∈ cpus, [∗list] r ∈ D c, regPointsTo c r (DFrac.own 1) (g.wgregs c r)) ∗
        bigSepM (M := GMapF PAddr) (fun a b => wlatPointsto (paZ a) (DFrac.own 1) 0 b) g.wgimg ∗
        ([∗list] c ∈ cpus, hartView c) ∗
        wlogLb [] ∗
        ([∗list] d ∈ DevId.all, devFragAt (MachGS.era (hlc := hlc) (GF := GF)) d (g.wgdev.st d)))
      ⊢@{IProp GF} |={⊤}=> ([∗list] e ∈ epowerFork gen, ewpTriv (hlc := hlc) (GF := GF) ⊤ e)) :
    epfViolationFreeHart (epInit gen, g) := by
  intro ρ2 hrun
  -- S2, ⇐ : a pf run of the fabric-shared machine IS an erased run
  have herased := epfRtcErased (epInit gen, g) ρ2 hrun
  rw [show (epInit gen, g).1 = epInit gen from rfl, epoolListInit] at herased
  -- S3, the φ export
  have hnv := (weakEvAdequacyPhi (hlc := hlc) (GF := GF) gen g D hD Hgen Hpow Hgen0 Hlog Hws Hwp
    (epoolList ρ2.1) ρ2.2 herased).1
  -- the layout transport
  exact noViolationViolationHart ρ2.1 ρ2.2 hnv

end adequacy

end Weak
