/-
Weak: **whole-system adequacy over the weak machine** (M1c).

Rocq: `iris/WeakAdequacy.v` @ xxvzwolszwmp (1cc222280).

The Rocq header, in substance (Rocq vocabulary).  `RiscvAdequacy.riscv_system_adequacy` restated
over `WeakLang.weak_riscv_lang`: pick a hart list `cs` and a FRESH-ERA weak state `g` (power on,
generation 0, EMPTY log, every hart at `ws_init`); if the caller can prove the pool's WPs from the
initial resources, then every configuration reachable from the pool (one loop per chosen hart,
plus the device threads) is reducible, and (the φ form) no hart's coherence floor has reached a
foreign agent's unpublished owned store (`noViolation`).  As in the SC theorem the conclusion is
META-level (`toVal` is constantly `none`, so not-stuck IS reducible and the postconditions are
vacuous), and the device-thread WPs are PREMISES (`WeakExec` supplies the device lifting rule
they are proved with; no device invariant is in scope at M1c).

THE INITIAL RESOURCE BUNDLE: per hart, the register points-to over the caller's register set
`D c` (the SC bundle's); one `wlatPointsto (paZ a) 1 0 b` per byte `a ↦ b` of the era-initial
image (timestamp 0: nothing has been written yet); one `hartView c` per hart (the client half of
the hart's weak-state cell at `wsInit`, value hidden); `wlogLb []`; the device fragments.

SCOPE CUTS, all deliberate (Rocq's): SINGLE ERA / NO POWER THREAD (`power` is not in the pool, the
state interpretation pins power-on/generation 0); NO BOOT CARVE (every byte is handed out as an
exclusive weak points-to); THE UNUSED SC GHOSTS GET PLACEHOLDER NAMES (the record's heap, memory
model, kmap, ... names are `0`, and its client slots are the trivial ones; neither the state
interpretation nor the client bundle owns anything at those names, so nothing can be derived from
them).

**Deviations from Rocq.**

1. NAMES: the tree's camelCase (map below).  Rocq's ambient `GenId` class does not exist in Lean
   (WeakExec deviation 1): the theorems take the generation `gen : Nat` explicitly, and Rocq's
   premise `gen_id = 0` is `Hgid : gen = 0`.
2. CAMERAS (WeakGhost deviation 7): Rocq's `riscvGpreS Σ`, `weakGpreS Σ` (and
   `weak_system_adequacy`'s unused `sieG Σ`, which has no Lean counterpart) are the classes
   `[MachGpreS hlc GF] [WeakGpreS GF]`; the client premise's `∀ (HR : riscvGS Σ) (HW : weakGS
   Σ)` is `∀ [MachGS hlc GF] [WeakGS GF]`.  `hlc` is generic (Rocq: `HasLc`, as
   `MachCSL.powerAdequacyCore`).
3. THE DEVICES (WeakLang deviation 2, WeakExec deviation 4).  Rocq's three device threads
   `UartLoop; DiskLoop; PlicLoop` are the root tasks of every device of `DevId.all`, at their loop
   boundary (`WExpr.dev gen d rootTask (.pure ())`, exactly `wpowerFork`'s device half); the
   premise's three WPs are one `[∗list] d ∈ DevId.all`, and Rocq's `uart_frag (duart) ∗
   plic_frag (dplic) ∗ virtio_frag (dvirtio)` is `[∗list] d ∈ DevId.all, devFragAt MachGS.era d
   (g.wgdev.st d)`.
4. THE REGISTER SET: Rocq's `D : CPU → gset register` is `D : CPU → List Register` with the
   premise `hD : ∀ c, (D c).Nodup` (a `gset` has no duplicates by construction); `[∗ set] c ∈
   fin_to_set CPU` is `[∗list] c ∈ cpus` (WeakGhost deviation 13); `register_lookup r (wgregs g
   c)` is `g.wgregs c r`.
5. STATEMENT SHAPES (WeakGhost deviation 9): the premise `⊢ bundle ={⊤}=∗ WPs` is
   `bundle ⊢ |={⊤}=> WPs`.  `rtc erased_step` is iris-lean's `-·->ₜₚ*`; `reducible (Λ := …) e2
   g2` is `Reducible (e2, g2)`.
6. THE SC RECORD: Rocq built `RiscvGS Σ (RiscvFixedGS …) (RiscvEraGS …)` with `1%positive`
   placeholders; Lean builds `MachCSL.bootFixedGS` at the adequacy's invariant world with `0`
   placeholders and the tree's trivial client slots (`weakAdeqFixedGS`), and the ambient
   `MachGS` over it with the allocated register and device names (`weakAdeqMachGS`).  The weak
   record is `weakAdeqWeakGS`.  Lean-only, as are the helpers `regCellsList` (the `D c` subset of
   a whole register file's cells), `wsHalvesAlloc` (one weak-state cell in two halves) and
   `bigSepL2ReplicateWwp`.
7. THE NEW `WGState` FIELDS `wgitv`, `wgrt` (WeakGhost deviation 18) are not mentioned by the
   state interpretation, so the fresh-era premises do not constrain them.

**Rocq → Lean name map.**  `wcpu_pool` `wcpuPool`, `weak_system_adequacy_phi`
`weakSystemAdequacyPhi`, `weak_system_adequacy` `weakSystemAdequacy`.

**Not ported:** nothing.

**Statements checked** (diffed against Rocq by hand): all; the changed spellings are the
deviations above.
-/
import Weak.WeakExec
import MachCSL.Adequacy

namespace Weak

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Iris.Std
open Language.Notation PrimStep
open MachCSL MachCSL.Stdpp
open LeanRV64D

/-! ## 1. The initial thread pool -/

/-- One loop per chosen hart, plus every device's root task at its loop boundary (deviation 3).
No power thread. -/
def wcpuPool (gen : Nat) (cs : List CPU) : List WExpr :=
  cs.map (WExpr.loop gen) ++ DevId.all.map (fun d => WExpr.dev gen d rootTask (.pure ()))

/-! ## 2. The records the adequacy builds (deviation 6) -/

section records

variable {hlc : HasLC} {GF : BundledGFunctors}

/-- The SC record's reserved regions (W8-β′): none -- the weak adequacy runs no
`PowerOn` mint and reads no reserved-region discipline; no dynamic hop
registry either (W8 (f2-ctx) [OWN.49]: the static list is empty, so it
registers no pipe slots). -/
def WeakAdequacy.rsvNone : KernelRsv :=
  ⟨[], ⟨List.nodup_nil, fun a ha => by simp [rsvBytes] at ha, List.nodup_nil⟩⟩

/-- The fixed record: the adequacy's invariant world, placeholder names, trivial client slots. -/
@[reducible] def weakAdeqFixedGS [MachGpreS hlc GF] (Hinv : InvGS_gen hlc GF) :
    MachFixedGS hlc GF :=
  @bootFixedGS hlc GF _ WeakAdequacy.rsvNone Hinv 0 0 0 0 0 0 iprop(True) (fun _ => iprop(True)) (fun _ Q => Q) 0 []
    iprop(True) 0
    rxTagTriv (fun _ => inferInstance) (fun _ => inferInstance)
    killCredTriv inferInstance inferInstance
    consResTriv (fun _ _ _ => inferInstance)
    wildNone (fun _ => inferInstance) (fun _ => inferInstance)
    wildNone (fun _ => inferInstance) (fun _ => inferInstance)
    (fun _ _ => True) (fun _ => iprop(emp)) (fun _ _ => iprop(emp)) iprop(emp)
    (fun _ _ => iprop(True)) (fun _ _ => inferInstance)
    (fun _ => iprop(emp)) (fun _ _ => iprop(True)) (fun _ _ => inferInstance)

/-- The ambient SC instance: the fixed record, the allocated register and device names, every
other name a placeholder. -/
@[reducible] def weakAdeqMachGS [MachGpreS hlc GF] (Hinv : InvGS_gen hlc GF)
    (rn : CPU → GName) (dn : DevId → GName) (gen : Nat) : MachGS hlc GF where
  fixed := weakAdeqFixedGS Hinv
  regName := rn
  heapName := 0
  metaName := 0
  viewName := fun _ => 0
  iviewName := fun _ => 0
  rviewName := fun _ => 0
  topName := 0
  authName := 0
  resvName := 0
  lockSetName := fun _ => 0
  kmapName := 0
  kptRootName := 0
  devName := dn
  mirrorName := 0
  rsvName := 0
  chainName := 0
  gen := gen
  claimP := fun _ _ => iprop(True)
  claim_idle := fun _ => true_intro

/-- The weak record. -/
@[reducible] def weakAdeqWeakGS [WeakGpreS GF] (γlog γlat γcds : GName) (wsn : CPU → GName) :
    WeakGS GF where
  logName := γlog
  latName := γlat
  cdsName := γcds
  wsName := wsn

end records

/-! ## 3. Helpers -/

section helpers

variable {hlc : HasLC} {GF : BundledGFunctors}

/-- The cells of the registers in `D`, out of any map holding them (deviation 4). -/
theorem regCellsList [MachFixedGS hlc GF] (γ : GName) (f : RegFile) :
    ∀ (D : List Register) (m : RegMapF RegVal), D.Nodup →
      (∀ r ∈ D, get? m (regIdx r) = some ⟨r, f r⟩) →
      ([∗map] k ↦ v ∈ m, γ ↪◯MAP[k] v) ⊢@{IProp GF}
        [∗list] r ∈ D, γ ↪◯MAP[regIdx r] (⟨r, f r⟩ : RegVal)
  | [], _, _, _ => BigSepL.bigSepL_nil_intro
  | r :: D, m, hl, hm => by
    have hr : r ∉ D := (List.nodup_cons.mp hl).1
    iintro H
    icases (BigSepM.bigSepM_delete (hm r List.mem_cons_self)).1 $$ H with ⟨Hr, Hrest⟩
    iapply BigSepL.bigSepL_cons.2
    isplitl [Hr]
    · iexact Hr
    iapply (regCellsList γ f D (delete m (regIdx r)) (List.nodup_cons.mp hl).2 (by
      intro r' hr'
      have hne : regIdx r ≠ regIdx r' := fun h => hr (by rw [regIdx_injective h]; exact hr')
      rw [LawfulPartialMap.get?_delete_ne hne]
      exact hm r' (List.mem_cons_of_mem _ hr'))) $$ Hrest

/-- One hart's weak-state cell at `wsInit`, in two halves. -/
theorem wsHalvesAlloc [WeakGpreS GF] :
    ⊢@{IProp GF} |==> ∃ γ, (γ ↪VAR{.own (1 : Qp).half} wsInit) ∗
      (γ ↪VAR{.own (1 : Qp).half} wsInit) := by
  imod (ghost_var_alloc (GF := GF) wsInit) with ⟨%γ, H⟩
  imodintro
  iexists γ
  have h := (ghost_var_fractional (GF := GF) γ wsInit).fractional (1 : Qp).half (1 : Qp).half
  rw [Qp.half_add_half] at h
  iapply h.1 $$ H

/-- The pool's Φ-free WPs as the adequacy's `[∗list] e;Φ`, at the trivial postconditions. -/
theorem bigSepL2ReplicateWwp [MachGS hlc GF] [WeakGS GF] (es : List WExpr) :
    ([∗list] e ∈ es, wwpTriv (hlc := hlc) (GF := GF) ⊤ e) ⊢
      [∗list] e;Φ ∈ es;List.replicate es.length (fun _ : Empty => iprop(True)),
        WP e @ Stuckness.NotStuck ; ⊤ {{ Φ }} := by
  refine Entails.trans ?_ BigSepL2.bigSepL2_replicate_right.2
  exact .rfl

end helpers

/-! ## 4. The theorems -/

section adequacy

variable {hlc : HasLC} {GF : BundledGFunctors}

/-- THE φ FORM: every reachable configuration is violation-free and every thread in it is
reducible.  Rocq `weak_system_adequacy_phi`. -/
theorem weakSystemAdequacyPhi [MachGpreS hlc GF] [WeakGpreS GF]
    (gen : Nat) (cs : List CPU) (g : WGState) (D : CPU → List Register)
    (hD : ∀ c, (D c).Nodup)
    (Hgid : gen = 0)
    -- THE FRESH ERA: power on, generation 0, nothing written, nobody has observed anything
    (Hpow : g.wgpow = true) (Hgen0 : g.wggen = 0) (Hlog : g.wglog = [])
    (Hws : ∀ c : CPU, g.wgws c = wsInit)
    (Hwp : ∀ [MachGS hlc GF] [WeakGS GF],
      (([∗list] c ∈ cpus, [∗list] r ∈ D c, regPointsTo c r (DFrac.own 1) (g.wgregs c r)) ∗
        bigSepM (M := GMapF PAddr) (fun a b => wlatPointsto (paZ a) (DFrac.own 1) 0 b) g.wgimg ∗
        ([∗list] c ∈ cpus, hartView c) ∗
        wlogLb [] ∗
        ([∗list] d ∈ DevId.all, devFragAt (MachGS.era (hlc := hlc) (GF := GF)) d (g.wgdev.st d)))
      ⊢@{IProp GF} |={⊤}=>
        (([∗list] c ∈ cs, wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen c)) ∗
         ([∗list] d ∈ DevId.all,
            wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.dev gen d rootTask (.pure ())))))
    (t2 : List WExpr) (g2 : WGState)
    (hrtc : (wcpuPool gen cs, g) -·->ₜₚ* (t2, g2)) :
    noViolation g2.wglog g2.wgws ∧ ∀ e2, e2 ∈ t2 → Reducible (e2, g2) := by
  obtain ⟨n, κs, hsteps⟩ := (Language.erasedStep_nSteps _ _).mp hrtc
  suffices h : noViolation g2.wglog g2.wgws ∧
      ∀ e2, e2 ∈ t2 → NotStuck (Val := Empty) (e2, g2) by
    refine ⟨h.1, fun e2 he => ?_⟩
    rcases h.2 e2 he with hv | hr
    · exact absurd hv (by simp [ToVal.toVal])
    · exact hr
  refine wp_strong_adequacy_gen (hlc := hlc) (GF := GF) Stuckness.NotStuck (wcpuPool gen cs) g n
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
  -- ---- the conversions between the allocated shapes and the client's / the interpretation's ----
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
  -- ---- run the caller's proof to obtain the WPs ----
  imod (@Hwp HR HW) $$ [Hrc Hlatel Hcdsel HwsF Hlb Hdf] with ⟨Hwpc, Hwpd⟩
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
      @stateInterp WGState Empty GF (@weakIrisGS hlc GF HR HW).toStateInterp σ ns κs' nt),
    (List.replicate (wcpuPool gen cs).length (fun _ : Empty => iprop(True))),
    (fun _ => iprop(True)),
    (@weakIrisGS hlc GF HR HW).stateInterp_mono
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
  isplitl [Hwpc Hwpd]
  · iapply bigSepL2ReplicateWwp (hlc := hlc) (GF := GF) (wcpuPool gen cs)
    unfold wcpuPool
    iapply BigSepL.bigSepL_append.2
    rw [BigSepL.bigSepL_map, BigSepL.bigSepL_map]
    iframe Hwpc Hwpd
  iintro %es' %t2' %Heq %Hlen %Hns Hsi _ _
  -- THE EXPORT: the reachable state's own interpretation carries φ
  ihave %hnv := weakStateInterpExport (hlc := hlc) (GF := GF) g2 $$ Hsi
  iapply fupd_mask_intro_discard LawfulSet.empty_subset
  ipureintro
  exact ⟨hnv, fun e2 he => Hns e2 trivial he⟩

/-- The M1c theorem, as the projection of the φ form.  Rocq `weak_system_adequacy`. -/
theorem weakSystemAdequacy [MachGpreS hlc GF] [WeakGpreS GF]
    (gen : Nat) (cs : List CPU) (g : WGState) (D : CPU → List Register)
    (hD : ∀ c, (D c).Nodup)
    (Hgid : gen = 0)
    (Hpow : g.wgpow = true) (Hgen0 : g.wggen = 0) (Hlog : g.wglog = [])
    (Hws : ∀ c : CPU, g.wgws c = wsInit)
    (Hwp : ∀ [MachGS hlc GF] [WeakGS GF],
      (([∗list] c ∈ cpus, [∗list] r ∈ D c, regPointsTo c r (DFrac.own 1) (g.wgregs c r)) ∗
        bigSepM (M := GMapF PAddr) (fun a b => wlatPointsto (paZ a) (DFrac.own 1) 0 b) g.wgimg ∗
        ([∗list] c ∈ cpus, hartView c) ∗
        wlogLb [] ∗
        ([∗list] d ∈ DevId.all, devFragAt (MachGS.era (hlc := hlc) (GF := GF)) d (g.wgdev.st d)))
      ⊢@{IProp GF} |={⊤}=>
        (([∗list] c ∈ cs, wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen c)) ∗
         ([∗list] d ∈ DevId.all,
            wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.dev gen d rootTask (.pure ())))))
    (t2 : List WExpr) (g2 : WGState) (e2 : WExpr)
    (hrtc : (wcpuPool gen cs, g) -·->ₜₚ* (t2, g2)) (he2 : e2 ∈ t2) :
    Reducible (e2, g2) :=
  (weakSystemAdequacyPhi (hlc := hlc) (GF := GF) gen cs g D hD Hgid Hpow Hgen0 Hlog Hws Hwp t2 g2
    hrtc).2 e2 he2

end adequacy

end Weak
