/-
Weak: **Phase 1a, part 4 of the spinlock plan -- THE CAPSTONE `spinHandoff` and its
CERTIFICATES** (the smell tests that the lock protocol makes ownership load-bearing).

Rocq: `iris/AxSpinProt4.v` @ xxvzwolszwmp.

## The Rocq header, in substance

CAPSTONE `spinHandoff`: from `rvwmoCatConsistentT GT`, `ctrlClosed GT`, harts = {A, B}, B's row
`AxSpinProt3.bRow t1 t2 tx vx` (one FAILED amoswap reading 1, one SUCCESSFUL amoswap reading 0,
`ld x = vx`, `fence rw,w`, `sw lk ← 0` (WCrel)), hart A ARBITRARY (any run `sA0 →* sAN` covering
its row, and a WPd at the real protocol from `spinInit` = `isLock nm lk R ∗ notheld nm lk A`),
conclude `vx = b1 ∨ gxImg x = some vx`.  The lock's resource `R` (= ownership of `x` with locked
history writing only `b1`, `AxSpinProt.Rx`) starts PARKED in the genesis box; B's read of `x`
gets its value from `R` pulled out of the mailbox of the release its claim reads; the fact is
read back at B's row end.  Adequacy: `AxSpinGate.tierAAdequacyAnnGateT` with policy
`AxSpinProt2.splPol` (admissible by `splHok`, needs `ctrlClosed`), allocation `spinHobAlloc`.

CERTIFICATES
  (a) `AxSpinProt4.spaPremises`: on the concrete tagged graph `AxSpinProt4.spa` EVERY premise of
      the capstone holds (A's WPd PROVED at the real protocol, `aWpdSpa`); `AxSpinProt4.spaShape`:
      B's first amoswap reads 1 from A's claim, B's claim reads A's release, B's x-read reads A's
      `x := 1`, and the gate is non-trivial; `AxSpinProt4.spaSound`: the capstone fires there.
  (b) RACE `spr2WpdUnprovable`: A' = acquire; fence; release; `sd x ← 2`.  On the consistent,
      ctrl-closed `spr2` (B claims A''s release and reads `x = 2`) the conclusion is FALSE, so
      A''s WPd at the real protocol is UNPROVABLE.
  (c) SANITY TWIN `spr2WpdTrivial`: the same A' program / graph / hart / policy / stuckness /
      post IS verifiable at the TRIVIAL protocol.

## Deviations from Rocq

1. O2 STAGE C (as `AxSpinProt3` deviation 1): no text oracle -- Rocq's `Tf` arguments of
   `tierA_astep`/`tierA_wpd` are gone.
2. CONTEXTS (as `AxSpinWit` deviation 4): the capstone's `set` locals are the Lean-only defs
   `AxSpinProt4.cS0`/`cSN`/`cN`/`cPost`; `HwpA` and the certificate statements take
   `[InvGS_gen .hasNoLC spinGF] [AxannotGS spinGF]` instance binders.  Policies `spl_pol GT`
   passed explicitly (`@tierAWpd spinGF .hasNoLC _ _ (splPol GT) …`).
3. `spinΣ` ↦ `spinGF`, an explicit slot table: `AxSpinWit.spGF`'s slots 0–7 (inv/credits 0–3,
   history log `AxlogRF Hent` 4, annotation cameras 5–7) plus the `SpinlockG` cameras (saved
   predicate over `Geid` 8, hold map `Nat → Option Geid` 9, registry `Int → GName × GName` 10),
   with Lean-only instances `AxSpinProt4.spinGF*`.  The adequacy allocates the `SpinlockG` state
   through `spinHobAlloc` (as Rocq).
4. `vm_compute` ↦ `decide +kernel`; `Ltac vmr` is not a declaration (dropped).  `B0/B1/B2` ↦
   `b0/b1/b2`; `init_regstate` ↦ `zeroRegs`; `gx_img (gt_g GT)` ↦ `GT.gtG.gxImg`.

**Rocq → Lean name map.**  `spinΣ` `spinGF`, `spin_handoff` `spinHandoff`, `sp_ctrl` `spCtrl`,
`spa` `AxSpinProt4.spa`, `spr2` `spr2`, `spa_cat_t` `AxSpinProt4.spaCatT`, `spr2_cat_t`
`spr2CatT`, `spa_ctrl_closed` `AxSpinProt4.spaCtrlClosed`, `spr2_ctrl_closed` `spr2CtrlClosed`,
`spa_harts` `AxSpinProt4.spaHarts`, `spr2_harts` `spr2Harts`, `spa_shape`
`AxSpinProt4.spaShape`, `a_wpd_spa` `aWpdSpa`, `a_run_spa` `aRunSpa`, `spa_premises`
`AxSpinProt4.spaPremises`, `spa_sound` `AxSpinProt4.spaSound`, `r_run_spr2` `rRunSpr2`,
`spr2_shape` `spr2Shape`, `spr2_wpd_unprovable` `spr2WpdUnprovable`, `spr2_wpd_trivial`
`spr2WpdTrivial`.  Duplicated Rocq names (with AxSpinX7/X8) are file-qualified
(`AxSpinProt4.*`).  Lean-only (file-qualified): `AxSpinProt4.spinGF*` instances,
`AxSpinProt4.cS0`/`cSN`/`cN`/`cPost`.

**Dropped:** `vmr` (a tactic) and the §5 `Check`/`Print Assumptions` lines (the lint's axiom
check covers them).
-/
import Weak.AxSpinProt3

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D
open Dtag

/-! # 1. THE CAPSTONE -/

section spinGFSec

open Iris.Algebra

/-- Rocq `spinΣ := #[invΣ; axlogΣ hent; axannotΣ; spinlockΣ]`. -/
def spinGF : BundledGFunctors :=
  BundledGFunctors.default
  |>.set 0 ⟨InvMapF, inferInstance⟩
  |>.set 1 ⟨constOF CoPsetDisjL, inferInstance⟩
  |>.set 2 ⟨constOF (DisjointLeibnizSet PosSet), inferInstance⟩
  |>.set 3 ⟨Auth.AuthURF (constOF Credit), inferInstance⟩
  |>.set 4 ⟨AxlogRF Hent, inferInstance⟩
  |>.set 5 ⟨DFracAgree.DFracAgreeRF (LaterOF IdOF), inferInstance⟩
  |>.set 6 ⟨constOF (HeapView Geid (Agree (DiscreteO GName)) (GMapF Geid)), inferInstance⟩
  |>.set 7 ⟨constOF AxannotSetR, inferInstance⟩
  |>.set 8 ⟨DFracAgree.DFracAgreeRF (DiscreteFunOF (fun _ : Geid => LaterOF IdOF)),
    inferInstance⟩
  |>.set 9 ⟨constOF (HeapView Nat (Agree (DiscreteO (Option Geid))) (GMapF Nat)), inferInstance⟩
  |>.set 10 ⟨constOF (HeapView Int (Agree (DiscreteO (GName × GName))) (GMapF Int)),
    inferInstance⟩

instance AxSpinProt4.spinGFInvMap : ElemG spinGF InvMapF := ⟨0, rfl⟩
instance AxSpinProt4.spinGFEnabled : ElemG spinGF (constOF CoPsetDisjL) := ⟨1, rfl⟩
instance AxSpinProt4.spinGFDisabled : ElemG spinGF (constOF (DisjointLeibnizSet PosSet)) :=
  ⟨2, rfl⟩
instance AxSpinProt4.spinGFCredit : ElemG spinGF (Auth.AuthURF (constOF Credit)) := ⟨3, rfl⟩
instance AxSpinProt4.spinGFInvGpreS : InvGpreS spinGF :=
  ⟨⟨inferInstance, inferInstance, inferInstance⟩, ⟨inferInstance⟩⟩
instance AxSpinProt4.spinGFAxlogG : AxlogG spinGF Hent := { axlogInG := ⟨4, rfl⟩ }
instance AxSpinProt4.spinGFAxannotG : AxannotG spinGF :=
  { axannotSavedG := { elemG := ⟨5, rfl⟩ }, axannotMapG := ⟨⟨6, rfl⟩⟩, axannotSetG := ⟨7, rfl⟩ }
instance AxSpinProt4.spinGFSpinlockG : SpinlockG spinGF :=
  { spinSavedPredG := { elemG := ⟨8, rfl⟩ }, spinHoldG := ⟨⟨9, rfl⟩⟩,
    spinRegG := ⟨⟨10, rfl⟩⟩ }

end spinGFSec

/-- Lean-only (Rocq `set s0`). -/
def AxSpinProt4.cS0 (sA0 : Athread) (i : Agent) : Athread :=
  if i = hA then sA0 else ⟨hp cpu0 AxSpinProt3.bM0 zeroRegs, 0⟩
/-- Lean-only (Rocq `set sN`). -/
def AxSpinProt4.cSN (sAN : Athread) (i : Agent) : Athread :=
  if i = hA then sAN else ⟨hp cpu0 hlt zeroRegs, 5⟩
/-- Lean-only (Rocq `set nf`). -/
def AxSpinProt4.cN (nA : Nat) (i : Agent) : Nat := if i = hA then nA else 7
/-- Lean-only (Rocq `set post`). -/
def AxSpinProt4.cPost (GT : GdexecT) (vx : BitVec 8) (i : Agent) (_ : Athread) : Prop :=
  if i = hB then (vx = b1 ∨ GT.gtG.gxImg xa = some vx) else True

theorem spinHandoff (GT : GdexecT)
    (HconsT : rvwmoCatConsistentT GT) (Hcl : ctrlClosed GT)
    (Hharts : ∀ e, e ∈ GT.gtG.gxGmo → e.1 = hA ∨ e.1 = hB)
    (t1 t2 tx : Nat) (vx : BitVec 8)
    (HrowB : AxOpsem.grow (gtAdGd GT) hB = AxSpinProt3.bRow t1 t2 tx vx)
    (sA0 sAN : Athread) (nA : Nat)
    (HrunA : ∀ (_ : AxannotGS spinGF) (nm : spinN),
      nsteps (tierAAstep (gtAdGd GT) nm hA) nA sA0 sAN)
    (HkA : sA0.atK = 0) (HendA : sAN.atK = (AxOpsem.grow (gtAdGd GT) hA).length)
    (HwpA : ∀ [InvGS_gen .hasNoLC spinGF] [AxannotGS spinGF] (nm : spinN),
      ⊢ spinInit ya xa (gtAdGd GT) nm hA -∗
        @tierAWpd spinGF .hasNoLC _ _ (splPol GT) (gtAdGd GT) spinN Unit (spinOb ya xa) nm sA0
          .MaybeStuck hA (fun _ => iprop(True))) :
    vx = b1 ∨ GT.gtG.gxImg xa = some vx := by
  have Hin01 : ∀ i : Agent, i ∈ [hA, hB] → i = hA ∨ i = hB := by
    intro i Hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at Hi
    exact Hi
  have Hnd : [hA, hB].Nodup := by decide
  have Hharts' : ∀ e, e ∈ GT.gtG.gxGmo → e.1 ∈ [hA, hB] := by
    intro e He
    rcases Hharts e He with H | H <;> rw [H] <;> simp
  have Hcons := catTAd GT HconsT
  have Hrun : ∀ (_ : AxannotGS spinGF) (nm : spinN) i, i ∈ [hA, hB] →
      nsteps (tierAAstep (gtAdGd GT) nm i) (AxSpinProt4.cN nA i) (AxSpinProt4.cS0 sA0 i)
        (AxSpinProt4.cSN sAN i) := by
    intro Hann nm i Hi
    rcases Hin01 i Hi with rfl | rfl
    · exact HrunA Hann nm
    · exact AxSpinProt3.bRun cpu0 (gtAdGd GT) t1 t2 tx vx HrowB
  have Hk0 : ∀ i, i ∈ [hA, hB] → (AxSpinProt4.cS0 sA0 i).atK = 0 := by
    intro i Hi
    rcases Hin01 i Hi with rfl | rfl
    · exact HkA
    · rfl
  have Hend : ∀ i, i ∈ [hA, hB] →
      (AxSpinProt4.cSN sAN i).atK = (AxOpsem.grow (gtAdGd GT) i).length := by
    intro i Hi
    rcases Hin01 i Hi with rfl | rfl
    · exact HendA
    · show 5 = (AxOpsem.grow (gtAdGd GT) hB).length
      rw [HrowB]
      rfl
  have Hwp : ∀ [InvGS_gen .hasNoLC spinGF] [AxannotGS spinGF] (nm : spinN),
      ⊢ ([∗list] i ∈ [hA, hB], spinInit ya xa (gtAdGd GT) nm i) -∗
        [∗list] i ∈ [hA, hB],
          @tierAWpd spinGF .hasNoLC _ _ (splPol GT) (gtAdGd GT) spinN Unit (spinOb ya xa) nm
            (AxSpinProt4.cS0 sA0 i) .MaybeStuck i
            (fun s => iprop(⌜AxSpinProt4.cPost GT vx i s⌝)) := by
    intro Hinv Hann nm
    iintro HI
    icases (AxTokLedgerMp.bigSepLPair hA hB
      (fun i => spinInit (GF := spinGF) ya xa (gtAdGd GT) nm i)).1 $$ HI with ⟨HA, HB⟩
    iapply (AxTokLedgerMp.bigSepLPair hA hB _).2
    rw [show AxSpinProt4.cS0 sA0 hA = sA0 from if_pos rfl,
      show AxSpinProt4.cS0 sA0 hB = ⟨hp cpu0 AxSpinProt3.bM0 zeroRegs, 0⟩ from
        if_neg (by decide)]
    isplitl [HA]
    · iapply (AxSpinWit.tierAWpdMono (hlc := .hasNoLC) (pol := splPol GT) (gtAdGd GT) spinN Unit
        (spinOb ya xa) nm sA0 .MaybeStuck hA (fun _ => iprop(True))
        (fun s => iprop(⌜AxSpinProt4.cPost GT vx hA s⌝))
        (fun _ => pure_mono (fun _ => by
          unfold AxSpinProt4.cPost; rw [if_neg (by decide)]; trivial)))
      iapply HwpA nm $$ HA
    · iapply (AxSpinWit.tierAWpdMono (hlc := .hasNoLC) (pol := splPol GT) (gtAdGd GT) spinN Unit
        (spinOb ya xa) nm ⟨hp cpu0 AxSpinProt3.bM0 zeroRegs, 0⟩ .MaybeStuck hB
        (fun _ => iprop(⌜vx = b1 ∨ (gtAdGd GT).gdG.gxImg xa = some vx⌝))
        (fun s => iprop(⌜AxSpinProt4.cPost GT vx hB s⌝))
        (fun _ => pure_mono (fun Hv => by
          unfold AxSpinProt4.cPost; rw [if_pos rfl]; exact Hv)))
      unfold spinInit
      icases HB with ⟨Hil, Hnh⟩
      iapply (AxSpinProt3.wpdB (hlc := .hasNoLC) (GF := spinGF) GT nm cpu0 Hcons t1 t2 tx vx
        HrowB) $$ Hil Hnh
  have Hfin := @tierAAdequacyAnnGateT spinGF _ _ (splPol GT) GT spinN Unit (spinOb ya xa)
    (spinInit ya xa (gtAdGd GT)) (splAxpolWf GT) HconsT [hA, hB] Hnd Hharts'
    (AxSpinProt4.cS0 sA0) (AxSpinProt4.cSN sAN) (AxSpinProt4.cN nA) Hrun Hk0 Hend
    (AxSpinProt4.cPost GT vx) Hwp (spinHobAlloc (GF := spinGF) ya xa (gtAdGd GT) [hA, hB] Hnd)
    (splHok GT HconsT Hcl) hB (by simp)
  exact (if_pos rfl : AxSpinProt4.cPost GT vx hB _ = (vx = b1 ∨ GT.gtG.gxImg xa = some vx)) ▸ Hfin

/-! # 2. CERTIFICATE (a): SATISFIABILITY on `spa` -/

def spCtrl : List Tdep :=
  [(((hB, 0), (hB, 1)), DTctrl), (((hB, 0), (hB, 4)), DTctrl), (((hB, 1), (hB, 4)), DTctrl)]

def AxSpinProt4.spa : GdexecT :=
  mkgt [AxSpinProt3.aRow 0, AxSpinProt3.bRow 1 4 3 b1]
    [(hA, 0), (hB, 0), (hA, 1), (hA, 3), (hB, 1), (hB, 2), (hB, 4)] spCtrl

def spr2 : GdexecT :=
  mkgt [AxSpinProt3.rRow, AxSpinProt3.bRow 1 3 5 b2]
    [(hA, 0), (hB, 0), (hA, 2), (hB, 1), (hA, 3), (hB, 2), (hB, 4)] spCtrl

theorem AxSpinProt4.spaCatT : rvwmoCatConsistentT AxSpinProt4.spa :=
  catTConsistentBSound _ (by decide +kernel)
theorem spr2CatT : rvwmoCatConsistentT spr2 := catTConsistentBSound _ (by decide +kernel)
theorem AxSpinProt4.spaCtrlClosed : ctrlClosed AxSpinProt4.spa :=
  ctrlClosedBSound _ AxSpinProt4.spaCatT.1 (by decide +kernel)
theorem spr2CtrlClosed : ctrlClosed spr2 := ctrlClosedBSound _ spr2CatT.1 (by decide +kernel)

theorem AxSpinProt4.spaHarts :
    ∀ e, e ∈ AxSpinProt4.spa.gtG.gxGmo → e.1 = hA ∨ e.1 = hB := by
  intro e He
  have h : AxSpinProt4.spa.gtG.gxGmo.all (fun e : Geid => decide (e.1 = hA ∨ e.1 = hB)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.1 h e He)

theorem spr2Harts : ∀ e, e ∈ spr2.gtG.gxGmo → e.1 = hA ∨ e.1 = hB := by
  intro e He
  have h : spr2.gtG.gxGmo.all (fun e : Geid => decide (e.1 = hA ∨ e.1 = hB)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.1 h e He)

/-- The shape of `spa`: B's FIRST amoswap reads 1 from A's claim (the failed spin), B's claim
reads A's RELEASE (the handoff), B's x-read reads A's `x := 1`; the gate is non-trivial
(`gsrcT` at B's x-read). -/
theorem AxSpinProt4.spaShape :
    graphValue (gtAdGd AxSpinProt4.spa) (hB, 0) = some [b1] ∧
    grfAt AxSpinProt4.spa.gtG ya (hA, 0) (hB, 0) ∧
    graphValue (gtAdGd AxSpinProt4.spa) (hB, 1) = some [b0] ∧
    grfAt AxSpinProt4.spa.gtG ya (hA, 3) (hB, 1) ∧
    graphValue (gtAdGd AxSpinProt4.spa) (hB, 2) = some [b1] ∧
    grfAt AxSpinProt4.spa.gtG xa (hA, 1) (hB, 2) ∧
    ((hB, 0) : Geid) ∈ gsrcT AxSpinProt4.spa (hB, 2) := by
  refine ⟨by decide +kernel, (grfAtBSpec _ _ _ _).1 (by decide +kernel), by decide +kernel,
    (grfAtBSpec _ _ _ _).1 (by decide +kernel), by decide +kernel,
    (grfAtBSpec _ _ _ _).1 (by decide +kernel), ?_⟩
  exact (gsrcTSpec _ _ _).2 ⟨(hB, 1), by decide +kernel, .inr ((gpoBSpec _ _ _).1 (by decide +kernel)),
    by decide +kernel⟩

theorem aWpdSpa :
    ∀ [InvGS_gen .hasNoLC spinGF] [AxannotGS spinGF] (nm : spinN),
      ⊢ spinInit ya xa (gtAdGd AxSpinProt4.spa) nm hA -∗
        @tierAWpd spinGF .hasNoLC _ _ (splPol AxSpinProt4.spa) (gtAdGd AxSpinProt4.spa) spinN Unit
          (spinOb ya xa) nm ⟨hp cpu0 AxSpinProt3.aM0 zeroRegs, 0⟩ .MaybeStuck hA
          (fun _ => iprop(True)) := by
  intro _ _ nm
  unfold spinInit
  iintro ⟨Hil, Hnh⟩
  iapply (AxSpinProt3.wpdA (hlc := .hasNoLC) (GF := spinGF) AxSpinProt4.spa nm cpu0
    (catTAd AxSpinProt4.spa AxSpinProt4.spaCatT) 0 rfl) $$ Hil Hnh

theorem aRunSpa : ∀ (_ : AxannotGS spinGF) (nm : spinN),
    nsteps (tierAAstep (gtAdGd AxSpinProt4.spa) nm hA) 5
      ⟨hp cpu0 AxSpinProt3.aM0 zeroRegs, 0⟩ ⟨hp cpu0 hlt zeroRegs, 4⟩ :=
  fun _ _ => AxSpinProt3.aRun cpu0 (gtAdGd AxSpinProt4.spa) 0 rfl

/-- EVERY premise of `spinHandoff` on `spa`, as one conjunction. -/
theorem AxSpinProt4.spaPremises :
    rvwmoCatConsistentT AxSpinProt4.spa ∧ ctrlClosed AxSpinProt4.spa ∧
    (∀ e, e ∈ AxSpinProt4.spa.gtG.gxGmo → e.1 = hA ∨ e.1 = hB) ∧
    AxOpsem.grow (gtAdGd AxSpinProt4.spa) hB = AxSpinProt3.bRow 1 4 3 b1 ∧
    (∀ (_ : AxannotGS spinGF) (nm : spinN),
      nsteps (tierAAstep (gtAdGd AxSpinProt4.spa) nm hA) 5
        ⟨hp cpu0 AxSpinProt3.aM0 zeroRegs, 0⟩ ⟨hp cpu0 hlt zeroRegs, 4⟩) ∧
    (⟨hp cpu0 AxSpinProt3.aM0 zeroRegs, 0⟩ : Athread).atK = 0 ∧
    (⟨hp cpu0 hlt zeroRegs, 4⟩ : Athread).atK =
      (AxOpsem.grow (gtAdGd AxSpinProt4.spa) hA).length ∧
    (∀ [InvGS_gen .hasNoLC spinGF] [AxannotGS spinGF] (nm : spinN),
      ⊢ spinInit ya xa (gtAdGd AxSpinProt4.spa) nm hA -∗
        @tierAWpd spinGF .hasNoLC _ _ (splPol AxSpinProt4.spa) (gtAdGd AxSpinProt4.spa) spinN Unit
          (spinOb ya xa) nm ⟨hp cpu0 AxSpinProt3.aM0 zeroRegs, 0⟩ .MaybeStuck hA
          (fun _ => iprop(True))) :=
  ⟨AxSpinProt4.spaCatT, AxSpinProt4.spaCtrlClosed, AxSpinProt4.spaHarts, rfl, aRunSpa, rfl, rfl,
    aWpdSpa⟩

theorem AxSpinProt4.spaSound : b1 = b1 ∨ AxSpinProt4.spa.gtG.gxImg xa = some b1 :=
  spinHandoff AxSpinProt4.spa AxSpinProt4.spaCatT AxSpinProt4.spaCtrlClosed AxSpinProt4.spaHarts
    1 4 3 b1 rfl _ _ 5 aRunSpa rfl rfl aWpdSpa

/-! # 3. CERTIFICATE (b): THE RACE -/

theorem rRunSpr2 : ∀ (_ : AxannotGS spinGF) (nm : spinN),
    nsteps (tierAAstep (gtAdGd spr2) nm hA) 5
      ⟨hp cpu0 AxSpinProt3.rM0 zeroRegs, 0⟩ ⟨hp cpu0 hlt zeroRegs, 4⟩ :=
  fun _ _ => AxSpinProt3.rRun cpu0 (gtAdGd spr2) rfl

/-- B claims A''s release and its x-read reads A''s post-release `x := 2`. -/
theorem spr2Shape :
    grfAt spr2.gtG ya (hA, 2) (hB, 1) ∧
    graphValue (gtAdGd spr2) (hB, 2) = some [b2] ∧
    grfAt spr2.gtG xa (hA, 3) (hB, 2) :=
  ⟨(grfAtBSpec _ _ _ _).1 (by decide +kernel), by decide +kernel,
    (grfAtBSpec _ _ _ _).1 (by decide +kernel)⟩

theorem spr2WpdUnprovable :
    ¬ (∀ [InvGS_gen .hasNoLC spinGF] [AxannotGS spinGF] (nm : spinN),
        ⊢ spinInit ya xa (gtAdGd spr2) nm hA -∗
          @tierAWpd spinGF .hasNoLC _ _ (splPol spr2) (gtAdGd spr2) spinN Unit (spinOb ya xa) nm
            ⟨hp cpu0 AxSpinProt3.rM0 zeroRegs, 0⟩ .MaybeStuck hA (fun _ => iprop(True))) := by
  intro Hwp
  rcases spinHandoff spr2 spr2CatT spr2CtrlClosed spr2Harts 1 3 5 b2 rfl _ _ 5 rRunSpr2 rfl rfl
    Hwp with H | H
  · exact b1NeB2 H.symm
  · have Himg : (spr2.gtG.gxImg xa = some b2) = False :=
      eq_false (by decide +kernel)
    exact Himg ▸ H

/-! # 4. CERTIFICATE (c): SANITY TWIN at the trivial protocol -/

theorem spr2WpdTrivial :
    ∀ [InvGS_gen .hasNoLC spinGF] [AxannotGS spinGF] (nm : Unit),
      ⊢ (iprop(emp) : IProp spinGF) -∗
        @tierAWpd spinGF .hasNoLC _ _ (splPol spr2) (gtAdGd spr2) Unit Unit trivOb nm
          ⟨hp cpu0 AxSpinProt3.rM0 zeroRegs, 0⟩ .MaybeStuck hA (fun _ => iprop(True)) := by
  intro _ _ nm
  cases nm
  iintro _
  iapply (AxSpinProt3.wpdRTriv (hlc := .hasNoLC) (GF := spinGF) spr2 cpu0 rfl)

end Weak
