/-
Weak: **Phase 1b, part 4 of the spinlock plan -- THE CAPSTONE `spinHandoff5` and its
CERTIFICATES.**

Rocq: `iris/AxSpinProt8.v` @ xxvzwolszwmp.

## The Rocq header, in substance

CAPSTONE `spinHandoff5`: for ANY hart A with a WPd at `spinOb5` from `spinInit5`
(= `isLock R5 ∗ notheld A`) and any run, on every tagged-consistent ctrl-closed 2-hart graph
whose genesis lk->cpu byte is 0 and where B's row is `b5Row` (non-holder `ld cpu`; failed
amoswap; claim; `ld x`; `lw lk`; fence; release; RE-CLAIM; fence; release):
  (tx = 0 ∨ B's x-read reads a write gmo-before B's claim)   [placement]
  ∧ vl ≠ 0                                                   [holder's lw, REQUIRED (3)]
  ∧ vc ≠ cv B                        [non-holder's lk->cpu read, D4 acquire arm].
Proof: `AxSpinGate.tierAAdequacyAnnGateT` + `wpdB5` + `splHok` + `spinHobAlloc5`; the three
facts are deposited AT THE READS and read back at B's row end (`shHltReadbackM`); `QB5Final`
turns them into the conclusion (`cpuReadNotMine` with the row fact "B has no po-earlier lk->cpu
write").
CERTIFICATES
  (a) `spa5Premises` -- EVERY premise on `spa5` (A PROVED at the real protocol: `wpdA5`);
      `spa5Shape`: B's first amoswap reads A's claim (failed spin), B's claim reads A's
      release, B's RE-CLAIM reads B's OWN release `(B,6)`, B's `lw` reads its own claim (= 1),
      B's non-holder cpu read reads A's `cpu := cv A`, B's x-read reads A's `x := 1`;
      `spa5Sound`: the capstone fires there.  Consistency and ctrl-closure by kernel decision.
  (b) `spr5WpdUnprovable` -- THE SHARPER RACE: A' writes `x := 1` (the SAME value A writes)
      AFTER its release; on the consistent, ctrl-closed `spr5` B reads it gmo-AFTER B's claim,
      so the PLACEMENT conjunct is false: A''s WPd at `spinOb5` is unprovable.
  (c) `spr5WpdTrivial` -- the same A' IS verifiable at the trivial protocol.

## Deviations from Rocq

1. O2 STAGE C (as `AxSpinProt3` deviation 1): no text oracle -- Rocq's `Tf` arguments of
   `tierA_astep`/`tierA_wpd` are gone.
2. CONTEXTS (as `AxSpinProt4` deviation 2): Rocq section `post`'s variables are explicit
   leading arguments of `QB5Final` (Rocq order); the capstone's `set` locals are the Lean-only
   defs `AxSpinProt8.cS0`/`cSN`/`cN`/`cPost`; `HwpA` and the certificate statements take
   `[InvGS_gen .hasNoLC spinGF] [AxannotGS spinGF]` instance binders; the policy `spl_pol GT` is
   passed explicitly.  `spinΣ` ↦ `AxSpinProt4`'s `spinGF`.
3. `vm_compute` ↦ `decide +kernel`; `B0/B1/B2` ↦ `b0/b1/b2`; `init_regstate` ↦ `zeroRegs`;
   `gx_img (gt_g GT)` ↦ `GT.gtG.gxImg`.

**Rocq → Lean name map.**  `QB5_final` `QB5Final`, `spin_handoff5` `spinHandoff5`, `sp5_ctrl`
`sp5Ctrl`, `spa5` `spa5`, `spr5` `spr5`, `spa5_cat_t` `spa5CatT`, `spr5_cat_t` `spr5CatT`,
`spa5_ctrl_closed` `spa5CtrlClosed`, `spr5_ctrl_closed` `spr5CtrlClosed`, `spa5_harts`
`spa5Harts`, `spr5_harts` `spr5Harts`, `spa5_shape` `spa5Shape`, `a5_wpd_spa5` `a5WpdSpa5`,
`a5_run_spa5` `a5RunSpa5`, `spa5_premises` `spa5Premises`, `spa5_sound` `spa5Sound`,
`r5_run_spr5` `r5RunSpr5`, `spr5_shape` `spr5Shape`, `spr5_wpd_unprovable`
`spr5WpdUnprovable`, `spr5_wpd_trivial` `spr5WpdTrivial`.  Lean-only (file-qualified):
`AxSpinProt8.cS0`/`cSN`/`cN`/`cPost`.

**Dropped:** the §6 `Check`/`Print Assumptions` lines (the lint's axiom check covers them).
-/
import Weak.AxSpinProt7b
import Weak.AxSpinProt4

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D
open Dtag

/-! # 1. Pure consequences of B's raw post -/

theorem QB5Final (GD : Gdexec) (Hcons : rvwmoCatConsistent GD) (tc : Nat) (vc : BitVec 8)
    (t1 t2 tx : Nat) (vx : BitVec 8) (tl : Nat) (vl : BitVec 8) (t3 : Nat)
    (Hrow : AxOpsem.grow GD hB = b5Row tc vc t1 t2 tx vx tl vl t3)
    (Himgc : GD.gdG.gxImg ca = some b0) :
    QB5 GD.gdG tx vx →
    (tx = 0 ∨ ∃ w, gwriteAt GD.gdG tx = some w ∧ gmoLt GD.gdG w (hB, 2)) ∧ vl ≠ b0 ∧ vc ≠ b2 := by
  rintro ⟨Hpl, Hlw, Hrd⟩
  have Hl0 := b5L GD tc vc t1 t2 tx vx tl vl t3 Hrow 0 _ rfl
  have Hl4 := b5L GD tc vc t1 t2 tx vx tl vl t3 Hrow 4 _ rfl
  refine ⟨?_, ?_, ?_⟩
  · rcases Hpl with H | ⟨w, Hat, Hw, Hw2 | Hlt⟩
    · exact .inl H
    · exfalso
      subst Hw2
      exact xaNeYa (b5WritesYa GD tc vc t1 t2 tx vx tl vl t3 Hrow _ _ _ Hw rfl)
    · exact .inr ⟨w, Hat, Hlt⟩
  · exact Hlw tl vl (grbLoad _ _ _ _ _ Hl4)
  · obtain ⟨Hwf, Hppo, Hlv, -⟩ := Hcons
    have Hal : clAligned [ca] GD.gdG := by
      intro w a v Ha Hw a' Ha'
      rw [List.mem_singleton] at Ha Ha'
      subst Ha Ha'
      exact ⟨v, Hw⟩
    have Hcvl : ∀ k, (cv5 k).length = [ca].length := by
      intro k
      unfold cv5
      split <;> rfl
    have Hrdv : ∀ (j : Nat) a, [ca][j]? = some a →
        ∃ t v, greadsByte GD.gdG (hB, 0) a t v ∧ [vc][j]? = some v := by
      intro j a Hj
      match j, Hj with
      | 0, Hj =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at Hj
        subst Hj
        exact ⟨tc, vc, grbLoad _ _ _ _ _ Hl0, rfl⟩
      | _ + 1, Hj => simp at Hj
    have Himg : ∀ a, a ∈ [ca] → GD.gdG.gxImg a = some b0 := by
      intro a Ha
      rw [List.mem_singleton.1 Ha]
      exact Himgc
    have Hnz : cv5 ((hB, 0) : Geid).1 ≠ List.replicate [ca].length b0 := by
      show (if hB = hB then [b2] else [b1]) ≠ [b0]
      rw [if_pos rfl]
      intro H
      exact b0NeB2 (List.cons.inj H).1.symm
    have Hinj : ∀ k, k ≠ ((hB, 0) : Geid).1 → cv5 k ≠ cv5 ((hB, 0) : Geid).1 := by
      intro k Hk
      have Hk' : k ≠ hB := Hk
      show (if k = hB then [b2] else [b1]) ≠ (if hB = hB then [b2] else [b1])
      rw [if_neg Hk', if_pos rfl]
      intro H
      exact b1NeB2 (List.cons.inj H).1
    have Hns : ∀ w a v, a ∈ [ca] → gwritesByte GD.gdG w a v →
        WeakRvwmoGraph.gpo GD.gdG w (hB, 0) → False := by
      intro w a v Ha Hw Hpo
      rw [List.mem_singleton] at Ha
      subst Ha
      exact b5NoCa GD tc vc t1 t2 tx vx tl vl t3 Hrow w v Hw Hpo.1
    have Hppo1 : ∀ e1 e2, gppo1 GD.gdG e1 e2 → gmoLt GD.gdG e1 e2 :=
      fun e1 e2 H => Hppo e1 e2 (.inl (.inl H))
    have Hne := cpuReadNotMine [ca] cv5 GD.gdG (hB, 0) [vc] Hwf Hlv Hppo1 Hal Hcvl rfl Hrdv Himg
      Hnz Hinj Hns Hrd
    intro Hv
    apply Hne
    subst Hv
    decide

/-! # 2. THE CAPSTONE -/

/-- Lean-only (Rocq `set s0`). -/
def AxSpinProt8.cS0 (sA0 : Athread) (i : Agent) : Athread :=
  if i = hA then sA0 else ⟨hp cpu0 b5M0 zeroRegs, 0⟩
/-- Lean-only (Rocq `set sN`). -/
def AxSpinProt8.cSN (sAN : Athread) (i : Agent) : Athread :=
  if i = hA then sAN else ⟨hp cpu0 hlt zeroRegs, 10⟩
/-- Lean-only (Rocq `set nf`). -/
def AxSpinProt8.cN (nA : Nat) (i : Agent) : Nat := if i = hA then nA else 13
/-- Lean-only (Rocq `set post`). -/
def AxSpinProt8.cPost (GT : GdexecT) (tx : Nat) (vx : BitVec 8) (i : Agent) (_ : Athread) :
    Prop :=
  if i = hB then QB5 (gtAdGd GT).gdG tx vx else True

theorem spinHandoff5 (GT : GdexecT)
    (HconsT : rvwmoCatConsistentT GT) (Hcl : ctrlClosed GT)
    (Hharts : ∀ e, e ∈ GT.gtG.gxGmo → e.1 = hA ∨ e.1 = hB)
    (Himgc : GT.gtG.gxImg ca = some b0)
    (tc : Nat) (vc : BitVec 8) (t1 t2 tx : Nat) (vx : BitVec 8) (tl : Nat) (vl : BitVec 8)
    (t3 : Nat)
    (HrowB : AxOpsem.grow (gtAdGd GT) hB = b5Row tc vc t1 t2 tx vx tl vl t3)
    (sA0 sAN : Athread) (nA : Nat)
    (HrunA : ∀ (_ : AxannotGS spinGF) (nm : spinN),
      nsteps (tierAAstep (gtAdGd GT) nm hA) nA sA0 sAN)
    (HkA : sA0.atK = 0) (HendA : sAN.atK = (AxOpsem.grow (gtAdGd GT) hA).length)
    (HwpA : ∀ [InvGS_gen .hasNoLC spinGF] [AxannotGS spinGF] (nm : spinN),
      ⊢ spinInit5 ya xa [ca] (gtAdGd GT) nm hA -∗
        @tierAWpd spinGF .hasNoLC _ _ (splPol GT) (gtAdGd GT) spinN Unit
          (spinOb5 ya xa [ca] cv5) nm sA0 .MaybeStuck hA (fun _ => iprop(True))) :
    (tx = 0 ∨ ∃ w, gwriteAt GT.gtG tx = some w ∧ gmoLt GT.gtG w (hB, 2)) ∧
    vl ≠ b0 ∧ vc ≠ b2 := by
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
      nsteps (tierAAstep (gtAdGd GT) nm i) (AxSpinProt8.cN nA i) (AxSpinProt8.cS0 sA0 i)
        (AxSpinProt8.cSN sAN i) := by
    intro Hann nm i Hi
    rcases Hin01 i Hi with rfl | rfl
    · exact HrunA Hann nm
    · exact b5Run cpu0 (gtAdGd GT) tc vc t1 t2 tx vx tl vl t3 HrowB
  have Hk0 : ∀ i, i ∈ [hA, hB] → (AxSpinProt8.cS0 sA0 i).atK = 0 := by
    intro i Hi
    rcases Hin01 i Hi with rfl | rfl
    · exact HkA
    · rfl
  have Hend : ∀ i, i ∈ [hA, hB] →
      (AxSpinProt8.cSN sAN i).atK = (AxOpsem.grow (gtAdGd GT) i).length := by
    intro i Hi
    rcases Hin01 i Hi with rfl | rfl
    · exact HendA
    · show 10 = (AxOpsem.grow (gtAdGd GT) hB).length
      rw [HrowB]
      rfl
  have Hwp : ∀ [InvGS_gen .hasNoLC spinGF] [AxannotGS spinGF] (nm : spinN),
      ⊢ ([∗list] i ∈ [hA, hB], spinInit5 ya xa [ca] (gtAdGd GT) nm i) -∗
        [∗list] i ∈ [hA, hB],
          @tierAWpd spinGF .hasNoLC _ _ (splPol GT) (gtAdGd GT) spinN Unit
            (spinOb5 ya xa [ca] cv5) nm (AxSpinProt8.cS0 sA0 i) .MaybeStuck i
            (fun s => iprop(⌜AxSpinProt8.cPost GT tx vx i s⌝)) := by
    intro Hinv Hann nm
    iintro HI
    icases (AxTokLedgerMp.bigSepLPair hA hB
      (fun i => spinInit5 (GF := spinGF) ya xa [ca] (gtAdGd GT) nm i)).1 $$ HI with ⟨HA, HB⟩
    iapply (AxTokLedgerMp.bigSepLPair hA hB _).2
    rw [show AxSpinProt8.cS0 sA0 hA = sA0 from if_pos rfl,
      show AxSpinProt8.cS0 sA0 hB = ⟨hp cpu0 b5M0 zeroRegs, 0⟩ from if_neg (by decide)]
    isplitl [HA]
    · iapply (AxSpinWit.tierAWpdMono (hlc := .hasNoLC) (pol := splPol GT) (gtAdGd GT) spinN Unit
        (spinOb5 ya xa [ca] cv5) nm sA0 .MaybeStuck hA (fun _ => iprop(True))
        (fun s => iprop(⌜AxSpinProt8.cPost GT tx vx hA s⌝))
        (fun _ => pure_mono (fun _ => by
          unfold AxSpinProt8.cPost; rw [if_neg (by decide)]; trivial)))
      iapply HwpA nm $$ HA
    · iapply (AxSpinWit.tierAWpdMono (hlc := .hasNoLC) (pol := splPol GT) (gtAdGd GT) spinN Unit
        (spinOb5 ya xa [ca] cv5) nm ⟨hp cpu0 b5M0 zeroRegs, 0⟩ .MaybeStuck hB
        (fun _ => iprop(⌜QB5 (gtAdGd GT).gdG tx vx⌝))
        (fun s => iprop(⌜AxSpinProt8.cPost GT tx vx hB s⌝))
        (fun _ => pure_mono (fun Hv => by
          unfold AxSpinProt8.cPost; rw [if_pos rfl]; exact Hv)))
      unfold spinInit5
      icases HB with ⟨Hil, Hnh⟩
      iapply (wpdB5 (hlc := .hasNoLC) (GF := spinGF) GT nm cpu0 Hcons tc vc t1 t2 tx vx tl vl
        t3 HrowB) $$ Hil Hnh
  have HxC : xa ∉ [ca] := by
    rw [List.mem_singleton]
    exact fun h => caNeXa h.symm
  have HndC : [ca].Nodup := by simp
  have Hfin := @tierAAdequacyAnnGateT spinGF _ _ (splPol GT) GT spinN Unit
    (spinOb5 ya xa [ca] cv5) (spinInit5 ya xa [ca] (gtAdGd GT)) (splAxpolWf GT) HconsT [hA, hB]
    Hnd Hharts' (AxSpinProt8.cS0 sA0) (AxSpinProt8.cSN sAN) (AxSpinProt8.cN nA) Hrun Hk0 Hend
    (AxSpinProt8.cPost GT tx vx) Hwp
    (spinHobAlloc5 (GF := spinGF) ya xa [ca] cv5 (gtAdGd GT) [hA, hB] Hnd HxC HndC)
    (splHok GT HconsT Hcl) hB (by simp)
  have Hq : QB5 (gtAdGd GT).gdG tx vx :=
    (if_pos rfl : AxSpinProt8.cPost GT tx vx hB _ = QB5 (gtAdGd GT).gdG tx vx) ▸ Hfin
  exact QB5Final (gtAdGd GT) Hcons tc vc t1 t2 tx vx tl vl t3 HrowB Himgc Hq

/-! # 3. CERTIFICATE (a): SATISFIABILITY on `spa5` -/

/-- B's branch-feeding amoswap reads control every po-later store (closed). -/
def sp5Ctrl : List Tdep :=
  [(((hB, 1), (hB, 2)), DTctrl), (((hB, 1), (hB, 6)), DTctrl),
   (((hB, 1), (hB, 7)), DTctrl), (((hB, 1), (hB, 9)), DTctrl),
   (((hB, 2), (hB, 6)), DTctrl), (((hB, 2), (hB, 7)), DTctrl),
   (((hB, 2), (hB, 9)), DTctrl), (((hB, 7), (hB, 9)), DTctrl)]

/-- A claims genesis, writes cpu := cv A, x := 1, cpu := 0, releases; B reads cpu = cv A
(non-holder), FAILS once (reads A's claim), claims A's release, reads x = 1, reads its own claim
at `lw lk` (= 1), releases, RE-CLAIMS ITS OWN release, releases. -/
def spa5 : GdexecT :=
  mkgt [a5Row 0, b5Row 2 b1 1 6 4 b1 7 b1 8]
    [(hA, 0), (hA, 1), (hB, 0), (hB, 1), (hA, 2), (hA, 3), (hA, 5),
     (hB, 2), (hB, 3), (hB, 4), (hB, 6), (hB, 7), (hB, 9)] sp5Ctrl

/-- THE RACE: A' = acquire; fence; release; `sd x ← 1` (value allowed, placement not): B claims
A''s release, then reads A''s post-release `x := 1`, which is gmo-AFTER B's claim. -/
def spr5 : GdexecT :=
  mkgt [r5Row, b5Row 0 b0 1 3 5 b1 4 b1 6]
    [(hA, 0), (hB, 0), (hB, 1), (hA, 2), (hB, 2), (hA, 3), (hB, 3),
     (hB, 4), (hB, 6), (hB, 7), (hB, 9)] sp5Ctrl

theorem spa5CatT : rvwmoCatConsistentT spa5 := catTConsistentBSound _ (by decide +kernel)
theorem spr5CatT : rvwmoCatConsistentT spr5 := catTConsistentBSound _ (by decide +kernel)
theorem spa5CtrlClosed : ctrlClosed spa5 := ctrlClosedBSound _ spa5CatT.1 (by decide +kernel)
theorem spr5CtrlClosed : ctrlClosed spr5 := ctrlClosedBSound _ spr5CatT.1 (by decide +kernel)

theorem spa5Harts : ∀ e, e ∈ spa5.gtG.gxGmo → e.1 = hA ∨ e.1 = hB := by
  intro e He
  have h : spa5.gtG.gxGmo.all (fun e : Geid => decide (e.1 = hA ∨ e.1 = hB)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.1 h e He)

theorem spr5Harts : ∀ e, e ∈ spr5.gtG.gxGmo → e.1 = hA ∨ e.1 = hB := by
  intro e He
  have h : spr5.gtG.gxGmo.all (fun e : Geid => decide (e.1 = hA ∨ e.1 = hB)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.1 h e He)

/-- The shape of `spa5`: every item of the task is exercised.  (ii) B's first amoswap reads A's
claim (failed spin); B's claim reads A's release; B's SECOND claim reads B's OWN release
`(B,6)`; (iii) B's `lw lk` reads its own claim, value 1; (iv) B's non-holder cpu read reads A's
`cpu := cv A` write; and B's x-read reads A's `x := 1`. -/
theorem spa5Shape :
    graphValue (gtAdGd spa5) (hB, 1) = some [b1] ∧ grfAt spa5.gtG ya (hA, 0) (hB, 1) ∧
    grfAt spa5.gtG ya (hA, 5) (hB, 2) ∧
    grfAt spa5.gtG ya (hB, 6) (hB, 7) ∧
    graphValue (gtAdGd spa5) (hB, 4) = some [b1] ∧ grfAt spa5.gtG ya (hB, 2) (hB, 4) ∧
    graphValue (gtAdGd spa5) (hB, 0) = some [b1] ∧ grfAt spa5.gtG ca (hA, 1) (hB, 0) ∧
    graphValue (gtAdGd spa5) (hB, 3) = some [b1] ∧ grfAt spa5.gtG xa (hA, 2) (hB, 3) :=
  ⟨by decide +kernel, (grfAtBSpec _ _ _ _).1 (by decide +kernel),
    (grfAtBSpec _ _ _ _).1 (by decide +kernel), (grfAtBSpec _ _ _ _).1 (by decide +kernel),
    by decide +kernel, (grfAtBSpec _ _ _ _).1 (by decide +kernel),
    by decide +kernel, (grfAtBSpec _ _ _ _).1 (by decide +kernel),
    by decide +kernel, (grfAtBSpec _ _ _ _).1 (by decide +kernel)⟩

theorem a5WpdSpa5 :
    ∀ [InvGS_gen .hasNoLC spinGF] [AxannotGS spinGF] (nm : spinN),
      ⊢ spinInit5 ya xa [ca] (gtAdGd spa5) nm hA -∗
        @tierAWpd spinGF .hasNoLC _ _ (splPol spa5) (gtAdGd spa5) spinN Unit
          (spinOb5 ya xa [ca] cv5) nm ⟨hp cpu0 a5M0 zeroRegs, 0⟩ .MaybeStuck hA
          (fun _ => iprop(True)) := by
  intro _ _ nm
  unfold spinInit5
  iintro ⟨Hil, Hnh⟩
  iapply (wpdA5 (hlc := .hasNoLC) (GF := spinGF) spa5 nm cpu0 (catTAd spa5 spa5CatT) 0 rfl)
    $$ Hil Hnh

theorem a5RunSpa5 : ∀ (_ : AxannotGS spinGF) (nm : spinN),
    nsteps (tierAAstep (gtAdGd spa5) nm hA) 7
      ⟨hp cpu0 a5M0 zeroRegs, 0⟩ ⟨hp cpu0 hlt zeroRegs, 6⟩ :=
  fun _ _ => a5Run cpu0 (gtAdGd spa5) 0 rfl

/-- EVERY premise of `spinHandoff5` on `spa5`, as one conjunction. -/
theorem spa5Premises :
    rvwmoCatConsistentT spa5 ∧ ctrlClosed spa5 ∧
    (∀ e, e ∈ spa5.gtG.gxGmo → e.1 = hA ∨ e.1 = hB) ∧
    spa5.gtG.gxImg ca = some b0 ∧
    AxOpsem.grow (gtAdGd spa5) hB = b5Row 2 b1 1 6 4 b1 7 b1 8 ∧
    (∀ (_ : AxannotGS spinGF) (nm : spinN),
      nsteps (tierAAstep (gtAdGd spa5) nm hA) 7
        ⟨hp cpu0 a5M0 zeroRegs, 0⟩ ⟨hp cpu0 hlt zeroRegs, 6⟩) ∧
    (⟨hp cpu0 a5M0 zeroRegs, 0⟩ : Athread).atK = 0 ∧
    (⟨hp cpu0 hlt zeroRegs, 6⟩ : Athread).atK = (AxOpsem.grow (gtAdGd spa5) hA).length ∧
    (∀ [InvGS_gen .hasNoLC spinGF] [AxannotGS spinGF] (nm : spinN),
      ⊢ spinInit5 ya xa [ca] (gtAdGd spa5) nm hA -∗
        @tierAWpd spinGF .hasNoLC _ _ (splPol spa5) (gtAdGd spa5) spinN Unit
          (spinOb5 ya xa [ca] cv5) nm ⟨hp cpu0 a5M0 zeroRegs, 0⟩ .MaybeStuck hA
          (fun _ => iprop(True))) :=
  ⟨spa5CatT, spa5CtrlClosed, spa5Harts, rfl, rfl, a5RunSpa5, rfl, rfl, a5WpdSpa5⟩

/-- The capstone fires on `spa5`; its conclusion is TRUE there. -/
theorem spa5Sound :
    (4 = 0 ∨ ∃ w, gwriteAt spa5.gtG 4 = some w ∧ gmoLt spa5.gtG w (hB, 2)) ∧
    b1 ≠ b0 ∧ b1 ≠ b2 :=
  spinHandoff5 spa5 spa5CatT spa5CtrlClosed spa5Harts rfl 2 b1 1 6 4 b1 7 b1 8 rfl _ _ 7
    a5RunSpa5 rfl rfl a5WpdSpa5

/-! # 4. CERTIFICATE (b): THE SHARPER RACE (placement, not value) -/

theorem r5RunSpr5 : ∀ (_ : AxannotGS spinGF) (nm : spinN),
    nsteps (tierAAstep (gtAdGd spr5) nm hA) 5
      ⟨hp cpu0 r5M0 zeroRegs, 0⟩ ⟨hp cpu0 hlt zeroRegs, 4⟩ :=
  fun _ _ => r5Run cpu0 (gtAdGd spr5) rfl

/-- B claims A''s release; B's x-read reads A''s post-release `x := 1` (SAME value as the
positive A writes), which is gmo-AFTER B's claim. -/
theorem spr5Shape :
    grfAt spr5.gtG ya (hA, 2) (hB, 2) ∧
    graphValue (gtAdGd spr5) (hB, 3) = some [b1] ∧
    grfAt spr5.gtG xa (hA, 3) (hB, 3) ∧
    gmoLt spr5.gtG (hB, 2) (hA, 3) :=
  ⟨(grfAtBSpec _ _ _ _).1 (by decide +kernel), by decide +kernel,
    (grfAtBSpec _ _ _ _).1 (by decide +kernel), (gmoLtBSpec _ _ _).1 (by decide +kernel)⟩

theorem spr5WpdUnprovable :
    ¬ (∀ [InvGS_gen .hasNoLC spinGF] [AxannotGS spinGF] (nm : spinN),
        ⊢ spinInit5 ya xa [ca] (gtAdGd spr5) nm hA -∗
          @tierAWpd spinGF .hasNoLC _ _ (splPol spr5) (gtAdGd spr5) spinN Unit
            (spinOb5 ya xa [ca] cv5) nm ⟨hp cpu0 r5M0 zeroRegs, 0⟩ .MaybeStuck hA
            (fun _ => iprop(True))) := by
  intro Hwp
  rcases (spinHandoff5 spr5 spr5CatT spr5CtrlClosed spr5Harts rfl 0 b0 1 3 5 b1 4 b1 6 rfl _ _ 5
    r5RunSpr5 rfl rfl Hwp).1 with H | ⟨w, Hw, Hlt⟩
  · exact absurd H (by decide)
  · have Hat : gwriteAt spr5.gtG 5 = some (hA, 3) := by decide +kernel
    rw [Hat] at Hw
    cases Hw
    have Hb := (gmoLtBSpec _ _ _).2 Hlt
    have Hf : gmoLtB spr5.gtG (hA, 3) (hB, 2) = false := by decide +kernel
    rw [Hf] at Hb
    cases Hb

/-! # 5. CERTIFICATE (c): SANITY TWIN at the trivial protocol -/

theorem spr5WpdTrivial :
    ∀ [InvGS_gen .hasNoLC spinGF] [AxannotGS spinGF] (nm : Unit),
      ⊢ (iprop(emp) : IProp spinGF) -∗
        @tierAWpd spinGF .hasNoLC _ _ (splPol spr5) (gtAdGd spr5) Unit Unit trivOb nm
          ⟨hp cpu0 r5M0 zeroRegs, 0⟩ .MaybeStuck hA (fun _ => iprop(True)) := by
  intro _ _ nm
  cases nm
  iintro _
  iapply (wpdR5Triv (hlc := .hasNoLC) (GF := spinGF) spr5 cpu0 rfl)

end Weak
