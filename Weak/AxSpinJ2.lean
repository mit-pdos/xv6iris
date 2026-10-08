/-
Weak: the allocpid-SHAPED capstones of `AxSpinU4` re-derived with distinctness via
ISSUED-FRAGMENT EXCLUSIVITY, through the JOINT adequacy `AxSpinJ.tierAAdequacyAnnGateJointT`,
at `Ixv6` (GF := `AxSpinX7.xv6GF`, instance `axGA2 … (protXv6 Lx) nm`, policy `xv6Pol GT`,
`xv6Hok`).

Rocq: `iris/AxSpinJ2.v` @ xxvzwolszwmp.

## The Rocq header, in substance

PIPELINE MILESTONE: hand `Pexv6` nodes at real widths (no fetch/decode), layout `Lx` for the
protocol (+ `L3` below for the third hart's init), certificate graphs decided by the shipped
checker.

Per-hart iProp posts: `Φ A := UPost nm G A wA` = `⌜npSrc⌝ ∗ FRAG nm wA` (the minted EXCLUSIVE
◯{v}, v's word = the read word, READ BACK at row end), `Φ B` likewise, `Φ C := True`.  Hjoint =
`AxSpinU2.upostJoint` (two fragments at one ghost name ⇒ different words).  NO use of the pure
dichotomy `AxSpinU3.uDistinct`.

CAPSTONES
  `uAlloc2Joint` -- `AxSpinU4.uAlloc2`'s exact statement (2 harts), `wA ≠ wB` now from fragment
    exclusivity.
  `uAllocOpen` -- THEOREM 2's SHAPE, OPEN THIRD HART: harts `[A, B, C]`; A and B run the CS rows
    (`uRow`); C is ARBITRARY: any program/run with `HwpC : ∀ Hinv Hann nm, ⊢ xv6Init L3 GD nm C -∗
    WPd_C {{ True }}` at `Ixv6`.  Conclusion: `upost A wA ∧ upost B wB ∧ wA ≠ wB`.
    THIS IS THE OWNERSHIP-LOAD-BEARING STATEMENT: without `HwpC`, `wA ≠ wB` is FALSE --
    certificate (b) exhibits a consistent, ctrl-closed 3-hart graph satisfying every other
    premise on which an unlocked C store makes `wA = wB`.
THE THIRD HART'S INIT.  `Lx` lists harts `[A, B]` only; `L3` := `Lx` with `xlHarts := [A, B, C]`
  (C has NO private bytes).  `protL3Lx`: `protXv6 L3 ⊢ protXv6 Lx` (`priv L3 ⊆ priv Lx`), so the
  allocation `xv6HobAlloc L3` feeds the SAME `Ixv6` instance; A/B's `wpdCs` (at `Lx`) consumes
  `isLock`/`notheld` from `xv6Init L3` (convertible: lock/nextpid addresses coincide).
CERTIFICATES
  (a′) `ua3Sound`: C := the SAME CS program on the concrete `ua3` (A, then B, then C each claim
       the previous release; nextpid 0 → 1 → 2 → 3); every premise of `uAllocOpen` is
       discharged (`ua3Premises`), C's WPd is `wpdCs` (`uWpdOn3`).  (2-hart: `uaJointSound`.)
  (b)  `ur3WpdUnprovable`: C := an UNLOCKED nextpid writer (`sw nextpid ← 0`).  On the
       consistent, ctrl-closed `ur3` (`ur3Premises`: every premise but `HwpC`) A reads the image
       0 and writes 1; C's 0 lands gmo-after A's store; B claims A's release and reads C's 0
       (`ur3Shape`): `wA = wB = 0`, so C's WPd at `Ixv6` is UNPROVABLE.
  (c′) `ur3WpdTrivial`: SANITY TWIN -- the same C IS verifiable at the trivial protocol.

## Deviations from Rocq

1. VOCABULARY (as `AxSpinU4` deviation 1): `Z` ↦ `Int`, `bv n` ↦ `BitVec n`, `gt_g GT` ↦
   `GT.gtG`, `gd_g GD` ↦ `GD.gdG`, `l !! j` ↦ `l[j]?`, `pa_z` ↦ `paZ`, `Z_to_bv 32` ↦
   `BitVec.ofInt 32`, `bv_unsigned w + 1 < 2^32` ↦ `w.toNat + 1 < 2 ^ 32`, `a ≤ b < c` ↦
   `a ≤ b ∧ b < c`, `B0` ↦ `b0`, `init_regstate` ↦ `zeroRegs`, `AThread p k` ↦ `⟨p, k⟩`,
   `M unit` ↦ `SailM Unit` (`rzM0` an `abbrev`); `OBX` is `protXv6 Lx` inline, `xv6Σ` is
   `AxSpinX7.xv6GF`.  Rocq's `Notation hC := 2` is `abbrev hC : Nat := 2` (as AxSpinWit's
   `hA`/`hB`).  Rocq `a ++ b ++ c` (right-nested) is written `a ++ (b ++ c)`.
2. CONTEXTS: `Φab`'s instance arguments are the explicit function arguments of Rocq's type;
   `wpdCsAb` takes `Hinv Hann` explicitly (as Rocq); `HwpC`, `Hwp`, `Hjoint` and the certificate
   statements bind `[InvGS_gen .hasNoLC xv6GF] [AxannotGS xv6GF]` as instance binders.
   `prot_L3_Lx`/`xv6_Hob_alloc3` are stated for any `{GF} [AxSpinX.Xv6G GF]` (Rocq: any `Σ`
   with `xv6G Σ`).  The capstones' `set` locals are Lean-only defs `AxSpinJ2.oS0`/`oSN`/`oN`
   (`u_alloc_open`'s `s0`/`sN`/`nf`; `u_alloc2_joint`'s are constant lambdas).  Section
   `runrz`'s unused `axirisG Σ` is dropped (`cpu` an explicit leading argument); section
   `wpdRZ`'s variables are `{hlc GF} [InvGS_gen hlc GF] [AxannotGS GF]` then explicit
   `GT cpu Hrow` (any `hlc`); the local instances `rz_pol`/`rz_G` are inlined (`xv6Pol GT` and
   `shG (gtAdGd GT) Unit Unit trivOb ()` passed explicitly).  O2 STAGE C: Rocq's `Tf` argument
   of `tierA_astep`/`tierA_wpd` is gone (the rows contain no fetch events, so row positions,
   gmo lists and ctrl edges are Rocq's verbatim).
3. `harts_of_gmo3` takes the `∀ e ∈ gmo` form in place of `Forall` (as `AxSpinX7.hartsOfGmo`);
   the certificates' `repeat constructor` ↦ a decided `List.all`.  `vm_compute`/`vmr` ↦
   `decide +kernel`.  `fe_trivu` is `AxSpinU4.feTrivu`.
4. PROOFS: the `xv6Init L3` → `Lx` conversions of `isLock`/`notheld` are the Lean-only
   `.rfl` bridge `AxSpinJ2.initL3Cs` (proof-mode `iexact` does not unfold `L3`); the 3-element
   big-sep split is the Lean-only `AxSpinJ2.bigSepLTriple`; `Φab`'s branch values are the
   Lean-only `AxSpinJ2.ΦabA`/`ΦabB`/`ΦabC`.
5. The §5 `Check`/`Print Assumptions` lines are not ported (the lint's axiom check covers them).

**Rocq → Lean name map.**  `hC` `hC`, `L3` `AxSpinJ2.L3` (dup: AxLock3), `priv_L3_Lx`
`privL3Lx`, `wok_L3_Lx` `wokL3Lx`, `L3_ok` `L3Ok`, `prot_L3_Lx` `protL3Lx`, `xv6_Hob_alloc3`
`xv6HobAlloc3`, `Φab` `Φab`, `joint_AB` `jointAB`, `wpd_cs_ab` `wpdCsAb`, `u_alloc2_joint`
`uAlloc2Joint`, `u_alloc_open` `uAllocOpen`, `harts_of_gmo3` `hartsOfGmo3`, `u_wpd_on3`
`uWpdOn3`, `two32` `two32`, `nowrap_two` `nowrapTwo`, `ua3_rowC` `ua3RowC`, `ua3` `ua3`,
`ua3_cat_t` `ua3CatT`, `ua3_ctrl_closed` `ua3CtrlClosed`, `ua3_harts` `ua3Harts`, `ua3_shape`
`ua3Shape`, `ua3_premises` `ua3Premises`, `ua3_sound` `ua3Sound`, `ua_joint_sound`
`uaJointSound`, `rz_m0` `rzM0`, `rz_row` `rzRow`, `ur3_rowB` `ur3RowB`, `ur3` `ur3`,
`ur3_cat_t` `ur3CatT`, `ur3_ctrl_closed` `ur3CtrlClosed`, `ur3_harts` `ur3Harts`, `ur3_shape`
`ur3Shape`, `rz_run` `rzRun`, `rz_run_ur3` `rzRunUr3`, `ur3_premises` `ur3Premises`,
`ur3_wpd_unprovable` `ur3WpdUnprovable`, `wpdRZ_triv` `wpdRZTriv`, `ur3_wpd_trivial`
`ur3WpdTrivial`.
Lean-only (file-qualified): `AxSpinJ2.bigSepLTriple`, `AxSpinJ2.initL3Cs`,
`AxSpinJ2.ΦabA`/`ΦabB`/`ΦabC`, `AxSpinJ2.oS0`/`oSN`/`oN`.

**Dropped:** none.  Rocq 38 definitions/theorems + the notation `hC` + the 2 local instances
`rz_pol`/`rz_G` (inlined); Lean 47 = 38 ported + `hC` + 8 Lean-only.
-/
import Weak.AxSpinU4
import Weak.AxSpinJ

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D
open Dtag

abbrev hC : Nat := 2

/-! # 1. The 3-hart layout `L3` (init only; the protocol stays `protXv6 Lx`) -/

def AxSpinJ2.L3 : Xlay where
  xlLk := Lx.xlLk
  xlNp := Lx.xlNp
  xlHarts := [hA, hB, hC]
  xlStk := Lx.xlStk
  xlCpuf := Lx.xlCpuf
  xlRo := Lx.xlRo
  xlText := Lx.xlText

theorem privL3Lx (a : Int) (j : Agent) : priv AxSpinJ2.L3 a j → priv Lx a j := by
  rintro ⟨-, Hs⟩
  by_cases hj : j = hB
  · subst hj
    exact ⟨by show hB ∈ [hA, hB]; simp, Hs⟩
  · exfalso
    simp only [AxSpinJ2.L3, Lx, if_neg hj] at Hs
    rcases Hs with Hs | Hs <;> exact notElemOfEmpty Hs

theorem wokL3Lx (a : Int) (j : Agent) : wok AxSpinJ2.L3 a j → wok Lx a j := by
  rintro (H | H | H)
  · exact Or.inl H
  · exact Or.inr (Or.inl H)
  · exact Or.inr (Or.inr (privL3Lx a j H))

theorem L3Ok : xlayOk AxSpinJ2.L3 := by
  obtain ⟨H1, H2, H3, H4, -, -⟩ := LxOk
  refine ⟨H1, fun a j Hp => H2 a j (privL3Lx a j Hp),
    fun a j1 j2 Hp1 Hp2 => H3 a j1 j2 (privL3Lx a j1 Hp1) (privL3Lx a j2 Hp2),
    fun a j Hro Hw => H4 a j Hro (wokL3Lx a j Hw), ?_, ?_⟩
  · show [hA, hB, hC].Nodup
    decide
  · intro i Hi
    have Hi' : i ∈ [hA, hB, hC] := Hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at Hi'
    unfold NCPU
    rcases Hi' with rfl | rfl | rfl <;> decide

theorem protL3Lx {GF : BundledGFunctors} [AxSpinX.Xv6G GF] (nm : Xv6N) (GD : Gdexec) (σ : Unit)
    (s : GSet Geid) :
    protXv6 (GF := GF) AxSpinJ2.L3 nm GD σ s ⊢ protXv6 Lx nm GD σ s := by
  unfold protXv6
  exact sep_mono (pure_mono fun ⟨Hwc, Hcpu, Hwok⟩ =>
    ⟨Hwc, Hcpu, fun e a v He Hw => wokL3Lx a e.1 (Hwok e a v He Hw)⟩) .rfl

/-- The allocation at harts `[A, B, C]`, into the `Ixv6` protocol state. -/
theorem xv6HobAlloc3 {GF : BundledGFunctors} [AxSpinX.Xv6G GF] (GD : Gdexec) (n0 : Int) :
    (∀ a, a ∈ clb Lx → GD.gdG.gxImg a = some b0) →
    0 ≤ n0 ∧ n0 < 2 ^ 32 →
    (∀ (j : Nat) a v, (npb Lx)[j]? = some a →
      (WeakInterpProj.wbytes 4 (BitVec.ofInt 32 n0))[j]? = some v → GD.gdG.gxImg a = some v) →
    ⊢ iprop(|==> ∃ (nm : Xv6N) (σ0 : Unit), protXv6 (GF := GF) Lx nm GD σ0 ∅ ∗
      [∗list] i ∈ [hA, hB, hC], xv6Init AxSpinJ2.L3 GD nm i) := by
  intro Hcl Hn0 Hnp
  have H : ⊢ iprop(|==> ∃ (nm : Xv6N) (σ0 : Unit), protXv6 (GF := GF) AxSpinJ2.L3 nm GD σ0 ∅ ∗
      [∗list] i ∈ [hA, hB, hC], xv6Init AxSpinJ2.L3 GD nm i) :=
    xv6HobAlloc AxSpinJ2.L3 GD n0 L3Ok Hcl Hn0 Hnp
  imod H with ⟨%nm, %σ0, Hob, Hi⟩
  imodintro
  iexists nm, σ0
  isplitl [Hob]
  · iapply (protL3Lx nm GD σ0 ∅) $$ Hob
  · iexact Hi

/-! # 2. Per-hart posts and the joint step -/

/-- Lean-only: the three-element big separating conjunction. -/
theorem AxSpinJ2.bigSepLTriple {GF : BundledGFunctors} {α : Type} (x y z : α)
    (Φ : α → IProp GF) : ([∗list] a ∈ [x, y, z], Φ a) ⊣⊢ Φ x ∗ (Φ y ∗ Φ z) :=
  BigSepL.bigSepL_cons.trans (sep_congr .rfl (AxTokLedgerMp.bigSepLPair y z Φ))

/-- Lean-only: the CS resources of `xv6Init L3`, at `Lx` (convertible). -/
theorem AxSpinJ2.initL3Cs {GF : BundledGFunctors} [AxSpinX.Xv6G GF] (GD : Gdexec) (nm : Xv6N)
    (i : Agent) :
    xv6Init (GF := GF) AxSpinJ2.L3 GD nm i ⊢
      isLock nm.xnReg Lx.xlLk (RPid Lx nm.xnH nm.xnM nm.xnI GD) ∗ notheld nm.xnReg Lx.xlLk i := by
  have Hb1 : isLock (GF := GF) nm.xnReg AxSpinJ2.L3.xlLk
      (RPid AxSpinJ2.L3 nm.xnH nm.xnM nm.xnI GD) ⊢
      isLock nm.xnReg Lx.xlLk (RPid Lx nm.xnH nm.xnM nm.xnI GD) := .rfl
  have Hb2 : notheld (GF := GF) nm.xnReg AxSpinJ2.L3.xlLk i ⊢ notheld nm.xnReg Lx.xlLk i := .rfl
  unfold xv6Init
  iintro ⟨-, -, -, Hil, Hnh⟩
  isplitl [Hil]
  · iapply Hb1 $$ Hil
  · iapply Hb2 $$ Hnh

/-- Φ A / Φ B: the read-back post with the EXCLUSIVE fragment; anyone else: True. -/
def Φab (G : Gexec) (wA wB : BitVec 32) :
    InvGS_gen .hasNoLC AxSpinX7.xv6GF → AxannotGS AxSpinX7.xv6GF → Xv6N → Agent → Athread →
      IProp AxSpinX7.xv6GF :=
  fun _ _ nm i _ =>
    if i = hA then UPost nm G hA wA else if i = hB then UPost nm G hB wB else iprop(True)

theorem AxSpinJ2.ΦabA (G : Gexec) (wA wB : BitVec 32) (Hinv : InvGS_gen .hasNoLC AxSpinX7.xv6GF)
    (Hann : AxannotGS AxSpinX7.xv6GF) (nm : Xv6N) (s : Athread) :
    Φab G wA wB Hinv Hann nm hA s = UPost nm G hA wA := by
  simp [Φab]

theorem AxSpinJ2.ΦabB (G : Gexec) (wA wB : BitVec 32) (Hinv : InvGS_gen .hasNoLC AxSpinX7.xv6GF)
    (Hann : AxannotGS AxSpinX7.xv6GF) (nm : Xv6N) (s : Athread) :
    Φab G wA wB Hinv Hann nm hB s = UPost nm G hB wB := by
  simp [Φab]

theorem AxSpinJ2.ΦabC (G : Gexec) (wA wB : BitVec 32) (Hinv : InvGS_gen .hasNoLC AxSpinX7.xv6GF)
    (Hann : AxannotGS AxSpinX7.xv6GF) (nm : Xv6N) (s : Athread) :
    Φab G wA wB Hinv Hann nm hC s = iprop(True) := by
  simp [Φab]

theorem jointAB (G : Gexec) (wA wB : BitVec 32) (nm : Xv6N) :
    ⊢ UPost (GF := AxSpinX7.xv6GF) nm G hA wA -∗ UPost nm G hB wB -∗
      ⌜upost G hA wA ∧ upost G hB wB ∧ wA ≠ wB⌝ := by
  iintro HA HB
  unfold UPost FRAG
  icases HA with ⟨%HsA, %vA, HfA, %HvA⟩
  icases HB with ⟨%HsB, %vB, HfB, %HvB⟩
  ihave %Hne := (upostJoint (GF := AxSpinX7.xv6GF) nm G hA hB wA wB) $$ [HfA HfB]
  · unfold UPost FRAG
    isplitl [HfA]
    · isplitr
      · ipureintro
        exact HsA
      · iexists vA
        isplitl [HfA]
        · iexact HfA
        · ipureintro
          exact HvA
    · isplitr
      · ipureintro
        exact HsB
      · iexists vB
        isplitl [HfB]
        · iexact HfB
        · ipureintro
          exact HvB
  ipureintro
  exact ⟨⟨HsA, vA, HvA⟩, ⟨HsB, vB, HvB⟩, Hne⟩

/-- The CS hart's WPd at `Φab` (A or B). -/
theorem wpdCsAb (GT : GdexecT) (Hcons : rvwmoCatConsistent (gtAdGd GT)) (wA wB : BitVec 32)
    (Hinv : InvGS_gen .hasNoLC AxSpinX7.xv6GF) (Hann : AxannotGS AxSpinX7.xv6GF) (nm : Xv6N)
    (i : Agent) (t : Nat) (ts : List Nat) (w8 : BitVec 32)
    (Hi : i = hA ∧ w8 = wA ∨ i = hB ∧ w8 = wB)
    (Hrow : AxOpsem.grow (gtAdGd GT) i = uRow t ts w8) (Hn : w8.toNat + 1 < 2 ^ 32) :
    ⊢ isLock (GF := AxSpinX7.xv6GF) nm.xnReg Lx.xlLk
        (RPid Lx nm.xnH nm.xnM nm.xnI (gtAdGd GT)) -∗
      notheld nm.xnReg Lx.xlLk i -∗
      @tierAWpd AxSpinX7.xv6GF .hasNoLC Hinv Hann (xv6Pol GT) (gtAdGd GT) Xv6N Unit (protXv6 Lx)
        nm ⟨hp cpu0 uM0 zeroRegs, 0⟩ .MaybeStuck i (Φab (gtAdGd GT).gdG wA wB Hinv Hann nm i) := by
  have h := wpdCs (hlc := .hasNoLC) (GF := AxSpinX7.xv6GF) GT nm cpu0 Hcons i t ts w8 Hrow Hn
  refine h.trans (wand_mono .rfl (wand_mono .rfl
    (AxSpinWit.tierAWpdMono (hlc := .hasNoLC) (pol := xv6Pol GT) (gtAdGd GT) Xv6N Unit
      (protXv6 Lx) nm _ .MaybeStuck i _ _ (fun s => ?_))))
  rcases Hi with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [AxSpinJ2.ΦabA]
  · rw [AxSpinJ2.ΦabB]

/-! # 3. CAPSTONES -/

/-- `AxSpinU4.uAlloc2`'s statement, distinctness from fragment exclusivity. -/
theorem uAlloc2Joint (GT : GdexecT)
    (HconsT : rvwmoCatConsistentT GT) (Hcl : ctrlClosed GT)
    (Hharts : ∀ e, e ∈ GT.gtG.gxGmo → e.1 = hA ∨ e.1 = hB)
    (Himgc : ∀ a, a ∈ clb Lx → GT.gtG.gxImg a = some b0)
    (n0 : Int) (Hn0 : 0 ≤ n0 ∧ n0 < 2 ^ 32)
    (Himgn : ∀ (j : Nat) a v, (npb Lx)[j]? = some a →
      (WeakInterpProj.wbytes 4 (BitVec.ofInt 32 n0))[j]? = some v → GT.gtG.gxImg a = some v)
    (tA : Nat) (tsA : List Nat) (wA : BitVec 32) (tB : Nat) (tsB : List Nat) (wB : BitVec 32)
    (HrA : AxOpsem.grow (gtAdGd GT) hA = uRow tA tsA wA)
    (HrB : AxOpsem.grow (gtAdGd GT) hB = uRow tB tsB wB)
    (HnA : wA.toNat + 1 < 2 ^ 32) (HnB : wB.toNat + 1 < 2 ^ 32) :
    upost GT.gtG hA wA ∧ upost GT.gtG hB wB ∧ wA ≠ wB := by
  have Hin01 : ∀ i : Agent, i ∈ [hA, hB] → i = hA ∨ i = hB := by
    intro i Hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at Hi
    exact Hi
  have Hnd : [hA, hB].Nodup := by decide
  have Hharts' : ∀ e, e ∈ GT.gtG.gxGmo → e.1 ∈ [hA, hB] := by
    intro e He
    rcases Hharts e He with H | H <;> rw [H] <;> simp
  have Hcons := catTAd GT HconsT
  have Hrun : ∀ (_ : AxannotGS AxSpinX7.xv6GF) (nm : Xv6N) i, i ∈ [hA, hB] →
      nsteps (tierAAstep (gtAdGd GT) nm i) ((fun _ => 6) i)
        ((fun _ => (⟨hp cpu0 uM0 zeroRegs, 0⟩ : Athread)) i)
        ((fun _ => (⟨hp cpu0 hlt zeroRegs, 5⟩ : Athread)) i) := by
    intro _ nm i Hi
    rcases Hin01 i Hi with rfl | rfl
    · exact uRun cpu0 (gtAdGd GT) hA tA tsA wA HrA
    · exact uRun cpu0 (gtAdGd GT) hB tB tsB wB HrB
  have Hk0 : ∀ i, i ∈ [hA, hB] →
      ((fun _ => (⟨hp cpu0 uM0 zeroRegs, 0⟩ : Athread)) i).atK = 0 := fun _ _ => rfl
  have Hend : ∀ i, i ∈ [hA, hB] →
      ((fun _ => (⟨hp cpu0 hlt zeroRegs, 5⟩ : Athread)) i).atK =
        (AxOpsem.grow (gtAdGd GT) i).length := by
    intro i Hi
    rcases Hin01 i Hi with rfl | rfl
    · show 5 = (AxOpsem.grow (gtAdGd GT) hA).length
      rw [HrA]
      rfl
    · show 5 = (AxOpsem.grow (gtAdGd GT) hB).length
      rw [HrB]
      rfl
  have Hwp : ∀ [Hinv : InvGS_gen .hasNoLC AxSpinX7.xv6GF] [Hann : AxannotGS AxSpinX7.xv6GF]
      (nm : Xv6N),
      ⊢ ([∗list] i ∈ [hA, hB], xv6Init Lx (gtAdGd GT) nm i) -∗
        [∗list] i ∈ [hA, hB],
          @tierAWpd AxSpinX7.xv6GF .hasNoLC _ _ (xv6Pol GT) (gtAdGd GT) Xv6N Unit (protXv6 Lx)
            nm ((fun _ => (⟨hp cpu0 uM0 zeroRegs, 0⟩ : Athread)) i) .MaybeStuck i
            (Φab (gtAdGd GT).gdG wA wB Hinv Hann nm i) := by
    intro Hinv Hann nm
    iintro HI
    icases (AxTokLedgerMp.bigSepLPair hA hB
      (fun i => xv6Init (GF := AxSpinX7.xv6GF) Lx (gtAdGd GT) nm i)).1 $$ HI with ⟨HA, HB⟩
    iapply (AxTokLedgerMp.bigSepLPair hA hB _).2
    isplitl [HA]
    · unfold xv6Init
      icases HA with ⟨-, -, -, Hil, Hnh⟩
      iapply (wpdCsAb GT Hcons wA wB Hinv Hann nm hA tA tsA wA (.inl ⟨rfl, rfl⟩) HrA HnA)
        $$ Hil Hnh
    · unfold xv6Init
      icases HB with ⟨-, -, -, Hil, Hnh⟩
      iapply (wpdCsAb GT Hcons wA wB Hinv Hann nm hB tB tsB wB (.inr ⟨rfl, rfl⟩) HrB HnB)
        $$ Hil Hnh
  have Hjoint : ∀ [Hinv : InvGS_gen .hasNoLC AxSpinX7.xv6GF] [Hann : AxannotGS AxSpinX7.xv6GF]
      (nm : Xv6N),
      ⊢ ([∗list] i ∈ [hA, hB], Φab (gtAdGd GT).gdG wA wB Hinv Hann nm i
          ((fun _ => (⟨hp cpu0 hlt zeroRegs, 5⟩ : Athread)) i)) ==∗
        ⌜upost (gtAdGd GT).gdG hA wA ∧ upost (gtAdGd GT).gdG hB wB ∧ wA ≠ wB⌝ := by
    intro Hinv Hann nm
    have Hpair : ([∗list] i ∈ [hA, hB], Φab (gtAdGd GT).gdG wA wB Hinv Hann nm i
          ((fun _ => (⟨hp cpu0 hlt zeroRegs, 5⟩ : Athread)) i)) ⊢
        UPost nm (gtAdGd GT).gdG hA wA ∗ UPost nm (gtAdGd GT).gdG hB wB := by
      refine (AxTokLedgerMp.bigSepLPair hA hB _).1.trans ?_
      rw [AxSpinJ2.ΦabA, AxSpinJ2.ΦabB]
    iintro HI
    ihave HI := Hpair $$ HI
    icases HI with ⟨HA, HB⟩
    imodintro
    iapply (jointAB (gtAdGd GT).gdG wA wB nm) $$ HA HB
  exact @tierAAdequacyAnnGateJointT AxSpinX7.xv6GF _ _ (xv6Pol GT) GT Xv6N Unit (protXv6 Lx)
    (xv6Init Lx (gtAdGd GT)) (xv6AxpolWf GT) HconsT [hA, hB] Hnd Hharts'
    (fun _ => (⟨hp cpu0 uM0 zeroRegs, 0⟩ : Athread))
    (fun _ => (⟨hp cpu0 hlt zeroRegs, 5⟩ : Athread)) (fun _ => 6) Hrun Hk0 Hend
    (Φab (gtAdGd GT).gdG wA wB) Hwp _ Hjoint
    (xv6HobAlloc (GF := AxSpinX7.xv6GF) Lx (gtAdGd GT) n0 LxOk Himgc Hn0 Himgn)
    (xv6Hok GT HconsT Hcl)

/-- Lean-only (Rocq `u_alloc_open`'s `set s0`). -/
def AxSpinJ2.oS0 (sC0 : Athread) (i : Agent) : Athread :=
  if i = hC then sC0 else ⟨hp cpu0 uM0 zeroRegs, 0⟩
/-- Lean-only (Rocq `u_alloc_open`'s `set sN`). -/
def AxSpinJ2.oSN (sCN : Athread) (i : Agent) : Athread :=
  if i = hC then sCN else ⟨hp cpu0 hlt zeroRegs, 5⟩
/-- Lean-only (Rocq `u_alloc_open`'s `set nf`). -/
def AxSpinJ2.oN (nC : Nat) (i : Agent) : Nat := if i = hC then nC else 6

/-- THEOREM 2's SHAPE: OPEN THIRD HART C (arbitrary verified program).  Ownership is
load-bearing: drop `HwpC` and the conclusion is false (certificate (b)). -/
theorem uAllocOpen (GT : GdexecT)
    (HconsT : rvwmoCatConsistentT GT) (Hcl : ctrlClosed GT)
    (Hharts : ∀ e, e ∈ GT.gtG.gxGmo → e.1 = hA ∨ e.1 = hB ∨ e.1 = hC)
    (Himgc : ∀ a, a ∈ clb Lx → GT.gtG.gxImg a = some b0)
    (n0 : Int) (Hn0 : 0 ≤ n0 ∧ n0 < 2 ^ 32)
    (Himgn : ∀ (j : Nat) a v, (npb Lx)[j]? = some a →
      (WeakInterpProj.wbytes 4 (BitVec.ofInt 32 n0))[j]? = some v → GT.gtG.gxImg a = some v)
    (tA : Nat) (tsA : List Nat) (wA : BitVec 32) (tB : Nat) (tsB : List Nat) (wB : BitVec 32)
    (HrA : AxOpsem.grow (gtAdGd GT) hA = uRow tA tsA wA)
    (HrB : AxOpsem.grow (gtAdGd GT) hB = uRow tB tsB wB)
    (HnA : wA.toNat + 1 < 2 ^ 32) (HnB : wB.toNat + 1 < 2 ^ 32)
    (sC0 sCN : Athread) (nC : Nat)
    (HrunC : ∀ (_ : AxannotGS AxSpinX7.xv6GF) (nm : Xv6N),
      nsteps (tierAAstep (gtAdGd GT) nm hC) nC sC0 sCN)
    (HkC : sC0.atK = 0) (HendC : sCN.atK = (AxOpsem.grow (gtAdGd GT) hC).length)
    (HwpC : ∀ [InvGS_gen .hasNoLC AxSpinX7.xv6GF] [AxannotGS AxSpinX7.xv6GF] (nm : Xv6N),
      ⊢ xv6Init AxSpinJ2.L3 (gtAdGd GT) nm hC -∗
        @tierAWpd AxSpinX7.xv6GF .hasNoLC _ _ (xv6Pol GT) (gtAdGd GT) Xv6N Unit (protXv6 Lx) nm
          sC0 .MaybeStuck hC (fun _ => iprop(True))) :
    upost GT.gtG hA wA ∧ upost GT.gtG hB wB ∧ wA ≠ wB := by
  have Hin3 : ∀ i : Agent, i ∈ [hA, hB, hC] → i = hA ∨ i = hB ∨ i = hC := by
    intro i Hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at Hi
    exact Hi
  have Hnd : [hA, hB, hC].Nodup := by decide
  have Hharts' : ∀ e, e ∈ GT.gtG.gxGmo → e.1 ∈ [hA, hB, hC] := by
    intro e He
    rcases Hharts e He with H | H | H <;> rw [H] <;> simp
  have Hcons := catTAd GT HconsT
  have Hrun : ∀ (_ : AxannotGS AxSpinX7.xv6GF) (nm : Xv6N) i, i ∈ [hA, hB, hC] →
      nsteps (tierAAstep (gtAdGd GT) nm i) (AxSpinJ2.oN nC i) (AxSpinJ2.oS0 sC0 i)
        (AxSpinJ2.oSN sCN i) := by
    intro Hann nm i Hi
    rcases Hin3 i Hi with rfl | rfl | rfl
    · exact uRun cpu0 (gtAdGd GT) hA tA tsA wA HrA
    · exact uRun cpu0 (gtAdGd GT) hB tB tsB wB HrB
    · exact HrunC Hann nm
  have Hk0 : ∀ i, i ∈ [hA, hB, hC] → (AxSpinJ2.oS0 sC0 i).atK = 0 := by
    intro i Hi
    rcases Hin3 i Hi with rfl | rfl | rfl
    · rfl
    · rfl
    · exact HkC
  have Hend : ∀ i, i ∈ [hA, hB, hC] →
      (AxSpinJ2.oSN sCN i).atK = (AxOpsem.grow (gtAdGd GT) i).length := by
    intro i Hi
    rcases Hin3 i Hi with rfl | rfl | rfl
    · show 5 = (AxOpsem.grow (gtAdGd GT) hA).length
      rw [HrA]
      rfl
    · show 5 = (AxOpsem.grow (gtAdGd GT) hB).length
      rw [HrB]
      rfl
    · exact HendC
  have Hwp : ∀ [Hinv : InvGS_gen .hasNoLC AxSpinX7.xv6GF] [Hann : AxannotGS AxSpinX7.xv6GF]
      (nm : Xv6N),
      ⊢ ([∗list] i ∈ [hA, hB, hC], xv6Init AxSpinJ2.L3 (gtAdGd GT) nm i) -∗
        [∗list] i ∈ [hA, hB, hC],
          @tierAWpd AxSpinX7.xv6GF .hasNoLC _ _ (xv6Pol GT) (gtAdGd GT) Xv6N Unit (protXv6 Lx)
            nm (AxSpinJ2.oS0 sC0 i) .MaybeStuck i (Φab (gtAdGd GT).gdG wA wB Hinv Hann nm i) := by
    intro Hinv Hann nm
    iintro HI
    icases (AxSpinJ2.bigSepLTriple hA hB hC
      (fun i => xv6Init (GF := AxSpinX7.xv6GF) AxSpinJ2.L3 (gtAdGd GT) nm i)).1 $$ HI
      with ⟨HA, HB, HC⟩
    iapply (AxSpinJ2.bigSepLTriple hA hB hC _).2
    rw [show AxSpinJ2.oS0 sC0 hA = ⟨hp cpu0 uM0 zeroRegs, 0⟩ from if_neg (by decide),
      show AxSpinJ2.oS0 sC0 hB = ⟨hp cpu0 uM0 zeroRegs, 0⟩ from if_neg (by decide),
      show AxSpinJ2.oS0 sC0 hC = sC0 from if_pos rfl]
    isplitl [HA]
    · ihave HA := AxSpinJ2.initL3Cs (gtAdGd GT) nm hA $$ HA
      icases HA with ⟨Hil, Hnh⟩
      iapply (wpdCsAb GT Hcons wA wB Hinv Hann nm hA tA tsA wA (.inl ⟨rfl, rfl⟩) HrA HnA)
        $$ Hil Hnh
    isplitl [HB]
    · ihave HB := AxSpinJ2.initL3Cs (gtAdGd GT) nm hB $$ HB
      icases HB with ⟨Hil, Hnh⟩
      iapply (wpdCsAb GT Hcons wA wB Hinv Hann nm hB tB tsB wB (.inr ⟨rfl, rfl⟩) HrB HnB)
        $$ Hil Hnh
    · iapply (AxSpinWit.tierAWpdMono (hlc := .hasNoLC) (pol := xv6Pol GT) (gtAdGd GT) Xv6N Unit
        (protXv6 Lx) nm sC0 .MaybeStuck hC (fun _ => iprop(True))
        (Φab (gtAdGd GT).gdG wA wB Hinv Hann nm hC)
        (fun s => by rw [AxSpinJ2.ΦabC]))
      iapply HwpC nm $$ HC
  have Hjoint : ∀ [Hinv : InvGS_gen .hasNoLC AxSpinX7.xv6GF] [Hann : AxannotGS AxSpinX7.xv6GF]
      (nm : Xv6N),
      ⊢ ([∗list] i ∈ [hA, hB, hC], Φab (gtAdGd GT).gdG wA wB Hinv Hann nm i
          (AxSpinJ2.oSN sCN i)) ==∗
        ⌜upost (gtAdGd GT).gdG hA wA ∧ upost (gtAdGd GT).gdG hB wB ∧ wA ≠ wB⌝ := by
    intro Hinv Hann nm
    have Htri : ([∗list] i ∈ [hA, hB, hC], Φab (gtAdGd GT).gdG wA wB Hinv Hann nm i
          (AxSpinJ2.oSN sCN i)) ⊢
        UPost nm (gtAdGd GT).gdG hA wA ∗ (UPost nm (gtAdGd GT).gdG hB wB ∗ iprop(True)) := by
      refine (AxSpinJ2.bigSepLTriple hA hB hC _).1.trans ?_
      rw [AxSpinJ2.ΦabA, AxSpinJ2.ΦabB, AxSpinJ2.ΦabC]
    iintro HI
    ihave HI := Htri $$ HI
    icases HI with ⟨HA, HB, -⟩
    imodintro
    iapply (jointAB (gtAdGd GT).gdG wA wB nm) $$ HA HB
  exact @tierAAdequacyAnnGateJointT AxSpinX7.xv6GF _ _ (xv6Pol GT) GT Xv6N Unit (protXv6 Lx)
    (xv6Init AxSpinJ2.L3 (gtAdGd GT)) (xv6AxpolWf GT) HconsT [hA, hB, hC] Hnd Hharts'
    (AxSpinJ2.oS0 sC0) (AxSpinJ2.oSN sCN) (AxSpinJ2.oN nC) Hrun Hk0 Hend
    (Φab (gtAdGd GT).gdG wA wB) Hwp _ Hjoint
    (xv6HobAlloc3 (GF := AxSpinX7.xv6GF) (gtAdGd GT) n0 Himgc Hn0 Himgn)
    (xv6Hok GT HconsT Hcl)

/-! # 4. CERTIFICATES -/

theorem hartsOfGmo3 (GT : GdexecT) :
    (∀ e, e ∈ GT.gtG.gxGmo → e.1 = hA ∨ e.1 = hB ∨ e.1 = hC) →
    ∀ e, e ∈ GT.gtG.gxGmo → e.1 = hA ∨ e.1 = hB ∨ e.1 = hC :=
  fun H e He => H e He

/-- C's CS WPd from the `L3` init. -/
theorem uWpdOn3 (GT : GdexecT) (HconsT : rvwmoCatConsistentT GT) (i : Agent) (t : Nat)
    (ts : List Nat) (w8 : BitVec 32) (Hrow : AxOpsem.grow (gtAdGd GT) i = uRow t ts w8)
    (Hn : w8.toNat + 1 < 2 ^ 32) :
    ∀ [InvGS_gen .hasNoLC AxSpinX7.xv6GF] [AxannotGS AxSpinX7.xv6GF] (nm : Xv6N),
      ⊢ xv6Init AxSpinJ2.L3 (gtAdGd GT) nm i -∗
        @tierAWpd AxSpinX7.xv6GF .hasNoLC _ _ (xv6Pol GT) (gtAdGd GT) Xv6N Unit (protXv6 Lx) nm
          ⟨hp cpu0 uM0 zeroRegs, 0⟩ .MaybeStuck i (fun _ => iprop(True)) := by
  intro _ _ nm
  iintro HI
  ihave HI := AxSpinJ2.initL3Cs (gtAdGd GT) nm i $$ HI
  icases HI with ⟨Hil, Hnh⟩
  iapply (AxSpinWit.tierAWpdMono (hlc := .hasNoLC) (pol := xv6Pol GT) (gtAdGd GT) Xv6N Unit
    (protXv6 Lx) nm ⟨hp cpu0 uM0 zeroRegs, 0⟩ .MaybeStuck i
    (fun _ => UPost nm (gtAdGd GT).gdG i w8) (fun _ => iprop(True))
    (fun _ => true_intro))
  iapply (wpdCs (hlc := .hasNoLC) (GF := AxSpinX7.xv6GF) GT nm cpu0 (catTAd GT HconsT) i t ts
    w8 Hrow Hn) $$ Hil Hnh

/-! (a′) A, then B, then C: each claims the previous release and reads the previous increment
(nextpid 0 → 1 → 2 → 3). -/

def two32 : BitVec 32 := BitVec.ofInt 32 2
theorem nowrapTwo : two32.toNat + 1 < 2 ^ 32 := by decide +kernel

def ua3RowC : List Lbl := uRow 6 [5, 5, 5, 5] two32
def ua3 : GdexecT :=
  mkgt [uaRowA, uaRowB, ua3RowC]
    [(hA, 0), (hA, 1), (hA, 2), (hA, 4),
     (hB, 0), (hB, 1), (hB, 2), (hB, 4),
     (hC, 0), (hC, 1), (hC, 2), (hC, 4)]
    (uCtrl hA ++ (uCtrl hB ++ uCtrl hC))

theorem ua3CatT : rvwmoCatConsistentT ua3 :=
  catTConsistentBSound _ (by decide +kernel)
theorem ua3CtrlClosed : ctrlClosed ua3 :=
  ctrlClosedBSound _ ua3CatT.1 (by decide +kernel)
theorem ua3Harts : ∀ e, e ∈ ua3.gtG.gxGmo → e.1 = hA ∨ e.1 = hB ∨ e.1 = hC := by
  apply hartsOfGmo3
  intro e He
  have h : ua3.gtG.gxGmo.all (fun e : Geid => decide (e.1 = hA ∨ e.1 = hB ∨ e.1 = hC)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.1 h e He)

theorem ua3Shape :
    grfAt ua3.gtG (paZ lkpa) (hA, 4) (hB, 0) ∧ grfAt ua3.gtG (paZ nppa) (hA, 2) (hB, 1) ∧
    grfAt ua3.gtG (paZ lkpa) (hB, 4) (hC, 0) ∧ grfAt ua3.gtG (paZ nppa) (hB, 2) (hC, 1) :=
  ⟨(grfAtBSpec _ _ _ _).1 (by decide +kernel), (grfAtBSpec _ _ _ _).1 (by decide +kernel),
    (grfAtBSpec _ _ _ _).1 (by decide +kernel), (grfAtBSpec _ _ _ _).1 (by decide +kernel)⟩

/-- Every premise of `uAllocOpen` on `ua3`, with C := the CS program. -/
theorem ua3Premises :
    rvwmoCatConsistentT ua3 ∧ ctrlClosed ua3 ∧
    (∀ e, e ∈ ua3.gtG.gxGmo → e.1 = hA ∨ e.1 = hB ∨ e.1 = hC) ∧
    (∀ a, a ∈ clb Lx → ua3.gtG.gxImg a = some b0) ∧
    (∀ (j : Nat) a v, (npb Lx)[j]? = some a →
      (WeakInterpProj.wbytes 4 (BitVec.ofInt 32 0))[j]? = some v → ua3.gtG.gxImg a = some v) ∧
    AxOpsem.grow (gtAdGd ua3) hA = uaRowA ∧ AxOpsem.grow (gtAdGd ua3) hB = uaRowB ∧
    AxOpsem.grow (gtAdGd ua3) hC = ua3RowC ∧
    zero32.toNat + 1 < 2 ^ 32 ∧ one32.toNat + 1 < 2 ^ 32 ∧
    (∀ (_ : AxannotGS AxSpinX7.xv6GF) (nm : Xv6N),
      nsteps (tierAAstep (gtAdGd ua3) nm hC) 6
        ⟨hp cpu0 uM0 zeroRegs, 0⟩ ⟨hp cpu0 hlt zeroRegs, 5⟩) ∧
    (AxOpsem.grow (gtAdGd ua3) hC).length = 5 ∧
    (∀ [InvGS_gen .hasNoLC AxSpinX7.xv6GF] [AxannotGS AxSpinX7.xv6GF] (nm : Xv6N),
      ⊢ xv6Init AxSpinJ2.L3 (gtAdGd ua3) nm hC -∗
        @tierAWpd AxSpinX7.xv6GF .hasNoLC _ _ (xv6Pol ua3) (gtAdGd ua3) Xv6N Unit (protXv6 Lx)
          nm ⟨hp cpu0 uM0 zeroRegs, 0⟩ .MaybeStuck hC (fun _ => iprop(True))) :=
  ⟨ua3CatT, ua3CtrlClosed, ua3Harts, imgtClb ua3 rfl, imgtNp ua3 rfl, rfl, rfl, rfl, nowrapZero,
    nowrapOne, uRunOn ua3 hC 6 [5, 5, 5, 5] two32 rfl, rfl,
    uWpdOn3 ua3 ua3CatT hC 6 [5, 5, 5, 5] two32 rfl nowrapTwo⟩

/-- The open capstone fires on `ua3` (C verified, non-trivial); TRUE there. -/
theorem ua3Sound : upost ua3.gtG hA zero32 ∧ upost ua3.gtG hB one32 ∧ zero32 ≠ one32 :=
  uAllocOpen ua3 ua3CatT ua3CtrlClosed ua3Harts (imgtClb ua3 rfl) 0 ⟨by decide, by decide⟩
    (imgtNp ua3 rfl) 0 [0, 0, 0, 0] zero32 3 [2, 2, 2, 2] one32 rfl rfl nowrapZero nowrapOne
    _ _ 6 (uRunOn ua3 hC 6 [5, 5, 5, 5] two32 rfl) rfl rfl
    (uWpdOn3 ua3 ua3CatT hC 6 [5, 5, 5, 5] two32 rfl nowrapTwo)

/-- The 2-hart joint capstone on AxSpinU4's `ua`. -/
theorem uaJointSound : upost ua.gtG hA zero32 ∧ upost ua.gtG hB one32 ∧ zero32 ≠ one32 :=
  uAlloc2Joint ua uaCatT uaCtrlClosed uaHarts (imgtClb ua rfl) 0 ⟨by decide, by decide⟩
    (imgtNp ua rfl) 0 [0, 0, 0, 0] zero32 3 [2, 2, 2, 2] one32 rfl rfl nowrapZero nowrapOne

/-! (b) THE RACE: C stores nextpid := 0 WITHOUT the lock. -/

abbrev rzM0 : SailM Unit := stv 4 nppa zero32 hlt
def rzRow : List Lbl :=
  [.LStore false (paZ nppa) (WeakInterpProj.wbytes 4 zero32) .WCplain]
/-- A: claims genesis (t=0), reads image nextpid 0, writes 1 (w2), releases (w3).  C: writes 0
(w4).  B: claims A's release (w3), reads C's 0 (w4). -/
def ur3RowB : List Lbl := uRow 3 [4, 4, 4, 4] zero32
def ur3 : GdexecT :=
  mkgt [uaRowA, ur3RowB, rzRow]
    [(hA, 0), (hA, 1), (hA, 2), (hA, 4), (hC, 0),
     (hB, 0), (hB, 1), (hB, 2), (hB, 4)]
    (uCtrl hA ++ uCtrl hB)

theorem ur3CatT : rvwmoCatConsistentT ur3 :=
  catTConsistentBSound _ (by decide +kernel)
theorem ur3CtrlClosed : ctrlClosed ur3 :=
  ctrlClosedBSound _ ur3CatT.1 (by decide +kernel)
theorem ur3Harts : ∀ e, e ∈ ur3.gtG.gxGmo → e.1 = hA ∨ e.1 = hB ∨ e.1 = hC := by
  apply hartsOfGmo3
  intro e He
  have h : ur3.gtG.gxGmo.all (fun e : Geid => decide (e.1 = hA ∨ e.1 = hB ∨ e.1 = hC)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.1 h e He)

/-- B claims A's release; C's unlocked store lands gmo-between A's store and B's lw, and B's lw
reads it. -/
theorem ur3Shape :
    grfAt ur3.gtG (paZ lkpa) (hA, 4) (hB, 0) ∧
    gmoLt ur3.gtG (hA, 2) (hC, 0) ∧ gmoLt ur3.gtG (hC, 0) (hB, 1) ∧
    grfAt ur3.gtG (paZ nppa) (hC, 0) (hB, 1) :=
  ⟨(grfAtBSpec _ _ _ _).1 (by decide +kernel), (gmoLtBSpec _ _ _).1 (by decide +kernel),
    (gmoLtBSpec _ _ _).1 (by decide +kernel), (grfAtBSpec _ _ _ _).1 (by decide +kernel)⟩

theorem rzRun (cpu : CPU) (GD : Gdexec) (Hrow : AxOpsem.grow GD hC = rzRow) :
    nsteps (astepAnyNfGv GD hC) 1 ⟨hp cpu rzM0 zeroRegs, 0⟩ ⟨hp cpu hlt zeroRegs, 1⟩ := by
  refine nsteps_l (nrunWrite cpu GD hC 4 (by decide) nppa nppaRam zero32 hlt zeroRegs 0
    .WCplain (by rw [Hrow]; rfl)) ?_
  exact nsteps_O _

theorem rzRunUr3 : ∀ (_ : AxannotGS AxSpinX7.xv6GF) (nm : Xv6N),
    nsteps (tierAAstep (gtAdGd ur3) nm hC) 1
      ⟨hp cpu0 rzM0 zeroRegs, 0⟩ ⟨hp cpu0 hlt zeroRegs, 1⟩ :=
  fun _ _ => rzRun cpu0 (gtAdGd ur3) rfl

/-- Every premise of `uAllocOpen` on `ur3` EXCEPT `HwpC`; there `wA = wB`. -/
theorem ur3Premises :
    rvwmoCatConsistentT ur3 ∧ ctrlClosed ur3 ∧
    (∀ e, e ∈ ur3.gtG.gxGmo → e.1 = hA ∨ e.1 = hB ∨ e.1 = hC) ∧
    (∀ a, a ∈ clb Lx → ur3.gtG.gxImg a = some b0) ∧
    (∀ (j : Nat) a v, (npb Lx)[j]? = some a →
      (WeakInterpProj.wbytes 4 (BitVec.ofInt 32 0))[j]? = some v → ur3.gtG.gxImg a = some v) ∧
    AxOpsem.grow (gtAdGd ur3) hA = uaRowA ∧ AxOpsem.grow (gtAdGd ur3) hB = ur3RowB ∧
    zero32.toNat + 1 < 2 ^ 32 ∧
    (∀ (_ : AxannotGS AxSpinX7.xv6GF) (nm : Xv6N),
      nsteps (tierAAstep (gtAdGd ur3) nm hC) 1
        ⟨hp cpu0 rzM0 zeroRegs, 0⟩ ⟨hp cpu0 hlt zeroRegs, 1⟩) ∧
    (AxOpsem.grow (gtAdGd ur3) hC).length = 1 ∧
    ¬ (zero32 ≠ zero32) :=
  ⟨ur3CatT, ur3CtrlClosed, ur3Harts, imgtClb ur3 rfl, imgtNp ur3 rfl, rfl, rfl, nowrapZero,
    rzRunUr3, rfl, fun H => H rfl⟩

theorem ur3WpdUnprovable :
    ¬ (∀ [InvGS_gen .hasNoLC AxSpinX7.xv6GF] [AxannotGS AxSpinX7.xv6GF] (nm : Xv6N),
        ⊢ xv6Init AxSpinJ2.L3 (gtAdGd ur3) nm hC -∗
          @tierAWpd AxSpinX7.xv6GF .hasNoLC _ _ (xv6Pol ur3) (gtAdGd ur3) Xv6N Unit (protXv6 Lx)
            nm ⟨hp cpu0 rzM0 zeroRegs, 0⟩ .MaybeStuck hC (fun _ => iprop(True))) := by
  intro Hwp
  obtain ⟨-, -, Hne⟩ := uAllocOpen ur3 ur3CatT ur3CtrlClosed ur3Harts (imgtClb ur3 rfl) 0
    ⟨by decide, by decide⟩ (imgtNp ur3 rfl) 0 [0, 0, 0, 0] zero32 3 [4, 4, 4, 4] zero32 rfl rfl
    nowrapZero nowrapZero _ _ 1 rzRunUr3 rfl rfl Hwp
  exact Hne rfl

/-! (c′) THE SANITY TWIN at the trivial protocol -/

section wpdRZ
variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF] [AxannotGS GF]

theorem wpdRZTriv (GT : GdexecT) (cpu : CPU) (Hrow : AxOpsem.grow (gtAdGd GT) hC = rzRow) :
    ⊢ @tierAWpd GF hlc _ _ (xv6Pol GT) (gtAdGd GT) Unit Unit trivOb ()
      ⟨hp cpu rzM0 zeroRegs, 0⟩ .MaybeStuck hC (fun _ => iprop(True)) := by
  have Hne : 0 ≠ (AxOpsem.grow (gtAdGd GT) hC).length := by rw [Hrow]; simp [rzRow]
  have Hl0 : gxLbl (gtAdGd GT).gdG (hC, 0) =
      some (.LStore false (paZ nppa) (WeakInterpProj.wbytes 4 zero32) .WCplain) := by
    rw [gxLblGrow, Hrow]; rfl
  have H := nshWrite (hlc := hlc) (GF := GF) (pol := xv6Pol GT) (gtAdGd GT) Unit Unit trivOb ()
    cpu hC (fun _ => iprop(True)) 4 nppa nppaRam zero32 hlt 0 Hne iprop(True)
    (fun rs => by
      have Hval : graphData (gtAdGd GT) (hC, 0) = some (WeakInterpProj.wbytes 4 zero32) := by
        unfold graphData; rw [Hl0]; rfl
      iintro _
      iapply (evPlain (hlc := hlc) (pol := xv6Pol GT) (gtAdGd GT) Unit Unit trivOb () hC 0
        iprop(True) iprop(True) _ _ Hval) $$ []
      · iapply feTrivu
      iintro _ _
      iapply (shHltTrue (hlc := hlc) (pol := xv6Pol GT) (gtAdGd GT) Unit Unit trivOb () cpu hC
        (0 + 1)) $$ %rs)
  iapply H $$ [] %zeroRegs
  itrivial

end wpdRZ

theorem ur3WpdTrivial :
    ∀ [InvGS_gen .hasNoLC AxSpinX7.xv6GF] [AxannotGS AxSpinX7.xv6GF] (nm : Unit),
      ⊢ (iprop(emp) : IProp AxSpinX7.xv6GF) -∗
        @tierAWpd AxSpinX7.xv6GF .hasNoLC _ _ (xv6Pol ur3) (gtAdGd ur3) Unit Unit trivOb nm
          ⟨hp cpu0 rzM0 zeroRegs, 0⟩ .MaybeStuck hC (fun _ => iprop(True)) := by
  intro _ _ nm
  cases nm
  iintro _
  iapply (wpdRZTriv (hlc := .hasNoLC) (GF := AxSpinX7.xv6GF) ur3 cpu0 rfl)

end Weak
