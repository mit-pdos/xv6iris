/-
Weak: **Phase 1c, part 7 of the spinlock plan -- THE CAPSTONE at the joint instance `protXv6 Lx`
and its CERTIFICATES.**

Rocq: `iris/AxSpinX7.v` @ xxvzwolszwmp.

## The Rocq header, in substance

`xv6Handoff`: for ANY hart A with a WPd at `protXv6 Lx` from `xv6Init` (= kernelText ∗ cpuOwn ∗
stackOwn ∗ isLock pid_lock RPid ∗ notheld A) and any run, on every tagged-consistent ctrl-closed
2-hart graph whose genesis image has lk->cpu = 0 and nextpid = n0, whose lk->cpu writes are
aligned 8-byte `sd`s (`clAligned`, a graph/code premise) and where B's row is `AxSpinX4.bRow`
(+ `HnowrapB` for B's nextpid read):
    v1  = Xv                 B's stack reload            (PRIVATE class)
  ∧ v3  = one32              B's noff read               (PRIVATE class)
  ∧ v4  = image              B's text/PT read            (READ-ONLY class)
  ∧ v5  ≠ cpB                B's non-holder lk->cpu read (Φ_cpu at 8 bytes, REAL cpuAddr)
  ∧ v10 = cpB                B's HOLDER lk->cpu read     ((b), D4 release arm)
Proof: `tierAAdequacyAnnGateT` + `AxSpinX5.wpdB` + `xv6Hok` + `xv6HobAlloc`; `QBFinal` turns
the five facts deposited at B's reads into the conclusion.

CERTIFICATES
  (a) `AxSpinX7.spaPremises` -- EVERY premise on the concrete graph `AxSpinX8.spa` (A PROVED at
      the real protocol: `AxSpinX6.wpdA`); `AxSpinX7.spaSound`: the capstone fires there.
      `spa` is NOT SC (B's stack reload and B's holder lk->cpu read are gmo-BEFORE the stores
      they read: forwarded); `AxSpinX7.spaShape` records it plus the handoff reads.  `spaSc`
      (`spaScShape`, `spaScSound`) is the SC twin.
  (b) `AxSpinX7.sprWpdUnprovable` -- THE lk->cpu RACE: A' writes its own `cpA` to lk->cpu without
      the lock; on the consistent, ctrl-closed `AxSpinX8.spr` B's holder read returns it, so A''s
      WPd at `protXv6 Lx` is UNPROVABLE.
  (c) `AxSpinX7.sprWpdTrivial` -- the same A' IS verifiable at the trivial protocol.

## Deviations from Rocq

1. VOCABULARY (as `AxSpinX5` deviation 1): `Z` ↦ `Int`, `bv n` ↦ `BitVec n`, `gd_g GD` ↦
   `GD.gdG`, `gx_img (gt_g GT)` ↦ `GT.gtG.gxImg`, `l !! j` ↦ `l[j]?` (indices typed `Nat`),
   `pa_z` ↦ `paZ`, `Z_to_bv 32` ↦ `BitVec.ofInt 32`, `bv_unsigned v` ↦ `v.toNat` (so the nowrap
   premises are over `Nat`), `a ≤ b < c` ↦ `a ≤ b ∧ b < c`, `B0` ↦ `b0`, `init_regstate` ↦
   `zeroRegs`, `AThread p k` ↦ `⟨p, k⟩`, `Forall P l` ↦ `∀ e, e ∈ l → P e` (so `hartsOfGmo` is
   the identity), `cpus_ptr_inj` ↦ `cpuAddr_inj`.  The notation `OBX` is `protXv6 Lx` inline.
2. `issΣ`/`subG_issΣ`/`xv6Σ`/`xv6G_xv6Σ` ↦ `AxSpinX7.xv6GF`, an explicit slot table: the
   `AxSpinProt4.spinGF` slots 0–10 (inv/credits 0–3, `AxlogRF Hent` 4, annotation cameras 5–7,
   `SpinlockG` cameras 8–10) plus `MonoNatRF` at 11 (Rocq `mono_natΣ`) and the issued set
   `constOF (Auth (DisjointLeibnizSet (GSet Int)))` at 12 (Rocq `issΣ`; its `ElemG` instance is
   `subG_issΣ`), with Lean-only instances `AxSpinX7.xv6GF*`; `xv6G_xv6Σ` ↦
   `AxSpinX7.xv6GFXv6G`.  iris-lean's `MonoNatG` carries a `name` field (unused by
   `MonoNat.own_alloc`, which allocates a fresh name); it is set to `0`.  The adequacy allocates
   the `Xv6G` ghost state through `xv6HobAlloc` (as Rocq).
3. CONTEXTS (as `AxSpinProt4` deviation 2): section `post`'s variables are explicit leading
   arguments of `QBFinal` (Rocq order); the capstone's `set` locals are the Lean-only defs
   `AxSpinX7.cS0`/`cSN`/`cN`/`cPost`; `HwpA` and the certificate statements take
   `[InvGS_gen .hasNoLC xv6GF] [AxannotGS xv6GF]` instance binders; the policy `xv6Pol GT` is
   passed explicitly.  O2 STAGE C: Rocq's `Tf` argument of `tierA_astep`/`tierA_wpd` is gone
   (the Rocq rows contain no fetch events, `AxSpinX8` deviation 3).
4. PROOFS: `vm_compute`/`vmr` ↦ `decide +kernel`; the `zv` Ltac is inlined as
   `simp only [lkZV, …]`; `spa_harts`-style `repeat constructor` ↦ a decided `List.all`.

**Rocq → Lean name map.**  `xv6Σ` `AxSpinX7.xv6GF`, `xv6G_xv6Σ` `AxSpinX7.xv6GFXv6G`,
`issΣ` slot 12 of `AxSpinX7.xv6GF`, `subG_issΣ` `AxSpinX7.xv6GFIss`, `cvx_inj_B` `cvxInjB`,
`cpA_ne_cpB` `cpANeCpB`, `QB_final` `QBFinal`, `xv6_handoff` `xv6Handoff`, `harts_of_gmo`
`hartsOfGmo`, `spa_harts` `AxSpinX7.spaHarts` (dup), `spa_sc_harts` `spaScHarts`, `spr_harts`
`AxSpinX7.sprHarts` (dup), `imgt_clb` `imgtClb`, `imgt_np` `imgtNp`, `al_of_rows` `alOfRows`,
`gx_lbl_hart` `gxLblHart`, `spa_al` `spaAl`, `spa_sc_al` `spaScAl`, `spr_al` `sprAl`,
`nowrap_one` `nowrapOne`, `nowrap_zero` `nowrapZero`, `a_wpd_on` `aWpdOn`, `a_run_on` `aRunOn`,
`spa_shape` `AxSpinX7.spaShape` (dup), `spa_premises` `AxSpinX7.spaPremises` (dup), `spa_sound`
`AxSpinX7.spaSound` (dup), `spa_sc_shape` `spaScShape`, `spa_sc_sound` `spaScSound`,
`r_run_spr` `rRunSpr`, `spr_shape` `sprShape`, `spr_wpd_unprovable`
`AxSpinX7.sprWpdUnprovable` (dup), `spr_wpd_trivial` `AxSpinX7.sprWpdTrivial` (dup).
Lean-only (file-qualified): the `AxSpinX7.xv6GF*` instances, `AxSpinX7.cS0`/`cSN`/`cN`/`cPost`.

**Dropped:** the §5 `Check`/`Print Assumptions` lines (the lint's axiom check covers them).
`issΣ` is not a separate declaration (deviation 2).  Rocq 32 decls (`issΣ`, `subG_issΣ`,
`xv6Σ`, `xv6G_xv6Σ` + 28 lemmas/theorems); Lean 44 = 31 ported (`xv6GF`, 2 instances, 28
theorems) + 13 Lean-only (9 slot instances, `cS0`/`cSN`/`cN`/`cPost`).
-/
import Weak.AxSpinX6
import Weak.AxSpinX8
import Weak.AxSpinGate

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D
open Dtag

/-! # 1. The ghost-functor table -/

section xv6GFSec

open Iris.Algebra

/-- Rocq `xv6Σ := #[invΣ; axlogΣ hent; axannotΣ; spinlockΣ; mono_natΣ; issΣ]`. -/
def AxSpinX7.xv6GF : BundledGFunctors :=
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
  |>.set 11 ⟨MonoNatRF, inferInstance⟩
  |>.set 12 ⟨constOF (Auth (DisjointLeibnizSet (GSet Int))), inferInstance⟩

instance AxSpinX7.xv6GFInvMap : ElemG AxSpinX7.xv6GF InvMapF := ⟨0, rfl⟩
instance AxSpinX7.xv6GFEnabled : ElemG AxSpinX7.xv6GF (constOF CoPsetDisjL) := ⟨1, rfl⟩
instance AxSpinX7.xv6GFDisabled :
    ElemG AxSpinX7.xv6GF (constOF (DisjointLeibnizSet PosSet)) := ⟨2, rfl⟩
instance AxSpinX7.xv6GFCredit : ElemG AxSpinX7.xv6GF (Auth.AuthURF (constOF Credit)) := ⟨3, rfl⟩
instance AxSpinX7.xv6GFInvGpreS : InvGpreS AxSpinX7.xv6GF :=
  ⟨⟨inferInstance, inferInstance, inferInstance⟩, ⟨inferInstance⟩⟩
instance AxSpinX7.xv6GFAxlogG : AxlogG AxSpinX7.xv6GF Hent := { axlogInG := ⟨4, rfl⟩ }
instance AxSpinX7.xv6GFAxannotG : AxannotG AxSpinX7.xv6GF :=
  { axannotSavedG := { elemG := ⟨5, rfl⟩ }, axannotMapG := ⟨⟨6, rfl⟩⟩, axannotSetG := ⟨7, rfl⟩ }
instance AxSpinX7.xv6GFSpinlockG : SpinlockG AxSpinX7.xv6GF :=
  { spinSavedPredG := { elemG := ⟨8, rfl⟩ }, spinHoldG := ⟨⟨9, rfl⟩⟩,
    spinRegG := ⟨⟨10, rfl⟩⟩ }
instance AxSpinX7.xv6GFMonoNat : MonoNatG AxSpinX7.xv6GF := { elem := ⟨11, rfl⟩, name := 0 }
/-- Rocq `subG_issΣ`. -/
instance AxSpinX7.xv6GFIss :
    ElemG AxSpinX7.xv6GF (constOF (Auth (DisjointLeibnizSet (GSet Int)))) := ⟨12, rfl⟩
/-- Rocq `xv6G_xv6Σ`. -/
instance AxSpinX7.xv6GFXv6G : AxSpinX.Xv6G AxSpinX7.xv6GF := { xv6IssG := AxSpinX7.xv6GFIss }

end xv6GFSec

/-! # 2. Pure consequences of B's post -/

theorem cvxInjB (k : Agent) : cvx k = cvx hB → k = hB := by
  intro H
  have h := congrArg Fin.val (cpuAddr_inj (wbytes8Inj _ _ H))
  rw [cpuOfNat hB (by decide)] at h
  by_cases hk : k < NCPU
  · rw [cpuOfNat k hk] at h
    exact h
  · unfold cpuOf at h
    rw [dif_neg hk] at h
    exact absurd h (by decide)

theorem cpANeCpB : cpA ≠ cpB := by
  intro H
  exact absurd (cpuAddr_inj H) (by decide)

section post

theorem QBFinal (GD : Gdexec) (Hcons : rvwmoCatConsistent GD) (t1 t3 t4 t5 : List Nat)
    (t6 : Nat) (t8 t10 : List Nat) (v1 v4 v5 v10 : BitVec 64) (v3 v8 : BitVec 32)
    (Hrow : AxOpsem.grow GD hB = AxSpinX4.bRow t1 t3 t4 t5 t6 t8 t10 v1 v4 v5 v10 v3 v8)
    (Himgc : ∀ a, a ∈ clb Lx → GD.gdG.gxImg a = some b0) (Hal : clAligned (clb Lx) GD.gdG) :
    QB GD.gdG →
    v1 = Xv ∧ v3 = one32 ∧
    (∀ (j : Nat) a, (clRange (paZ ropa) 8)[j]? = some a →
      GD.gdG.gxImg a = (WeakInterpProj.wbytes 8 v4)[j]?) ∧
    v5 ≠ cpB ∧ v10 = cpB := by
  intro HQ
  unfold QB at HQ
  obtain ⟨HF1, HF3, HF4, HF5, HF10⟩ := HQ
  obtain ⟨Hwf, Hppo, Hlv, -⟩ := Hcons
  have bL := AxSpinX5.bL GD t1 t3 t4 t5 t6 t8 t10 v1 v4 v5 v10 v3 v8 Hrow
  have Hl1 := bL 1 _ rfl
  have Hl3 := bL 3 _ rfl
  have Hl4 := bL 4 _ rfl
  have Hl5 := bL 5 _ rfl
  have Hl10 := bL 10 _ rfl
  have hcl : (clb Lx).length = 8 := by simp [clb, clRange]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact wbytes8Inj' _ _ (readFactWord GD.gdG Hwf (hB, 1) (paZ skpa) t1 8 v1 _ Hl1
      (wbytesLength 8 Xv) HF1)
  · exact wbytes4Inj _ _ (readFactWord GD.gdG Hwf (hB, 3) (paZ nfpa) t3 4 v3 _ Hl3
      (wbytesLength 4 one32) HF3)
  · intro j a Hj
    obtain ⟨rfl, Hjl⟩ := AxSpinX4.clRangeLookup _ _ _ _ Hj
    obtain ⟨t, Ht⟩ := loadnReads GD.gdG Hwf (hB, 4) (paZ ropa) t4 8 v4 j Hl4 Hjl
    have Ha : paZ ropa + (j : Int) ∈ clRange (paZ ropa) 8 := List.mem_of_getElem? Hj
    obtain ⟨-, H⟩ := HF4 _ _ _ Ha Ht
    rw [H, wbytesLookup (m := 8) 8 v4 j Hjl]
  · have Hppo1 : ∀ e1 e2, gppo1 GD.gdG e1 e2 → gmoLt GD.gdG e1 e2 :=
      fun e1 e2 H => Hppo e1 e2 (Or.inl (Or.inl H))
    have Hcvl : ∀ k, (cvx k).length = (clb Lx).length := fun k => by rw [cvxLength, hcl]
    have Hrd : ∀ (j : Nat) a, (clb Lx)[j]? = some a →
        ∃ t v, greadsByte GD.gdG (hB, 5) a t v ∧ (WeakInterpProj.wbytes 8 v5)[j]? = some v := by
      intro j a Hj
      rw [clbLcpa] at Hj
      obtain ⟨rfl, Hjl⟩ := AxSpinX4.clRangeLookup _ _ _ _ Hj
      obtain ⟨t, Ht⟩ := loadnReads GD.gdG Hwf (hB, 5) (paZ lcpa) t5 8 v5 j Hl5 Hjl
      exact ⟨t, _, Ht, wbytesLookup (m := 8) 8 v5 j Hjl⟩
    have Hnz : cvx (hB, 5).1 ≠ List.replicate (clb Lx).length b0 := by
      rw [hcl]
      exact cvxNz hB
    have Hinj : ∀ k, k ≠ (hB, 5).1 → cvx k ≠ cvx (hB, 5).1 :=
      fun k Hk Heq => Hk (cvxInjB k Heq)
    have Hns : ∀ w a v, a ∈ clb Lx → gwritesByte GD.gdG w a v →
        WeakRvwmoGraph.gpo GD.gdG w (hB, 5) → False := by
      intro w a v Ha Hw Hpo
      obtain ⟨wi, wk⟩ := w
      obtain ⟨Hh, Hk, -, -⟩ := Hpo
      dsimp only at Hh Hk
      subst Hh
      have Hc := AxSpinX5.bWr GD t1 t3 t4 t5 t6 t8 t10 v1 v4 v5 v10 v3 v8 Hrow wk a v Hw
      have Ha' := (clbLx a).1 Ha
      simp only [lkZV, lcZV, skZV, nfZV, npZV] at Ha' Hc
      omega
    have Hne := cpuReadNotMine (clb Lx) cvx GD.gdG (hB, 5) (WeakInterpProj.wbytes 8 v5) Hwf Hlv
      Hppo1 Hal Hcvl (by rw [wbytesLength, hcl]) Hrd Himgc Hnz Hinj Hns HF5
    intro Heq
    subst Heq
    exact Hne rfl
  · have Hrd : ∀ (j : Nat) a, (clb Lx)[j]? = some a →
        ∃ t v, greadsByte GD.gdG (hB, 10) a t v ∧ (WeakInterpProj.wbytes 8 v10)[j]? = some v := by
      intro j a Hj
      rw [clbLcpa] at Hj
      obtain ⟨rfl, Hjl⟩ := AxSpinX4.clRangeLookup _ _ _ _ Hj
      obtain ⟨t, Ht⟩ := loadnReads GD.gdG Hwf (hB, 10) (paZ lcpa) t10 8 v10 j Hl10 Hjl
      exact ⟨t, _, Ht, wbytesLookup (m := 8) 8 v10 j Hjl⟩
    obtain ⟨Heq, -⟩ := holderCpuRead Lx GD.gdG (hB, 10) hB (WeakInterpProj.wbytes 8 v10)
      (wbytesLength 8 v10) Hrd HF10
    exact wbytes8Inj' _ cpB Heq

end post

/-! # 3. THE CAPSTONE -/

/-- Lean-only (Rocq `set s0`). -/
def AxSpinX7.cS0 (sA0 : Athread) (i : Agent) : Athread :=
  if i = hA then sA0 else ⟨hp cpu0 AxSpinX4.bM0 zeroRegs, 0⟩
/-- Lean-only (Rocq `set sN`). -/
def AxSpinX7.cSN (sAN : Athread) (i : Agent) : Athread :=
  if i = hA then sAN else ⟨hp cpu0 hlt zeroRegs, 14⟩
/-- Lean-only (Rocq `set nf`). -/
def AxSpinX7.cN (nA : Nat) (i : Agent) : Nat := if i = hA then nA else 15
/-- Lean-only (Rocq `set post`). -/
def AxSpinX7.cPost (GT : GdexecT) (i : Agent) (_ : Athread) : Prop :=
  if i = hB then QB (gtAdGd GT).gdG else True

theorem xv6Handoff (GT : GdexecT)
    (HconsT : rvwmoCatConsistentT GT) (Hcl : ctrlClosed GT)
    (Hharts : ∀ e, e ∈ GT.gtG.gxGmo → e.1 = hA ∨ e.1 = hB)
    (Himgc : ∀ a, a ∈ clb Lx → GT.gtG.gxImg a = some b0)
    (n0 : Int) (Hn0 : 0 ≤ n0 ∧ n0 < 2 ^ 32)
    (Himgn : ∀ (j : Nat) a v, (npb Lx)[j]? = some a →
      (WeakInterpProj.wbytes 4 (BitVec.ofInt 32 n0))[j]? = some v → GT.gtG.gxImg a = some v)
    (Hal : clAligned (clb Lx) GT.gtG)
    (t1 t3 t4 t5 : List Nat) (t6 : Nat) (t8 t10 : List Nat) (v1 v4 v5 v10 : BitVec 64)
    (v3 v8 : BitVec 32)
    (HrowB : AxOpsem.grow (gtAdGd GT) hB = AxSpinX4.bRow t1 t3 t4 t5 t6 t8 t10 v1 v4 v5 v10 v3 v8)
    (HnowrapB : v8.toNat + 1 < 2 ^ 32)
    (sA0 sAN : Athread) (nA : Nat)
    (HrunA : ∀ (_ : AxannotGS AxSpinX7.xv6GF) (nm : Xv6N),
      nsteps (tierAAstep (gtAdGd GT) nm hA) nA sA0 sAN)
    (HkA : sA0.atK = 0) (HendA : sAN.atK = (AxOpsem.grow (gtAdGd GT) hA).length)
    (HwpA : ∀ [InvGS_gen .hasNoLC AxSpinX7.xv6GF] [AxannotGS AxSpinX7.xv6GF] (nm : Xv6N),
      ⊢ xv6Init Lx (gtAdGd GT) nm hA -∗
        @tierAWpd AxSpinX7.xv6GF .hasNoLC _ _ (xv6Pol GT) (gtAdGd GT) Xv6N Unit (protXv6 Lx) nm
          sA0 .MaybeStuck hA (fun _ => iprop(True))) :
    v1 = Xv ∧ v3 = one32 ∧
    (∀ (j : Nat) a, (clRange (paZ ropa) 8)[j]? = some a →
      GT.gtG.gxImg a = (WeakInterpProj.wbytes 8 v4)[j]?) ∧
    v5 ≠ cpB ∧ v10 = cpB := by
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
      nsteps (tierAAstep (gtAdGd GT) nm i) (AxSpinX7.cN nA i) (AxSpinX7.cS0 sA0 i)
        (AxSpinX7.cSN sAN i) := by
    intro Hann nm i Hi
    rcases Hin01 i Hi with rfl | rfl
    · exact HrunA Hann nm
    · exact AxSpinX4.bRun cpu0 (gtAdGd GT) t1 t3 t4 t5 t6 t8 t10 v1 v4 v5 v10 v3 v8 HrowB
  have Hk0 : ∀ i, i ∈ [hA, hB] → (AxSpinX7.cS0 sA0 i).atK = 0 := by
    intro i Hi
    rcases Hin01 i Hi with rfl | rfl
    · exact HkA
    · rfl
  have Hend : ∀ i, i ∈ [hA, hB] →
      (AxSpinX7.cSN sAN i).atK = (AxOpsem.grow (gtAdGd GT) i).length := by
    intro i Hi
    rcases Hin01 i Hi with rfl | rfl
    · exact HendA
    · show 14 = (AxOpsem.grow (gtAdGd GT) hB).length
      rw [HrowB]
      rfl
  have Hwp : ∀ [InvGS_gen .hasNoLC AxSpinX7.xv6GF] [AxannotGS AxSpinX7.xv6GF] (nm : Xv6N),
      ⊢ ([∗list] i ∈ [hA, hB], xv6Init Lx (gtAdGd GT) nm i) -∗
        [∗list] i ∈ [hA, hB],
          @tierAWpd AxSpinX7.xv6GF .hasNoLC _ _ (xv6Pol GT) (gtAdGd GT) Xv6N Unit (protXv6 Lx)
            nm (AxSpinX7.cS0 sA0 i) .MaybeStuck i
            (fun s => iprop(⌜AxSpinX7.cPost GT i s⌝)) := by
    intro Hinv Hann nm
    iintro HI
    icases (AxTokLedgerMp.bigSepLPair hA hB
      (fun i => xv6Init (GF := AxSpinX7.xv6GF) Lx (gtAdGd GT) nm i)).1 $$ HI with ⟨HA, HB⟩
    iapply (AxTokLedgerMp.bigSepLPair hA hB _).2
    rw [show AxSpinX7.cS0 sA0 hA = sA0 from if_pos rfl,
      show AxSpinX7.cS0 sA0 hB = ⟨hp cpu0 AxSpinX4.bM0 zeroRegs, 0⟩ from if_neg (by decide)]
    isplitl [HA]
    · iapply (AxSpinWit.tierAWpdMono (hlc := .hasNoLC) (pol := xv6Pol GT) (gtAdGd GT) Xv6N Unit
        (protXv6 Lx) nm sA0 .MaybeStuck hA (fun _ => iprop(True))
        (fun s => iprop(⌜AxSpinX7.cPost GT hA s⌝))
        (fun _ => pure_mono (fun _ => by
          unfold AxSpinX7.cPost; rw [if_neg (by decide)]; trivial)))
      iapply HwpA nm $$ HA
    · iapply (AxSpinWit.tierAWpdMono (hlc := .hasNoLC) (pol := xv6Pol GT) (gtAdGd GT) Xv6N Unit
        (protXv6 Lx) nm ⟨hp cpu0 AxSpinX4.bM0 zeroRegs, 0⟩ .MaybeStuck hB
        (fun _ => iprop(⌜QB (gtAdGd GT).gdG⌝))
        (fun s => iprop(⌜AxSpinX7.cPost GT hB s⌝))
        (fun _ => pure_mono (fun Hv => by
          unfold AxSpinX7.cPost; rw [if_pos rfl]; exact Hv)))
      unfold xv6Init
      icases HB with ⟨-, -, -, Hil, Hnh⟩
      iapply (AxSpinX5.wpdB (hlc := .hasNoLC) (GF := AxSpinX7.xv6GF) GT nm cpu0 Hcons t1 t3 t4
        t5 t6 t8 t10 v1 v4 v5 v10 v3 v8 HrowB HnowrapB) $$ Hil Hnh
  have Hfin := @tierAAdequacyAnnGateT AxSpinX7.xv6GF _ _ (xv6Pol GT) GT Xv6N Unit (protXv6 Lx)
    (xv6Init Lx (gtAdGd GT)) (xv6AxpolWf GT) HconsT [hA, hB] Hnd Hharts'
    (AxSpinX7.cS0 sA0) (AxSpinX7.cSN sAN) (AxSpinX7.cN nA) Hrun Hk0 Hend
    (AxSpinX7.cPost GT) Hwp
    (xv6HobAlloc (GF := AxSpinX7.xv6GF) Lx (gtAdGd GT) n0 LxOk Himgc Hn0 Himgn)
    (xv6Hok GT HconsT Hcl) hB (by simp)
  have Hq : QB (gtAdGd GT).gdG :=
    (if_pos rfl : AxSpinX7.cPost GT hB _ = QB (gtAdGd GT).gdG) ▸ Hfin
  exact QBFinal (gtAdGd GT) Hcons t1 t3 t4 t5 t6 t8 t10 v1 v4 v5 v10 v3 v8 HrowB Himgc Hal Hq

/-! # 4. CERTIFICATES -/

theorem hartsOfGmo (GT : GdexecT) :
    (∀ e, e ∈ GT.gtG.gxGmo → e.1 = hA ∨ e.1 = hB) →
    ∀ e, e ∈ GT.gtG.gxGmo → e.1 = hA ∨ e.1 = hB :=
  fun H e He => H e He

theorem AxSpinX7.spaHarts : ∀ e, e ∈ AxSpinX8.spa.gtG.gxGmo → e.1 = hA ∨ e.1 = hB := by
  apply hartsOfGmo
  intro e He
  have h : AxSpinX8.spa.gtG.gxGmo.all (fun e : Geid => decide (e.1 = hA ∨ e.1 = hB)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.1 h e He)

theorem spaScHarts : ∀ e, e ∈ spaSc.gtG.gxGmo → e.1 = hA ∨ e.1 = hB := by
  apply hartsOfGmo
  intro e He
  have h : spaSc.gtG.gxGmo.all (fun e : Geid => decide (e.1 = hA ∨ e.1 = hB)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.1 h e He)

theorem AxSpinX7.sprHarts : ∀ e, e ∈ AxSpinX8.spr.gtG.gxGmo → e.1 = hA ∨ e.1 = hB := by
  apply hartsOfGmo
  intro e He
  have h : AxSpinX8.spr.gtG.gxGmo.all (fun e : Geid => decide (e.1 = hA ∨ e.1 = hB)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.1 h e He)

/-- Image premises (`mkgt`'s image is all zeros). -/
theorem imgtClb (GT : GdexecT) (Himg : GT.gtG.gxImg = imgt) :
    ∀ a, a ∈ clb Lx → GT.gtG.gxImg a = some b0 := by
  intro a _
  rw [Himg]
  rfl

theorem imgtNp (GT : GdexecT) (Himg : GT.gtG.gxImg = imgt) :
    ∀ (j : Nat) a v, (npb Lx)[j]? = some a →
      (WeakInterpProj.wbytes 4 (BitVec.ofInt 32 0))[j]? = some v → GT.gtG.gxImg a = some v := by
  intro j a v _ Hv
  rw [Himg]
  have h0 : WeakInterpProj.wbytes 4 (BitVec.ofInt 32 0) = List.replicate 4 b0 := by
    decide +kernel
  rw [h0] at Hv
  rw [List.eq_of_mem_replicate (List.mem_of_getElem? Hv)]
  rfl

/-- Alignment of lk->cpu writes from the rows (every write touching lk->cpu is an 8-byte `sd`
at its base). -/
theorem alOfRows (GT : GdexecT)
    (Hcases : ∀ w a v, gwritesByte GT.gtG w a v → paZ lcpa ≤ a ∧ a < paZ lcpa + 8 →
      ∃ (val : BitVec 64) (cls : WmClass),
        gxLbl GT.gtG w = some (.LStore false (paZ lcpa) (WeakInterpProj.wbytes 8 val) cls)) :
    clAligned (clb Lx) GT.gtG := by
  rw [clbLcpa]
  apply clAlignedOfSd
  intro w a v Ha Hw
  rw [inClr] at Ha
  obtain ⟨val, cls, Hl⟩ := Hcases w a v Hw ⟨Ha.1, by have := Ha.2; omega⟩
  exact ⟨_, WeakInterpProj.wbytes 8 val, Hl, rfl, wbytesLength 8 val⟩

theorem gxLblHart (GT : GdexecT) (rA rB : List Lbl) (Hp : GT.gtG.gxProg = [rA, rB]) (w : Geid)
    (l : Lbl) : gxLbl GT.gtG w = some l → w.1 = hA ∨ w.1 = hB := by
  unfold gxLbl
  rw [Hp]
  obtain ⟨wi, wk⟩ := w
  rcases wi with _ | _ | wi
  · intro _
    exact Or.inl rfl
  · intro _
    exact Or.inr rfl
  · simp

theorem spaAl : clAligned (clb Lx) AxSpinX8.spa.gtG := by
  apply alOfRows
  intro w a v Hw Ha
  obtain ⟨l, -, -, -, Hl, -⟩ := id Hw
  obtain ⟨wi, wk⟩ := w
  rcases gxLblHart AxSpinX8.spa spaRowA spaRowB rfl _ _ Hl with Hi | Hi <;>
    dsimp only at Hi <;> subst Hi
  · rcases aWr (gtAdGd AxSpinX8.spa) 0 [0, 0, 0, 0] zero32 rfl wk a v Hw with
      Hc | Hc | Hc | Hc | Hc <;> simp only [lkZV, lcZV, npZV] at Ha Hc <;> (try omega)
    · obtain ⟨rfl, -⟩ := Hc
      exact ⟨cpA, .WCplain, rfl⟩
    · obtain ⟨rfl, -⟩ := Hc
      exact ⟨zero64, .WCplain, rfl⟩
  · rcases AxSpinX5.bWr (gtAdGd AxSpinX8.spa) (List.replicate 8 3) (List.replicate 4 4)
      (List.replicate 8 0) (List.replicate 8 2) 7 (List.replicate 4 5) (List.replicate 8 9) Xv
      zero64 cpA cpB one32 one32 rfl wk a v Hw with
      Hc | Hc | Hc | Hc | Hc | Hc | Hc <;> simp only [lkZV, lcZV, npZV, skZV, nfZV] at Ha Hc <;>
      (try omega)
    · obtain ⟨rfl, -⟩ := Hc
      exact ⟨cpB, .WCplain, rfl⟩
    · obtain ⟨rfl, -⟩ := Hc
      exact ⟨zero64, .WCplain, rfl⟩

theorem spaScAl : clAligned (clb Lx) spaSc.gtG := by
  apply alOfRows
  intro w a v Hw Ha
  obtain ⟨l, -, -, -, Hl, -⟩ := id Hw
  obtain ⟨wi, wk⟩ := w
  rcases gxLblHart spaSc spaRowA spaScRowB rfl _ _ Hl with Hi | Hi <;>
    dsimp only at Hi <;> subst Hi
  · rcases aWr (gtAdGd spaSc) 0 [0, 0, 0, 0] zero32 rfl wk a v Hw with
      Hc | Hc | Hc | Hc | Hc <;> simp only [lkZV, lcZV, npZV] at Ha Hc <;> (try omega)
    · obtain ⟨rfl, -⟩ := Hc
      exact ⟨cpA, .WCplain, rfl⟩
    · obtain ⟨rfl, -⟩ := Hc
      exact ⟨zero64, .WCplain, rfl⟩
  · rcases AxSpinX5.bWr (gtAdGd spaSc) (List.replicate 8 3) (List.replicate 4 4)
      (List.replicate 8 0) (List.replicate 8 2) 7 (List.replicate 4 5) (List.replicate 8 9) Xv
      zero64 cpA cpB one32 one32 rfl wk a v Hw with
      Hc | Hc | Hc | Hc | Hc | Hc | Hc <;> simp only [lkZV, lcZV, npZV, skZV, nfZV] at Ha Hc <;>
      (try omega)
    · obtain ⟨rfl, -⟩ := Hc
      exact ⟨cpB, .WCplain, rfl⟩
    · obtain ⟨rfl, -⟩ := Hc
      exact ⟨zero64, .WCplain, rfl⟩

theorem sprAl : clAligned (clb Lx) AxSpinX8.spr.gtG := by
  apply alOfRows
  intro w a v Hw Ha
  obtain ⟨l, -, -, -, Hl, -⟩ := id Hw
  obtain ⟨wi, wk⟩ := w
  rcases gxLblHart AxSpinX8.spr AxSpinX4.rRow sprRowB rfl _ _ Hl with Hi | Hi <;>
    dsimp only at Hi <;> subst Hi
  · obtain ⟨rfl, -⟩ := rWr (gtAdGd AxSpinX8.spr) rfl wk a v Hw
    exact ⟨cpA, .WCplain, rfl⟩
  · rcases AxSpinX5.bWr (gtAdGd AxSpinX8.spr) (List.replicate 8 1) (List.replicate 4 2)
      (List.replicate 8 0) (List.replicate 8 0) 0 (List.replicate 4 0) (List.replicate 8 5) Xv
      zero64 zero64 cpA one32 zero32 rfl wk a v Hw with
      Hc | Hc | Hc | Hc | Hc | Hc | Hc <;> simp only [lkZV, lcZV, npZV, skZV, nfZV] at Ha Hc <;>
      (try omega)
    · obtain ⟨rfl, -⟩ := Hc
      exact ⟨cpB, .WCplain, rfl⟩
    · obtain ⟨rfl, -⟩ := Hc
      exact ⟨zero64, .WCplain, rfl⟩

theorem nowrapOne : one32.toNat + 1 < 2 ^ 32 := by decide +kernel
theorem nowrapZero : zero32.toNat + 1 < 2 ^ 32 := by decide +kernel

theorem aWpdOn (GT : GdexecT) (HconsT : rvwmoCatConsistentT GT)
    (Hrow : AxOpsem.grow (gtAdGd GT) hA = spaRowA) :
    ∀ [InvGS_gen .hasNoLC AxSpinX7.xv6GF] [AxannotGS AxSpinX7.xv6GF] (nm : Xv6N),
      ⊢ xv6Init Lx (gtAdGd GT) nm hA -∗
        @tierAWpd AxSpinX7.xv6GF .hasNoLC _ _ (xv6Pol GT) (gtAdGd GT) Xv6N Unit (protXv6 Lx) nm
          ⟨hp cpu0 AxSpinX4.aM0 zeroRegs, 0⟩ .MaybeStuck hA (fun _ => iprop(True)) := by
  intro _ _ nm
  unfold xv6Init
  iintro ⟨-, -, -, Hil, Hnh⟩
  iapply (AxSpinX6.wpdA (hlc := .hasNoLC) (GF := AxSpinX7.xv6GF) GT nm cpu0 (catTAd GT HconsT)
    0 [0, 0, 0, 0] zero32 Hrow nowrapZero) $$ Hil Hnh

theorem aRunOn (GT : GdexecT) (Hrow : AxOpsem.grow (gtAdGd GT) hA = spaRowA) :
    ∀ (_ : AxannotGS AxSpinX7.xv6GF) (nm : Xv6N),
      nsteps (tierAAstep (gtAdGd GT) nm hA) 8
        ⟨hp cpu0 AxSpinX4.aM0 zeroRegs, 0⟩ ⟨hp cpu0 hlt zeroRegs, 7⟩ :=
  fun _ _ => AxSpinX4.aRun cpu0 (gtAdGd GT) 0 [0, 0, 0, 0] zero32 Hrow

/-- (a) THE SHAPE of `spa`: the deferred/forwarded cases are really taken. -/
theorem AxSpinX7.spaShape :
    gmoLt AxSpinX8.spa.gtG (hB, 1) (hB, 0) ∧ grfAt AxSpinX8.spa.gtG (paZ skpa) (hB, 0) (hB, 1) ∧
    gmoLt AxSpinX8.spa.gtG (hB, 10) (hB, 7) ∧
    grfAt AxSpinX8.spa.gtG (paZ lcpa) (hB, 7) (hB, 10) ∧
    grfAt AxSpinX8.spa.gtG (paZ lkpa) (hA, 6) (hB, 6) ∧
    grfAt AxSpinX8.spa.gtG (paZ lcpa) (hA, 1) (hB, 5) ∧
    grfAt AxSpinX8.spa.gtG (paZ nppa) (hA, 3) (hB, 8) :=
  ⟨(gmoLtBSpec _ _ _).1 (by decide +kernel), (grfAtBSpec _ _ _ _).1 (by decide +kernel),
    (gmoLtBSpec _ _ _).1 (by decide +kernel), (grfAtBSpec _ _ _ _).1 (by decide +kernel),
    (grfAtBSpec _ _ _ _).1 (by decide +kernel), (grfAtBSpec _ _ _ _).1 (by decide +kernel),
    (grfAtBSpec _ _ _ _).1 (by decide +kernel)⟩

/-- EVERY premise of `xv6Handoff` on `spa`. -/
theorem AxSpinX7.spaPremises :
    rvwmoCatConsistentT AxSpinX8.spa ∧ ctrlClosed AxSpinX8.spa ∧
    (∀ e, e ∈ AxSpinX8.spa.gtG.gxGmo → e.1 = hA ∨ e.1 = hB) ∧
    (∀ a, a ∈ clb Lx → AxSpinX8.spa.gtG.gxImg a = some b0) ∧
    (∀ (j : Nat) a v, (npb Lx)[j]? = some a →
      (WeakInterpProj.wbytes 4 (BitVec.ofInt 32 0))[j]? = some v →
      AxSpinX8.spa.gtG.gxImg a = some v) ∧
    clAligned (clb Lx) AxSpinX8.spa.gtG ∧
    AxOpsem.grow (gtAdGd AxSpinX8.spa) hB = spaRowB ∧ one32.toNat + 1 < 2 ^ 32 ∧
    (∀ (_ : AxannotGS AxSpinX7.xv6GF) (nm : Xv6N),
      nsteps (tierAAstep (gtAdGd AxSpinX8.spa) nm hA) 8
        ⟨hp cpu0 AxSpinX4.aM0 zeroRegs, 0⟩ ⟨hp cpu0 hlt zeroRegs, 7⟩) ∧
    (⟨hp cpu0 AxSpinX4.aM0 zeroRegs, 0⟩ : Athread).atK = 0 ∧
    (⟨hp cpu0 hlt zeroRegs, 7⟩ : Athread).atK =
      (AxOpsem.grow (gtAdGd AxSpinX8.spa) hA).length ∧
    (∀ [InvGS_gen .hasNoLC AxSpinX7.xv6GF] [AxannotGS AxSpinX7.xv6GF] (nm : Xv6N),
      ⊢ xv6Init Lx (gtAdGd AxSpinX8.spa) nm hA -∗
        @tierAWpd AxSpinX7.xv6GF .hasNoLC _ _ (xv6Pol AxSpinX8.spa) (gtAdGd AxSpinX8.spa) Xv6N
          Unit (protXv6 Lx) nm ⟨hp cpu0 AxSpinX4.aM0 zeroRegs, 0⟩ .MaybeStuck hA
          (fun _ => iprop(True))) :=
  ⟨AxSpinX8.spaCatT, AxSpinX8.spaCtrlClosed, AxSpinX7.spaHarts, imgtClb AxSpinX8.spa rfl,
    imgtNp AxSpinX8.spa rfl, spaAl, rfl, nowrapOne, aRunOn AxSpinX8.spa rfl, rfl, rfl,
    aWpdOn AxSpinX8.spa AxSpinX8.spaCatT rfl⟩

/-- The capstone fires on `spa`; its conclusion is TRUE there. -/
theorem AxSpinX7.spaSound :
    Xv = Xv ∧ one32 = one32 ∧
    (∀ (j : Nat) a, (clRange (paZ ropa) 8)[j]? = some a →
      AxSpinX8.spa.gtG.gxImg a = (WeakInterpProj.wbytes 8 zero64)[j]?) ∧
    cpA ≠ cpB ∧ cpB = cpB :=
  xv6Handoff AxSpinX8.spa AxSpinX8.spaCatT AxSpinX8.spaCtrlClosed AxSpinX7.spaHarts
    (imgtClb AxSpinX8.spa rfl) 0 ⟨by decide, by decide⟩ (imgtNp AxSpinX8.spa rfl) spaAl
    (List.replicate 8 3) (List.replicate 4 4) (List.replicate 8 0) (List.replicate 8 2) 7
    (List.replicate 4 5) (List.replicate 8 9) Xv zero64 cpA cpB one32 one32 rfl nowrapOne
    _ _ 8 (aRunOn AxSpinX8.spa rfl) rfl rfl (aWpdOn AxSpinX8.spa AxSpinX8.spaCatT rfl)

/-- The SC twin: B's reload and holder read in their gmo cases. -/
theorem spaScShape : gmoLt spaSc.gtG (hB, 0) (hB, 1) ∧ gmoLt spaSc.gtG (hB, 7) (hB, 10) :=
  ⟨(gmoLtBSpec _ _ _).1 (by decide +kernel), (gmoLtBSpec _ _ _).1 (by decide +kernel)⟩

theorem spaScSound :
    Xv = Xv ∧ one32 = one32 ∧
    (∀ (j : Nat) a, (clRange (paZ ropa) 8)[j]? = some a →
      spaSc.gtG.gxImg a = (WeakInterpProj.wbytes 8 zero64)[j]?) ∧
    cpA ≠ cpB ∧ cpB = cpB :=
  xv6Handoff spaSc spaScCatT spaScCtrlClosed spaScHarts (imgtClb spaSc rfl) 0
    ⟨by decide, by decide⟩ (imgtNp spaSc rfl) spaScAl
    (List.replicate 8 3) (List.replicate 4 4) (List.replicate 8 0) (List.replicate 8 2) 7
    (List.replicate 4 5) (List.replicate 8 9) Xv zero64 cpA cpB one32 one32 rfl nowrapOne
    _ _ 8 (aRunOn spaSc rfl) rfl rfl (aWpdOn spaSc spaScCatT rfl)

/-! (b) THE lk->cpu RACE -/

theorem rRunSpr : ∀ (_ : AxannotGS AxSpinX7.xv6GF) (nm : Xv6N),
    nsteps (tierAAstep (gtAdGd AxSpinX8.spr) nm hA) 1
      ⟨hp cpu0 AxSpinX4.rM0 zeroRegs, 0⟩ ⟨hp cpu0 hlt zeroRegs, 1⟩ :=
  fun _ _ => AxSpinX4.rRun cpu0 (gtAdGd AxSpinX8.spr) rfl

/-- B claims the GENESIS lock, writes `cpB`; A' (lock-less) writes `cpA` gmo-after it; B's holder
read returns A''s value. -/
theorem sprShape :
    graphValue (gtAdGd AxSpinX8.spr) (hB, 6) = some AxSpinX4.z4 ∧
    gmoLt AxSpinX8.spr.gtG (hB, 7) (hA, 0) ∧ gmoLt AxSpinX8.spr.gtG (hA, 0) (hB, 10) ∧
    grfAt AxSpinX8.spr.gtG (paZ lcpa) (hA, 0) (hB, 10) ∧
    graphValue (gtAdGd AxSpinX8.spr) (hB, 10) = some (WeakInterpProj.wbytes 8 cpA) :=
  ⟨by decide +kernel, (gmoLtBSpec _ _ _).1 (by decide +kernel),
    (gmoLtBSpec _ _ _).1 (by decide +kernel), (grfAtBSpec _ _ _ _).1 (by decide +kernel),
    by decide +kernel⟩

theorem AxSpinX7.sprWpdUnprovable :
    ¬ (∀ [InvGS_gen .hasNoLC AxSpinX7.xv6GF] [AxannotGS AxSpinX7.xv6GF] (nm : Xv6N),
        ⊢ xv6Init Lx (gtAdGd AxSpinX8.spr) nm hA -∗
          @tierAWpd AxSpinX7.xv6GF .hasNoLC _ _ (xv6Pol AxSpinX8.spr) (gtAdGd AxSpinX8.spr) Xv6N
            Unit (protXv6 Lx) nm ⟨hp cpu0 AxSpinX4.rM0 zeroRegs, 0⟩ .MaybeStuck hA
            (fun _ => iprop(True))) := by
  intro Hwp
  obtain ⟨-, -, -, -, H⟩ := xv6Handoff AxSpinX8.spr AxSpinX8.sprCatT AxSpinX8.sprCtrlClosed
    AxSpinX7.sprHarts (imgtClb AxSpinX8.spr rfl) 0 ⟨by decide, by decide⟩
    (imgtNp AxSpinX8.spr rfl) sprAl
    (List.replicate 8 1) (List.replicate 4 2) (List.replicate 8 0) (List.replicate 8 0) 0
    (List.replicate 4 0) (List.replicate 8 5) Xv zero64 zero64 cpA one32 zero32 rfl nowrapZero
    _ _ 1 rRunSpr rfl rfl Hwp
  exact cpANeCpB H

/-! (c) THE SANITY TWIN at the trivial protocol -/

theorem AxSpinX7.sprWpdTrivial :
    ∀ [InvGS_gen .hasNoLC AxSpinX7.xv6GF] [AxannotGS AxSpinX7.xv6GF] (nm : Unit),
      ⊢ (iprop(emp) : IProp AxSpinX7.xv6GF) -∗
        @tierAWpd AxSpinX7.xv6GF .hasNoLC _ _ (xv6Pol AxSpinX8.spr) (gtAdGd AxSpinX8.spr) Unit
          Unit trivOb nm ⟨hp cpu0 AxSpinX4.rM0 zeroRegs, 0⟩ .MaybeStuck hA
          (fun _ => iprop(True)) := by
  intro _ _ nm
  cases nm
  iintro _
  iapply (AxSpinX6.wpdRTriv (hlc := .hasNoLC) (GF := AxSpinX7.xv6GF) AxSpinX8.spr cpu0 rfl)

end Weak
