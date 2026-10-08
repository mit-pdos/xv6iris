/-
Weak: **Phase 1c, part 6 of the spinlock plan -- HART A's WPd at the joint instance `protXv6 Lx`**
(the positive lock holder: claim, `sd lk->cpu ← cpuAddr A`, `lw nextpid`, `sw nextpid ← v+1`,
`sd lk->cpu ← 0`, fence, release -- the release draws lk->cpu from (A,4) and `locked ∗ RNp` from
(A,3)), and the RACE hart A' (`sd lk->cpu ← cpuAddr A` WITHOUT the lock) at the TRIVIAL protocol
(the sanity twin).  Proved over ANY graph with A's row `AxSpinX4.aRow` (resp. `AxSpinX4.rRow`).

Rocq: `iris/AxSpinX6.v` @ xxvzwolszwmp.

## Deviations from Rocq

1. VOCABULARY (as `AxSpinX5` deviation 1): `Z` ↦ `Int`, `bv n` ↦ `BitVec n`, `gd_g GD` ↦
   `GD.gdG`, `l !! j` ↦ `l[j]?` (indices typed `Nat`), `pa_z` ↦ `paZ`, `Z_to_bv 32` ↦
   `BitVec.ofInt 32`, `bv_add v2 one32` ↦ `v2 + one32`, `bv_unsigned v2` ↦ `v2.toNat` (so
   `Hnowrap : v2.toNat + 1 < 2 ^ 32`, over `Nat`), `a ≤ b < c` ↦ `a ≤ b ∧ b < c`,
   `init_regstate` ↦ `zeroRegs`, `AThread p k` ↦ `⟨p, k⟩`.
2. CONTEXTS (as `AxSpinX5` deviation 2): Rocq section variables are explicit leading arguments
   in Rocq's order, only where Rocq's section mechanism includes them (§1 `GD t0 t2 v2 Hrow`;
   §2 `GT nm cpu`, then `Hcons t0 t2 v2 Hrow [Hnowrap]` where `Proof using` names them; §3
   `GT cpu [Hrow]`).  `invGS_gen HasNoLc Σ` ↦ `[InvGS_gen hlc GF]` for any `hlc`;
   `axannotG Σ`+`axannotGS Σ` ↦ `[AxannotGS GF]`; `xv6G Σ` ↦ `[AxSpinX.Xv6G GF]`.  The local
   instances `a_pol`/`a_G`/`r_pol`/`r_G` are inlined: the policy `xv6Pol GT` and the instances
   `AxSpinX2.xG Lx GT nm` (= `shG …`) / `shG (gtAdGd GT) Unit Unit trivOb ()` are passed
   explicitly.  O2 STAGE C: Rocq's `Tf` argument of `AxGA2`/`tierA_wpd` is gone.
3. STATEMENT SHAPES: wand chains `A -∗ B` ↦ `⊢ A -∗ B`; the Rocq notations `TWA`/`TWR`/`LK`/
   `RNP`/`RCPU`/`ISL`/`RHA`/`NPFA` are file-local Lean notations with the same expansions
   (`OB`/`RP`/`HwfG`/`aL` unfolded); `NPFA`'s read fact is the Lean-only reducible
   `AxSpinX6.npRd`.
4. PROOFS: Rocq `vm_compute` facts by `decide +kernel`; the `zv` Ltac is inlined as
   `simp only [lkZV, …]`; `feTrivx` reuses `AxSpinProt3.feTriv` (same statement at this policy).

**Rocq → Lean name map.**  `aL` `AxSpinX6.aL` (dup), `a_wr` `aWr`, `a_wr_before` `aWrBefore`,
`r_wr` `rWr`, `gdata_stA` `gdataStA`, `wA6` `wA6`, `wA5` `AxSpinX6.wA5` (dup), `wA4`
`AxSpinX6.wA4` (dup), `wA3` `AxSpinX6.wA3` (dup), `wA2` `AxSpinX6.wA2` (dup), `wA1`
`AxSpinX6.wA1` (dup), `wA0w` `AxSpinX6.wA0w` (dup), `wpdA` `AxSpinX6.wpdA` (dup), `fe_trivx`
`feTrivx`, `wpdR_triv` `AxSpinX6.wpdRTriv` (dup).  Lean-only (file-qualified): `AxSpinX6.npRd`
(`NPFA`'s read fact).

**Dropped:** none (Rocq 19 decls incl. the 4 local instances (inlined); Lean 16 = 15 + 1
Lean-only).
-/
import Weak.AxSpinX5

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D

/-! # 1. Hart A's row facts -/

section rowA

theorem AxSpinX6.aL (GD : Gdexec) (t0 : Nat) (t2 : List Nat) (v2 : BitVec 32)
    (Hrow : AxOpsem.grow GD hA = AxSpinX4.aRow t0 t2 v2) (k : Nat) (lb : Lbl) :
    (AxSpinX4.aRow t0 t2 v2)[k]? = some lb → gxLbl GD.gdG (hA, k) = some lb := by
  intro Hk
  rw [gxLblGrow, Hrow]
  exact Hk

theorem aWr (GD : Gdexec) (t0 : Nat) (t2 : List Nat) (v2 : BitVec 32)
    (Hrow : AxOpsem.grow GD hA = AxSpinX4.aRow t0 t2 v2) (k : Nat) (a : Int) (v : BitVec 8) :
    gwritesByte GD.gdG (hA, k) a v →
    (k = 0 ∧ paZ lkpa ≤ a ∧ a < paZ lkpa + 4) ∨ (k = 1 ∧ paZ lcpa ≤ a ∧ a < paZ lcpa + 8) ∨
    (k = 3 ∧ paZ nppa ≤ a ∧ a < paZ nppa + 4) ∨ (k = 4 ∧ paZ lcpa ≤ a ∧ a < paZ lcpa + 8) ∨
    (k = 6 ∧ paZ lkpa ≤ a ∧ a < paZ lkpa + 4) := by
  rintro ⟨l, base, vs, j, Hl, Hwr, Hv, Ha⟩
  rw [gxLblGrow, Hrow] at Hl
  have Hj := (List.getElem?_eq_some_iff.1 Hv).1
  unfold accAddr at Ha
  subst Ha
  rcases k with _ | _ | _ | _ | _ | _ | _ | k <;>
    simp [AxSpinX4.aRow] at Hl
  all_goals (subst Hl; simp only [lbWr, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at Hwr)
  all_goals (obtain ⟨rfl, rfl⟩ := Hwr)
  all_goals (simp only [wbytesLength, AxSpinX4.z4, AxSpinX4.o4] at Hj; omega)

theorem aWrBefore (GD : Gdexec) (t0 : Nat) (t2 : List Nat) (v2 : BitVec 32)
    (Hrow : AxOpsem.grow GD hA = AxSpinX4.aRow t0 t2 v2) (w : Geid) (a : Int) (v : BitVec 8)
    (k : Nat) :
    gwritesByte GD.gdG w a v → WeakRvwmoGraph.gpo GD.gdG w (hA, k) →
    ∃ k', w = (hA, k') ∧ k' < k ∧
      ((k' = 0 ∧ paZ lkpa ≤ a ∧ a < paZ lkpa + 4) ∨ (k' = 1 ∧ paZ lcpa ≤ a ∧ a < paZ lcpa + 8) ∨
       (k' = 3 ∧ paZ nppa ≤ a ∧ a < paZ nppa + 4) ∨ (k' = 4 ∧ paZ lcpa ≤ a ∧ a < paZ lcpa + 8) ∨
       (k' = 6 ∧ paZ lkpa ≤ a ∧ a < paZ lkpa + 4)) := by
  obtain ⟨wi, wk⟩ := w
  rintro Hw ⟨Hh, Hlt, -, -⟩
  dsimp only at Hh Hlt
  subst Hh
  exact ⟨wk, rfl, Hlt, aWr GD t0 t2 v2 Hrow wk a v Hw⟩

end rowA

/-- The race row: one write, at lk->cpu. -/
theorem rWr (GD : Gdexec) (Hrow : AxOpsem.grow GD hA = AxSpinX4.rRow) (k : Nat) (a : Int)
    (v : BitVec 8) :
    gwritesByte GD.gdG (hA, k) a v → k = 0 ∧ paZ lcpa ≤ a ∧ a < paZ lcpa + 8 := by
  rintro ⟨l, base, vs, j, Hl, Hwr, Hv, Ha⟩
  rw [gxLblGrow, Hrow] at Hl
  have Hj := (List.getElem?_eq_some_iff.1 Hv).1
  unfold accAddr at Ha
  subst Ha
  rcases k with _ | k <;> simp [AxSpinX4.rRow] at Hl
  subst Hl
  simp only [lbWr, Option.some.injEq, Prod.mk.injEq] at Hwr
  obtain ⟨rfl, rfl⟩ := Hwr
  simp only [wbytesLength] at Hj
  omega

/-! # 2. Hart A's WPd (post True) -/

theorem gdataStA (GT : GdexecT) (k : Nat) (base : Int) (n : Nat) (val : BitVec (8 * n))
    (cls : WmClass) :
    gxLbl (gtAdGd GT).gdG (hA, k) =
      some (.LStore false base (WeakInterpProj.wbytes n val) cls) →
    graphData (gtAdGd GT) (hA, k) = some (WeakInterpProj.wbytes n val) := by
  intro Hl
  unfold graphData
  rw [Hl]
  rfl

/-- Lean-only: `NPFA`'s read fact (the nextpid read `(A,2)` reads the bytes of `v`). -/
abbrev AxSpinX6.npRd (G : Gexec) (v : Int) : Prop :=
  ∀ (j : Nat) a t b, (npb Lx)[j]? = some a → greadsByte G (hA, 2) a t b →
    (WeakInterpProj.wbytes 4 (BitVec.ofInt 32 v))[j]? = some b

section wpdA
variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF] [AxannotGS GF]
  [AxSpinX.Xv6G GF]

set_option hygiene false in
local notation "ΦA" => (fun _ : Athread => iprop(True))
set_option hygiene false in
local notation "TWA " s:max => @tierAWpd GF hlc _ _ (xv6Pol GT) (gtAdGd GT) Xv6N Unit
  (protXv6 Lx) nm s .MaybeStuck hA (fun _ => iprop(True))
set_option hygiene false in
local notation "LK" => locked (GF := GF) nm.xnReg Lx.xlLk hA (hA, 0)
set_option hygiene false in
local notation "RNP " e:max => RNp (GF := GF) Lx nm.xnH nm.xnM nm.xnI (gtAdGd GT) e
set_option hygiene false in
local notation "RCPU " e:max => RCpu (GF := GF) Lx nm.xnH (gtAdGd GT) e
set_option hygiene false in
local notation "ISL" =>
  isLock (GF := GF) nm.xnReg Lx.xlLk (RPid Lx nm.xnH nm.xnM nm.xnI (gtAdGd GT))
set_option hygiene false in
local notation "RHA " e:max =>
  iprop(True ∗ RVL (GF := GF) nm.xnH (gtAdGd GT) (clb Lx) e (cvx hA))
set_option hygiene false in
local notation "NPFA" =>
  iprop(∃ (v : Int), RNpv (GF := GF) Lx GT nm (hA, 0) v ∗ ⌜AxSpinX6.npRd (gtAdGd GT).gdG v⌝)

/-- THE RELEASE (k6): lk->cpu from (A,4), `locked ∗ RNp` from (A,3). -/
theorem wA6 (GT : GdexecT) (nm : Xv6N) (cpu : CPU) (Hcons : rvwmoCatConsistent (gtAdGd GT))
    (t0 : Nat) (t2 : List Nat) (v2 : BitVec 32)
    (Hrow : AxOpsem.grow (gtAdGd GT) hA = AxSpinX4.aRow t0 t2 v2) :
    ⊢ ISL -∗ AxAnnot.annotOwn (hA, 3) iprop(LK ∗ RNP (hA, 3)) -∗
      AxAnnot.annotOwn (hA, 4) (RCPU (hA, 4)) -∗
      ∀ rs : RegFile, TWA ⟨hp cpu aEnd rs, 6⟩ := by
  have Hne : 6 ≠ (AxOpsem.grow (gtAdGd GT) hA).length := by rw [Hrow]; simp [AxSpinX4.aRow]
  have Hl3 := AxSpinX6.aL (gtAdGd GT) t0 t2 v2 Hrow 3 _ rfl
  have Hl4 := AxSpinX6.aL (gtAdGd GT) t0 t2 v2 Hrow 4 _ rfl
  have Hl5 := AxSpinX6.aL (gtAdGd GT) t0 t2 v2 Hrow 5 _ rfl
  have Hl6 := AxSpinX6.aL (gtAdGd GT) t0 t2 v2 Hrow 6 _ rfl
  have hnone : get? ({[((hA, 4) : Geid) := RCPU (hA, 4)]} : Mea GF) (hA, 3) = none :=
    lookupSingletonNe (by decide)
  have H := nshWrite (hlc := hlc) (pol := xv6Pol GT) (gtAdGd GT) Xv6N Unit (protXv6 Lx) nm cpu hA
    ΦA 4 lkpa lkpaRam zero32 hlt 6 Hne
    iprop(ISL ∗ AxAnnot.annotOwn (hA, 3) iprop(LK ∗ RNP (hA, 3)) ∗
      AxAnnot.annotOwn (hA, 4) (RCPU (hA, 4)))
    (fun rs => by
      have Hval := gdataStA GT 6 _ 4 zero32 _ Hl6
      obtain ⟨Hw6, Hsg6⟩ := gwbStoren _ _ _ _ _ Hl6
      have Hzw : zw Lx.xlLk (gtAdGd GT).gdG (hA, 6) := by
        have H := Hw6 0 b0 (by decide +kernel)
        rw [AxSpinX5.addZero] at H
        exact H
      have Hlw : ∀ a v', gwritesByte (gtAdGd GT).gdG (hA, 6) a v' → a ∈ lwb Lx := by
        intro a v' Hw
        obtain ⟨j, Hj, rfl⟩ := Hsg6 a v' Hw
        have hj := (List.getElem?_eq_some_iff.1 Hj).1
        simp only [AxSpinX4.z4, wbytesLength] at hj
        exact (lwbLx _).2 ⟨by omega, by omega⟩
      have Hob3 : gobCat (gtAdGd GT) (hA, 3) (hA, 6) :=
        fenceGob (gtAdGd GT) hA 3 5 6 _ _ _ _ Hl3 rfl Hl5 Hl6 (by decide) (by decide)
      have Hob4 : gobCat (gtAdGd GT) (hA, 4) (hA, 6) :=
        fenceGob (gtAdGd GT) hA 4 5 6 _ _ _ _ Hl4 rfl Hl5 Hl6 (by decide) (by decide)
      have Hsub : (FiniteMap.dom_set (insert ({[((hA, 4) : Geid) := RCPU (hA, 4)]} : Mea GF)
          (hA, 3) iprop(LK ∗ RNP (hA, 3))) : GSet Geid) ⊆
          @Axpol.lobp (xv6Pol GT) (gtAdGd GT) (hA, 6) := by
        have H3 : ((hA, 3) : Geid) ∈ @Axpol.lobp (xv6Pol GT) (gtAdGd GT) (hA, 6) :=
          fenceLobp (gtAdGd GT) Hcons hA 3 5 6 _ _ _ _ Hl3 rfl Hl5 Hl6 (by decide) (by decide)
        have H4 : ((hA, 4) : Geid) ∈ @Axpol.lobp (xv6Pol GT) (gtAdGd GT) (hA, 6) :=
          fenceLobp (gtAdGd GT) Hcons hA 4 5 6 _ _ _ _ Hl4 rfl Hl5 Hl6 (by decide) (by decide)
        rw [domInsert, domSingleton]
        intro x hx
        rcases elemOfUnion.1 hx with h | h
        · rw [elemOfSingleton.1 h]; exact H3
        · rw [elemOfSingleton.1 h]; exact H4
      have Hmk : ⊢ AxAnnot.annotOwn (hA, 3) iprop(LK ∗ RNP (hA, 3)) -∗
          AxAnnot.annotOwn (hA, 4) (RCPU (hA, 4)) -∗
          [∗map] e ↦ P ∈ (insert ({[((hA, 4) : Geid) := RCPU (hA, 4)]} : Mea GF) (hA, 3)
            iprop(LK ∗ RNP (hA, 3))), AxAnnot.annotOwn e P := by
        iintro Ha Hb
        iapply (BigSepM.bigSepM_insert hnone).2
        isplitl [Ha]
        · iexact Ha
        · iapply BigSepM.bigSepM_singleton.2
          iexact Hb
      have Hsplit : ⊢ ([∗map] Rin ∈ (insert ({[((hA, 4) : Geid) := RCPU (hA, 4)]} : Mea GF)
          (hA, 3) iprop(LK ∗ RNP (hA, 3))), Rin) -∗
          iprop(locked nm.xnReg Lx.xlLk hA (hA, 0) ∗ RCpu Lx nm.xnH (gtAdGd GT) (hA, 4) ∗
            RNp Lx nm.xnH nm.xnM nm.xnI (gtAdGd GT) (hA, 3)) := by
        iintro H
        icases (BigSepM.bigSepM_insert hnone).1 $$ H with ⟨⟨Hlk, HN⟩, HC⟩
        ihave HC := (BigSepM.bigSepM_singleton (M := GMapF Geid)).1 $$ HC
        isplitl [Hlk]
        · iexact Hlk
        isplitl [HC]
        · iexact HC
        · iexact HN
      iintro ⟨#Hil, H3, H4⟩
      ihave Hm := Hmk $$ H3 H4
      ihave Hw := Hsplit
      ihave Hfe := (fxReleasePid (hlc := hlc) Lx GT nm LxOk Hcons (hA, 6) hA (hA, 0) (hA, 4)
        (hA, 3) (insert ({[((hA, 4) : Geid) := RCPU (hA, 4)]} : Mea GF) (hA, 3)
          iprop(LK ∗ RNP (hA, 3))) Hzw (fun t v => storenNoRead _ _ _ _ _ _ _ _ Hl6) Hlw Hob4
        Hob3) $$ Hil Hw
      iapply (evDrawM (hlc := hlc) (pol := xv6Pol GT) (gtAdGd GT) Xv6N Unit (protXv6 Lx) nm
        (xv6AxpolWf GT) hA 6 _ (notheld nm.xnReg Lx.xlLk hA) iprop(True) _ _ Hval Hsub)
        $$ Hm [Hfe]
      · iapply (@flowEqDynMono hlc GF _ (AxSpinX2.xG Lx GT nm) (xv6Pol GT) (gtAdGd GT) (hA, 6) _ _
          (notheld nm.xnReg Lx.xlLk hA) iprop(notheld nm.xnReg Lx.xlLk hA ∗ True)) $$ [] Hfe
        inext
        iintro H
        isplitl [H]
        · iexact H
        · itrivial
      iintro _ _
      iapply (shHltTrue (hlc := hlc) (pol := xv6Pol GT) (gtAdGd GT) Xv6N Unit (protXv6 Lx) nm
        cpu hA (6 + 1)) $$ %rs)
  iintro #Hil H3 H4
  iapply H $$ [$Hil $H3 $H4]

theorem AxSpinX6.wA5 (GT : GdexecT) (nm : Xv6N) (cpu : CPU)
    (Hcons : rvwmoCatConsistent (gtAdGd GT)) (t0 : Nat) (t2 : List Nat) (v2 : BitVec 32)
    (Hrow : AxOpsem.grow (gtAdGd GT) hA = AxSpinX4.aRow t0 t2 v2) :
    ⊢ ISL -∗ AxAnnot.annotOwn (hA, 3) iprop(LK ∗ RNP (hA, 3)) -∗
      AxAnnot.annotOwn (hA, 4) (RCPU (hA, 4)) -∗
      ∀ rs : RegFile, TWA ⟨hp cpu (fnc aEnd) rs, 5⟩ := by
  have Hne : 5 ≠ (AxOpsem.grow (gtAdGd GT) hA).length := by rw [Hrow]; simp [AxSpinX4.aRow]
  have H := nshFence (hlc := hlc) (pol := xv6Pol GT) (gtAdGd GT) Xv6N Unit (protXv6 Lx) nm cpu hA
    ΦA aEnd 5 Hne
    iprop(ISL ∗ AxAnnot.annotOwn (hA, 3) iprop(LK ∗ RNP (hA, 3)) ∗
      AxAnnot.annotOwn (hA, 4) (RCPU (hA, 4)))
    (fun rs => by
      iintro ⟨#Hil, H3, H4⟩
      inext
      iapply (wA6 (hlc := hlc) GT nm cpu Hcons t0 t2 v2 Hrow) $$ Hil H3 H4 %rs)
  iintro #Hil H3 H4
  iapply H $$ [$Hil $H3 $H4]

/-- k4: `sd lk->cpu ← 0`, the handle drawn from (A,1) (ppo rule 1). -/
theorem AxSpinX6.wA4 (GT : GdexecT) (nm : Xv6N) (cpu : CPU)
    (Hcons : rvwmoCatConsistent (gtAdGd GT)) (t0 : Nat) (t2 : List Nat) (v2 : BitVec 32)
    (Hrow : AxOpsem.grow (gtAdGd GT) hA = AxSpinX4.aRow t0 t2 v2) :
    ⊢ ISL -∗ AxAnnot.annotOwn (hA, 3) iprop(LK ∗ RNP (hA, 3)) -∗
      AxAnnot.annotOwn (hA, 1) (RHA (hA, 1)) -∗
      ∀ rs : RegFile, TWA ⟨hp cpu aRel rs, 4⟩ := by
  have Hne : 4 ≠ (AxOpsem.grow (gtAdGd GT) hA).length := by rw [Hrow]; simp [AxSpinX4.aRow]
  have Hl1 := AxSpinX6.aL (gtAdGd GT) t0 t2 v2 Hrow 1 _ rfl
  have Hl4 := AxSpinX6.aL (gtAdGd GT) t0 t2 v2 Hrow 4 _ rfl
  have H := nshWrite (hlc := hlc) (pol := xv6Pol GT) (gtAdGd GT) Xv6N Unit (protXv6 Lx) nm cpu hA
    ΦA 8 lcpa lcpaRam zero64 (fnc aEnd) 4 Hne
    iprop(ISL ∗ AxAnnot.annotOwn (hA, 3) iprop(LK ∗ RNP (hA, 3)) ∗
      AxAnnot.annotOwn (hA, 1) (RHA (hA, 1)))
    (fun rs => by
      have Hval := gdataStA GT 4 _ 8 zero64 _ Hl4
      obtain ⟨Hw4, Hsg4⟩ := gwbStoren _ _ _ _ _ Hl4
      obtain ⟨Hw1, -⟩ := gwbStoren _ _ _ _ _ Hl1
      have Hw4_0 := Hw4 0 _ (wbytesLookupGen 8 zero64 0 (by decide))
      have Hacc : gaccesses (gtAdGd GT).gdG (hA, 1) (paZ lcpa + ((0 : Nat) : Int)) :=
        Or.inl ⟨_, Hw1 0 _ (wbytesLookupGen 8 cpA 0 (by decide))⟩
      have Hpo : WeakRvwmoGraph.gpo (gtAdGd GT).gdG (hA, 1) (hA, 4) :=
        gpoRow (gtAdGd GT) hA 1 4 _ _ Hl1 Hl4 (by decide)
      have Hlt : gmoLt (gtAdGd GT).gdG (hA, 1) (hA, 4) :=
        obCatSubGmo (gtAdGd GT) _ _ Hcons (ppo1Gob (gtAdGd GT) (hA, 1) (hA, 4) _ _ Hpo Hacc Hw4_0)
      have Hin : ((hA, 1) : Geid) ∈ @Axpol.lobp (xv6Pol GT) (gtAdGd GT) (hA, 4) :=
        locLobp (gtAdGd GT) Hcons (hA, 1) (hA, 4) _ _ _ Hl1 rfl Hpo Hacc Hw4_0
      have Hisw : gisW (gtAdGd GT).gdG (hA, 4) = true := by unfold gisW; rw [Hl4]; rfl
      have Hwr : ∀ (j : Nat) a v, (clb Lx)[j]? = some a →
          (WeakInterpProj.wbytes 8 zero64)[j]? = some v →
          gwritesByte (gtAdGd GT).gdG (hA, 4) a v := by
        intro j a v Hj Hv
        rw [clbLcpa] at Hj
        obtain ⟨rfl, -⟩ := AxSpinX4.clRangeLookup _ _ _ _ Hj
        exact Hw4 j v Hv
      have Hsg : ∀ a v, gwritesByte (gtAdGd GT).gdG (hA, 4) a v → a ∈ clb Lx := by
        intro a v Hw
        obtain ⟨j, Hj, rfl⟩ := Hsg4 a v Hw
        have hj := (List.getElem?_eq_some_iff.1 Hj).1
        rw [wbytesLength] at hj
        rw [clbLx]
        simp only [lkZV, lcZV]
        omega
      have Hw0 : ⊢ ([∗map] Rin ∈ ({[((hA, 1) : Geid) := RHA (hA, 1)]} : Mea GF), Rin) -∗
          iprop(True ∗ ∃ vold, RVL nm.xnH (gtAdGd GT) (clb Lx) (hA, 1) vold) := by
        iintro H
        ihave H := (BigSepM.bigSepM_singleton (M := GMapF Geid)).1 $$ H
        icases H with ⟨-, H⟩
        isplitr
        · itrivial
        · iexists _
          iexact H
      iintro ⟨#Hil, H3, H1⟩
      ihave Hw := Hw0
      ihave Hfe := (fxCpuWrite (hlc := hlc) Lx GT nm LxOk Hcons (hA, 4) (hA, 1)
        (WeakInterpProj.wbytes 8 zero64) iprop(True) ({[((hA, 1) : Geid) := RHA (hA, 1)]} : Mea GF)
        Hisw Hlt (Or.inr zero64Bytes) Hwr Hsg) $$ Hw
      iapply (evDraw (hlc := hlc) (pol := xv6Pol GT) (gtAdGd GT) Xv6N Unit (protXv6 Lx) nm
        (xv6AxpolWf GT) hA 4 (hA, 1) _ (RCPU (hA, 4)) iprop(True) _ _ Hval Hin) $$ H1 [Hfe]
      · iapply (@flowEqDynMono hlc GF _ (AxSpinX2.xG Lx GT nm) (xv6Pol GT) (gtAdGd GT) (hA, 4) _ _
          iprop(True ∗ RVL nm.xnH (gtAdGd GT) (clb Lx) (hA, 4) (WeakInterpProj.wbytes 8 zero64))
          iprop(RCPU (hA, 4) ∗ True)) $$ [] Hfe
        inext
        iintro ⟨-, H⟩
        isplitl [H]
        · iunfold RCpu
          iexists _
          iexact H
        · itrivial
      iintro H4 _
      iapply (AxSpinX6.wA5 (hlc := hlc) GT nm cpu Hcons t0 t2 v2 Hrow) $$ Hil H3 H4 %rs)
  iintro #Hil H3 H1
  iapply H $$ [$Hil $H3 $H1]

/-- k3: `sw nextpid ← v+1`, drawn from the lw (A,2) by ppo rule 1. -/
theorem AxSpinX6.wA3 (GT : GdexecT) (nm : Xv6N) (cpu : CPU)
    (Hcons : rvwmoCatConsistent (gtAdGd GT)) (t0 : Nat) (t2 : List Nat) (v2 : BitVec 32)
    (Hrow : AxOpsem.grow (gtAdGd GT) hA = AxSpinX4.aRow t0 t2 v2)
    (Hnowrap : v2.toNat + 1 < 2 ^ 32) :
    ⊢ ISL -∗ AxAnnot.annotOwn (hA, 2) iprop(LK ∗ NPFA) -∗
      AxAnnot.annotOwn (hA, 1) (RHA (hA, 1)) -∗
      ∀ rs : RegFile, TWA ⟨hp cpu (aInc v2) rs, 3⟩ := by
  have Hne : 3 ≠ (AxOpsem.grow (gtAdGd GT) hA).length := by rw [Hrow]; simp [AxSpinX4.aRow]
  have Hl0 := AxSpinX6.aL (gtAdGd GT) t0 t2 v2 Hrow 0 _ rfl
  have Hl2 := AxSpinX6.aL (gtAdGd GT) t0 t2 v2 Hrow 2 _ rfl
  have Hl3 := AxSpinX6.aL (gtAdGd GT) t0 t2 v2 Hrow 3 _ rfl
  have Hwf := Hcons.1
  have H := nshWrite (hlc := hlc) (pol := xv6Pol GT) (gtAdGd GT) Xv6N Unit (protXv6 Lx) nm cpu hA
    ΦA 4 nppa nppaRam (v2 + one32 : BitVec 32) aRel 3 Hne
    iprop(ISL ∗ AxAnnot.annotOwn (hA, 2) iprop(LK ∗ NPFA) ∗
      AxAnnot.annotOwn (hA, 1) (RHA (hA, 1)))
    (fun rs => by
      have Hval := gdataStA GT 3 _ 4 (v2 + one32 : BitVec 32) _ Hl3
      obtain ⟨Hw3, Hsg3⟩ := gwbStoren _ _ _ _ _ Hl3
      have Hin : ((hA, 2) : Geid) ∈ @Axpol.lobp (xv6Pol GT) (gtAdGd GT) (hA, 3) := by
        obtain ⟨t, Ht⟩ := loadnReads (gtAdGd GT).gdG Hwf (hA, 2) (paZ nppa) t2 4 v2 0 Hl2
          (by decide)
        exact locLobp (gtAdGd GT) Hcons (hA, 2) (hA, 3) _ _ _ Hl2 rfl
          (gpoRow (gtAdGd GT) hA 2 3 _ _ Hl2 Hl3 (by decide)) (Or.inr ⟨t, _, Ht⟩)
          (Hw3 0 _ (wbytesLookupGen 4 (v2 + one32) 0 (by decide)))
      have Hlt03 : gmoLt (gtAdGd GT).gdG (hA, 0) (hA, 3) :=
        obCatSubGmo (gtAdGd GT) _ _ Hcons
          (acqGob (gtAdGd GT) hA 0 3 _ _ _ _ _ _ Hl0 Hl3 rfl (by decide))
      have Hisw : gisW (gtAdGd GT).gdG (hA, 3) = true := by unfold gisW; rw [Hl3]; rfl
      have Hsg : ∀ a v', gwritesByte (gtAdGd GT).gdG (hA, 3) a v' → a ∈ npb Lx := by
        intro a v' Hw
        obtain ⟨j, Hj, rfl⟩ := Hsg3 a v' Hw
        have hj := (List.getElem?_eq_some_iff.1 Hj).1
        rw [wbytesLength] at hj
        exact (npbLx _).2 ⟨by omega, by omega⟩
      have Harith : ∀ v : Int, 0 ≤ v ∧ v < 2 ^ 32 →
          (∀ (j : Nat) a t b, (npb Lx)[j]? = some a →
            greadsByte (gtAdGd GT).gdG (hA, 2) a t b →
            (WeakInterpProj.wbytes 4 (BitVec.ofInt 32 v))[j]? = some b) →
          v + 1 < 2 ^ 32 ∧
          ∀ (j : Nat) a b, (npb Lx)[j]? = some a →
            (WeakInterpProj.wbytes 4 (BitVec.ofInt 32 (v + 1)))[j]? = some b →
            gwritesByte (gtAdGd GT).gdG (hA, 3) a b := by
        intro v Hv Hrd
        have Hword : WeakInterpProj.wbytes 4 v2 = WeakInterpProj.wbytes 4 (BitVec.ofInt 32 v) :=
          readFactWord (gtAdGd GT).gdG Hwf (hA, 2) (paZ nppa) t2 4 v2 _ Hl2 (wbytesLength 4 _) Hrd
        have Hword' := wbytes4Inj _ _ Hword
        obtain ⟨Hlt, Heq⟩ := npSucc v v2 Hv Hword'.symm Hnowrap
        refine ⟨Hlt, ?_⟩
        intro j a b Hj Hb
        rw [Heq] at Hb
        have Hj' : (clRange (paZ nppa) 4)[j]? = some a := Hj
        obtain ⟨rfl, -⟩ := AxSpinX4.clRangeLookup _ _ _ _ Hj'
        exact Hw3 j b Hb
      have Hsing : ⊢ ([∗map] Rin ∈ ({[((hA, 2) : Geid) := iprop(LK ∗ NPFA)]} : Mea GF), Rin) -∗
          iprop(LK ∗ NPFA) := by
        iintro H
        iapply (BigSepM.bigSepM_singleton (M := GMapF Geid)).1 $$ H
      iintro ⟨#Hil, H2, H1⟩
      ihave Hw := Hsing
      ihave Hfe := (fxNpIncr (hlc := hlc) Lx GT nm LxOk Hcons (hA, 3) (hA, 2) (hA, 0) LK
        ({[((hA, 2) : Geid) := iprop(LK ∗ NPFA)]} : Mea GF) Hisw Hlt03 Hsg Harith) $$ Hw
      iapply (evDraw (hlc := hlc) (pol := xv6Pol GT) (gtAdGd GT) Xv6N Unit (protXv6 Lx) nm
        (xv6AxpolWf GT) hA 3 (hA, 2) _ iprop(LK ∗ RNP (hA, 3))
        iprop(∃ (v : Int), issuedFrag nm.xnI v ∗ ⌜AxSpinX6.npRd (gtAdGd GT).gdG v⌝) _ _ Hval Hin)
        $$ H2 [Hfe]
      · iapply (@flowEqDynMono hlc GF _ (AxSpinX2.xG Lx GT nm) (xv6Pol GT) (gtAdGd GT) (hA, 3) _ _
          iprop(LK ∗ RNP (hA, 3) ∗
            ∃ (v : Int), issuedFrag nm.xnI v ∗ ⌜AxSpinX6.npRd (gtAdGd GT).gdG v⌝)
          iprop((LK ∗ RNP (hA, 3)) ∗
            ∃ (v : Int), issuedFrag nm.xnI v ∗ ⌜AxSpinX6.npRd (gtAdGd GT).gdG v⌝)) $$ [] Hfe
        inext
        iintro ⟨Hl, Hn, Hv⟩
        isplitl [Hl Hn]
        · isplitl [Hl]
          · iexact Hl
          · iexact Hn
        · iexact Hv
      iintro H3 _
      iapply (AxSpinX6.wA4 (hlc := hlc) GT nm cpu Hcons t0 t2 v2 Hrow) $$ Hil H3 H1 %rs)
  iintro #Hil H2 H1
  iapply H $$ [$Hil $H2 $H1]

/-- k2: `lw nextpid`, `locked ∗ RNp` drawn from the claim (rule 5). -/
theorem AxSpinX6.wA2 (GT : GdexecT) (nm : Xv6N) (cpu : CPU)
    (Hcons : rvwmoCatConsistent (gtAdGd GT)) (t0 : Nat) (t2 : List Nat) (v2 : BitVec 32)
    (Hrow : AxOpsem.grow (gtAdGd GT) hA = AxSpinX4.aRow t0 t2 v2)
    (Hnowrap : v2.toNat + 1 < 2 ^ 32) :
    ⊢ ISL -∗ AxAnnot.annotOwn (hA, 0) iprop(LK ∗ RNP (hA, 0)) -∗
      AxAnnot.annotOwn (hA, 1) (RHA (hA, 1)) -∗
      ∀ rs : RegFile, TWA ⟨hp cpu aNp rs, 2⟩ := by
  have Hne : 2 ≠ (AxOpsem.grow (gtAdGd GT) hA).length := by rw [Hrow]; simp [AxSpinX4.aRow]
  have Hl0 := AxSpinX6.aL (gtAdGd GT) t0 t2 v2 Hrow 0 _ rfl
  have Hl2 := AxSpinX6.aL (gtAdGd GT) t0 t2 v2 Hrow 2 _ rfl
  have Hadv := advLoad (gtAdGd GT) hA 2 false (paZ nppa) t2 (WeakInterpProj.wbytes 4 v2)
    (by rw [← gxLblGrow]; exact Hl2)
  have H := nshRead (hlc := hlc) (pol := xv6Pol GT) (gtAdGd GT) Xv6N Unit (protXv6 Lx) nm cpu hA
    ΦA 4 (by decide) nppa nppaRam (AxSpinX4.ldkK 4 aInc) 2 Hne Hadv
    iprop(ISL ∗ AxAnnot.annotOwn (hA, 0) iprop(LK ∗ RNP (hA, 0)) ∗
      AxAnnot.annotOwn (hA, 1) (RHA (hA, 1)))
    (fun v rs Hgv => by
      have Hv : v = WeakInterpProj.wbytes 4 v2 := by
        have Hgv' := Hgv
        unfold graphValue at Hgv'
        rw [Hl2] at Hgv'
        simp only [Option.bind_some, lblValue, Option.some.injEq] at Hgv'
        exact Hgv'.symm
      have Hnw : gisW (gtAdGd GT).gdG (hA, 2) = false := by unfold gisW; rw [Hl2]; rfl
      have Hin : ((hA, 0) : Geid) ∈ @Axpol.lobp (xv6Pol GT) (gtAdGd GT) (hA, 2) :=
        acqLobp (gtAdGd GT) Hcons hA 0 2 _ _ _ _ _ _ Hl0 Hl2 rfl (by decide)
      have Hlt : gmoLt (gtAdGd GT).gdG (hA, 0) (hA, 2) :=
        obCatSubGmo (gtAdGd GT) _ _ Hcons
          (acqGob (gtAdGd GT) hA 0 2 _ _ _ _ _ _ Hl0 Hl2 rfl (by decide))
      have Hnowr : ∀ w a v', a ∈ npb Lx → gwritesByte (gtAdGd GT).gdG w a v' →
          WeakRvwmoGraph.gpo (gtAdGd GT).gdG w (hA, 2) → gmoLt (gtAdGd GT).gdG w (hA, 2) := by
        intro w a v' Ha Hw Hpo
        exfalso
        obtain ⟨k', rfl, Hk, Hc⟩ := aWrBefore (gtAdGd GT) t0 t2 v2 Hrow w a v' 2 Hw Hpo
        rw [npbLx] at Ha
        simp only [lkZV, lcZV, npZV] at Ha Hc
        omega
      have Hsing : ⊢ ([∗map] Rin ∈ ({[((hA, 0) : Geid) := iprop(LK ∗ RNP (hA, 0))]} : Mea GF),
          Rin) -∗ iprop(LK ∗ RNP (hA, 0)) := by
        iintro H
        iapply (BigSepM.bigSepM_singleton (M := GMapF Geid)).1 $$ H
      iintro ⟨#Hil, H0, H1⟩
      ihave Hw := Hsing
      ihave Hfe := (fxNpRead (hlc := hlc) Lx GT nm LxOk Hcons (hA, 2) (hA, 0) LK
        ({[((hA, 0) : Geid) := iprop(LK ∗ RNP (hA, 0))]} : Mea GF) Hnw Hlt Hnowr) $$ Hw
      iapply (evDraw (hlc := hlc) (pol := xv6Pol GT) (gtAdGd GT) Xv6N Unit (protXv6 Lx) nm
        (xv6AxpolWf GT) hA 2 (hA, 0) _ iprop(LK ∗ NPFA) iprop(True) _ _ Hgv Hin) $$ H0 [Hfe]
      · iapply (@flowEqDynMono hlc GF _ (AxSpinX2.xG Lx GT nm) (xv6Pol GT) (gtAdGd GT) (hA, 2) _ _
          iprop(LK ∗ NPFA) iprop((LK ∗ NPFA) ∗ True)) $$ [] Hfe
        inext
        iintro H
        isplitl [H]
        · iexact H
        · itrivial
      iintro H2 _
      subst Hv
      rw [wordOfBytesWbytes]
      iapply (AxSpinX6.wA3 (hlc := hlc) GT nm cpu Hcons t0 t2 v2 Hrow Hnowrap) $$ Hil H2 H1 %rs)
  iintro #Hil H0 H1
  iapply H $$ [$Hil $H0 $H1]

/-- k1: `sd lk->cpu ← cpuAddr A` -- `RCpu` drawn from the claim (rule 5), Φ_cpu from the
value. -/
theorem AxSpinX6.wA1 (GT : GdexecT) (nm : Xv6N) (cpu : CPU)
    (Hcons : rvwmoCatConsistent (gtAdGd GT)) (t0 : Nat) (t2 : List Nat) (v2 : BitVec 32)
    (Hrow : AxOpsem.grow (gtAdGd GT) hA = AxSpinX4.aRow t0 t2 v2)
    (Hnowrap : v2.toNat + 1 < 2 ^ 32) :
    ⊢ ISL -∗ AxAnnot.annotOwn (hA, 0) iprop(LK ∗ RNP (hA, 0)) -∗
      AxAnnot.annotOwn (hA, 0) (RCPU (hA, 0)) -∗
      ∀ rs : RegFile, TWA ⟨hp cpu aCs rs, 1⟩ := by
  have Hne : 1 ≠ (AxOpsem.grow (gtAdGd GT) hA).length := by rw [Hrow]; simp [AxSpinX4.aRow]
  have Hl0 := AxSpinX6.aL (gtAdGd GT) t0 t2 v2 Hrow 0 _ rfl
  have Hl1 := AxSpinX6.aL (gtAdGd GT) t0 t2 v2 Hrow 1 _ rfl
  have H := nshWrite (hlc := hlc) (pol := xv6Pol GT) (gtAdGd GT) Xv6N Unit (protXv6 Lx) nm cpu hA
    ΦA 8 lcpa lcpaRam cpA aNp 1 Hne
    iprop(ISL ∗ AxAnnot.annotOwn (hA, 0) iprop(LK ∗ RNP (hA, 0)) ∗
      AxAnnot.annotOwn (hA, 0) (RCPU (hA, 0)))
    (fun rs => by
      have Hval := gdataStA GT 1 _ 8 cpA _ Hl1
      obtain ⟨Hw1, Hsg1⟩ := gwbStoren _ _ _ _ _ Hl1
      have Hin : ((hA, 0) : Geid) ∈ @Axpol.lobp (xv6Pol GT) (gtAdGd GT) (hA, 1) :=
        acqLobp (gtAdGd GT) Hcons hA 0 1 _ _ _ _ _ _ Hl0 Hl1 rfl (by decide)
      have Hlt : gmoLt (gtAdGd GT).gdG (hA, 0) (hA, 1) :=
        obCatSubGmo (gtAdGd GT) _ _ Hcons
          (acqGob (gtAdGd GT) hA 0 1 _ _ _ _ _ _ Hl0 Hl1 rfl (by decide))
      have Hisw : gisW (gtAdGd GT).gdG (hA, 1) = true := by unfold gisW; rw [Hl1]; rfl
      have Hwr : ∀ (j : Nat) a v, (clb Lx)[j]? = some a → (cvx hA)[j]? = some v →
          gwritesByte (gtAdGd GT).gdG (hA, 1) a v := by
        intro j a v Hj Hv
        rw [clbLcpa] at Hj
        obtain ⟨rfl, -⟩ := AxSpinX4.clRangeLookup _ _ _ _ Hj
        exact Hw1 j v Hv
      have Hsg : ∀ a v, gwritesByte (gtAdGd GT).gdG (hA, 1) a v → a ∈ clb Lx := by
        intro a v Hw
        obtain ⟨j, Hj, rfl⟩ := Hsg1 a v Hw
        have hj := (List.getElem?_eq_some_iff.1 Hj).1
        rw [wbytesLength] at hj
        rw [clbLx]
        simp only [lkZV, lcZV]
        omega
      have Hw0 : ⊢ ([∗map] Rin ∈ ({[((hA, 0) : Geid) := RCPU (hA, 0)]} : Mea GF), Rin) -∗
          iprop(True ∗ ∃ vold, RVL nm.xnH (gtAdGd GT) (clb Lx) (hA, 0) vold) := by
        iintro H
        ihave H := (BigSepM.bigSepM_singleton (M := GMapF Geid)).1 $$ H
        isplitr
        · itrivial
        · iunfold RCpu at H
          iexact H
      iintro ⟨#Hil, H0, H0c⟩
      ihave Hw := Hw0
      ihave Hfe := (fxCpuWrite (hlc := hlc) Lx GT nm LxOk Hcons (hA, 1) (hA, 0) (cvx hA)
        iprop(True) ({[((hA, 0) : Geid) := RCPU (hA, 0)]} : Mea GF) Hisw Hlt (Or.inl rfl) Hwr Hsg)
        $$ Hw
      iapply (evDraw (hlc := hlc) (pol := xv6Pol GT) (gtAdGd GT) Xv6N Unit (protXv6 Lx) nm
        (xv6AxpolWf GT) hA 1 (hA, 0) _ (RHA (hA, 1)) iprop(True) _ _ Hval Hin) $$ H0c [Hfe]
      · iapply (@flowEqDynMono hlc GF _ (AxSpinX2.xG Lx GT nm) (xv6Pol GT) (gtAdGd GT) (hA, 1) _ _
          (RHA (hA, 1)) iprop(RHA (hA, 1) ∗ True)) $$ [] Hfe
        inext
        iintro H
        isplitl [H]
        · iexact H
        · itrivial
      iintro H1 _
      iapply (AxSpinX6.wA2 (hlc := hlc) GT nm cpu Hcons t0 t2 v2 Hrow Hnowrap) $$ Hil H0 H1 %rs)
  iintro #Hil H0 H0c
  iapply H $$ [$Hil $H0 $H0c]

/-- k0 (write half): the CLAIM, `notheld` in hand; `RPid` deposited in two fragments. -/
theorem AxSpinX6.wA0w (GT : GdexecT) (nm : Xv6N) (cpu : CPU)
    (Hcons : rvwmoCatConsistent (gtAdGd GT)) (t0 : Nat) (t2 : List Nat) (v2 : BitVec 32)
    (Hrow : AxOpsem.grow (gtAdGd GT) hA = AxSpinX4.aRow t0 t2 v2)
    (Hnowrap : v2.toNat + 1 < 2 ^ 32) :
    ⊢ ISL -∗ notheld (GF := GF) nm.xnReg Lx.xlLk hA -∗
      ∀ rs : RegFile, TWA ⟨hp cpu (amoW aCs hlt zero32) rs, 0⟩ := by
  have Hne : 0 ≠ (AxOpsem.grow (gtAdGd GT) hA).length := by rw [Hrow]; simp [AxSpinX4.aRow]
  have Hl0 := AxSpinX6.aL (gtAdGd GT) t0 t2 v2 Hrow 0 _ rfl
  have H := nshRmwWrite (hlc := hlc) (pol := xv6Pol GT) (gtAdGd GT) Xv6N Unit (protXv6 Lx) nm cpu
    hA ΦA 4 lkpa lkpaRam one32 (if zero32 = zero32 then aCs else hlt) 0 Hne
    iprop(ISL ∗ notheld (GF := GF) nm.xnReg Lx.xlLk hA)
    (fun rs => by
      have Hval : graphData (gtAdGd GT) (hA, 0) = some (WeakInterpProj.wbytes 4 one32) := by
        unfold graphData; rw [Hl0]; rfl
      obtain ⟨Hr0, Hw0, Hsg0, -⟩ := gwbRmwn _ _ _ _ _ _ _ Hl0
      have Hcl : lkClaim Lx.xlLk (gtAdGd GT).gdG (hA, 0) (gwriteAt (gtAdGd GT).gdG t0) := by
        refine ⟨t0, ?_, rfl, ?_⟩
        · have H := Hr0 0 t0 b0 rfl (by decide +kernel)
          rw [AxSpinX5.addZero] at H
          exact H
        · have H := Hw0 0 b1 (by decide +kernel)
          rw [AxSpinX5.addZero] at H
          exact H
      have Hlw : ∀ a v', gwritesByte (gtAdGd GT).gdG (hA, 0) a v' → a ∈ lwb Lx := by
        intro a v' Hw
        obtain ⟨j, Hj, rfl⟩ := Hsg0 a v' Hw
        have hj := (List.getElem?_eq_some_iff.1 Hj).1
        simp only [AxSpinX4.o4, wbytesLength] at hj
        exact (lwbLx _).2 ⟨by omega, by omega⟩
      iintro ⟨#Hil, Hnh⟩
      ihave Hfe := (fxClaim (hlc := hlc) Lx GT nm LxOk Hcons (hA, 0) (gwriteAt (gtAdGd GT).gdG t0)
        Hcl Hlw) $$ Hnh Hil
      iapply (evPlain (hlc := hlc) (pol := xv6Pol GT) (gtAdGd GT) Xv6N Unit (protXv6 Lx) nm hA 0
        iprop(LK ∗ RNP (hA, 0)) (RCPU (hA, 0)) _ _ Hval) $$ [Hfe]
      · iapply (@flowEqDynMono hlc GF _ (AxSpinX2.xG Lx GT nm) (xv6Pol GT) (gtAdGd GT) (hA, 0) _
          (∅ : Mea GF)
          iprop(locked nm.xnReg Lx.xlLk (hA, 0).1 (hA, 0) ∗
            RPid Lx nm.xnH nm.xnM nm.xnI (gtAdGd GT) (hA, 0))
          iprop((LK ∗ RNP (hA, 0)) ∗ RCPU (hA, 0))) $$ [] Hfe
        inext
        iintro ⟨Hl, HR⟩
        iunfold RPid at HR
        icases HR with ⟨Hc, Hn⟩
        isplitl [Hl Hn]
        · isplitl [Hl]
          · iexact Hl
          · iexact Hn
        · iexact Hc
      iintro H0 H0c
      rw [amoClaimNext]
      iapply (AxSpinX6.wA1 (hlc := hlc) GT nm cpu Hcons t0 t2 v2 Hrow Hnowrap) $$ Hil H0 H0c %rs)
  iintro #Hil Hnh
  iapply H $$ [$Hil $Hnh]

theorem AxSpinX6.wpdA (GT : GdexecT) (nm : Xv6N) (cpu : CPU)
    (Hcons : rvwmoCatConsistent (gtAdGd GT)) (t0 : Nat) (t2 : List Nat) (v2 : BitVec 32)
    (Hrow : AxOpsem.grow (gtAdGd GT) hA = AxSpinX4.aRow t0 t2 v2)
    (Hnowrap : v2.toNat + 1 < 2 ^ 32) :
    ⊢ ISL -∗ notheld (GF := GF) nm.xnReg Lx.xlLk hA -∗
      TWA ⟨hp cpu AxSpinX4.aM0 zeroRegs, 0⟩ := by
  have Hne : 0 ≠ (AxOpsem.grow (gtAdGd GT) hA).length := by rw [Hrow]; simp [AxSpinX4.aRow]
  have H := nshRmwRead (hlc := hlc) (pol := xv6Pol GT) (gtAdGd GT) Xv6N Unit (protXv6 Lx) nm cpu
    hA ΦA 4 (by decide) lkpa lkpaRam (amoK aCs hlt) 0 [t0, t0, t0, t0] AxSpinX4.z4 AxSpinX4.o4
    .WCplain Hne (by rw [Hrow]; rfl)
    iprop(ISL ∗ notheld (GF := GF) nm.xnReg Lx.xlLk hA)
    (fun rs => by
      iintro ⟨#Hil, Hnh⟩
      rw [acqAfterClaim]
      iapply (AxSpinX6.wA0w (hlc := hlc) GT nm cpu Hcons t0 t2 v2 Hrow Hnowrap) $$ Hil Hnh %rs)
  iintro #Hil Hnh
  iapply H $$ [$Hil $Hnh] %zeroRegs

end wpdA

/-! # 3. The race hart A' at the TRIVIAL protocol (sanity twin) -/

section wpdR
variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF] [AxannotGS GF]

theorem feTrivx (GT : GdexecT) (e : Geid) (s0 : GSet Geid) (fi : Mea GF) :
    ⊢ @flowEqDyn hlc GF _ (shG (gtAdGd GT) Unit Unit trivOb ()) (gtAdGd GT) e s0 fi
      iprop(True ∗ True) :=
  feTriv (hlc := hlc) (pol := xv6Pol GT) (gtAdGd GT) e s0 fi

theorem AxSpinX6.wpdRTriv (GT : GdexecT) (cpu : CPU)
    (Hrow : AxOpsem.grow (gtAdGd GT) hA = AxSpinX4.rRow) :
    ⊢ @tierAWpd GF hlc _ _ (xv6Pol GT) (gtAdGd GT) Unit Unit trivOb ()
      ⟨hp cpu AxSpinX4.rM0 zeroRegs, 0⟩ .MaybeStuck hA (fun _ => iprop(True)) := by
  have Hne : 0 ≠ (AxOpsem.grow (gtAdGd GT) hA).length := by rw [Hrow]; simp [AxSpinX4.rRow]
  have Hl0 : gxLbl (gtAdGd GT).gdG (hA, 0) =
      some (.LStore false (paZ lcpa) (WeakInterpProj.wbytes 8 cpA) .WCplain) := by
    rw [gxLblGrow, Hrow]; rfl
  have H := nshWrite (hlc := hlc) (GF := GF) (pol := xv6Pol GT) (gtAdGd GT) Unit Unit trivOb ()
    cpu hA (fun _ => iprop(True)) 8 lcpa lcpaRam cpA hlt 0 Hne iprop(True)
    (fun rs => by
      have Hval : graphData (gtAdGd GT) (hA, 0) = some (WeakInterpProj.wbytes 8 cpA) := by
        unfold graphData; rw [Hl0]; rfl
      iintro _
      iapply (evPlain (hlc := hlc) (pol := xv6Pol GT) (gtAdGd GT) Unit Unit trivOb () hA 0
        iprop(True) iprop(True) _ _ Hval) $$ []
      · iapply feTrivx
      iintro _ _
      iapply (shHltTrue (hlc := hlc) (pol := xv6Pol GT) (gtAdGd GT) Unit Unit trivOb () cpu hA
        (0 + 1)) $$ %rs)
  iapply H $$ [] %zeroRegs
  itrivial

end wpdR

end Weak
