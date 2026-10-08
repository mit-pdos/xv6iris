/-
Weak: **Phase 1c, part 5 of the spinlock plan -- HART B's WPd at the joint instance `protXv6 Lx`**
(every class exercised), proved over ANY graph with B's row `AxSpinX4.bRow` (row parameters =
read sources / values).

Rocq: `iris/AxSpinX5.v` @ xxvzwolszwmp.

## The Rocq header, in substance

THE POST `QB` (five facts, each DEPOSITED AT ITS READ by a rule of `AxSpinX2` and read back at
the row end, `shHltReadbackM`):
  F1  the stack reload reads X               (`fxPrivReadn`, private)
  F3  the noff read reads 1                  (`fxPrivReadn`, private)
  F4  the text/PT read reads the image       (`fxRoReadn`, read-only)
  F5  the non-holder lk->cpu read: `rdFact`  (`fxCpuRacy`, Φ_cpu)
  F10 the HOLDER's lk->cpu read reads `cvx B` ((b): `fxOwnedRead` when B's `sd lk->cpu` is
      gmo-before the read -- the handle drawn from the sd's annotation -- else `fxFwdRead`,
      forwarding; the WPd CASE-SPLITS on the pinned graph in phase 1).
THE CS: claim (`fxClaim`, `RPid` split into `locked ∗ RNp` and `RCpu` at the claim),
`sd lk->cpu ← cvx B` (`fxCpuWrite`, `RCpu` drawn from the claim, rule 5), `lw nextpid`
(`fxNpRead`, `RNp` drawn from the claim), `sw nextpid ← v+1` (`fxNpIncr`, drawn from the lw by
ppo rule 1; ●mono and ◯{v} minted), `sd lk->cpu ← 0` (`fxCpuWrite`, drawn from the holder read
or the first sd), fence, release (`fxReleasePid`: lk->cpu from (B,11), nextpid ∗ locked from
(B,9), both through the fence).
ROW PREMISE beyond the shape: `Hnowrap` (the nextpid value read is not 2³²−1).

## Deviations from Rocq

1. VOCABULARY (as `AxSpinX2` deviation 1): `Z` ↦ `Int`, `bv n` ↦ `BitVec n`, `gd_g GD` ↦
   `GD.gdG`, `gx_img G a` ↦ `G.gxImg a`, `l !! j` ↦ `l[j]?` (indices typed `Nat`), `cl_range` ↦
   `clRange`, `pa_z` ↦ `paZ`, `Z_to_bv 32` ↦ `BitVec.ofInt 32`, `bv_add v8 one32` ↦
   `v8 + one32`, `bv_unsigned v8` ↦ `v8.toNat` (so `Hnowrap : v8.toNat + 1 < 2 ^ 32`, over
   `Nat`), `0 ≤ v < 2^32` ↦ `0 ≤ v ∧ v < 2 ^ 32`, `a < b < c` ↦ `a ≤ b ∧ b < c`,
   `init_regstate` ↦ `zeroRegs`, `AThread p k` ↦ `⟨p, k⟩`, `gmo_lt_b` ↦ `gmoLtB`.
2. CONTEXTS (as `AxSpinX2` deviation 2): Rocq section variables are explicit leading arguments
   in Rocq's order, only where Rocq's section mechanism includes them (§2 `GD t1 … v8 Hrow`;
   §3 `GT nm cpu`, then `Hcons t1 … v8 Hrow [Hnowrap]` where `Proof using` names them).
   `invGS_gen HasNoLc Σ` ↦ `[InvGS_gen hlc GF]` for any `hlc`; `axannotG Σ`+`axannotGS Σ` ↦
   `[AxannotGS GF]`; `xv6G Σ` ↦ `[AxSpinX.Xv6G GF]`.  The local instances `b_pol`/`b_G` are
   inlined: the policy `xv6Pol GT` and the instance `AxSpinX2.xG Lx GT nm` (= `shG …`) are
   passed explicitly.  O2 STAGE C: Rocq's `Tf` argument of `AxGA2`/`tierA_wpd` is gone.
3. STATEMENT SHAPES: wand chains `A -∗ B` ↦ `⊢ A -∗ B`; the Rocq notations `TWB`/`ΦB`/`LK`/
   `RNP`/`RCPU`/`ISL`/`FB`/`RH`/`NPF` are file-local Lean notations with the same expansions
   (`OB`/`RP`/`SH`/`HwfG` unfolded); `NPF`'s read fact is the Lean-only reducible
   `AxSpinX5.npRd`.  `F1`…`F10` are `abbrev`s (Rocq `Definition`s) so that proof-mode
   unification sees through them against the rules' literal facts.
4. PROOFS: `wB14`'s `pose (m := …)` is the chain of Lean-only reducible maps
   `AxSpinX5.mB10/mB5/mB4/mB3/mB`; the `zv` Ltac is inlined as `simp only [lkZV, …]`; Rocq
   `vm_compute` facts by `decide +kernel`; `destruct (gmo_lt_b …) eqn:Hb` ↦
   `cases Hb : gmoLtB …` with `gmoLtBSpec`.
5. `wbytes8_inj'` is kept as `wbytes8Inj'` (same statement as `AxSpinX.wbytes8Inj`).

**Rocq → Lean name map.**  `lbl_ts_len` `lblTsLen`, `loadn_reads` `loadnReads`,
`read_fact_word` `readFactWord`, `wbytes4_inj` `wbytes4Inj`, `wbytes8_inj'` `wbytes8Inj'`,
`np_succ` `npSucc`, `bL` `AxSpinX5.bL` (dup), `b_wr` `AxSpinX5.bWr` (dup), `b_wr_po` `bWrPo`,
`F1` `AxSpinX5.F1` (dup), `F3` `F3`, `F4` `F4`, `F5` `F5`, `F10` `F10`, `QB` `QB`,
`adv_load` `advLoad`, `gdata_st` `gdataSt`, `wB14` `wB14`, `wB13` `wB13`, `wB12` `wB12`,
`wB11` `wB11`, `b_wr_before` `bWrBefore`, `wB10` `AxSpinX5.wB10` (dup), `wB9` `AxSpinX5.wB9`
(dup), `wB8` `AxSpinX5.wB8` (dup), `wB7` `wB7`, `wB6w` `wB6w`, `wB6` `AxSpinX5.wB6` (dup),
`wB5` `AxSpinX5.wB5` (dup), `wB4` `AxSpinX5.wB4` (dup), `wB3` `AxSpinX5.wB3` (dup), `wB2`
`AxSpinX5.wB2` (dup), `wB1` `wB1`, `wpdB` `AxSpinX5.wpdB` (dup).  Lean-only (file-qualified):
`AxSpinX5.mB10`, `AxSpinX5.mB5`, `AxSpinX5.mB4`, `AxSpinX5.mB3`, `AxSpinX5.mB` (wB14's map),
`AxSpinX5.npRd` (`NPF`'s read fact), `AxSpinX5.addZero` (`x + ((0 : Nat) : Int) = x`, Rocq's
`rewrite Z.add_0_r`).

**Dropped:** none (36 Rocq decls incl. the 2 local instances `b_pol`/`b_G` (inlined) and not
counting the `zv` Ltac; 41 Lean = 34 + 7 Lean-only).
-/
import Weak.AxSpinProt7b
import Weak.AxSpinX2
import Weak.AxSpinX4

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D

/-! # 1. Generic row facts -/

theorem lblTsLen (G : Gexec) (Hwf : gwf G) (e : Geid) (aq : Bool) (base : Int) (ts : List Nat)
    (vs : List (BitVec 8)) : gxLbl G e = some (.LLoad aq base ts vs) → vs.length = ts.length := by
  unfold gxLbl
  cases Hp : G.gxProg[e.1]? with
  | none => intro Hl; simp at Hl
  | some p =>
    intro Hl
    exact Hwf.2.2 e.1 p e.2 _ Hp Hl

/-- The bytes of an n-byte load: every byte is read (lengths from gwf). -/
theorem loadnReads (G : Gexec) (Hwf : gwf G) (e : Geid) (base : Int) (ts : List Nat) (n : Nat)
    (v : BitVec (8 * n)) (j : Nat) :
    gxLbl G e = some (.LLoad false base ts (WeakInterpProj.wbytes n v)) → j < n →
    ∃ t, greadsByte G e (base + (j : Int)) t (nthByte v j) := by
  intro Hl Hj
  have Hlen := lblTsLen G Hwf e false base ts _ Hl
  rw [wbytesLength] at Hlen
  have Ht : ts[j]? = some (ts[j]'(by omega)) := List.getElem?_eq_getElem _
  exact ⟨_, (grbLoadn G e base ts _ Hl).1 j _ _ Ht (wbytesLookup n v j Hj)⟩

/-- A fact "each byte `j` of `Cw` read by `e` is `vs[j]?`" pins the label's word, when every byte
is read. -/
theorem readFactWord (G : Gexec) (Hwf : gwf G) (e : Geid) (base : Int) (ts : List Nat) (n : Nat)
    (v : BitVec (8 * n)) (vs : List (BitVec 8)) :
    gxLbl G e = some (.LLoad false base ts (WeakInterpProj.wbytes n v)) → vs.length = n →
    (∀ (j : Nat) a t b, (clRange base n)[j]? = some a → greadsByte G e a t b → vs[j]? = some b) →
    WeakInterpProj.wbytes n v = vs := by
  intro Hl Hlv Hf
  apply List.ext_getElem?
  intro j
  by_cases Hj : j < n
  · obtain ⟨t, Hr⟩ := loadnReads G Hwf e base ts n v j Hl Hj
    rw [wbytesLookup n v j Hj]
    exact (Hf j _ t _ (clRangeLookup2 base n j Hj) Hr).symm
  · rw [List.getElem?_eq_none (by rw [wbytesLength]; omega), List.getElem?_eq_none (by omega)]

theorem wbytes4Inj (a b : BitVec 32) :
    WeakInterpProj.wbytes 4 a = WeakInterpProj.wbytes 4 b → a = b := by
  intro H
  have ha := wordOfBytesWbytes 4 a
  have hb := wordOfBytesWbytes 4 b
  rw [H] at ha
  exact ha.symm.trans hb

theorem wbytes8Inj' (a b : BitVec 64) :
    WeakInterpProj.wbytes 8 a = WeakInterpProj.wbytes 8 b → a = b := by
  intro H
  have ha := wordOfBytesWbytes 8 a
  have hb := wordOfBytesWbytes 8 b
  rw [H] at ha
  exact ha.symm.trans hb

/-- The nextpid increment at the word level. -/
theorem npSucc (v : Int) (v8 : BitVec 32) :
    0 ≤ v ∧ v < 2 ^ 32 → BitVec.ofInt 32 v = v8 → v8.toNat + 1 < 2 ^ 32 →
    v + 1 < 2 ^ 32 ∧ BitVec.ofInt 32 (v + 1) = v8 + one32 := by
  intro Hv Heq Hnw
  subst Heq
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le Hv.1
  have hn : n < 4294967296 := by have := Hv.2; omega
  have Hu : (BitVec.ofInt 32 (n : Int)).toNat = n := by
    rw [BitVec.toNat_ofInt]
    omega
  rw [Hu] at Hnw
  refine ⟨by omega, ?_⟩
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, Hu, BitVec.toNat_ofInt, show one32.toNat = 1 from by decide]
  omega

/-! # 2. Hart B's row facts -/

section rowB

theorem AxSpinX5.bL (GD : Gdexec) (t1 t3 t4 t5 : List Nat) (t6 : Nat) (t8 t10 : List Nat)
    (v1 v4 v5 v10 : BitVec 64) (v3 v8 : BitVec 32)
    (Hrow : AxOpsem.grow GD hB = AxSpinX4.bRow t1 t3 t4 t5 t6 t8 t10 v1 v4 v5 v10 v3 v8)
    (k : Nat) (lb : Lbl) :
    (AxSpinX4.bRow t1 t3 t4 t5 t6 t8 t10 v1 v4 v5 v10 v3 v8)[k]? = some lb →
    gxLbl GD.gdG (hB, k) = some lb := by
  intro Hk
  rw [gxLblGrow, Hrow]
  exact Hk

/-- Hart B's writes, by position and address range. -/
theorem AxSpinX5.bWr (GD : Gdexec) (t1 t3 t4 t5 : List Nat) (t6 : Nat) (t8 t10 : List Nat)
    (v1 v4 v5 v10 : BitVec 64) (v3 v8 : BitVec 32)
    (Hrow : AxOpsem.grow GD hB = AxSpinX4.bRow t1 t3 t4 t5 t6 t8 t10 v1 v4 v5 v10 v3 v8)
    (k : Nat) (a : Int) (v : BitVec 8) :
    gwritesByte GD.gdG (hB, k) a v →
    (k = 0 ∧ paZ skpa ≤ a ∧ a < paZ skpa + 8) ∨ (k = 2 ∧ paZ nfpa ≤ a ∧ a < paZ nfpa + 4) ∨
    (k = 6 ∧ paZ lkpa ≤ a ∧ a < paZ lkpa + 4) ∨ (k = 7 ∧ paZ lcpa ≤ a ∧ a < paZ lcpa + 8) ∨
    (k = 9 ∧ paZ nppa ≤ a ∧ a < paZ nppa + 4) ∨ (k = 11 ∧ paZ lcpa ≤ a ∧ a < paZ lcpa + 8) ∨
    (k = 13 ∧ paZ lkpa ≤ a ∧ a < paZ lkpa + 4) := by
  rintro ⟨l, base, vs, j, Hl, Hwr, Hv, Ha⟩
  rw [gxLblGrow, Hrow] at Hl
  have Hj := (List.getElem?_eq_some_iff.1 Hv).1
  unfold accAddr at Ha
  subst Ha
  rcases k with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k <;>
    simp [AxSpinX4.bRow] at Hl
  all_goals (subst Hl; simp only [lbWr, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at Hwr)
  all_goals (obtain ⟨rfl, rfl⟩ := Hwr)
  all_goals (simp only [wbytesLength, AxSpinX4.z4, AxSpinX4.o4] at Hj; omega)

theorem bWrPo (GD : Gdexec) (t1 t3 t4 t5 : List Nat) (t6 : Nat) (t8 t10 : List Nat)
    (v1 v4 v5 v10 : BitVec 64) (v3 v8 : BitVec 32)
    (Hrow : AxOpsem.grow GD hB = AxSpinX4.bRow t1 t3 t4 t5 t6 t8 t10 v1 v4 v5 v10 v3 v8)
    (k : Nat) (a : Int) (v : BitVec 8) :
    gwritesByte GD.gdG (hB, k) a v → ∀ k', k < k' →
    (k' ≤ 2 → paZ skpa ≤ a ∧ a < paZ skpa + 8) ∧
    (k' ≤ 7 → ((paZ skpa ≤ a ∧ a < paZ skpa + 8) ∨ (paZ nfpa ≤ a ∧ a < paZ nfpa + 4) ∨
                (paZ lkpa ≤ a ∧ a < paZ lkpa + 4))) := by
  intro Hw k' Hk
  have H := AxSpinX5.bWr GD t1 t3 t4 t5 t6 t8 t10 v1 v4 v5 v10 v3 v8 Hrow k a v Hw
  refine ⟨fun h => ?_, fun h => ?_⟩ <;> omega

end rowB

/-! # 3. Hart B's WPd -/

abbrev AxSpinX5.F1 (G : Gexec) : Prop :=
  ∀ (j : Nat) a t v, (clRange (paZ skpa) 8)[j]? = some a → greadsByte G (hB, 1) a t v →
    (WeakInterpProj.wbytes 8 Xv)[j]? = some v
abbrev F3 (G : Gexec) : Prop :=
  ∀ (j : Nat) a t v, (clRange (paZ nfpa) 4)[j]? = some a → greadsByte G (hB, 3) a t v →
    (WeakInterpProj.wbytes 4 one32)[j]? = some v
abbrev F4 (G : Gexec) : Prop :=
  ∀ a t v, a ∈ clRange (paZ ropa) 8 → greadsByte G (hB, 4) a t v → t = 0 ∧ G.gxImg a = some v
abbrev F5 (G : Gexec) : Prop := rdFact (clb Lx) cvx G (hB, 5)
abbrev F10 (G : Gexec) : Prop :=
  ∀ (j : Nat) a t v, (clb Lx)[j]? = some a → greadsByte G (hB, 10) a t v → (cvx hB)[j]? = some v
def QB (G : Gexec) : Prop := AxSpinX5.F1 G ∧ F3 G ∧ F4 G ∧ F5 G ∧ F10 G

theorem advLoad (GD : Gdexec) (i k : Nat) (aq : Bool) (base : Int) (ts : List Nat)
    (vs : List (BitVec 8)) :
    (AxOpsem.grow GD i)[k]? = some (.LLoad aq base ts vs) →
    ∀ lb, (AxOpsem.grow GD i)[k]? = some lb → aidentAdvRd (aident lb) = 1 := by
  intro H lb H'
  rw [H] at H'
  cases H'
  rfl

/-- Lean-only: `NPF`'s read fact (the nextpid read `(B,8)` reads the bytes of `v`). -/
abbrev AxSpinX5.npRd (G : Gexec) (v : Int) : Prop :=
  ∀ (j : Nat) a t b, (npb Lx)[j]? = some a → greadsByte G (hB, 8) a t b →
    (WeakInterpProj.wbytes 4 (BitVec.ofInt 32 v))[j]? = some b

/-- Lean-only: `wB14`'s readback map (Rocq `pose (m := …)`), innermost first. -/
abbrev AxSpinX5.mB10 {GF : BundledGFunctors.{0,0,0}} (G : Gexec) : Mea GF :=
  {[((hB, 10) : Geid) := iprop(⌜F10 G⌝)]}
abbrev AxSpinX5.mB5 {GF : BundledGFunctors.{0,0,0}} (G : Gexec) : Mea GF :=
  insert (AxSpinX5.mB10 G) (hB, 5) iprop(⌜F5 G⌝)
abbrev AxSpinX5.mB4 {GF : BundledGFunctors.{0,0,0}} (G : Gexec) : Mea GF :=
  insert (AxSpinX5.mB5 G) (hB, 4) iprop(⌜F4 G⌝)
abbrev AxSpinX5.mB3 {GF : BundledGFunctors.{0,0,0}} (G : Gexec) : Mea GF :=
  insert (AxSpinX5.mB4 G) (hB, 3) iprop(⌜F3 G⌝)
abbrev AxSpinX5.mB {GF : BundledGFunctors.{0,0,0}} (G : Gexec) : Mea GF :=
  insert (AxSpinX5.mB3 G) (hB, 1) iprop(⌜AxSpinX5.F1 G⌝)

theorem gdataSt (GT : GdexecT) (k : Nat) (base : Int) (n : Nat) (val : BitVec (8 * n))
    (cls : WmClass) :
    gxLbl (gtAdGd GT).gdG (hB, k) =
      some (.LStore false base (WeakInterpProj.wbytes n val) cls) →
    graphData (gtAdGd GT) (hB, k) = some (WeakInterpProj.wbytes n val) := by
  intro Hl
  unfold graphData
  rw [Hl]
  rfl

/-- po-earlier writes of hart B before position `k` at a given range. -/
theorem bWrBefore (GT : GdexecT) (t1 t3 t4 t5 : List Nat) (t6 : Nat) (t8 t10 : List Nat)
    (v1 v4 v5 v10 : BitVec 64) (v3 v8 : BitVec 32)
    (Hrow : AxOpsem.grow (gtAdGd GT) hB = AxSpinX4.bRow t1 t3 t4 t5 t6 t8 t10 v1 v4 v5 v10 v3 v8)
    (w : Geid) (a : Int) (v : BitVec 8) (k : Nat) :
    gwritesByte (gtAdGd GT).gdG w a v → WeakRvwmoGraph.gpo (gtAdGd GT).gdG w (hB, k) →
    ∃ k', w = (hB, k') ∧ k' < k ∧
      ((k' = 0 ∧ paZ skpa ≤ a ∧ a < paZ skpa + 8) ∨ (k' = 2 ∧ paZ nfpa ≤ a ∧ a < paZ nfpa + 4) ∨
       (k' = 6 ∧ paZ lkpa ≤ a ∧ a < paZ lkpa + 4) ∨ (k' = 7 ∧ paZ lcpa ≤ a ∧ a < paZ lcpa + 8) ∨
       (k' = 9 ∧ paZ nppa ≤ a ∧ a < paZ nppa + 4) ∨
       (k' = 11 ∧ paZ lcpa ≤ a ∧ a < paZ lcpa + 8) ∨
       (k' = 13 ∧ paZ lkpa ≤ a ∧ a < paZ lkpa + 4)) := by
  obtain ⟨wi, wk⟩ := w
  rintro Hw ⟨Hh, Hlt, -, -⟩
  dsimp only at Hh Hlt
  subst Hh
  exact ⟨wk, rfl, Hlt,
    AxSpinX5.bWr (gtAdGd GT) t1 t3 t4 t5 t6 t8 t10 v1 v4 v5 v10 v3 v8 Hrow wk a v Hw⟩

theorem AxSpinX5.addZero (x : Int) : x + ((0 : Nat) : Int) = x := by omega

section wpdB
variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF] [AxannotGS GF]
  [AxSpinX.Xv6G GF]

set_option hygiene false in
local notation "ΦB" => (fun _ : Athread => iprop(⌜QB (gtAdGd GT).gdG⌝))
set_option hygiene false in
local notation "TWB " s:max => @tierAWpd GF hlc _ _ (xv6Pol GT) (gtAdGd GT) Xv6N Unit
  (protXv6 Lx) nm s .MaybeStuck hB (fun _ => iprop(⌜QB (gtAdGd GT).gdG⌝))
set_option hygiene false in
local notation "LK" => locked (GF := GF) nm.xnReg Lx.xlLk hB (hB, 6)
set_option hygiene false in
local notation "RNP " e:max => RNp (GF := GF) Lx nm.xnH nm.xnM nm.xnI (gtAdGd GT) e
set_option hygiene false in
local notation "RCPU " e:max => RCpu (GF := GF) Lx nm.xnH (gtAdGd GT) e
set_option hygiene false in
local notation "ISL" =>
  isLock (GF := GF) nm.xnReg Lx.xlLk (RPid Lx nm.xnH nm.xnM nm.xnI (gtAdGd GT))
set_option hygiene false in
local notation "FB" => iprop(AxAnnot.annotOwn (GF := GF) (hB, 1)
    iprop(⌜AxSpinX5.F1 (gtAdGd GT).gdG⌝) ∗
  AxAnnot.annotOwn (hB, 3) iprop(⌜F3 (gtAdGd GT).gdG⌝) ∗
  AxAnnot.annotOwn (hB, 4) iprop(⌜F4 (gtAdGd GT).gdG⌝) ∗
  AxAnnot.annotOwn (hB, 5) iprop(⌜F5 (gtAdGd GT).gdG⌝))
set_option hygiene false in
local notation "RH " e:max =>
  iprop(True ∗ RVL (GF := GF) nm.xnH (gtAdGd GT) (clb Lx) e (cvx hB))
set_option hygiene false in
local notation "NPF" =>
  iprop(∃ (v : Int), RNpv (GF := GF) Lx GT nm (hB, 6) v ∗ ⌜AxSpinX5.npRd (gtAdGd GT).gdG v⌝)

theorem wB14 (GT : GdexecT) (nm : Xv6N) (cpu : CPU) :
    ⊢ FB -∗ AxAnnot.annotOwn (hB, 10) iprop(⌜F10 (gtAdGd GT).gdG⌝) -∗
      ∀ rs : RegFile, TWB ⟨hp cpu hlt rs, 14⟩ := by
  have h5 : get? (AxSpinX5.mB10 (GF := GF) (gtAdGd GT).gdG) (hB, 5) = none :=
    lookupSingletonNe (by decide)
  have h4 : get? (AxSpinX5.mB5 (GF := GF) (gtAdGd GT).gdG) (hB, 4) = none := by
    unfold AxSpinX5.mB5
    rw [lookupInsertNe (by decide)]
    exact h5
  have h3 : get? (AxSpinX5.mB4 (GF := GF) (gtAdGd GT).gdG) (hB, 3) = none := by
    unfold AxSpinX5.mB4 AxSpinX5.mB5
    rw [lookupInsertNe (by decide), lookupInsertNe (by decide)]
    exact lookupSingletonNe (by decide)
  have h1 : get? (AxSpinX5.mB3 (GF := GF) (gtAdGd GT).gdG) (hB, 1) = none := by
    unfold AxSpinX5.mB3 AxSpinX5.mB4 AxSpinX5.mB5
    rw [lookupInsertNe (by decide), lookupInsertNe (by decide), lookupInsertNe (by decide)]
    exact lookupSingletonNe (by decide)
  have Hm : ∀ e, e ∈ (FiniteMap.dom_set (AxSpinX5.mB (GF := GF) (gtAdGd GT).gdG) : GSet Geid) →
      e.1 = hB := by
    intro e He
    unfold AxSpinX5.mB AxSpinX5.mB3 AxSpinX5.mB4 AxSpinX5.mB5 AxSpinX5.mB10 at He
    rw [domInsert, domInsert, domInsert, domInsert, domSingleton] at He
    rcases elemOfUnion.1 He with H | H
    · rw [elemOfSingleton.1 H]
    rcases elemOfUnion.1 H with H | H
    · rw [elemOfSingleton.1 H]
    rcases elemOfUnion.1 H with H | H
    · rw [elemOfSingleton.1 H]
    rcases elemOfUnion.1 H with H | H <;> rw [elemOfSingleton.1 H]
  have HRQ : ([∗map] R ∈ AxSpinX5.mB (GF := GF) (gtAdGd GT).gdG, R) ⊢
      ⌜QB (gtAdGd GT).gdG⌝ := by
    iintro H
    icases (BigSepM.bigSepM_insert h1).1 $$ H with ⟨%H1, H⟩
    icases (BigSepM.bigSepM_insert h3).1 $$ H with ⟨%H3, H⟩
    icases (BigSepM.bigSepM_insert h4).1 $$ H with ⟨%H4, H⟩
    icases (BigSepM.bigSepM_insert h5).1 $$ H with ⟨%H5, H⟩
    ihave %H10 := (BigSepM.bigSepM_singleton (M := GMapF Geid)).1 $$ H
    ipureintro
    exact ⟨H1, H3, H4, H5, H10⟩
  have Hmk : ⊢ FB -∗ AxAnnot.annotOwn (hB, 10) iprop(⌜F10 (gtAdGd GT).gdG⌝) -∗
      [∗map] e ↦ P ∈ AxSpinX5.mB (GF := GF) (gtAdGd GT).gdG, AxAnnot.annotOwn e P := by
    iintro ⟨H1, H3, H4, H5⟩ H10
    iapply (BigSepM.bigSepM_insert h1).2
    isplitl [H1]
    · iexact H1
    iapply (BigSepM.bigSepM_insert h3).2
    isplitl [H3]
    · iexact H3
    iapply (BigSepM.bigSepM_insert h4).2
    isplitl [H4]
    · iexact H4
    iapply (BigSepM.bigSepM_insert h5).2
    isplitl [H5]
    · iexact H5
    iapply BigSepM.bigSepM_singleton.2
    iexact H10
  iintro HF H10
  ihave Hm' := Hmk $$ HF H10
  iapply (shHltReadbackM (hlc := hlc) (pol := xv6Pol GT) (gtAdGd GT) Xv6N Unit (protXv6 Lx) nm
    cpu hB 14 _ Hm _ HRQ) $$ Hm'

/-- THE RELEASE (k13): lk->cpu from (B,11), `locked ∗ RNp` from (B,9). -/
theorem wB13 (GT : GdexecT) (nm : Xv6N) (cpu : CPU) (Hcons : rvwmoCatConsistent (gtAdGd GT))
    (t1 t3 t4 t5 : List Nat) (t6 : Nat) (t8 t10 : List Nat) (v1 v4 v5 v10 : BitVec 64)
    (v3 v8 : BitVec 32)
    (Hrow : AxOpsem.grow (gtAdGd GT) hB = AxSpinX4.bRow t1 t3 t4 t5 t6 t8 t10 v1 v4 v5 v10 v3 v8) :
    ⊢ ISL -∗ AxAnnot.annotOwn (hB, 9) iprop(LK ∗ RNP (hB, 9)) -∗
      AxAnnot.annotOwn (hB, 11) (RCPU (hB, 11)) -∗ FB -∗
      AxAnnot.annotOwn (hB, 10) iprop(⌜F10 (gtAdGd GT).gdG⌝) -∗
      ∀ rs : RegFile, TWB ⟨hp cpu bEnd rs, 13⟩ := by
  have Hne : 13 ≠ (AxOpsem.grow (gtAdGd GT) hB).length := by rw [Hrow]; simp [AxSpinX4.bRow]
  have Hl9 := AxSpinX5.bL (gtAdGd GT) t1 t3 t4 t5 t6 t8 t10 v1 v4 v5 v10 v3 v8 Hrow 9 _ rfl
  have Hl11 := AxSpinX5.bL (gtAdGd GT) t1 t3 t4 t5 t6 t8 t10 v1 v4 v5 v10 v3 v8 Hrow 11 _ rfl
  have Hl12 := AxSpinX5.bL (gtAdGd GT) t1 t3 t4 t5 t6 t8 t10 v1 v4 v5 v10 v3 v8 Hrow 12 _ rfl
  have Hl13 := AxSpinX5.bL (gtAdGd GT) t1 t3 t4 t5 t6 t8 t10 v1 v4 v5 v10 v3 v8 Hrow 13 _ rfl
  have hnone : get? ({[((hB, 11) : Geid) := RCPU (hB, 11)]} : Mea GF) (hB, 9) = none :=
    lookupSingletonNe (by decide)
  have H := nshWrite (hlc := hlc) (pol := xv6Pol GT) (gtAdGd GT) Xv6N Unit (protXv6 Lx) nm cpu hB
    ΦB 4 lkpa lkpaRam zero32 hlt 13 Hne
    iprop(ISL ∗ AxAnnot.annotOwn (hB, 9) iprop(LK ∗ RNP (hB, 9)) ∗
      AxAnnot.annotOwn (hB, 11) (RCPU (hB, 11)) ∗ FB ∗
      AxAnnot.annotOwn (hB, 10) iprop(⌜F10 (gtAdGd GT).gdG⌝))
    (fun rs => by
      have Hval := gdataSt GT 13 _ 4 zero32 _ Hl13
      obtain ⟨Hw13, Hsg13⟩ := gwbStoren _ _ _ _ _ Hl13
      have Hzw : zw Lx.xlLk (gtAdGd GT).gdG (hB, 13) := by
        have H := Hw13 0 b0 (by decide +kernel)
        rw [AxSpinX5.addZero] at H
        exact H
      have Hlw : ∀ a v', gwritesByte (gtAdGd GT).gdG (hB, 13) a v' → a ∈ lwb Lx := by
        intro a v' Hw
        obtain ⟨j, Hj, rfl⟩ := Hsg13 a v' Hw
        have hj := (List.getElem?_eq_some_iff.1 Hj).1
        simp only [AxSpinX4.z4, wbytesLength] at hj
        exact (lwbLx _).2 ⟨by omega, by omega⟩
      have Hob9 : gobCat (gtAdGd GT) (hB, 9) (hB, 13) :=
        fenceGob (gtAdGd GT) hB 9 12 13 _ _ _ _ Hl9 rfl Hl12 Hl13 (by decide) (by decide)
      have Hob11 : gobCat (gtAdGd GT) (hB, 11) (hB, 13) :=
        fenceGob (gtAdGd GT) hB 11 12 13 _ _ _ _ Hl11 rfl Hl12 Hl13 (by decide) (by decide)
      have Hsub : (FiniteMap.dom_set (insert ({[((hB, 11) : Geid) := RCPU (hB, 11)]} : Mea GF)
          (hB, 9) iprop(LK ∗ RNP (hB, 9))) : GSet Geid) ⊆
          @Axpol.lobp (xv6Pol GT) (gtAdGd GT) (hB, 13) := by
        have H9 : ((hB, 9) : Geid) ∈ @Axpol.lobp (xv6Pol GT) (gtAdGd GT) (hB, 13) :=
          fenceLobp (gtAdGd GT) Hcons hB 9 12 13 _ _ _ _ Hl9 rfl Hl12 Hl13 (by decide) (by decide)
        have H11 : ((hB, 11) : Geid) ∈ @Axpol.lobp (xv6Pol GT) (gtAdGd GT) (hB, 13) :=
          fenceLobp (gtAdGd GT) Hcons hB 11 12 13 _ _ _ _ Hl11 rfl Hl12 Hl13 (by decide)
            (by decide)
        rw [domInsert, domSingleton]
        intro x hx
        rcases elemOfUnion.1 hx with h | h
        · rw [elemOfSingleton.1 h]; exact H9
        · rw [elemOfSingleton.1 h]; exact H11
      have Hmk : ⊢ AxAnnot.annotOwn (hB, 9) iprop(LK ∗ RNP (hB, 9)) -∗
          AxAnnot.annotOwn (hB, 11) (RCPU (hB, 11)) -∗
          [∗map] e ↦ P ∈ (insert ({[((hB, 11) : Geid) := RCPU (hB, 11)]} : Mea GF) (hB, 9)
            iprop(LK ∗ RNP (hB, 9))), AxAnnot.annotOwn e P := by
        iintro Ha Hb
        iapply (BigSepM.bigSepM_insert hnone).2
        isplitl [Ha]
        · iexact Ha
        · iapply BigSepM.bigSepM_singleton.2
          iexact Hb
      have Hsplit : ⊢ ([∗map] Rin ∈ (insert ({[((hB, 11) : Geid) := RCPU (hB, 11)]} : Mea GF)
          (hB, 9) iprop(LK ∗ RNP (hB, 9))), Rin) -∗
          iprop(locked nm.xnReg Lx.xlLk hB (hB, 6) ∗ RCpu Lx nm.xnH (gtAdGd GT) (hB, 11) ∗
            RNp Lx nm.xnH nm.xnM nm.xnI (gtAdGd GT) (hB, 9)) := by
        iintro H
        icases (BigSepM.bigSepM_insert hnone).1 $$ H with ⟨⟨Hlk, HN⟩, HC⟩
        ihave HC := (BigSepM.bigSepM_singleton (M := GMapF Geid)).1 $$ HC
        isplitl [Hlk]
        · iexact Hlk
        isplitl [HC]
        · iexact HC
        · iexact HN
      iintro ⟨#Hil, H9, H11, HF, H10⟩
      ihave Hm := Hmk $$ H9 H11
      ihave Hw := Hsplit
      ihave Hfe := (fxReleasePid (hlc := hlc) Lx GT nm LxOk Hcons (hB, 13) hB (hB, 6) (hB, 11)
        (hB, 9) (insert ({[((hB, 11) : Geid) := RCPU (hB, 11)]} : Mea GF) (hB, 9)
          iprop(LK ∗ RNP (hB, 9))) Hzw (fun t v => storenNoRead _ _ _ _ _ _ _ _ Hl13) Hlw Hob11
        Hob9) $$ Hil Hw
      iapply (evDrawM (hlc := hlc) (pol := xv6Pol GT) (gtAdGd GT) Xv6N Unit (protXv6 Lx) nm
        (xv6AxpolWf GT) hB 13 _ (notheld nm.xnReg Lx.xlLk hB) iprop(True) _ _ Hval Hsub)
        $$ Hm [Hfe]
      · iapply (@flowEqDynMono hlc GF _ (AxSpinX2.xG Lx GT nm) (xv6Pol GT) (gtAdGd GT) (hB, 13) _ _
          (notheld nm.xnReg Lx.xlLk hB) iprop(notheld nm.xnReg Lx.xlLk hB ∗ True)) $$ [] Hfe
        inext
        iintro H
        isplitl [H]
        · iexact H
        · itrivial
      iintro _ _
      iapply (wB14 (hlc := hlc) GT nm cpu) $$ HF H10 %rs)
  iintro #Hil H9 H11 HF H10
  iapply H $$ [$Hil $H9 $H11 $HF $H10]

theorem wB12 (GT : GdexecT) (nm : Xv6N) (cpu : CPU) (Hcons : rvwmoCatConsistent (gtAdGd GT))
    (t1 t3 t4 t5 : List Nat) (t6 : Nat) (t8 t10 : List Nat) (v1 v4 v5 v10 : BitVec 64)
    (v3 v8 : BitVec 32)
    (Hrow : AxOpsem.grow (gtAdGd GT) hB = AxSpinX4.bRow t1 t3 t4 t5 t6 t8 t10 v1 v4 v5 v10 v3 v8) :
    ⊢ ISL -∗ AxAnnot.annotOwn (hB, 9) iprop(LK ∗ RNP (hB, 9)) -∗
      AxAnnot.annotOwn (hB, 11) (RCPU (hB, 11)) -∗ FB -∗
      AxAnnot.annotOwn (hB, 10) iprop(⌜F10 (gtAdGd GT).gdG⌝) -∗
      ∀ rs : RegFile, TWB ⟨hp cpu (fnc bEnd) rs, 12⟩ := by
  have Hne : 12 ≠ (AxOpsem.grow (gtAdGd GT) hB).length := by rw [Hrow]; simp [AxSpinX4.bRow]
  have H := nshFence (hlc := hlc) (pol := xv6Pol GT) (gtAdGd GT) Xv6N Unit (protXv6 Lx) nm cpu hB
    ΦB bEnd 12 Hne
    iprop(ISL ∗ AxAnnot.annotOwn (hB, 9) iprop(LK ∗ RNP (hB, 9)) ∗
      AxAnnot.annotOwn (hB, 11) (RCPU (hB, 11)) ∗ FB ∗
      AxAnnot.annotOwn (hB, 10) iprop(⌜F10 (gtAdGd GT).gdG⌝))
    (fun rs => by
      iintro ⟨#Hil, H9, H11, HF, H10⟩
      inext
      iapply (wB13 (hlc := hlc) GT nm cpu Hcons t1 t3 t4 t5 t6 t8 t10 v1 v4 v5 v10 v3 v8 Hrow)
        $$ Hil H9 H11 HF H10 %rs)
  iintro #Hil H9 H11 HF H10
  iapply H $$ [$Hil $H9 $H11 $HF $H10]

/-- k11: `sd lk->cpu ← 0`, the handle drawn from `d` ((B,7) itself, or the holder read (B,10)
that re-deposited it), anchored at (B,7). -/
theorem wB11 (GT : GdexecT) (nm : Xv6N) (cpu : CPU) (Hcons : rvwmoCatConsistent (gtAdGd GT))
    (t1 t3 t4 t5 : List Nat) (t6 : Nat) (t8 t10 : List Nat) (v1 v4 v5 v10 : BitVec 64)
    (v3 v8 : BitVec 32)
    (Hrow : AxOpsem.grow (gtAdGd GT) hB = AxSpinX4.bRow t1 t3 t4 t5 t6 t8 t10 v1 v4 v5 v10 v3 v8)
    (d : Geid) (Hd : d ∈ @Axpol.lobp (xv6Pol GT) (gtAdGd GT) (hB, 11)) :
    ⊢ ISL -∗ AxAnnot.annotOwn (hB, 9) iprop(LK ∗ RNP (hB, 9)) -∗
      AxAnnot.annotOwn d (RH (hB, 7)) -∗ FB -∗
      AxAnnot.annotOwn (hB, 10) iprop(⌜F10 (gtAdGd GT).gdG⌝) -∗
      ∀ rs : RegFile, TWB ⟨hp cpu bRel rs, 11⟩ := by
  have Hne : 11 ≠ (AxOpsem.grow (gtAdGd GT) hB).length := by rw [Hrow]; simp [AxSpinX4.bRow]
  have Hl7 := AxSpinX5.bL (gtAdGd GT) t1 t3 t4 t5 t6 t8 t10 v1 v4 v5 v10 v3 v8 Hrow 7 _ rfl
  have Hl11 := AxSpinX5.bL (gtAdGd GT) t1 t3 t4 t5 t6 t8 t10 v1 v4 v5 v10 v3 v8 Hrow 11 _ rfl
  have H := nshWrite (hlc := hlc) (pol := xv6Pol GT) (gtAdGd GT) Xv6N Unit (protXv6 Lx) nm cpu hB
    ΦB 8 lcpa lcpaRam zero64 (fnc bEnd) 11 Hne
    iprop(ISL ∗ AxAnnot.annotOwn (hB, 9) iprop(LK ∗ RNP (hB, 9)) ∗
      AxAnnot.annotOwn d (RH (hB, 7)) ∗ FB ∗
      AxAnnot.annotOwn (hB, 10) iprop(⌜F10 (gtAdGd GT).gdG⌝))
    (fun rs => by
      have Hval := gdataSt GT 11 _ 8 zero64 _ Hl11
      obtain ⟨Hw11, Hsg11⟩ := gwbStoren _ _ _ _ _ Hl11
      obtain ⟨Hw7, -⟩ := gwbStoren _ _ _ _ _ Hl7
      have Hlt : gmoLt (gtAdGd GT).gdG (hB, 7) (hB, 11) :=
        obCatSubGmo (gtAdGd GT) _ _ Hcons (ppo1Gob (gtAdGd GT) (hB, 7) (hB, 11) _ _
          (gpoRow (gtAdGd GT) hB 7 11 _ _ Hl7 Hl11 (by decide))
          (Or.inl ⟨_, Hw7 0 _ (wbytesLookupGen 8 cpB 0 (by decide))⟩)
          (Hw11 0 _ (wbytesLookupGen 8 zero64 0 (by decide))))
      have Hisw : gisW (gtAdGd GT).gdG (hB, 11) = true := by unfold gisW; rw [Hl11]; rfl
      have Hwr : ∀ (j : Nat) a v, (clb Lx)[j]? = some a →
          (WeakInterpProj.wbytes 8 zero64)[j]? = some v →
          gwritesByte (gtAdGd GT).gdG (hB, 11) a v := by
        intro j a v Hj Hv
        rw [clbLcpa] at Hj
        obtain ⟨rfl, -⟩ := AxSpinX4.clRangeLookup _ _ _ _ Hj
        exact Hw11 j v Hv
      have Hsg : ∀ a v, gwritesByte (gtAdGd GT).gdG (hB, 11) a v → a ∈ clb Lx := by
        intro a v Hw
        obtain ⟨j, Hj, rfl⟩ := Hsg11 a v Hw
        have hj := (List.getElem?_eq_some_iff.1 Hj).1
        rw [wbytesLength] at hj
        rw [clbLx]
        simp only [lkZV, lcZV]
        omega
      have Hw0 : ⊢ ([∗map] Rin ∈ ({[d := RH (hB, 7)]} : Mea GF), Rin) -∗
          iprop(True ∗ ∃ vold, RVL nm.xnH (gtAdGd GT) (clb Lx) (hB, 7) vold) := by
        iintro H
        ihave H := (BigSepM.bigSepM_singleton (M := GMapF Geid)).1 $$ H
        icases H with ⟨-, H⟩
        isplitr
        · itrivial
        · iexists _
          iexact H
      iintro ⟨#Hil, H9, HD, HF, H10⟩
      ihave Hw := Hw0
      ihave Hfe := (fxCpuWrite (hlc := hlc) Lx GT nm LxOk Hcons (hB, 11) (hB, 7)
        (WeakInterpProj.wbytes 8 zero64) iprop(True) ({[d := RH (hB, 7)]} : Mea GF) Hisw Hlt
        (Or.inr zero64Bytes) Hwr Hsg) $$ Hw
      iapply (evDraw (hlc := hlc) (pol := xv6Pol GT) (gtAdGd GT) Xv6N Unit (protXv6 Lx) nm
        (xv6AxpolWf GT) hB 11 d _ (RCPU (hB, 11)) iprop(True) _ _ Hval Hd) $$ HD [Hfe]
      · iapply (@flowEqDynMono hlc GF _ (AxSpinX2.xG Lx GT nm) (xv6Pol GT) (gtAdGd GT) (hB, 11) _ _
          iprop(True ∗ RVL nm.xnH (gtAdGd GT) (clb Lx) (hB, 11) (WeakInterpProj.wbytes 8 zero64))
          iprop(RCPU (hB, 11) ∗ True)) $$ [] Hfe
        inext
        iintro ⟨-, H⟩
        isplitl [H]
        · iunfold RCpu
          iexists _
          iexact H
        · itrivial
      iintro H11 _
      iapply (wB12 (hlc := hlc) GT nm cpu Hcons t1 t3 t4 t5 t6 t8 t10 v1 v4 v5 v10 v3 v8 Hrow)
        $$ Hil H9 H11 HF H10 %rs)
  iintro #Hil H9 HD HF H10
  iapply H $$ [$Hil $H9 $HD $HF $H10]

/-- k10: THE HOLDER's lk->cpu read -- the phase-1 case split on the pinned graph: owned
last-value read (gmo case) or forwarding. -/
theorem AxSpinX5.wB10 (GT : GdexecT) (nm : Xv6N) (cpu : CPU)
    (Hcons : rvwmoCatConsistent (gtAdGd GT))
    (t1 t3 t4 t5 : List Nat) (t6 : Nat) (t8 t10 : List Nat) (v1 v4 v5 v10 : BitVec 64)
    (v3 v8 : BitVec 32)
    (Hrow : AxOpsem.grow (gtAdGd GT) hB = AxSpinX4.bRow t1 t3 t4 t5 t6 t8 t10 v1 v4 v5 v10 v3 v8) :
    ⊢ ISL -∗ AxAnnot.annotOwn (hB, 9) iprop(LK ∗ RNP (hB, 9)) -∗
      AxAnnot.annotOwn (hB, 7) (RH (hB, 7)) -∗ FB -∗
      ∀ rs : RegFile, TWB ⟨hp cpu bHold rs, 10⟩ := by
  have Hne : 10 ≠ (AxOpsem.grow (gtAdGd GT) hB).length := by rw [Hrow]; simp [AxSpinX4.bRow]
  have Hl7 := AxSpinX5.bL (gtAdGd GT) t1 t3 t4 t5 t6 t8 t10 v1 v4 v5 v10 v3 v8 Hrow 7 _ rfl
  have Hl10 := AxSpinX5.bL (gtAdGd GT) t1 t3 t4 t5 t6 t8 t10 v1 v4 v5 v10 v3 v8 Hrow 10 _ rfl
  have Hl11 := AxSpinX5.bL (gtAdGd GT) t1 t3 t4 t5 t6 t8 t10 v1 v4 v5 v10 v3 v8 Hrow 11 _ rfl
  have Hwf := Hcons.1
  obtain ⟨Hw7, -⟩ := gwbStoren _ _ _ _ _ Hl7
  obtain ⟨Hw11, -⟩ := gwbStoren _ _ _ _ _ Hl11
  have Hpo7 : WeakRvwmoGraph.gpo (gtAdGd GT).gdG (hB, 7) (hB, 10) :=
    gpoRow (gtAdGd GT) hB 7 10 _ _ Hl7 Hl10 (by decide)
  have Hw11_0 := Hw11 0 _ (wbytesLookupGen 8 zero64 0 (by decide))
  have Hin7 : ((hB, 7) : Geid) ∈ @Axpol.lobp (xv6Pol GT) (gtAdGd GT) (hB, 11) :=
    locLobp (gtAdGd GT) Hcons (hB, 7) (hB, 11) _ _ _ Hl7 rfl
      (gpoRow (gtAdGd GT) hB 7 11 _ _ Hl7 Hl11 (by decide))
      (Or.inl ⟨_, Hw7 0 _ (wbytesLookupGen 8 cpB 0 (by decide))⟩) Hw11_0
  have Hin10 : ((hB, 10) : Geid) ∈ @Axpol.lobp (xv6Pol GT) (gtAdGd GT) (hB, 11) := by
    obtain ⟨t, Ht⟩ := loadnReads (gtAdGd GT).gdG Hwf (hB, 10) (paZ lcpa) t10 8 v10 0 Hl10
      (by decide)
    exact locLobp (gtAdGd GT) Hcons (hB, 10) (hB, 11) _ _ _ Hl10 rfl
      (gpoRow (gtAdGd GT) hB 10 11 _ _ Hl10 Hl11 (by decide)) (Or.inr ⟨t, _, Ht⟩) Hw11_0
  have Hcw : ∀ (j : Nat) a v, (clb Lx)[j]? = some a → (cvx hB)[j]? = some v →
      gwritesByte (gtAdGd GT).gdG (hB, 7) a v := by
    intro j a v Hj Hv
    rw [clbLcpa] at Hj
    obtain ⟨rfl, -⟩ := AxSpinX4.clRangeLookup _ _ _ _ Hj
    exact Hw7 j v Hv
  have Hadv := advLoad (gtAdGd GT) hB 10 false (paZ lcpa) t10 (WeakInterpProj.wbytes 8 v10)
    (by rw [← gxLblGrow]; exact Hl10)
  have H := nshRead (hlc := hlc) (pol := xv6Pol GT) (gtAdGd GT) Xv6N Unit (protXv6 Lx) nm cpu hB
    ΦB 8 (by decide) lcpa lcpaRam (AxSpinX4.ldkK 8 (fun _ => bRel)) 10 Hne Hadv
    iprop(ISL ∗ AxAnnot.annotOwn (hB, 9) iprop(LK ∗ RNP (hB, 9)) ∗
      AxAnnot.annotOwn (hB, 7) (RH (hB, 7)) ∗ FB)
    (fun v rs Hgv => by
      have Hnw : gisW (gtAdGd GT).gdG (hB, 10) = false := by unfold gisW; rw [Hl10]; rfl
      cases Hb : gmoLtB (gtAdGd GT).gdG (hB, 7) (hB, 10) with
      | true =>
        -- the sd is gmo-before the read: the OWNED last-value read
        have Hlt := (gmoLtBSpec _ _ _).1 Hb
        have Hin : ((hB, 7) : Geid) ∈ @Axpol.lobp (xv6Pol GT) (gtAdGd GT) (hB, 10) :=
          lobpIntro (gtAdGd GT) _ _ _ Hl7 rfl Hpo7 Hlt
        have Hlast : ∀ w a v', a ∈ clb Lx → gwritesByte (gtAdGd GT).gdG w a v' →
            WeakRvwmoGraph.gpo (gtAdGd GT).gdG w (hB, 10) →
            gmoLt (gtAdGd GT).gdG w (hB, 10) := by
          intro w a v' Ha Hw Hpo
          obtain ⟨k', rfl, Hk, Hc⟩ := bWrBefore GT t1 t3 t4 t5 t6 t8 t10 v1 v4 v5 v10 v3 v8 Hrow
            w a v' 10 Hw Hpo
          rw [clbLx] at Ha
          simp only [lkZV, lcZV, npZV, skZV, nfZV] at Ha Hc
          have Hk7 : k' = 7 := by omega
          subst Hk7
          exact Hlt
        have Hsing : ⊢ ([∗map] Rin ∈ ({[((hB, 7) : Geid) := RH (hB, 7)]} : Mea GF), Rin) -∗
            RH (hB, 7) := by
          iintro H
          iapply (BigSepM.bigSepM_singleton (M := GMapF Geid)).1 $$ H
        iintro ⟨#Hil, H9, H7, HF⟩
        ihave Hw := Hsing
        ihave Hfe := (fxOwnedRead (hlc := hlc) Lx GT nm LxOk Hcons (hB, 10) (hB, 7) (clb Lx)
          (cvx hB) iprop(True) ({[((hB, 7) : Geid) := RH (hB, 7)]} : Mea GF) Hnw
          (fun a Ha => clbXO Lx a Ha) Hlt Hlast) $$ Hw
        iapply (evDraw (hlc := hlc) (pol := xv6Pol GT) (gtAdGd GT) Xv6N Unit (protXv6 Lx) nm
          (xv6AxpolWf GT) hB 10 (hB, 7) _ (RH (hB, 7)) iprop(⌜F10 (gtAdGd GT).gdG⌝) _ _ Hgv Hin)
          $$ H7 Hfe
        iintro H10a H10
        iapply (wB11 (hlc := hlc) GT nm cpu Hcons t1 t3 t4 t5 t6 t8 t10 v1 v4 v5 v10 v3 v8 Hrow
          (hB, 10) Hin10) $$ Hil H9 H10a HF H10 %rs
      | false =>
        -- not gmo-before: FORWARDED, the pure value
        have Hnlt : ¬ gmoLt (gtAdGd GT).gdG (hB, 7) (hB, 10) := by
          intro H
          rw [(gmoLtBSpec _ _ _).2 H] at Hb
          cases Hb
        have Hlen : (cvx hB).length = (clb Lx).length := by
          rw [cvxLength]
          simp [clb, clRange]
        have Hbetw : ∀ w' a v', a ∈ clb Lx → gwritesByte (gtAdGd GT).gdG w' a v' →
            WeakRvwmoGraph.gpo (gtAdGd GT).gdG (hB, 7) w' →
            WeakRvwmoGraph.gpo (gtAdGd GT).gdG w' (hB, 10) → False := by
          intro w' a v' Ha Hw' Hpo1 Hpo2
          obtain ⟨k', rfl, Hk, Hc⟩ := bWrBefore GT t1 t3 t4 t5 t6 t8 t10 v1 v4 v5 v10 v3 v8 Hrow
            w' a v' 10 Hw' Hpo2
          have Hlt1 : 7 < k' := Hpo1.2.1
          rw [clbLx] at Ha
          simp only [lkZV, lcZV, npZV, skZV, nfZV] at Ha Hc
          omega
        iintro ⟨#Hil, H9, H7, HF⟩
        ihave Hfe := fxFwdRead (hlc := hlc) (GF := GF) Lx GT nm LxOk Hcons (hB, 10) (hB, 7)
          (clb Lx) (cvx hB) Hnw Hpo7 Hnlt Hcw Hlen Hbetw
        iapply (evPlain (hlc := hlc) (pol := xv6Pol GT) (gtAdGd GT) Xv6N Unit (protXv6 Lx) nm hB
          10 iprop(⌜F10 (gtAdGd GT).gdG⌝) iprop(True) _ _ Hgv) $$ [Hfe]
        · iapply (@flowEqDynMono hlc GF _ (AxSpinX2.xG Lx GT nm) (xv6Pol GT) (gtAdGd GT) (hB, 10) _
            (∅ : Mea GF) iprop(⌜F10 (gtAdGd GT).gdG⌝) iprop(⌜F10 (gtAdGd GT).gdG⌝ ∗ True))
            $$ [] Hfe
          inext
          iintro H
          isplitl [H]
          · iexact H
          · itrivial
        iintro H10 _
        iapply (wB11 (hlc := hlc) GT nm cpu Hcons t1 t3 t4 t5 t6 t8 t10 v1 v4 v5 v10 v3 v8 Hrow
          (hB, 7) Hin7) $$ Hil H9 H7 HF H10 %rs)
  iintro #Hil H9 H7 HF
  iapply H $$ [$Hil $H9 $H7 $HF]

/-- k9: `sw nextpid ← v+1` (Theorem 2's ghost step inside). -/
theorem AxSpinX5.wB9 (GT : GdexecT) (nm : Xv6N) (cpu : CPU)
    (Hcons : rvwmoCatConsistent (gtAdGd GT))
    (t1 t3 t4 t5 : List Nat) (t6 : Nat) (t8 t10 : List Nat) (v1 v4 v5 v10 : BitVec 64)
    (v3 v8 : BitVec 32)
    (Hrow : AxOpsem.grow (gtAdGd GT) hB = AxSpinX4.bRow t1 t3 t4 t5 t6 t8 t10 v1 v4 v5 v10 v3 v8)
    (Hnowrap : v8.toNat + 1 < 2 ^ 32) :
    ⊢ ISL -∗ AxAnnot.annotOwn (hB, 8) iprop(LK ∗ NPF) -∗
      AxAnnot.annotOwn (hB, 7) (RH (hB, 7)) -∗ FB -∗
      ∀ rs : RegFile, TWB ⟨hp cpu (bInc v8) rs, 9⟩ := by
  have Hne : 9 ≠ (AxOpsem.grow (gtAdGd GT) hB).length := by rw [Hrow]; simp [AxSpinX4.bRow]
  have Hl6 := AxSpinX5.bL (gtAdGd GT) t1 t3 t4 t5 t6 t8 t10 v1 v4 v5 v10 v3 v8 Hrow 6 _ rfl
  have Hl8 := AxSpinX5.bL (gtAdGd GT) t1 t3 t4 t5 t6 t8 t10 v1 v4 v5 v10 v3 v8 Hrow 8 _ rfl
  have Hl9 := AxSpinX5.bL (gtAdGd GT) t1 t3 t4 t5 t6 t8 t10 v1 v4 v5 v10 v3 v8 Hrow 9 _ rfl
  have Hwf := Hcons.1
  have H := nshWrite (hlc := hlc) (pol := xv6Pol GT) (gtAdGd GT) Xv6N Unit (protXv6 Lx) nm cpu hB
    ΦB 4 nppa nppaRam (v8 + one32 : BitVec 32) bHold 9 Hne
    iprop(ISL ∗ AxAnnot.annotOwn (hB, 8) iprop(LK ∗ NPF) ∗
      AxAnnot.annotOwn (hB, 7) (RH (hB, 7)) ∗ FB)
    (fun rs => by
      have Hval := gdataSt GT 9 _ 4 (v8 + one32 : BitVec 32) _ Hl9
      obtain ⟨Hw9, Hsg9⟩ := gwbStoren _ _ _ _ _ Hl9
      have Hin : ((hB, 8) : Geid) ∈ @Axpol.lobp (xv6Pol GT) (gtAdGd GT) (hB, 9) := by
        obtain ⟨t, Ht⟩ := loadnReads (gtAdGd GT).gdG Hwf (hB, 8) (paZ nppa) t8 4 v8 0 Hl8
          (by decide)
        exact locLobp (gtAdGd GT) Hcons (hB, 8) (hB, 9) _ _ _ Hl8 rfl
          (gpoRow (gtAdGd GT) hB 8 9 _ _ Hl8 Hl9 (by decide)) (Or.inr ⟨t, _, Ht⟩)
          (Hw9 0 _ (wbytesLookupGen 4 (v8 + one32) 0 (by decide)))
      have Hlt69 : gmoLt (gtAdGd GT).gdG (hB, 6) (hB, 9) :=
        obCatSubGmo (gtAdGd GT) _ _ Hcons
          (acqGob (gtAdGd GT) hB 6 9 _ _ _ _ _ _ Hl6 Hl9 rfl (by decide))
      have Hisw : gisW (gtAdGd GT).gdG (hB, 9) = true := by unfold gisW; rw [Hl9]; rfl
      have Hsg : ∀ a v', gwritesByte (gtAdGd GT).gdG (hB, 9) a v' → a ∈ npb Lx := by
        intro a v' Hw
        obtain ⟨j, Hj, rfl⟩ := Hsg9 a v' Hw
        have hj := (List.getElem?_eq_some_iff.1 Hj).1
        rw [wbytesLength] at hj
        exact (npbLx _).2 ⟨by omega, by omega⟩
      have Harith : ∀ v : Int, 0 ≤ v ∧ v < 2 ^ 32 →
          (∀ (j : Nat) a t b, (npb Lx)[j]? = some a →
            greadsByte (gtAdGd GT).gdG (hB, 8) a t b →
            (WeakInterpProj.wbytes 4 (BitVec.ofInt 32 v))[j]? = some b) →
          v + 1 < 2 ^ 32 ∧
          ∀ (j : Nat) a b, (npb Lx)[j]? = some a →
            (WeakInterpProj.wbytes 4 (BitVec.ofInt 32 (v + 1)))[j]? = some b →
            gwritesByte (gtAdGd GT).gdG (hB, 9) a b := by
        intro v Hv Hrd
        have Hword : WeakInterpProj.wbytes 4 v8 = WeakInterpProj.wbytes 4 (BitVec.ofInt 32 v) :=
          readFactWord (gtAdGd GT).gdG Hwf (hB, 8) (paZ nppa) t8 4 v8 _ Hl8 (wbytesLength 4 _) Hrd
        have Hword' := wbytes4Inj _ _ Hword
        obtain ⟨Hlt, Heq⟩ := npSucc v v8 Hv Hword'.symm Hnowrap
        refine ⟨Hlt, ?_⟩
        intro j a b Hj Hb
        rw [Heq] at Hb
        have Hj' : (clRange (paZ nppa) 4)[j]? = some a := Hj
        obtain ⟨rfl, -⟩ := AxSpinX4.clRangeLookup _ _ _ _ Hj'
        exact Hw9 j b Hb
      have Hsing : ⊢ ([∗map] Rin ∈ ({[((hB, 8) : Geid) := iprop(LK ∗ NPF)]} : Mea GF), Rin) -∗
          iprop(LK ∗ NPF) := by
        iintro H
        iapply (BigSepM.bigSepM_singleton (M := GMapF Geid)).1 $$ H
      iintro ⟨#Hil, H8, H7, HF⟩
      ihave Hw := Hsing
      ihave Hfe := (fxNpIncr (hlc := hlc) Lx GT nm LxOk Hcons (hB, 9) (hB, 8) (hB, 6) LK
        ({[((hB, 8) : Geid) := iprop(LK ∗ NPF)]} : Mea GF) Hisw Hlt69 Hsg Harith) $$ Hw
      iapply (evDraw (hlc := hlc) (pol := xv6Pol GT) (gtAdGd GT) Xv6N Unit (protXv6 Lx) nm
        (xv6AxpolWf GT) hB 9 (hB, 8) _ iprop(LK ∗ RNP (hB, 9))
        iprop(∃ (v : Int), issuedFrag nm.xnI v ∗ ⌜AxSpinX5.npRd (gtAdGd GT).gdG v⌝) _ _ Hval Hin)
        $$ H8 [Hfe]
      · iapply (@flowEqDynMono hlc GF _ (AxSpinX2.xG Lx GT nm) (xv6Pol GT) (gtAdGd GT) (hB, 9) _ _
          iprop(LK ∗ RNP (hB, 9) ∗
            ∃ (v : Int), issuedFrag nm.xnI v ∗ ⌜AxSpinX5.npRd (gtAdGd GT).gdG v⌝)
          iprop((LK ∗ RNP (hB, 9)) ∗
            ∃ (v : Int), issuedFrag nm.xnI v ∗ ⌜AxSpinX5.npRd (gtAdGd GT).gdG v⌝)) $$ [] Hfe
        inext
        iintro ⟨Hl, Hn, Hv⟩
        isplitl [Hl Hn]
        · isplitl [Hl]
          · iexact Hl
          · iexact Hn
        · iexact Hv
      iintro H9 _
      iapply (AxSpinX5.wB10 (hlc := hlc) GT nm cpu Hcons t1 t3 t4 t5 t6 t8 t10 v1 v4 v5 v10 v3 v8
        Hrow) $$ Hil H9 H7 HF %rs)
  iintro #Hil H8 H7 HF
  iapply H $$ [$Hil $H8 $H7 $HF]

/-- k8: `lw nextpid`, `locked ∗ RNp` drawn from the claim (rule 5). -/
theorem AxSpinX5.wB8 (GT : GdexecT) (nm : Xv6N) (cpu : CPU)
    (Hcons : rvwmoCatConsistent (gtAdGd GT))
    (t1 t3 t4 t5 : List Nat) (t6 : Nat) (t8 t10 : List Nat) (v1 v4 v5 v10 : BitVec 64)
    (v3 v8 : BitVec 32)
    (Hrow : AxOpsem.grow (gtAdGd GT) hB = AxSpinX4.bRow t1 t3 t4 t5 t6 t8 t10 v1 v4 v5 v10 v3 v8)
    (Hnowrap : v8.toNat + 1 < 2 ^ 32) :
    ⊢ ISL -∗ AxAnnot.annotOwn (hB, 6) iprop(LK ∗ RNP (hB, 6)) -∗
      AxAnnot.annotOwn (hB, 7) (RH (hB, 7)) -∗ FB -∗
      ∀ rs : RegFile, TWB ⟨hp cpu bNp rs, 8⟩ := by
  have Hne : 8 ≠ (AxOpsem.grow (gtAdGd GT) hB).length := by rw [Hrow]; simp [AxSpinX4.bRow]
  have Hl6 := AxSpinX5.bL (gtAdGd GT) t1 t3 t4 t5 t6 t8 t10 v1 v4 v5 v10 v3 v8 Hrow 6 _ rfl
  have Hl8 := AxSpinX5.bL (gtAdGd GT) t1 t3 t4 t5 t6 t8 t10 v1 v4 v5 v10 v3 v8 Hrow 8 _ rfl
  have Hadv := advLoad (gtAdGd GT) hB 8 false (paZ nppa) t8 (WeakInterpProj.wbytes 4 v8)
    (by rw [← gxLblGrow]; exact Hl8)
  have H := nshRead (hlc := hlc) (pol := xv6Pol GT) (gtAdGd GT) Xv6N Unit (protXv6 Lx) nm cpu hB
    ΦB 4 (by decide) nppa nppaRam (AxSpinX4.ldkK 4 bInc) 8 Hne Hadv
    iprop(ISL ∗ AxAnnot.annotOwn (hB, 6) iprop(LK ∗ RNP (hB, 6)) ∗
      AxAnnot.annotOwn (hB, 7) (RH (hB, 7)) ∗ FB)
    (fun v rs Hgv => by
      have Hv : v = WeakInterpProj.wbytes 4 v8 := by
        have Hgv' := Hgv
        unfold graphValue at Hgv'
        rw [Hl8] at Hgv'
        simp only [Option.bind_some, lblValue, Option.some.injEq] at Hgv'
        exact Hgv'.symm
      have Hnw : gisW (gtAdGd GT).gdG (hB, 8) = false := by unfold gisW; rw [Hl8]; rfl
      have Hin : ((hB, 6) : Geid) ∈ @Axpol.lobp (xv6Pol GT) (gtAdGd GT) (hB, 8) :=
        acqLobp (gtAdGd GT) Hcons hB 6 8 _ _ _ _ _ _ Hl6 Hl8 rfl (by decide)
      have Hlt : gmoLt (gtAdGd GT).gdG (hB, 6) (hB, 8) :=
        obCatSubGmo (gtAdGd GT) _ _ Hcons
          (acqGob (gtAdGd GT) hB 6 8 _ _ _ _ _ _ Hl6 Hl8 rfl (by decide))
      have Hnowr : ∀ w a v', a ∈ npb Lx → gwritesByte (gtAdGd GT).gdG w a v' →
          WeakRvwmoGraph.gpo (gtAdGd GT).gdG w (hB, 8) → gmoLt (gtAdGd GT).gdG w (hB, 8) := by
        intro w a v' Ha Hw Hpo
        exfalso
        obtain ⟨k', rfl, Hk, Hc⟩ := bWrBefore GT t1 t3 t4 t5 t6 t8 t10 v1 v4 v5 v10 v3 v8 Hrow
          w a v' 8 Hw Hpo
        rw [npbLx] at Ha
        simp only [lkZV, lcZV, npZV, skZV, nfZV] at Ha Hc
        omega
      have Hsing : ⊢ ([∗map] Rin ∈ ({[((hB, 6) : Geid) := iprop(LK ∗ RNP (hB, 6))]} : Mea GF),
          Rin) -∗ iprop(LK ∗ RNP (hB, 6)) := by
        iintro H
        iapply (BigSepM.bigSepM_singleton (M := GMapF Geid)).1 $$ H
      iintro ⟨#Hil, H6, H7, HF⟩
      ihave Hw := Hsing
      ihave Hfe := (fxNpRead (hlc := hlc) Lx GT nm LxOk Hcons (hB, 8) (hB, 6) LK
        ({[((hB, 6) : Geid) := iprop(LK ∗ RNP (hB, 6))]} : Mea GF) Hnw Hlt Hnowr) $$ Hw
      iapply (evDraw (hlc := hlc) (pol := xv6Pol GT) (gtAdGd GT) Xv6N Unit (protXv6 Lx) nm
        (xv6AxpolWf GT) hB 8 (hB, 6) _ iprop(LK ∗ NPF) iprop(True) _ _ Hgv Hin) $$ H6 [Hfe]
      · iapply (@flowEqDynMono hlc GF _ (AxSpinX2.xG Lx GT nm) (xv6Pol GT) (gtAdGd GT) (hB, 8) _ _
          iprop(LK ∗ NPF) iprop((LK ∗ NPF) ∗ True)) $$ [] Hfe
        inext
        iintro H
        isplitl [H]
        · iexact H
        · itrivial
      iintro H8 _
      subst Hv
      rw [wordOfBytesWbytes]
      iapply (AxSpinX5.wB9 (hlc := hlc) GT nm cpu Hcons t1 t3 t4 t5 t6 t8 t10 v1 v4 v5 v10 v3 v8
        Hrow Hnowrap) $$ Hil H8 H7 HF %rs)
  iintro #Hil H6 H7 HF
  iapply H $$ [$Hil $H6 $H7 $HF]

/-- k7: `sd lk->cpu ← cpuAddr B` -- `RCpu` drawn from the claim (rule 5), Φ_cpu from the value
(the writer's own REAL cpu pointer). -/
theorem wB7 (GT : GdexecT) (nm : Xv6N) (cpu : CPU) (Hcons : rvwmoCatConsistent (gtAdGd GT))
    (t1 t3 t4 t5 : List Nat) (t6 : Nat) (t8 t10 : List Nat) (v1 v4 v5 v10 : BitVec 64)
    (v3 v8 : BitVec 32)
    (Hrow : AxOpsem.grow (gtAdGd GT) hB = AxSpinX4.bRow t1 t3 t4 t5 t6 t8 t10 v1 v4 v5 v10 v3 v8)
    (Hnowrap : v8.toNat + 1 < 2 ^ 32) :
    ⊢ ISL -∗ AxAnnot.annotOwn (hB, 6) iprop(LK ∗ RNP (hB, 6)) -∗
      AxAnnot.annotOwn (hB, 6) (RCPU (hB, 6)) -∗ FB -∗
      ∀ rs : RegFile, TWB ⟨hp cpu bCs rs, 7⟩ := by
  have Hne : 7 ≠ (AxOpsem.grow (gtAdGd GT) hB).length := by rw [Hrow]; simp [AxSpinX4.bRow]
  have Hl6 := AxSpinX5.bL (gtAdGd GT) t1 t3 t4 t5 t6 t8 t10 v1 v4 v5 v10 v3 v8 Hrow 6 _ rfl
  have Hl7 := AxSpinX5.bL (gtAdGd GT) t1 t3 t4 t5 t6 t8 t10 v1 v4 v5 v10 v3 v8 Hrow 7 _ rfl
  have H := nshWrite (hlc := hlc) (pol := xv6Pol GT) (gtAdGd GT) Xv6N Unit (protXv6 Lx) nm cpu hB
    ΦB 8 lcpa lcpaRam cpB bNp 7 Hne
    iprop(ISL ∗ AxAnnot.annotOwn (hB, 6) iprop(LK ∗ RNP (hB, 6)) ∗
      AxAnnot.annotOwn (hB, 6) (RCPU (hB, 6)) ∗ FB)
    (fun rs => by
      have Hval := gdataSt GT 7 _ 8 cpB _ Hl7
      obtain ⟨Hw7, Hsg7⟩ := gwbStoren _ _ _ _ _ Hl7
      have Hin : ((hB, 6) : Geid) ∈ @Axpol.lobp (xv6Pol GT) (gtAdGd GT) (hB, 7) :=
        acqLobp (gtAdGd GT) Hcons hB 6 7 _ _ _ _ _ _ Hl6 Hl7 rfl (by decide)
      have Hlt : gmoLt (gtAdGd GT).gdG (hB, 6) (hB, 7) :=
        obCatSubGmo (gtAdGd GT) _ _ Hcons
          (acqGob (gtAdGd GT) hB 6 7 _ _ _ _ _ _ Hl6 Hl7 rfl (by decide))
      have Hisw : gisW (gtAdGd GT).gdG (hB, 7) = true := by unfold gisW; rw [Hl7]; rfl
      have Hwr : ∀ (j : Nat) a v, (clb Lx)[j]? = some a → (cvx hB)[j]? = some v →
          gwritesByte (gtAdGd GT).gdG (hB, 7) a v := by
        intro j a v Hj Hv
        rw [clbLcpa] at Hj
        obtain ⟨rfl, -⟩ := AxSpinX4.clRangeLookup _ _ _ _ Hj
        exact Hw7 j v Hv
      have Hsg : ∀ a v, gwritesByte (gtAdGd GT).gdG (hB, 7) a v → a ∈ clb Lx := by
        intro a v Hw
        obtain ⟨j, Hj, rfl⟩ := Hsg7 a v Hw
        have hj := (List.getElem?_eq_some_iff.1 Hj).1
        rw [wbytesLength] at hj
        rw [clbLx]
        simp only [lkZV, lcZV]
        omega
      have Hw0 : ⊢ ([∗map] Rin ∈ ({[((hB, 6) : Geid) := RCPU (hB, 6)]} : Mea GF), Rin) -∗
          iprop(True ∗ ∃ vold, RVL nm.xnH (gtAdGd GT) (clb Lx) (hB, 6) vold) := by
        iintro H
        ihave H := (BigSepM.bigSepM_singleton (M := GMapF Geid)).1 $$ H
        isplitr
        · itrivial
        · iunfold RCpu at H
          iexact H
      iintro ⟨#Hil, H6, H6c, HF⟩
      ihave Hw := Hw0
      ihave Hfe := (fxCpuWrite (hlc := hlc) Lx GT nm LxOk Hcons (hB, 7) (hB, 6) (cvx hB)
        iprop(True) ({[((hB, 6) : Geid) := RCPU (hB, 6)]} : Mea GF) Hisw Hlt (Or.inl rfl) Hwr Hsg)
        $$ Hw
      iapply (evDraw (hlc := hlc) (pol := xv6Pol GT) (gtAdGd GT) Xv6N Unit (protXv6 Lx) nm
        (xv6AxpolWf GT) hB 7 (hB, 6) _ (RH (hB, 7)) iprop(True) _ _ Hval Hin) $$ H6c [Hfe]
      · iapply (@flowEqDynMono hlc GF _ (AxSpinX2.xG Lx GT nm) (xv6Pol GT) (gtAdGd GT) (hB, 7) _ _
          (RH (hB, 7)) iprop(RH (hB, 7) ∗ True)) $$ [] Hfe
        inext
        iintro H
        isplitl [H]
        · iexact H
        · itrivial
      iintro H7 _
      iapply (AxSpinX5.wB8 (hlc := hlc) GT nm cpu Hcons t1 t3 t4 t5 t6 t8 t10 v1 v4 v5 v10 v3 v8
        Hrow Hnowrap) $$ Hil H6 H7 HF %rs)
  iintro #Hil H6 H6c HF
  iapply H $$ [$Hil $H6 $H6c $HF]

/-- k6: the CLAIM (the amoswap's write half), `notheld` in hand; `RPid` deposited in two
fragments: `locked ∗ RNp` and `RCpu`. -/
theorem wB6w (GT : GdexecT) (nm : Xv6N) (cpu : CPU) (Hcons : rvwmoCatConsistent (gtAdGd GT))
    (t1 t3 t4 t5 : List Nat) (t6 : Nat) (t8 t10 : List Nat) (v1 v4 v5 v10 : BitVec 64)
    (v3 v8 : BitVec 32)
    (Hrow : AxOpsem.grow (gtAdGd GT) hB = AxSpinX4.bRow t1 t3 t4 t5 t6 t8 t10 v1 v4 v5 v10 v3 v8)
    (Hnowrap : v8.toNat + 1 < 2 ^ 32) :
    ⊢ ISL -∗ notheld (GF := GF) nm.xnReg Lx.xlLk hB -∗ FB -∗
      ∀ rs : RegFile, TWB ⟨hp cpu (amoW bCs hlt zero32) rs, 6⟩ := by
  have Hne : 6 ≠ (AxOpsem.grow (gtAdGd GT) hB).length := by rw [Hrow]; simp [AxSpinX4.bRow]
  have Hl6 := AxSpinX5.bL (gtAdGd GT) t1 t3 t4 t5 t6 t8 t10 v1 v4 v5 v10 v3 v8 Hrow 6 _ rfl
  have H := nshRmwWrite (hlc := hlc) (pol := xv6Pol GT) (gtAdGd GT) Xv6N Unit (protXv6 Lx) nm cpu
    hB ΦB 4 lkpa lkpaRam one32 (if zero32 = zero32 then bCs else hlt) 6 Hne
    iprop(ISL ∗ notheld (GF := GF) nm.xnReg Lx.xlLk hB ∗ FB)
    (fun rs => by
      have Hval : graphData (gtAdGd GT) (hB, 6) = some (WeakInterpProj.wbytes 4 one32) := by
        unfold graphData; rw [Hl6]; rfl
      obtain ⟨Hr6, Hw6, Hsg6, -⟩ := gwbRmwn _ _ _ _ _ _ _ Hl6
      have Hcl : lkClaim Lx.xlLk (gtAdGd GT).gdG (hB, 6) (gwriteAt (gtAdGd GT).gdG t6) := by
        refine ⟨t6, ?_, rfl, ?_⟩
        · have H := Hr6 0 t6 b0 rfl (by decide +kernel)
          rw [AxSpinX5.addZero] at H
          exact H
        · have H := Hw6 0 b1 (by decide +kernel)
          rw [AxSpinX5.addZero] at H
          exact H
      have Hlw : ∀ a v', gwritesByte (gtAdGd GT).gdG (hB, 6) a v' → a ∈ lwb Lx := by
        intro a v' Hw
        obtain ⟨j, Hj, rfl⟩ := Hsg6 a v' Hw
        have hj := (List.getElem?_eq_some_iff.1 Hj).1
        simp only [AxSpinX4.o4, wbytesLength] at hj
        exact (lwbLx _).2 ⟨by omega, by omega⟩
      iintro ⟨#Hil, Hnh, HF⟩
      ihave Hfe := (fxClaim (hlc := hlc) Lx GT nm LxOk Hcons (hB, 6) (gwriteAt (gtAdGd GT).gdG t6)
        Hcl Hlw) $$ Hnh Hil
      iapply (evPlain (hlc := hlc) (pol := xv6Pol GT) (gtAdGd GT) Xv6N Unit (protXv6 Lx) nm hB 6
        iprop(LK ∗ RNP (hB, 6)) (RCPU (hB, 6)) _ _ Hval) $$ [Hfe]
      · iapply (@flowEqDynMono hlc GF _ (AxSpinX2.xG Lx GT nm) (xv6Pol GT) (gtAdGd GT) (hB, 6) _
          (∅ : Mea GF)
          iprop(locked nm.xnReg Lx.xlLk (hB, 6).1 (hB, 6) ∗
            RPid Lx nm.xnH nm.xnM nm.xnI (gtAdGd GT) (hB, 6))
          iprop((LK ∗ RNP (hB, 6)) ∗ RCPU (hB, 6))) $$ [] Hfe
        inext
        iintro ⟨Hl, HR⟩
        iunfold RPid at HR
        icases HR with ⟨Hc, Hn⟩
        isplitl [Hl Hn]
        · isplitl [Hl]
          · iexact Hl
          · iexact Hn
        · iexact Hc
      iintro H6 H6c
      rw [amoClaimNext]
      iapply (wB7 (hlc := hlc) GT nm cpu Hcons t1 t3 t4 t5 t6 t8 t10 v1 v4 v5 v10 v3 v8 Hrow
        Hnowrap) $$ Hil H6 H6c HF %rs)
  iintro #Hil Hnh HF
  iapply H $$ [$Hil $Hnh $HF]

theorem AxSpinX5.wB6 (GT : GdexecT) (nm : Xv6N) (cpu : CPU)
    (Hcons : rvwmoCatConsistent (gtAdGd GT))
    (t1 t3 t4 t5 : List Nat) (t6 : Nat) (t8 t10 : List Nat) (v1 v4 v5 v10 : BitVec 64)
    (v3 v8 : BitVec 32)
    (Hrow : AxOpsem.grow (gtAdGd GT) hB = AxSpinX4.bRow t1 t3 t4 t5 t6 t8 t10 v1 v4 v5 v10 v3 v8)
    (Hnowrap : v8.toNat + 1 < 2 ^ 32) :
    ⊢ ISL -∗ notheld (GF := GF) nm.xnReg Lx.xlLk hB -∗ FB -∗
      ∀ rs : RegFile, TWB ⟨hp cpu bAcq rs, 6⟩ := by
  have Hne : 6 ≠ (AxOpsem.grow (gtAdGd GT) hB).length := by rw [Hrow]; simp [AxSpinX4.bRow]
  have H := nshRmwRead (hlc := hlc) (pol := xv6Pol GT) (gtAdGd GT) Xv6N Unit (protXv6 Lx) nm cpu
    hB ΦB 4 (by decide) lkpa lkpaRam (amoK bCs hlt) 6 [t6, t6, t6, t6] AxSpinX4.z4 AxSpinX4.o4
    .WCplain Hne (by rw [Hrow]; rfl)
    iprop(ISL ∗ notheld (GF := GF) nm.xnReg Lx.xlLk hB ∗ FB)
    (fun rs => by
      iintro ⟨#Hil, Hnh, HF⟩
      rw [acqAfterClaim]
      iapply (wB6w (hlc := hlc) GT nm cpu Hcons t1 t3 t4 t5 t6 t8 t10 v1 v4 v5 v10 v3 v8 Hrow
        Hnowrap) $$ Hil Hnh HF %rs)
  iintro #Hil Hnh HF
  iapply H $$ [$Hil $Hnh $HF]

/-- k5: the NON-holder's racy lk->cpu read: `rdFact` at the read. -/
theorem AxSpinX5.wB5 (GT : GdexecT) (nm : Xv6N) (cpu : CPU)
    (Hcons : rvwmoCatConsistent (gtAdGd GT))
    (t1 t3 t4 t5 : List Nat) (t6 : Nat) (t8 t10 : List Nat) (v1 v4 v5 v10 : BitVec 64)
    (v3 v8 : BitVec 32)
    (Hrow : AxOpsem.grow (gtAdGd GT) hB = AxSpinX4.bRow t1 t3 t4 t5 t6 t8 t10 v1 v4 v5 v10 v3 v8)
    (Hnowrap : v8.toNat + 1 < 2 ^ 32) :
    ⊢ ISL -∗ notheld (GF := GF) nm.xnReg Lx.xlLk hB -∗
      AxAnnot.annotOwn (hB, 1) iprop(⌜AxSpinX5.F1 (gtAdGd GT).gdG⌝) -∗
      AxAnnot.annotOwn (hB, 3) iprop(⌜F3 (gtAdGd GT).gdG⌝) -∗
      AxAnnot.annotOwn (hB, 4) iprop(⌜F4 (gtAdGd GT).gdG⌝) -∗
      ∀ rs : RegFile, TWB ⟨hp cpu bRc rs, 5⟩ := by
  have Hne : 5 ≠ (AxOpsem.grow (gtAdGd GT) hB).length := by rw [Hrow]; simp [AxSpinX4.bRow]
  have Hl5 := AxSpinX5.bL (gtAdGd GT) t1 t3 t4 t5 t6 t8 t10 v1 v4 v5 v10 v3 v8 Hrow 5 _ rfl
  have Hadv := advLoad (gtAdGd GT) hB 5 false (paZ lcpa) t5 (WeakInterpProj.wbytes 8 v5)
    (by rw [← gxLblGrow]; exact Hl5)
  have H := nshRead (hlc := hlc) (pol := xv6Pol GT) (gtAdGd GT) Xv6N Unit (protXv6 Lx) nm cpu hB
    ΦB 8 (by decide) lcpa lcpaRam (AxSpinX4.ldkK 8 (fun _ => bAcq)) 5 Hne Hadv
    iprop(ISL ∗ notheld (GF := GF) nm.xnReg Lx.xlLk hB ∗
      AxAnnot.annotOwn (hB, 1) iprop(⌜AxSpinX5.F1 (gtAdGd GT).gdG⌝) ∗
      AxAnnot.annotOwn (hB, 3) iprop(⌜F3 (gtAdGd GT).gdG⌝) ∗
      AxAnnot.annotOwn (hB, 4) iprop(⌜F4 (gtAdGd GT).gdG⌝))
    (fun v rs Hgv => by
      have Hnw : gisW (gtAdGd GT).gdG (hB, 5) = false := by unfold gisW; rw [Hl5]; rfl
      iintro ⟨#Hil, Hnh, H1, H3, H4⟩
      ihave Hfe := fxCpuRacy (hlc := hlc) (GF := GF) Lx GT nm LxOk Hcons (hB, 5) Hnw
      iapply (evPlain (hlc := hlc) (pol := xv6Pol GT) (gtAdGd GT) Xv6N Unit (protXv6 Lx) nm hB 5
        iprop(⌜F5 (gtAdGd GT).gdG⌝) iprop(True) _ _ Hgv) $$ [Hfe]
      · iapply (@flowEqDynMono hlc GF _ (AxSpinX2.xG Lx GT nm) (xv6Pol GT) (gtAdGd GT) (hB, 5) _
          (∅ : Mea GF) iprop(⌜F5 (gtAdGd GT).gdG⌝) iprop(⌜F5 (gtAdGd GT).gdG⌝ ∗ True)) $$ [] Hfe
        inext
        iintro H
        isplitl [H]
        · iexact H
        · itrivial
      iintro H5 _
      iapply (AxSpinX5.wB6 (hlc := hlc) GT nm cpu Hcons t1 t3 t4 t5 t6 t8 t10 v1 v4 v5 v10 v3 v8
        Hrow Hnowrap) $$ Hil Hnh [$H1 $H3 $H4 $H5] %rs)
  iintro #Hil Hnh H1 H3 H4
  iapply H $$ [$Hil $Hnh $H1 $H3 $H4]

/-- k4: the READ-ONLY read (text / PTE word): the image. -/
theorem AxSpinX5.wB4 (GT : GdexecT) (nm : Xv6N) (cpu : CPU)
    (Hcons : rvwmoCatConsistent (gtAdGd GT))
    (t1 t3 t4 t5 : List Nat) (t6 : Nat) (t8 t10 : List Nat) (v1 v4 v5 v10 : BitVec 64)
    (v3 v8 : BitVec 32)
    (Hrow : AxOpsem.grow (gtAdGd GT) hB = AxSpinX4.bRow t1 t3 t4 t5 t6 t8 t10 v1 v4 v5 v10 v3 v8)
    (Hnowrap : v8.toNat + 1 < 2 ^ 32) :
    ⊢ ISL -∗ notheld (GF := GF) nm.xnReg Lx.xlLk hB -∗
      AxAnnot.annotOwn (hB, 1) iprop(⌜AxSpinX5.F1 (gtAdGd GT).gdG⌝) -∗
      AxAnnot.annotOwn (hB, 3) iprop(⌜F3 (gtAdGd GT).gdG⌝) -∗
      ∀ rs : RegFile, TWB ⟨hp cpu bRo rs, 4⟩ := by
  have Hne : 4 ≠ (AxOpsem.grow (gtAdGd GT) hB).length := by rw [Hrow]; simp [AxSpinX4.bRow]
  have Hl4 := AxSpinX5.bL (gtAdGd GT) t1 t3 t4 t5 t6 t8 t10 v1 v4 v5 v10 v3 v8 Hrow 4 _ rfl
  have Hadv := advLoad (gtAdGd GT) hB 4 false (paZ ropa) t4 (WeakInterpProj.wbytes 8 v4)
    (by rw [← gxLblGrow]; exact Hl4)
  have H := nshRead (hlc := hlc) (pol := xv6Pol GT) (gtAdGd GT) Xv6N Unit (protXv6 Lx) nm cpu hB
    ΦB 8 (by decide) ropa ropaRam (AxSpinX4.ldkK 8 (fun _ => bRc)) 4 Hne Hadv
    iprop(ISL ∗ notheld (GF := GF) nm.xnReg Lx.xlLk hB ∗
      AxAnnot.annotOwn (hB, 1) iprop(⌜AxSpinX5.F1 (gtAdGd GT).gdG⌝) ∗
      AxAnnot.annotOwn (hB, 3) iprop(⌜F3 (gtAdGd GT).gdG⌝))
    (fun v rs Hgv => by
      have Hnw : gisW (gtAdGd GT).gdG (hB, 4) = false := by unfold gisW; rw [Hl4]; rfl
      have Hnwr : ∀ w' a v', a ∈ clRange (paZ ropa) 8 → gwritesByte (gtAdGd GT).gdG w' a v' →
          WeakRvwmoGraph.gpo (gtAdGd GT).gdG w' (hB, 4) → False := by
        intro w' a v' Ha Hw' Hpo
        obtain ⟨k', rfl, Hk, Hc⟩ := bWrBefore GT t1 t3 t4 t5 t6 t8 t10 v1 v4 v5 v10 v3 v8 Hrow
          w' a v' 4 Hw' Hpo
        rw [inClr] at Ha
        simp only [lkZV, lcZV, npZV, skZV, nfZV, roZV] at Ha Hc
        omega
      iintro ⟨#Hil, Hnh, H1, H3⟩
      ihave Hfe := fxRoReadn (hlc := hlc) (GF := GF) Lx GT nm LxOk Hcons (hB, 4)
        (clRange (paZ ropa) 8) Hnw (fun a Ha => Ha) Hnwr
      iapply (evPlain (hlc := hlc) (pol := xv6Pol GT) (gtAdGd GT) Xv6N Unit (protXv6 Lx) nm hB 4
        iprop(⌜F4 (gtAdGd GT).gdG⌝) iprop(True) _ _ Hgv) $$ [Hfe]
      · iapply (@flowEqDynMono hlc GF _ (AxSpinX2.xG Lx GT nm) (xv6Pol GT) (gtAdGd GT) (hB, 4) _
          (∅ : Mea GF) iprop(⌜F4 (gtAdGd GT).gdG⌝) iprop(⌜F4 (gtAdGd GT).gdG⌝ ∗ True)) $$ [] Hfe
        inext
        iintro H
        isplitl [H]
        · iexact H
        · itrivial
      iintro H4 _
      iapply (AxSpinX5.wB5 (hlc := hlc) GT nm cpu Hcons t1 t3 t4 t5 t6 t8 t10 v1 v4 v5 v10 v3 v8
        Hrow Hnowrap) $$ Hil Hnh H1 H3 H4 %rs)
  iintro #Hil Hnh H1 H3
  iapply H $$ [$Hil $Hnh $H1 $H3]

/-- k3: the struct-cpu field read (PRIVATE reload of noff = 1). -/
theorem AxSpinX5.wB3 (GT : GdexecT) (nm : Xv6N) (cpu : CPU)
    (Hcons : rvwmoCatConsistent (gtAdGd GT))
    (t1 t3 t4 t5 : List Nat) (t6 : Nat) (t8 t10 : List Nat) (v1 v4 v5 v10 : BitVec 64)
    (v3 v8 : BitVec 32)
    (Hrow : AxOpsem.grow (gtAdGd GT) hB = AxSpinX4.bRow t1 t3 t4 t5 t6 t8 t10 v1 v4 v5 v10 v3 v8)
    (Hnowrap : v8.toNat + 1 < 2 ^ 32) :
    ⊢ ISL -∗ notheld (GF := GF) nm.xnReg Lx.xlLk hB -∗
      AxAnnot.annotOwn (hB, 1) iprop(⌜AxSpinX5.F1 (gtAdGd GT).gdG⌝) -∗
      ∀ rs : RegFile, TWB ⟨hp cpu bLn rs, 3⟩ := by
  have Hne : 3 ≠ (AxOpsem.grow (gtAdGd GT) hB).length := by rw [Hrow]; simp [AxSpinX4.bRow]
  have Hl2 := AxSpinX5.bL (gtAdGd GT) t1 t3 t4 t5 t6 t8 t10 v1 v4 v5 v10 v3 v8 Hrow 2 _ rfl
  have Hl3 := AxSpinX5.bL (gtAdGd GT) t1 t3 t4 t5 t6 t8 t10 v1 v4 v5 v10 v3 v8 Hrow 3 _ rfl
  obtain ⟨Hw2, -⟩ := gwbStoren _ _ _ _ _ Hl2
  have Hadv := advLoad (gtAdGd GT) hB 3 false (paZ nfpa) t3 (WeakInterpProj.wbytes 4 v3)
    (by rw [← gxLblGrow]; exact Hl3)
  have H := nshRead (hlc := hlc) (pol := xv6Pol GT) (gtAdGd GT) Xv6N Unit (protXv6 Lx) nm cpu hB
    ΦB 4 (by decide) nfpa nfpaRam (AxSpinX4.ldkK 4 (fun _ => bRo)) 3 Hne Hadv
    iprop(ISL ∗ notheld (GF := GF) nm.xnReg Lx.xlLk hB ∗
      AxAnnot.annotOwn (hB, 1) iprop(⌜AxSpinX5.F1 (gtAdGd GT).gdG⌝))
    (fun v rs Hgv => by
      have Hnw : gisW (gtAdGd GT).gdG (hB, 3) = false := by unfold gisW; rw [Hl3]; rfl
      have Hsrc : ∀ (j : Nat) a v', (clRange (paZ nfpa) 4)[j]? = some a →
          (WeakInterpProj.wbytes 4 one32)[j]? = some v' →
          gwritesByte (gtAdGd GT).gdG (hB, 2) a v' := by
        intro j a v' Hj Hv'
        obtain ⟨rfl, -⟩ := AxSpinX4.clRangeLookup _ _ _ _ Hj
        exact Hw2 j v' Hv'
      have Hlen : (WeakInterpProj.wbytes 4 one32).length = (clRange (paZ nfpa) 4).length := by
        rw [wbytesLength]
        simp [clRange]
      have Hlast : ∀ w' a v', a ∈ clRange (paZ nfpa) 4 → gwritesByte (gtAdGd GT).gdG w' a v' →
          WeakRvwmoGraph.gpo (gtAdGd GT).gdG w' (hB, 3) →
          w' = (hB, 2) ∨ WeakRvwmoGraph.gpo (gtAdGd GT).gdG w' (hB, 2) := by
        intro w' a v' Ha Hw' Hpo
        obtain ⟨k', rfl, Hk, Hc⟩ := bWrBefore GT t1 t3 t4 t5 t6 t8 t10 v1 v4 v5 v10 v3 v8 Hrow
          w' a v' 3 Hw' Hpo
        rw [inClr] at Ha
        simp only [lkZV, lcZV, npZV, skZV, nfZV] at Ha Hc
        left
        have Hk2 : k' = 2 := by omega
        rw [Hk2]
      iintro ⟨#Hil, Hnh, H1⟩
      ihave Hfe := fxPrivReadn (hlc := hlc) (GF := GF) Lx GT nm LxOk Hcons (hB, 3) (hB, 2)
        (clRange (paZ nfpa) 4) (WeakInterpProj.wbytes 4 one32) Hnw
        (fun a Ha => (privLx a _).2 ⟨rfl, Or.inr Ha⟩) Hsrc Hlen
        (gpoRow (gtAdGd GT) hB 2 3 _ _ Hl2 Hl3 (by decide)) Hlast
      iapply (evPlain (hlc := hlc) (pol := xv6Pol GT) (gtAdGd GT) Xv6N Unit (protXv6 Lx) nm hB 3
        iprop(⌜F3 (gtAdGd GT).gdG⌝) iprop(True) _ _ Hgv) $$ [Hfe]
      · iapply (@flowEqDynMono hlc GF _ (AxSpinX2.xG Lx GT nm) (xv6Pol GT) (gtAdGd GT) (hB, 3) _
          (∅ : Mea GF) iprop(⌜F3 (gtAdGd GT).gdG⌝) iprop(⌜F3 (gtAdGd GT).gdG⌝ ∗ True)) $$ [] Hfe
        inext
        iintro H
        isplitl [H]
        · iexact H
        · itrivial
      iintro H3 _
      iapply (AxSpinX5.wB4 (hlc := hlc) GT nm cpu Hcons t1 t3 t4 t5 t6 t8 t10 v1 v4 v5 v10 v3 v8
        Hrow Hnowrap) $$ Hil Hnh H1 H3 %rs)
  iintro #Hil Hnh H1
  iapply H $$ [$Hil $Hnh $H1]

/-- k2: the struct-cpu field write (PRIVATE). -/
theorem AxSpinX5.wB2 (GT : GdexecT) (nm : Xv6N) (cpu : CPU)
    (Hcons : rvwmoCatConsistent (gtAdGd GT))
    (t1 t3 t4 t5 : List Nat) (t6 : Nat) (t8 t10 : List Nat) (v1 v4 v5 v10 : BitVec 64)
    (v3 v8 : BitVec 32)
    (Hrow : AxOpsem.grow (gtAdGd GT) hB = AxSpinX4.bRow t1 t3 t4 t5 t6 t8 t10 v1 v4 v5 v10 v3 v8)
    (Hnowrap : v8.toNat + 1 < 2 ^ 32) :
    ⊢ ISL -∗ notheld (GF := GF) nm.xnReg Lx.xlLk hB -∗
      AxAnnot.annotOwn (hB, 1) iprop(⌜AxSpinX5.F1 (gtAdGd GT).gdG⌝) -∗
      ∀ rs : RegFile, TWB ⟨hp cpu bSn rs, 2⟩ := by
  have Hne : 2 ≠ (AxOpsem.grow (gtAdGd GT) hB).length := by rw [Hrow]; simp [AxSpinX4.bRow]
  have Hl2 := AxSpinX5.bL (gtAdGd GT) t1 t3 t4 t5 t6 t8 t10 v1 v4 v5 v10 v3 v8 Hrow 2 _ rfl
  have H := nshWrite (hlc := hlc) (pol := xv6Pol GT) (gtAdGd GT) Xv6N Unit (protXv6 Lx) nm cpu hB
    ΦB 4 nfpa nfpaRam one32 bLn 2 Hne
    iprop(ISL ∗ notheld (GF := GF) nm.xnReg Lx.xlLk hB ∗
      AxAnnot.annotOwn (hB, 1) iprop(⌜AxSpinX5.F1 (gtAdGd GT).gdG⌝))
    (fun rs => by
      have Hval := gdataSt GT 2 _ 4 one32 _ Hl2
      obtain ⟨-, Hsg2⟩ := gwbStoren _ _ _ _ _ Hl2
      have Hisw : gisW (gtAdGd GT).gdG (hB, 2) = true := by unfold gisW; rw [Hl2]; rfl
      have Hpriv : ∀ a v, gwritesByte (gtAdGd GT).gdG (hB, 2) a v → priv Lx a (hB, 2).1 := by
        intro a v Hw
        obtain ⟨j, Hj, rfl⟩ := Hsg2 a v Hw
        have hj := (List.getElem?_eq_some_iff.1 Hj).1
        rw [wbytesLength] at hj
        exact (privLx _ _).2 ⟨rfl, Or.inr ((inClr _ _ _).2 ⟨by omega, by omega⟩)⟩
      iintro ⟨#Hil, Hnh, H1⟩
      ihave Hfe := fxPrivWrite (hlc := hlc) (GF := GF) Lx GT nm LxOk Hcons (hB, 2) Hisw Hpriv
      iapply (evPlain (hlc := hlc) (pol := xv6Pol GT) (gtAdGd GT) Xv6N Unit (protXv6 Lx) nm hB 2
        iprop(True) iprop(True) _ _ Hval) $$ [Hfe]
      · iapply (@flowEqDynMono hlc GF _ (AxSpinX2.xG Lx GT nm) (xv6Pol GT) (gtAdGd GT) (hB, 2) _
          (∅ : Mea GF) iprop(True) iprop(True ∗ True)) $$ [] Hfe
        inext
        iintro _
        isplitl []
        · itrivial
        · itrivial
      iintro _ _
      iapply (AxSpinX5.wB3 (hlc := hlc) GT nm cpu Hcons t1 t3 t4 t5 t6 t8 t10 v1 v4 v5 v10 v3 v8
        Hrow Hnowrap) $$ Hil Hnh H1 %rs)
  iintro #Hil Hnh H1
  iapply H $$ [$Hil $Hnh $H1]

/-- k1: the stack RELOAD (PRIVATE; rfi -- forwarded when deferred). -/
theorem wB1 (GT : GdexecT) (nm : Xv6N) (cpu : CPU) (Hcons : rvwmoCatConsistent (gtAdGd GT))
    (t1 t3 t4 t5 : List Nat) (t6 : Nat) (t8 t10 : List Nat) (v1 v4 v5 v10 : BitVec 64)
    (v3 v8 : BitVec 32)
    (Hrow : AxOpsem.grow (gtAdGd GT) hB = AxSpinX4.bRow t1 t3 t4 t5 t6 t8 t10 v1 v4 v5 v10 v3 v8)
    (Hnowrap : v8.toNat + 1 < 2 ^ 32) :
    ⊢ ISL -∗ notheld (GF := GF) nm.xnReg Lx.xlLk hB -∗
      ∀ rs : RegFile, TWB ⟨hp cpu bLs rs, 1⟩ := by
  have Hne : 1 ≠ (AxOpsem.grow (gtAdGd GT) hB).length := by rw [Hrow]; simp [AxSpinX4.bRow]
  have Hl0 := AxSpinX5.bL (gtAdGd GT) t1 t3 t4 t5 t6 t8 t10 v1 v4 v5 v10 v3 v8 Hrow 0 _ rfl
  have Hl1 := AxSpinX5.bL (gtAdGd GT) t1 t3 t4 t5 t6 t8 t10 v1 v4 v5 v10 v3 v8 Hrow 1 _ rfl
  obtain ⟨Hw0, -⟩ := gwbStoren _ _ _ _ _ Hl0
  have Hadv := advLoad (gtAdGd GT) hB 1 false (paZ skpa) t1 (WeakInterpProj.wbytes 8 v1)
    (by rw [← gxLblGrow]; exact Hl1)
  have H := nshRead (hlc := hlc) (pol := xv6Pol GT) (gtAdGd GT) Xv6N Unit (protXv6 Lx) nm cpu hB
    ΦB 8 (by decide) skpa skpaRam (AxSpinX4.ldkK 8 (fun _ => bSn)) 1 Hne Hadv
    iprop(ISL ∗ notheld (GF := GF) nm.xnReg Lx.xlLk hB)
    (fun v rs Hgv => by
      have Hnw : gisW (gtAdGd GT).gdG (hB, 1) = false := by unfold gisW; rw [Hl1]; rfl
      have Hsrc : ∀ (j : Nat) a v', (clRange (paZ skpa) 8)[j]? = some a →
          (WeakInterpProj.wbytes 8 Xv)[j]? = some v' →
          gwritesByte (gtAdGd GT).gdG (hB, 0) a v' := by
        intro j a v' Hj Hv'
        obtain ⟨rfl, -⟩ := AxSpinX4.clRangeLookup _ _ _ _ Hj
        exact Hw0 j v' Hv'
      have Hlen : (WeakInterpProj.wbytes 8 Xv).length = (clRange (paZ skpa) 8).length := by
        rw [wbytesLength]
        simp [clRange]
      have Hlast : ∀ w' a v', a ∈ clRange (paZ skpa) 8 → gwritesByte (gtAdGd GT).gdG w' a v' →
          WeakRvwmoGraph.gpo (gtAdGd GT).gdG w' (hB, 1) →
          w' = (hB, 0) ∨ WeakRvwmoGraph.gpo (gtAdGd GT).gdG w' (hB, 0) := by
        intro w' a v' Ha Hw' Hpo
        obtain ⟨k', rfl, Hk, Hc⟩ := bWrBefore GT t1 t3 t4 t5 t6 t8 t10 v1 v4 v5 v10 v3 v8 Hrow
          w' a v' 1 Hw' Hpo
        left
        have Hk0 : k' = 0 := by omega
        rw [Hk0]
      iintro ⟨#Hil, Hnh⟩
      ihave Hfe := fxPrivReadn (hlc := hlc) (GF := GF) Lx GT nm LxOk Hcons (hB, 1) (hB, 0)
        (clRange (paZ skpa) 8) (WeakInterpProj.wbytes 8 Xv) Hnw
        (fun a Ha => (privLx a _).2 ⟨rfl, Or.inl Ha⟩) Hsrc Hlen
        (gpoRow (gtAdGd GT) hB 0 1 _ _ Hl0 Hl1 (by decide)) Hlast
      iapply (evPlain (hlc := hlc) (pol := xv6Pol GT) (gtAdGd GT) Xv6N Unit (protXv6 Lx) nm hB 1
        iprop(⌜AxSpinX5.F1 (gtAdGd GT).gdG⌝) iprop(True) _ _ Hgv) $$ [Hfe]
      · iapply (@flowEqDynMono hlc GF _ (AxSpinX2.xG Lx GT nm) (xv6Pol GT) (gtAdGd GT) (hB, 1) _
          (∅ : Mea GF) iprop(⌜AxSpinX5.F1 (gtAdGd GT).gdG⌝)
          iprop(⌜AxSpinX5.F1 (gtAdGd GT).gdG⌝ ∗ True)) $$ [] Hfe
        inext
        iintro H
        isplitl [H]
        · iexact H
        · itrivial
      iintro H1 _
      iapply (AxSpinX5.wB2 (hlc := hlc) GT nm cpu Hcons t1 t3 t4 t5 t6 t8 t10 v1 v4 v5 v10 v3 v8
        Hrow Hnowrap) $$ Hil Hnh H1 %rs)
  iintro #Hil Hnh
  iapply H $$ [$Hil $Hnh]

/-- k0: the stack SPILL (PRIVATE). -/
theorem AxSpinX5.wpdB (GT : GdexecT) (nm : Xv6N) (cpu : CPU)
    (Hcons : rvwmoCatConsistent (gtAdGd GT))
    (t1 t3 t4 t5 : List Nat) (t6 : Nat) (t8 t10 : List Nat) (v1 v4 v5 v10 : BitVec 64)
    (v3 v8 : BitVec 32)
    (Hrow : AxOpsem.grow (gtAdGd GT) hB = AxSpinX4.bRow t1 t3 t4 t5 t6 t8 t10 v1 v4 v5 v10 v3 v8)
    (Hnowrap : v8.toNat + 1 < 2 ^ 32) :
    ⊢ ISL -∗ notheld (GF := GF) nm.xnReg Lx.xlLk hB -∗
      TWB ⟨hp cpu AxSpinX4.bM0 zeroRegs, 0⟩ := by
  have Hne : 0 ≠ (AxOpsem.grow (gtAdGd GT) hB).length := by rw [Hrow]; simp [AxSpinX4.bRow]
  have Hl0 := AxSpinX5.bL (gtAdGd GT) t1 t3 t4 t5 t6 t8 t10 v1 v4 v5 v10 v3 v8 Hrow 0 _ rfl
  have H := nshWrite (hlc := hlc) (pol := xv6Pol GT) (gtAdGd GT) Xv6N Unit (protXv6 Lx) nm cpu hB
    ΦB 8 skpa skpaRam Xv bLs 0 Hne
    iprop(ISL ∗ notheld (GF := GF) nm.xnReg Lx.xlLk hB)
    (fun rs => by
      have Hval := gdataSt GT 0 _ 8 Xv _ Hl0
      obtain ⟨-, Hsg0⟩ := gwbStoren _ _ _ _ _ Hl0
      have Hisw : gisW (gtAdGd GT).gdG (hB, 0) = true := by unfold gisW; rw [Hl0]; rfl
      have Hpriv : ∀ a v, gwritesByte (gtAdGd GT).gdG (hB, 0) a v → priv Lx a (hB, 0).1 := by
        intro a v Hw
        obtain ⟨j, Hj, rfl⟩ := Hsg0 a v Hw
        have hj := (List.getElem?_eq_some_iff.1 Hj).1
        rw [wbytesLength] at hj
        exact (privLx _ _).2 ⟨rfl, Or.inl ((inClr _ _ _).2 ⟨by omega, by omega⟩)⟩
      iintro ⟨#Hil, Hnh⟩
      ihave Hfe := fxPrivWrite (hlc := hlc) (GF := GF) Lx GT nm LxOk Hcons (hB, 0) Hisw Hpriv
      iapply (evPlain (hlc := hlc) (pol := xv6Pol GT) (gtAdGd GT) Xv6N Unit (protXv6 Lx) nm hB 0
        iprop(True) iprop(True) _ _ Hval) $$ [Hfe]
      · iapply (@flowEqDynMono hlc GF _ (AxSpinX2.xG Lx GT nm) (xv6Pol GT) (gtAdGd GT) (hB, 0) _
          (∅ : Mea GF) iprop(True) iprop(True ∗ True)) $$ [] Hfe
        inext
        iintro _
        isplitl []
        · itrivial
        · itrivial
      iintro _ _
      iapply (wB1 (hlc := hlc) GT nm cpu Hcons t1 t3 t4 t5 t6 t8 t10 v1 v4 v5 v10 v3 v8 Hrow
        Hnowrap) $$ Hil Hnh %rs)
  iintro #Hil Hnh
  iapply H $$ [$Hil $Hnh] %zeroRegs

end wpdB

end Weak
