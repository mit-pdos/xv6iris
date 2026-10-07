/-
Weak: **A7 T3: the two lock3s certificates for the 2-hart program** (writer hart `A` running
`AxLock3Prog.l3pWRow`, reader hart `B` running `AxLock3Prog.l3pRRow`), over an ABSTRACT graph
`GD` (AxSL tier).

Rocq: `iris/AxLock3Thm.v` @ xxvzwolszwmp.

## The Rocq header, in substance

Builds on `AxLock3Prog` (rows, per-hart runs), `AxLock3Writer`/`AxLock3Reader(2)` (the four WPd
capstones: genesis/release-sourced × writer/reader), `AxProtLock3` (`lockAxpol`,
`lockHobAlloc`), `AxTierA2` (`tierAAdequacyAnn`) and the graph vocabulary.

THE DICHOTOMY.  Both acquires read the unlocked byte `b0` off `L` (`Hb0A`/`Hb0B`).
`gloadValue` pins each acquire's read either to the image (`t = 0`, genesis) or to a prior write
(`gwriteAt t = some w`).  The only writes of `b0` to `L` are `(A,3)` and `(B,3)` (each hart's
release — `lock3sWLwrite`/`lock3sRLwrite`).  A hart's acquire never sources its OWN release (the
release is `gacqPo`-after the acquire, hence `gmoLt`-after; `gvisible` would close a position
cycle).  Both genesis is excluded by `lockExtRmwReader0Unique` (forces `A = B`); both
release-sourced is a `gpos` cycle (`omega`).  This leaves the two cases of `lock3sDichotomy`.
The excluded third case (an acquire reading the other hart's `b1`) is excluded only by
`Hb0A`/`Hb0B` (stated honestly, as in Rocq).

`lock3sVerified` composes the four capstones via the dichotomy in the `[∗list]` shape of
`tierAAdequacyAnn`'s `Hwp`; `lock3sValue` discharges `tierAAdequacyAnn` at the concrete
`lock3GF` and reads `PreaderPure` back off the reader hart, specialising its first conjunct at
`j := A` via the row fact that `(A,1)` writes `x` with `vA`.

**Fetches.** None (hand-built monad terms; Stage C: no `T`).

## Deviations from Rocq

1. NAMES: camelCase (map below).  No name of this file is in the duplicated-name table.
   Lean-only helpers (file-qualified): `AxLock3Thm.bigSepLPair` (`[∗list]` over `[a, b]`),
   `AxLock3Thm.s0`/`sN`/`nSteps`/`post` (Rocq's proof-local `set`s of `lock3s_value`), and the
   `AxLock3Thm.lock3GF*` instances.
2. `lock3Σ := #[invΣ; axlogΣ hent; ax_lockΣ; axannotΣ]` ↦ `lock3GF`, an explicit slot table over
   `BundledGFunctors.default` (as `AxTokLedgerMp.mprGF`): wsat + credits at slots 0–3, the
   history log `AxlogRF Hent` at 4, the claimed set `constOF (Auth ClaimedUR)` at 5, the
   annotation cameras at 6–8.  THIS FILE ALLOCATES the concrete classes `AxlogG lock3GF Hent`,
   `AxLockG lock3GF`, `AxannotG lock3GF`, `InvGpreS lock3GF`; the ghost names themselves are
   allocated by `lockHobAlloc` (history + claimed) and `tierAAdequacyAnn` (annotations).
3. `lock3sVerified` is stated GENERICALLY (stronger): any `GF` with `[AxlogG GF Hent]
   [AxLockG GF]`, any `hlc` with `[InvGS_gen hlc GF] [AxannotGS GF]` (Rocq: `lock3Σ`,
   `HasNoLc`); the policy `lockAxpol` is passed explicitly (`@tierAWpd … lockAxpol …`).
   `init_regstate` ↦ arbitrary register files `rsA`/`rsB` in `lock3sVerified` (as the
   capstones, AxLock3Writer deviation 6) and `zeroRegs` (ExecLib) in `lock3sValue`.
4. O2 Stage C: Rocq's `T := λ _, False` and the reader capstones' `HTx` argument `(λ f, f)` are
   gone.  `tierAAstep` is `astepAnyNfGv` (the runs `l3pWRun`/`l3pRRun` apply directly).
5. Statement shapes: `gd_g GD` ↦ `GD.gdG`; `grow GD i !! k` ↦ `(AxOpsem.grow GD i)[k]?`;
   `Z` ↦ `Int`, `bv 8` ↦ `BitVec 8`, `Arch.pa` ↦ `PAddr`; `S k` ↦ `k + 1`; `if decide (i = A)`
   ↦ `if i = A`; Rocq's local notations `B0`/`B1` ↦ `b0`/`b1`.  Graph lemmas of the writer file
   are used at their Lean arities (`gwritesByteOfStore GD …`, `gwritesByteOfRmw GD …`: no
   `L x Hxy Lpa xpa HLeq Hxeq`).

**Rocq → Lean name map.**  `lock3Σ` `lock3GF`, `lock3s_gx_lbl_grow` `lock3sGxLblGrow`,
`lock3s_greads_byte_rmw0` `lock3sGreadsByteRmw0`, `lock3s_w_Lwrite` `lock3sWLwrite`,
`lock3s_r_Lwrite` `lock3sRLwrite`, `lock3s_dichotomy` `lock3sDichotomy`, `lock3s_verified`
`lock3sVerified`, `lock3s_value` `lock3sValue`.

**Dropped:** nothing (Rocq 1 definition + 7 lemmas; Lean 1 + 7, plus the Lean-only helpers of
deviation 1).
-/
import Weak.AxLock3Reader2
import Weak.AxTierA2
import Weak.ExecLib

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D

/-! # 0. A concrete functor list for adequacy (Rocq `lock3Σ`; header deviation 2) -/

section lock3GFSec
open Iris Iris.BI Iris.Std Std MachCSL COFE

def lock3GF : BundledGFunctors :=
  BundledGFunctors.default
  |>.set 0 ⟨InvMapF, inferInstance⟩
  |>.set 1 ⟨constOF CoPsetDisjL, inferInstance⟩
  |>.set 2 ⟨constOF (DisjointLeibnizSet PosSet), inferInstance⟩
  |>.set 3 ⟨Auth.AuthURF (constOF Credit), inferInstance⟩
  |>.set 4 ⟨AxlogRF Hent, inferInstance⟩
  |>.set 5 ⟨constOF (Auth ClaimedUR), inferInstance⟩
  |>.set 6 ⟨DFracAgree.DFracAgreeRF (LaterOF IdOF), inferInstance⟩
  |>.set 7 ⟨constOF (HeapView Geid (Agree (DiscreteO GName)) (GMapF Geid)), inferInstance⟩
  |>.set 8 ⟨constOF AxannotSetR, inferInstance⟩

instance AxLock3Thm.lock3GFInvMap : ElemG lock3GF InvMapF := ⟨0, rfl⟩
instance AxLock3Thm.lock3GFEnabled : ElemG lock3GF (constOF CoPsetDisjL) := ⟨1, rfl⟩
instance AxLock3Thm.lock3GFDisabled : ElemG lock3GF (constOF (DisjointLeibnizSet PosSet)) :=
  ⟨2, rfl⟩
instance AxLock3Thm.lock3GFCredit : ElemG lock3GF (Auth.AuthURF (constOF Credit)) := ⟨3, rfl⟩
instance AxLock3Thm.lock3GFInvGpreS : InvGpreS lock3GF :=
  ⟨⟨inferInstance, inferInstance, inferInstance⟩, ⟨inferInstance⟩⟩
instance AxLock3Thm.lock3GFAxlogG : AxlogG lock3GF Hent := { axlogInG := ⟨4, rfl⟩ }
instance AxLock3Thm.lock3GFAxLockG : AxLockG lock3GF := { axLockInG := ⟨5, rfl⟩ }
instance AxLock3Thm.lock3GFAxannotG : AxannotG lock3GF :=
  { axannotSavedG := { elemG := ⟨6, rfl⟩ }, axannotMapG := ⟨⟨7, rfl⟩⟩, axannotSetG := ⟨8, rfl⟩ }

end lock3GFSec

/-- Lean-only: `[∗list]` over a two-element list. -/
theorem AxLock3Thm.bigSepLPair {GF : BundledGFunctors} {α : Type} (a b : α)
    (Φ : α → IProp GF) : ([∗list] c ∈ [a, b], Φ c) ⊣⊢ Φ a ∗ Φ b :=
  BigSepL.bigSepL_cons.trans (sep_congr .rfl BigSepL.bigSepL_singleton)

/-! # 1. Graph helpers -/

theorem lock3sGxLblGrow (GD : Gdexec) (i k : Nat) :
    gxLbl GD.gdG (i, k) = (AxOpsem.grow GD i)[k]? := by
  unfold AxOpsem.grow growG gxLbl
  dsimp only
  cases GD.gdG.gxProg[i]? <;> rfl

theorem lock3sGreadsByteRmw0 (GD : Gdexec) (e : Geid) (base : Int) (t : Nat)
    (rv wv : BitVec 8) (aq rl : Bool) :
    gxLbl GD.gdG e = some (.LRmw aq rl base [t] [rv] [wv] .WCplain) →
    greadsByte GD.gdG e base t rv := fun Hlbl =>
  ⟨_, base, [t], [rv], 0, Hlbl, rfl, rfl, rfl, by simp [accAddr]⟩

/-- Every write of `L` on the WRITER-shaped row `i` is its RMW write-half (position 0, value
`b1`) or its release (position 3, value `b0`). -/
theorem lock3sWLwrite (GD : Gdexec) (L x : Int) (hxy : x ≠ L) (Lpa xpa : PAddr)
    (HLeq : L = l3pLbase Lpa) (Hxeq : x = l3pXbase xpa)
    (i : Agent) (t : Nat) (old v : BitVec 8) (Hrow : AxOpsem.grow GD i = l3pWRow Lpa xpa t old v)
    (w : Geid) (v' : BitVec 8) (Heq : w.1 = i) (Hwb : gwritesByte GD.gdG w L v') :
    (w = (i, 0) ∧ v' = b1) ∨ (w = (i, 3) ∧ v' = b0) := by
  obtain ⟨j, k⟩ := w
  simp only at Heq
  subst Heq
  have Hlbl := lock3sGxLblGrow GD j k
  rw [Hrow] at Hlbl
  match k, Hlbl, Hwb with
  | 0, Hlbl, Hwb =>
    have Hl0 : gxLbl GD.gdG (j, 0) = some (.LRmw true false L [t] [old] [b1] .WCplain) := by
      rw [Hlbl, HLeq]; rfl
    exact .inl ⟨rfl, gwritesByteDet _ _ _ _ _ Hwb
      (gwritesByteOfRmw GD (j, 0) L [t] [old] b1 true false Hl0).1⟩
  | 1, Hlbl, Hwb =>
    have Hl1 : gxLbl GD.gdG (j, 1) = some (.LStore false x [v] .WCplain) := by
      rw [Hlbl, Hxeq]; rfl
    exact absurd ((gwritesByteOfStore GD (j, 1) x v .WCplain Hl1).2 L v' Hwb).symm hxy
  | 2, Hlbl, Hwb =>
    obtain ⟨l, base, vs, jj, Hl, Hwr, _⟩ := Hwb
    rw [Hlbl] at Hl
    cases Hl
    simp [lbWr] at Hwr
  | 3, Hlbl, Hwb =>
    have Hl3 : gxLbl GD.gdG (j, 3) = some (.LStore false L [b0] .WCplain) := by
      rw [Hlbl, HLeq]; rfl
    exact .inr ⟨rfl, gwritesByteDet _ _ _ _ _ Hwb
      (gwritesByteOfStore GD (j, 3) L b0 .WCplain Hl3).1⟩
  | k' + 4, Hlbl, Hwb =>
    obtain ⟨l, base, vs, jj, Hl, _⟩ := Hwb
    rw [Hlbl] at Hl
    simp [l3pWRow] at Hl

/-- Same, for the READER-shaped row: position 1 is an `LLoad` (not a write at all). -/
theorem lock3sRLwrite (GD : Gdexec) (L x : Int) (hxy : x ≠ L) (Lpa xpa : PAddr)
    (HLeq : L = l3pLbase Lpa) (Hxeq : x = l3pXbase xpa)
    (i : Agent) (t : Nat) (old : BitVec 8) (tx : Nat) (vBl : BitVec 8)
    (Hrow : AxOpsem.grow GD i = l3pRRow Lpa xpa t old tx vBl)
    (w : Geid) (v' : BitVec 8) (Heq : w.1 = i) (Hwb : gwritesByte GD.gdG w L v') :
    (w = (i, 0) ∧ v' = b1) ∨ (w = (i, 3) ∧ v' = b0) := by
  have _ := hxy
  have _ := Hxeq
  obtain ⟨j, k⟩ := w
  simp only at Heq
  subst Heq
  have Hlbl := lock3sGxLblGrow GD j k
  rw [Hrow] at Hlbl
  match k, Hlbl, Hwb with
  | 0, Hlbl, Hwb =>
    have Hl0 : gxLbl GD.gdG (j, 0) = some (.LRmw true false L [t] [old] [b1] .WCplain) := by
      rw [Hlbl, HLeq]; rfl
    exact .inl ⟨rfl, gwritesByteDet _ _ _ _ _ Hwb
      (gwritesByteOfRmw GD (j, 0) L [t] [old] b1 true false Hl0).1⟩
  | 1, Hlbl, Hwb =>
    obtain ⟨l, base, vs, jj, Hl, Hwr, _⟩ := Hwb
    rw [Hlbl] at Hl
    cases Hl
    simp [lbWr] at Hwr
  | 2, Hlbl, Hwb =>
    obtain ⟨l, base, vs, jj, Hl, Hwr, _⟩ := Hwb
    rw [Hlbl] at Hl
    cases Hl
    simp [lbWr] at Hwr
  | 3, Hlbl, Hwb =>
    have Hl3 : gxLbl GD.gdG (j, 3) = some (.LStore false L [b0] .WCplain) := by
      rw [Hlbl, HLeq]; rfl
    exact .inr ⟨rfl, gwritesByteDet _ _ _ _ _ Hwb
      (gwritesByteOfStore GD (j, 3) L b0 .WCplain Hl3).1⟩
  | k' + 4, Hlbl, Hwb =>
    obtain ⟨l, base, vs, jj, Hl, _⟩ := Hwb
    rw [Hlbl] at Hl
    simp [l3pRRow] at Hl

/-! # 2. THE DICHOTOMY LEMMA -/

theorem lock3sDichotomy
    (GD : Gdexec) (L x : Int) (hxy : x ≠ L) (Lpa xpa : PAddr)
    (HLeq : L = l3pLbase Lpa) (Hxeq : x = l3pXbase xpa)
    (A B : Agent) (HAB : A ≠ B)
    (tA : Nat) (oldA vA : BitVec 8) (Hrow_A : AxOpsem.grow GD A = l3pWRow Lpa xpa tA oldA vA)
    (tB : Nat) (oldB : BitVec 8) (txB : Nat) (vB : BitVec 8)
    (Hrow_B : AxOpsem.grow GD B = l3pRRow Lpa xpa tB oldB txB vB)
    (Hcons : rvwmoCatConsistent GD)
    (Hharts : ∀ e : Geid, e ∈ GD.gdG.gxGmo → e.1 = A ∨ e.1 = B)
    (HimgL : GD.gdG.gxImg L = some b0)
    (Hb0A : oldA = b0) (Hb0B : oldB = b0) :
    (greadsByte GD.gdG (A, 0) L 0 b0 ∧
       gwritesByte GD.gdG (A, 3) L b0 ∧
       gobCat GD (A, 3) (B, 0) ∧
       lockExtRmwReader L GD (A, 3) (B, 0))
    ∨
    (greadsByte GD.gdG (B, 0) L 0 b0 ∧
       gwritesByte GD.gdG (B, 3) L b0 ∧
       gobCat GD (B, 3) (A, 0) ∧
       lockExtRmwReader L GD (B, 3) (A, 0)) := by
  have _ := HimgL
  subst Hb0A Hb0B
  obtain ⟨Hwf, Hppo, Hlv, _, _, _⟩ := Hcons
  have HlblA0 := l3pWLbl0 Lpa xpa GD A tA b0 vA Hrow_A
  rw [← HLeq] at HlblA0
  have HrdA0 := lock3sGreadsByteRmw0 GD (A, 0) L tA b0 b1 true false HlblA0
  have HwbA0 := (gwritesByteOfRmw GD (A, 0) L [tA] [b0] b1 true false HlblA0).1
  have HlblB0 := l3pRLbl0 Lpa xpa GD B tB b0 txB vB Hrow_B
  rw [← HLeq] at HlblB0
  have HrdB0 := lock3sGreadsByteRmw0 GD (B, 0) L tB b0 b1 true false HlblB0
  have HwbB0 := (gwritesByteOfRmw GD (B, 0) L [tB] [b0] b1 true false HlblB0).1
  have HlblA3 := l3pWLbl3 Lpa xpa GD A tA b0 vA Hrow_A
  rw [← HLeq] at HlblA3
  have HwbA3 := (gwritesByteOfStore GD (A, 3) L b0 .WCplain HlblA3).1
  have HlblB3 := l3pRLbl3 Lpa xpa GD B tB b0 txB vB Hrow_B
  rw [← HLeq] at HlblB3
  have HwbB3 := (gwritesByteOfStore GD (B, 3) L b0 .WCplain HlblB3).1
  have HA03 : gmoLt GD.gdG (A, 0) (A, 3) :=
    Hppo _ _ (.inl (.inr (.inr (.inr (.inr (.inl (l3pWGacqPoRel Lpa xpa GD A tA b0 vA
      Hrow_A)))))))
  have HB03 : gmoLt GD.gdG (B, 0) (B, 3) :=
    Hppo _ _ (.inl (.inr (.inr (.inr (.inr (.inl (l3pRGacqPoRel Lpa xpa GD B tB b0 txB vB
      Hrow_B)))))))
  have HmatchA := (Hlv (A, 0) L tA b0 HrdA0).1
  have HmatchB := (Hlv (B, 0) L tB b0 HrdB0).1
  have hgmo : ∀ w, gwritesByte GD.gdG w L b0 → w ∈ GD.gdG.gxGmo := fun w hw =>
    (List.mem_filter.1 (gwritesByteGwrites GD.gdG w L b0 Hwf hw)).1
  cases tA with
  | zero =>
    -- A genesis
    cases tB with
    | zero =>
      -- B genesis too: contradiction, forces A = B
      exfalso
      have Hr0A : lockExtRmwReader0 L GD (A, 0) := ⟨⟨b0, HrdA0⟩, ⟨b1, HwbA0⟩⟩
      have Hr0B : lockExtRmwReader0 L GD (B, 0) := ⟨⟨b0, HrdB0⟩, ⟨b1, HwbB0⟩⟩
      have Heq := lockExtRmwReader0Unique L GD (A, 0) (B, 0) ⟨Hwf, Hppo, Hlv, ‹_›, ‹_›, ‹_›⟩
        Hr0A Hr0B
      exact HAB (congrArg Prod.fst Heq)
    | succ tB' =>
      -- B release-sourced: resolve its source
      obtain ⟨w, Hgwa, Hwbw, Hvis⟩ := HmatchB
      rcases Hharts w (hgmo w Hwbw) with HwA | HwB
      · -- w = (A,3): B sourced by A's release, case (i)
        rcases lock3sWLwrite GD L x hxy Lpa xpa HLeq Hxeq A 0 b0 vA Hrow_A w b0 HwA Hwbw with
          ⟨rfl, Hbad⟩ | ⟨rfl, -⟩
        · exact absurd Hbad b0NeB1
        · refine .inl ⟨HrdA0, HwbA3, ?_, ?_⟩
          · exact gobCatStep GD _ _ (.inr (.inr (.inl ⟨⟨L, tB' + 1, b0, HrdB0, Hgwa⟩, HAB⟩)))
          · exact ⟨⟨tB' + 1, b0, HrdB0, Hgwa⟩, HAB, ⟨b1, HwbB0⟩⟩
      · -- w on hart B: self-source, contradiction
        exfalso
        rcases lock3sRLwrite GD L x hxy Lpa xpa HLeq Hxeq B (tB' + 1) b0 txB vB Hrow_B w b0 HwB
          Hwbw with ⟨rfl, Hbad⟩ | ⟨rfl, -⟩
        · exact b0NeB1 Hbad
        · rcases Hvis with ⟨_, _, Hp1⟩ | ⟨_, Hlt, _, _⟩
          · have Hp2 := HB03.2.2
            omega
          · simp at Hlt
  | succ tA' =>
    -- A release-sourced: resolve its source
    obtain ⟨wA, HgwaA, HwbwA, HvisA⟩ := HmatchA
    rcases Hharts wA (hgmo wA HwbwA) with HwAA | HwAB
    · -- wA on hart A: self-source, contradiction
      exfalso
      rcases lock3sWLwrite GD L x hxy Lpa xpa HLeq Hxeq A (tA' + 1) b0 vA Hrow_A wA b0 HwAA
        HwbwA with ⟨rfl, Hbad⟩ | ⟨rfl, -⟩
      · exact b0NeB1 Hbad
      · rcases HvisA with ⟨_, _, Hp1⟩ | ⟨_, Hlt, _, _⟩
        · have Hp2 := HA03.2.2
          omega
        · simp at Hlt
    · -- wA = (B,3): A release-sourced by B
      rcases lock3sRLwrite GD L x hxy Lpa xpa HLeq Hxeq B tB b0 txB vB Hrow_B wA b0 HwAB HwbwA
        with ⟨rfl, Hbad⟩ | ⟨rfl, -⟩
      · exact absurd Hbad b0NeB1
      · cases tB with
        | zero =>
          -- B genesis: case (ii)
          refine .inr ⟨HrdB0, HwbB3, ?_, ?_⟩
          · exact gobCatStep GD _ _
              (.inr (.inr (.inl ⟨⟨L, tA' + 1, b0, HrdA0, HgwaA⟩, Ne.symm HAB⟩)))
          · exact ⟨⟨tA' + 1, b0, HrdA0, HgwaA⟩, Ne.symm HAB, ⟨b1, HwbA0⟩⟩
        | succ tB' =>
          -- B also release-sourced: a position cycle, contradiction
          exfalso
          obtain ⟨wB, HgwaB, HwbwB, HvisB⟩ := HmatchB
          rcases Hharts wB (hgmo wB HwbwB) with HwBA | HwBB
          · rcases lock3sWLwrite GD L x hxy Lpa xpa HLeq Hxeq A (tA' + 1) b0 vA Hrow_A wB b0
              HwBA HwbwB with ⟨rfl, Hbad⟩ | ⟨rfl, -⟩
            · exact b0NeB1 Hbad
            · rcases HvisB with ⟨_, _, HpB⟩ | ⟨Heq, _, _, _⟩
              · rcases HvisA with ⟨_, _, HpA⟩ | ⟨Heq, _, _, _⟩
                · have Hp1 := HA03.2.2
                  have Hp2 := HB03.2.2
                  omega
                · exact HAB Heq.symm
              · exact HAB Heq
          · rcases lock3sRLwrite GD L x hxy Lpa xpa HLeq Hxeq B (tB' + 1) b0 txB vB Hrow_B wB b0
              HwBB HwbwB with ⟨rfl, Hbad⟩ | ⟨rfl, -⟩
            · exact b0NeB1 Hbad
            · rcases HvisB with ⟨_, _, Hp1⟩ | ⟨_, Hlt, _, _⟩
              · have Hp2 := HB03.2.2
                omega
              · simp at Hlt

/-! # 3. `lock3sVerified` — the WPd-level certificate (the four capstones via the dichotomy) -/

theorem lock3sVerified {GF : BundledGFunctors.{0,0,0}} [AxlogG GF Hent] [AxLockG GF]
    {hlc : HasLC} [InvGS_gen hlc GF] [AxannotGS GF]
    (GD : Gdexec) (L x : Int) (hxy : x ≠ L) (Lpa xpa : PAddr)
    (HLram : devAddr Lpa = false) (Hxram : devAddr xpa = false)
    (cpuA cpuB : CPU) (rsA rsB : RegFile) (HLeq : L = l3pLbase Lpa) (Hxeq : x = l3pXbase xpa)
    (A B : Agent) (HAB : A ≠ B)
    (tA : Nat) (oldA vA : BitVec 8) (Hrow_A : AxOpsem.grow GD A = l3pWRow Lpa xpa tA oldA vA)
    (tB : Nat) (oldB : BitVec 8) (txB : Nat) (vB : BitVec 8)
    (Hrow_B : AxOpsem.grow GD B = l3pRRow Lpa xpa tB oldB txB vB)
    (Hcons : rvwmoCatConsistent GD)
    (Hharts : ∀ e : Geid, e ∈ GD.gdG.gxGmo → e.1 = A ∨ e.1 = B)
    (HimgL : GD.gdG.gxImg L = some b0)
    (Hb0A : oldA = b0) (Hb0B : oldB = b0) (nm : lock3N) :
    ⊢ ([∗list] i ∈ [A, B], lock3Init (GF := GF) nm i) -∗
      [∗list] i ∈ [A, B],
        @tierAWpd GF hlc _ _ lockAxpol GD lock3N lock3ObSt0 (lock3ObStInterp0 L x) nm
          (if i = A then ⟨l3pWP0 Lpa xpa cpuA rsA vA, 0⟩ else ⟨l3pRP0 Lpa xpa cpuB rsB, 0⟩)
          .MaybeStuck i
          (fun _ => if i = A then iprop(True) else iprop(⌜PreaderPure L x GD B vB⌝)) := by
  have hBA : ¬ B = A := fun h => HAB h.symm
  rcases lock3sDichotomy GD L x hxy Lpa xpa HLeq Hxeq A B HAB tA oldA vA Hrow_A tB oldB txB vB
      Hrow_B Hcons Hharts HimgL Hb0A Hb0B with
    ⟨HrdA0, HwbA3, HgobAB, HrfeAB⟩ | ⟨HrdB0, HwbB3, HgobBA, HrfeBA⟩
  · have HWA := wpdWriterHart (GF := GF) (hlc := hlc) L x GD nm Lpa xpa cpuA A tA oldA vA hxy
      HLram Hxram HLeq Hxeq Hrow_A Hcons HimgL HrdA0 rsA
    have HWB := wpdReaderHartRel (GF := GF) (hlc := hlc) L x GD nm Lpa xpa cpuB B tB oldB txB vB
      hxy HLram Hxram HLeq Hxeq Hrow_B Hcons (A, 3) HwbA3 HgobAB HrfeAB A tA oldA vA rfl Hrow_A
      rsB
    unfold AxLock3Writer.twpd at HWA
    unfold AxLock3Reader.twpdr at HWB
    iintro H
    icases (AxLock3Thm.bigSepLPair A B _).1 $$ H with ⟨HA, HB⟩
    iapply (AxLock3Thm.bigSepLPair A B _).2
    simp only [↓reduceIte, if_neg hBA]
    isplitl [HA]
    · iapply HWA $$ HA
    · iapply HWB $$ HB
  · have HWA := wpdWriterHartRel (GF := GF) (hlc := hlc) L x GD nm Lpa xpa cpuA A tA oldA vA hxy
      HLram Hxram HLeq Hxeq Hrow_A Hcons (B, 3) HwbB3 HgobBA HrfeBA rsA
    have HWB := wpdReaderHart (GF := GF) (hlc := hlc) L x GD nm Lpa xpa cpuB B tB oldB txB vB
      hxy HLram Hxram HLeq Hxeq Hrow_B Hcons HimgL HrdB0 rsB
    unfold AxLock3Writer.twpd at HWA
    unfold AxLock3Reader.twpdr at HWB
    iintro H
    icases (AxLock3Thm.bigSepLPair A B _).1 $$ H with ⟨HA, HB⟩
    iapply (AxLock3Thm.bigSepLPair A B _).2
    simp only [↓reduceIte, if_neg hBA]
    isplitl [HA]
    · iapply HWA $$ HA
    · iapply HWB $$ HB

/-! # 4. `lock3sValue` — the PURE value certificate, via adequacy -/

/-- Lean-only: Rocq's proof-local `s0` of `lock3s_value`. -/
def AxLock3Thm.s0 (Lpa xpa : PAddr) (cpuA cpuB : CPU) (A : Agent) (vA : BitVec 8)
    (i : Agent) : Athread :=
  if i = A then ⟨l3pWP0 Lpa xpa cpuA zeroRegs vA, 0⟩ else ⟨l3pRP0 Lpa xpa cpuB zeroRegs, 0⟩

/-- Lean-only: Rocq's proof-local `sN`. -/
def AxLock3Thm.sN (cpuA cpuB : CPU) (A : Agent) (vB : BitVec 8) (i : Agent) : Athread :=
  if i = A then ⟨l3pWPfin cpuA zeroRegs, 4⟩
  else ⟨l3pRPfin cpuB zeroRegs (wordOfBytes 1 [vB]), 4⟩

/-- Lean-only: Rocq's proof-local `n`. -/
def AxLock3Thm.nSteps (A : Agent) (i : Agent) : Nat := if i = A then 5 else 6

/-- Lean-only: Rocq's proof-local `post`. -/
def AxLock3Thm.post (L x : Int) (GD : Gdexec) (A B : Agent) (vB : BitVec 8) (i : Agent)
    (_s : Athread) : Prop :=
  if i = A then True else PreaderPure L x GD B vB

theorem lock3sValue
    (GD : Gdexec) (L x : Int) (hxy : x ≠ L) (Lpa xpa : PAddr)
    (HLram : devAddr Lpa = false) (Hxram : devAddr xpa = false)
    (cpuA cpuB : CPU) (HLeq : L = l3pLbase Lpa) (Hxeq : x = l3pXbase xpa)
    (A B : Agent) (HAB : A ≠ B)
    (tA : Nat) (oldA vA : BitVec 8) (Hrow_A : AxOpsem.grow GD A = l3pWRow Lpa xpa tA oldA vA)
    (tB : Nat) (oldB : BitVec 8) (txB : Nat) (vB : BitVec 8)
    (Hrow_B : AxOpsem.grow GD B = l3pRRow Lpa xpa tB oldB txB vB)
    (Hcons : rvwmoCatConsistent GD)
    (Hharts : ∀ e : Geid, e ∈ GD.gdG.gxGmo → e.1 = A ∨ e.1 = B)
    (HimgL : GD.gdG.gxImg L = some b0)
    (Hb0A : oldA = b0) (Hb0B : oldB = b0) :
    (grfe GD.gdG (A, 3) (B, 0) → vB = vA) ∧
    (greadsByte GD.gdG (B, 0) L 0 b0 →
       ∀ bx, GD.gdG.gxImg x = some bx → vB = bx) := by
  have hBA : ¬ B = A := fun h => HAB h.symm
  have Hharts' : ∀ e : Geid, e ∈ GD.gdG.gxGmo → e.1 ∈ [A, B] := by
    intro e He
    rcases Hharts e He with h | h <;> simp [h]
  have Hnd : [A, B].Nodup := by simp [HAB]
  have HBmem : B ∈ [A, B] := by simp
  have Hk0 : ∀ i, i ∈ [A, B] → (AxLock3Thm.s0 Lpa xpa cpuA cpuB A vA i).atK = 0 := by
    intro i _
    unfold AxLock3Thm.s0
    split <;> rfl
  have Hend : ∀ i, i ∈ [A, B] →
      (AxLock3Thm.sN cpuA cpuB A vB i).atK = (AxOpsem.grow GD i).length := by
    intro i Hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at Hi
    unfold AxLock3Thm.sN
    rcases Hi with rfl | rfl
    · rw [if_pos rfl, Hrow_A]; rfl
    · rw [if_neg hBA, Hrow_B]; rfl
  have Hrun : ∀ (_ : AxannotGS lock3GF) (nm : lock3N) i, i ∈ [A, B] →
      nsteps (tierAAstep GD nm i) (AxLock3Thm.nSteps A i) (AxLock3Thm.s0 Lpa xpa cpuA cpuB A vA i)
        (AxLock3Thm.sN cpuA cpuB A vB i) := by
    intro _ nm i Hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at Hi
    unfold tierAAstep AxLock3Thm.nSteps AxLock3Thm.s0 AxLock3Thm.sN
    rcases Hi with rfl | rfl
    · simp only [↓reduceIte]
      exact l3pWRun Lpa xpa cpuA zeroRegs HLram Hxram GD i tA oldA vA Hrow_A
    · simp only [if_neg hBA]
      exact l3pRRun Lpa xpa cpuB zeroRegs HLram Hxram GD i tB oldB txB vB Hrow_B
  have Hwp : ∀ [InvGS_gen .hasNoLC lock3GF] [AxannotGS lock3GF] (nm : lock3N),
      ⊢ ([∗list] i ∈ [A, B], lock3Init (GF := lock3GF) nm i) -∗
        [∗list] i ∈ [A, B],
          @tierAWpd lock3GF .hasNoLC _ _ lockAxpol GD lock3N lock3ObSt0 (lock3ObStInterp0 L x)
            nm (AxLock3Thm.s0 Lpa xpa cpuA cpuB A vA i) .MaybeStuck i
            (fun s => iprop(⌜AxLock3Thm.post L x GD A B vB i s⌝)) := by
    intro _ _ nm
    have H := lock3sVerified (GF := lock3GF) (hlc := .hasNoLC) GD L x hxy Lpa xpa HLram Hxram
      cpuA cpuB zeroRegs zeroRegs HLeq Hxeq A B HAB tA oldA vA Hrow_A tB oldB txB vB Hrow_B Hcons
      Hharts HimgL Hb0A Hb0B nm
    have Hmono : ∀ j : Agent,
        @tierAWpd lock3GF .hasNoLC _ _ lockAxpol GD lock3N lock3ObSt0 (lock3ObStInterp0 L x) nm
          (if j = A then ⟨l3pWP0 Lpa xpa cpuA zeroRegs vA, 0⟩
           else ⟨l3pRP0 Lpa xpa cpuB zeroRegs, 0⟩) .MaybeStuck j
          (fun _ => if j = A then iprop(True) else iprop(⌜PreaderPure L x GD B vB⌝)) ⊢
        @tierAWpd lock3GF .hasNoLC _ _ lockAxpol GD lock3N lock3ObSt0 (lock3ObStInterp0 L x) nm
          (AxLock3Thm.s0 Lpa xpa cpuA cpuB A vA j) .MaybeStuck j
          (fun s => iprop(⌜AxLock3Thm.post L x GD A B vB j s⌝)) := by
      intro j
      unfold tierAWpd AxLock3Thm.s0
      refine @wpdMono .hasNoLC lock3GF _ (axGA2 GD lock3N lock3ObSt0 (lock3ObStInterp0 L x) nm)
        lockAxpol .MaybeStuck j _ _ _ (fun s => ?_)
      unfold AxLock3Thm.post
      by_cases h : j = A
      · simp only [h, ↓reduceIte]
        exact pure_intro trivial
      · simp only [if_neg h]
        exact .rfl
    iintro Hi
    ihave Hw := H $$ Hi
    iapply (BigSepL.bigSepL_mono_of_forall (fun {_ j} => Hmono j))
    iexact Hw
  have Hpost := @tierAAdequacyAnn lock3GF _ _ lockAxpol GD lock3N lock3ObSt0
    (lock3ObStInterp0 L x) lock3Init lockAxpolWf Hcons [A, B] Hnd Hharts'
    (AxLock3Thm.s0 Lpa xpa cpuA cpuB A vA) (AxLock3Thm.sN cpuA cpuB A vB) (AxLock3Thm.nSteps A)
    Hrun Hk0 Hend (AxLock3Thm.post L x GD A B vB) Hwp
    (lockHobAlloc L x hxy GD [A, B]) (lockAxpolHsPolSub GD) (lockAxpolHlobpSub GD) B HBmem
  unfold AxLock3Thm.post at Hpost
  rw [if_neg hBA] at Hpost
  obtain ⟨Hp1, Hp2⟩ := Hpost
  refine ⟨fun Hgrfe => ?_, Hp2⟩
  have Hlbl1 := l3pWLbl1 Lpa xpa GD A tA oldA vA Hrow_A
  rw [← Hxeq] at Hlbl1
  exact Hp1 A vA Hgrfe (gwritesByteOfStore GD (A, 1) x vA .WCplain Hlbl1).1

end Weak
