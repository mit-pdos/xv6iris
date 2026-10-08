/-
Weak: **UNIFY, part 3 of the spinlock plan -- THE PURE DICHOTOMY** for two harts running the
allocpid-shaped critical section `AxSpinU2.uRow` (4-byte lock word, 4-byte nextpid), over any
`rvwmoCatConsistent` graph whose events all belong to the two harts.

Rocq: `iris/AxSpinU3.v` @ xxvzwolszwmp.

## The Rocq header, in substance

`uSrcOther`: a claim that does not read the image reads the OTHER hart's release (lock-byte
writes are each hart's claim `1` and release `0`; a hart's own release is ppo-after its claim).
`uHandoff`: if hart `j`'s claim reads hart `i`'s release, then `j`'s `lw nextpid` reads, at EVERY
byte, `i`'s `sw nextpid` (gmo-before it: fence → rfe → acquire; the only other nextpid writer,
`j`'s own sw, is ppo-after the lw; an image read is refuted by `gloadValue`'s maximality) -- so
`w_j = w_i + 1` as words.
`uDistinct`: `w_A ≠ w_B` -- both claims reading the image is refuted by RMW atomicity
(`catRmwUniqueReader`); otherwise one hart reads the other's increment, and `w + 1 ≠ w`
(Hnowrap).
HONEST: GRAPH-TRUE for two correct rows; ownership plays no role here (the WPd side, AxSpinU2,
delivers the ownership facts; the race twin AxSpinU4 shows ownership is load-bearing for them).

## Deviations from Rocq

1. VOCABULARY (as `AxSpinU2` deviation 1): `Z` ↦ `Int`, `bv n` ↦ `BitVec n`, `gd_g GD` ↦
   `GD.gdG`, `l !! j` ↦ `l[j]?`, `bv_add w one32` ↦ `w + one32`, `bv_unsigned w + 1 < 2^32` ↦
   `w.toNat + 1 < 2 ^ 32` (over `Nat`), `B0`/`B1` ↦ `b0`/`b1`, `S n` ↦ `n + 1`.
2. CONTEXTS: Rocq section variables are explicit leading arguments in Rocq's order, only where
   Rocq's `Proof using` includes them (`GD Hcons`, then `i j Hij Hharts ti tj tsi tsj wi wj Hri
   Hrj`; `uSrcOther` drops `Hij` as Rocq's `clear Hij`/`Proof using` does).
3. `gwix_pos` is a duplicated Rocq name (also WeakRvwmoGraph, whose Lean `WeakRvwmoGraph.gwixPos`
   states `0 < gwix`): declared file-qualified `AxSpinU3.gwixPos` with Rocq's `≠ 0` statement,
   proved from the WeakRvwmoGraph one.
4. The `zv` Ltac is inlined as `simp only [lkZV, npZV]`; Rocq `vm_compute` facts by
   `decide +kernel`.  The trailing `Print Assumptions` is not ported.

**Rocq → Lean name map.**  `gwix_pos` `AxSpinU3.gwixPos` (dup), `bv_add_one_ne` `bvAddOneNe`,
`u_lbls` `uLbls`, `u_claim_facts` `uClaimFacts`, `w_mem` `wMem`, `u_src_other` `uSrcOther`,
`u_handoff` `uHandoff`, `u_distinct` `uDistinct`.

**Dropped:** none (8 Rocq decls; 8 Lean).
-/
import Weak.AxSpinU2

namespace Weak

open MachCSL Sail LeanRV64D

theorem AxSpinU3.gwixPos (G : Gexec) (w : Geid) : w ∈ gwrites G → gwix G w ≠ 0 := by
  intro Hin
  have := WeakRvwmoGraph.gwixPos G w Hin
  omega

theorem bvAddOneNe (w : BitVec 32) : w.toNat + 1 < 2 ^ 32 → w + one32 ≠ w := by
  intro Hn Heq
  have H := congrArg BitVec.toNat Heq
  rw [BitVec.toNat_add] at H
  have h1 : one32.toNat = 1 := by decide +kernel
  rw [h1, Nat.mod_eq_of_lt Hn] at H
  omega

/-! # The dichotomy -/

theorem uLbls (GD : Gdexec) (i : Agent) (t : Nat) (ts : List Nat) (w : BitVec 32) :
    AxOpsem.grow GD i = uRow t ts w →
    gxLbl GD.gdG (i, 0) = some (.LRmw true false (paZ lkpa) [t, t, t, t] AxSpinX4.z4 AxSpinX4.o4
      .WCplain) ∧
    gxLbl GD.gdG (i, 1) = some (.LLoad false (paZ nppa) ts (WeakInterpProj.wbytes 4 w)) ∧
    gxLbl GD.gdG (i, 2) = some (.LStore false (paZ nppa) (WeakInterpProj.wbytes 4 (w + one32))
      .WCplain) ∧
    gxLbl GD.gdG (i, 3) = some (.LFence true true false true) ∧
    gxLbl GD.gdG (i, 4) = some (.LStore false (paZ lkpa) AxSpinX4.z4 .WCrel) := by
  intro Hrow
  simp only [gxLblGrow, Hrow]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem uClaimFacts (GD : Gdexec) (Hcons : rvwmoCatConsistent GD) (i : Agent) (t : Nat)
    (ts : List Nat) (w : BitVec 32) :
    AxOpsem.grow GD i = uRow t ts w →
    greadsByte GD.gdG (i, 0) (paZ lkpa) t b0 ∧ gwritesByte GD.gdG (i, 0) (paZ lkpa) b1 ∧
    gmoLt GD.gdG (i, 0) (i, 1) ∧ gmoLt GD.gdG (i, 0) (i, 4) ∧ gmoLt GD.gdG (i, 2) (i, 4) ∧
    gmoLt GD.gdG (i, 1) (i, 2) := by
  intro Hrow
  obtain ⟨Hl0, Hl1, Hl2, Hl3, Hl4⟩ := uLbls GD i t ts w Hrow
  obtain ⟨Hwf, _⟩ := id Hcons
  obtain ⟨Hr, Hw, _, _⟩ := gwbRmwn _ _ _ _ _ _ _ Hl0
  have e0 : ∀ a : Int, a + ((0 : Nat) : Int) = a := fun a => by omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have H := Hr 0 t b0 rfl (by decide +kernel)
    rw [e0] at H
    exact H
  · have H := Hw 0 b1 o40
    rw [e0] at H
    exact H
  · exact obCatSubGmo GD _ _ Hcons (acqGob GD i 0 1 _ _ _ _ _ _ Hl0 Hl1 rfl (by omega))
  · exact obCatSubGmo GD _ _ Hcons (acqGob GD i 0 4 _ _ _ _ _ _ Hl0 Hl4 rfl (by omega))
  · exact obCatSubGmo GD _ _ Hcons
      (fenceGob GD i 2 3 4 _ _ _ _ Hl2 rfl Hl3 Hl4 (by omega) (by omega))
  · apply obCatSubGmo GD _ _ Hcons
    obtain ⟨t0, Ht0⟩ := loadnReads GD.gdG Hwf (i, 1) (paZ nppa) ts 4 w 0 Hl1 (by omega)
    obtain ⟨Hw2, _⟩ := gwbStoren _ _ _ _ _ Hl2
    exact ppo1Gob GD (i, 1) (i, 2) (paZ nppa + ((0 : Nat) : Int)) (nthByte (n := 4) (w + one32) 0)
      (gpoRow GD i 1 2 _ _ Hl1 Hl2 (by omega)) (Or.inr ⟨t0, nthByte (n := 4) w 0, Ht0⟩)
      (Hw2 0 _ (wbytesLookup 4 (m := 4) (w + one32) 0 (by omega)))

theorem wMem (GD : Gdexec) (Hcons : rvwmoCatConsistent GD) (w : Geid) (a : Int) (v : BitVec 8) :
    gwritesByte GD.gdG w a v → w ∈ GD.gdG.gxGmo ∧ w ∈ gwrites GD.gdG := by
  intro Hw
  obtain ⟨Hwf, _⟩ := id Hcons
  have Hwg := gwritesByteGwrites GD.gdG w _ _ Hwf Hw
  exact ⟨(List.mem_filter.1 Hwg).1, Hwg⟩

/-- `j`'s claim, when not reading the image, reads `i`'s release. -/
theorem uSrcOther (GD : Gdexec) (Hcons : rvwmoCatConsistent GD) (i j : Agent)
    (Hharts : ∀ e, e ∈ GD.gdG.gxGmo → e.1 = i ∨ e.1 = j) (ti tj : Nat) (tsi tsj : List Nat)
    (wi wj : BitVec 32) (Hri : AxOpsem.grow GD i = uRow ti tsi wi)
    (Hrj : AxOpsem.grow GD j = uRow tj tsj wj) (n : Nat) :
    tj = n + 1 → gwriteAt GD.gdG tj = some (i, 4) := by
  intro Ht
  obtain ⟨_, _, Hlv, _⟩ := id Hcons
  obtain ⟨Hrd, _, _, Hj04, _, _⟩ := uClaimFacts GD Hcons j tj tsj wj Hrj
  have H := (Hlv _ _ _ _ Hrd).1
  subst Ht
  obtain ⟨w, Hga, Hww, Hvis⟩ := H
  rw [Hga]
  obtain ⟨Hwm, _⟩ := wMem GD Hcons _ _ _ Hww
  obtain ⟨x, k⟩ := w
  rcases Hharts _ Hwm with Hx | Hx <;> change x = _ at Hx <;> subst x
  · rcases uWr GD i ti tsi wi k _ _ Hri Hww with ⟨rfl, _, Hv⟩ | ⟨rfl, j', Hj', Ha, _⟩ | ⟨rfl, _⟩
    · exact absurd (Hv rfl) b0NeB1
    · exfalso
      simp only [lkZV, npZV] at Ha <;> omega
    · rfl
  · exfalso
    rcases uWr GD j (n + 1) tsj wj k _ _ Hrj Hww with ⟨rfl, _, Hv⟩ | ⟨rfl, j', Hj', Ha, _⟩ |
      ⟨rfl, _⟩
    · exact b0NeB1 (Hv rfl)
    · simp only [lkZV, npZV] at Ha <;> omega
    · rcases Hvis with Hmo | ⟨_, Hlt, _⟩
      · exact gmoLtIrrefl _ _ (gmoLtTrans _ _ _ _ Hmo Hj04)
      · change 4 < 0 at Hlt
        omega

/-- THE HANDOFF VALUE: `j`'s claim reads `i`'s release ⇒ `j`'s lw reads `i`'s increment. -/
theorem uHandoff (GD : Gdexec) (Hcons : rvwmoCatConsistent GD) (i j : Agent) (Hij : i ≠ j)
    (Hharts : ∀ e, e ∈ GD.gdG.gxGmo → e.1 = i ∨ e.1 = j) (ti tj : Nat) (tsi tsj : List Nat)
    (wi wj : BitVec 32) (Hri : AxOpsem.grow GD i = uRow ti tsi wi)
    (Hrj : AxOpsem.grow GD j = uRow tj tsj wj) :
    gwriteAt GD.gdG tj = some (i, 4) → wj = wi + one32 := by
  intro Hsrc
  obtain ⟨Hwf, _, Hlv, _⟩ := id Hcons
  obtain ⟨Hrdj, _, Hj01, _, _, Hj12⟩ := uClaimFacts GD Hcons j tj tsj wj Hrj
  obtain ⟨_, _, _, _, Hi24, _⟩ := uClaimFacts GD Hcons i ti tsi wi Hri
  obtain ⟨_, _, Hli2, _, _⟩ := uLbls GD i ti tsi wi Hri
  obtain ⟨_, Hlj1, _, _, _⟩ := uLbls GD j tj tsj wj Hrj
  rcases tj with _ | n
  · simp only [gwriteAt, reduceCtorEq] at Hsrc
  obtain ⟨w, Hga, _, Hvis⟩ := (Hlv _ _ _ _ Hrdj).1
  rw [Hsrc] at Hga
  obtain rfl := Option.some.inj Hga
  have Hi4j0 : gmoLt GD.gdG (i, 4) (j, 0) := by
    rcases Hvis with h | ⟨Hh, _⟩
    · exact h
    · exact absurd Hh Hij
  have Hlt : gmoLt GD.gdG (i, 2) (j, 1) :=
    gmoLtTrans _ _ _ _ Hi24 (gmoLtTrans _ _ _ _ Hi4j0 Hj01)
  obtain ⟨Hwi2, _⟩ := gwbStoren _ _ _ _ _ Hli2
  apply wbytes4Inj
  apply List.ext_getElem?
  intro jj
  by_cases Hjj : jj < 4
  · rw [wbytesLookup 4 (m := 4) wj jj Hjj, wbytesLookup 4 (m := 4) (wi + one32) jj Hjj]
    congr 1
    obtain ⟨tt, Htt⟩ := loadnReads GD.gdG Hwf (j, 1) (paZ nppa) tsj 4 wj jj Hlj1 Hjj
    have Hw2 : gwritesByte GD.gdG (i, 2) (paZ nppa + (jj : Int))
        (nthByte (n := 4) (wi + one32) jj) :=
      Hwi2 jj _ (wbytesLookup 4 (m := 4) (wi + one32) jj Hjj)
    obtain ⟨Hm, Hmax⟩ := Hlv _ _ _ _ Htt
    rcases tt with _ | n'
    · exfalso
      have Hx := Hmax (i, 2) _ Hw2 (Or.inl Hlt)
      have Hp := AxSpinU3.gwixPos GD.gdG (i, 2) (wMem GD Hcons _ _ _ Hw2).2
      omega
    obtain ⟨w0, _, Hw0, Hvis0⟩ := Hm
    obtain ⟨Hw0m, _⟩ := wMem GD Hcons _ _ _ Hw0
    obtain ⟨x, k⟩ := w0
    rcases Hharts _ Hw0m with Hx | Hx <;> change x = _ at Hx <;> subst x
    · rcases uWr GD i ti tsi wi k _ _ Hri Hw0 with ⟨rfl, Ha, _⟩ | ⟨rfl, j', Hj', Ha, _⟩ |
        ⟨rfl, Ha, _⟩
      · exfalso
        simp only [lkZV, npZV] at Ha <;> omega
      · have Hjj' : j' = jj := by omega
        subst Hjj'
        exact gwritesByteDet _ _ _ _ _ Hw0 Hw2
      · exfalso
        simp only [lkZV, npZV] at Ha <;> omega
    · exfalso
      rcases uWr GD j (n + 1) tsj wj k _ _ Hrj Hw0 with ⟨rfl, Ha, _⟩ | ⟨rfl, j', Hj', Ha, _⟩ |
        ⟨rfl, Ha, _⟩
      · simp only [lkZV, npZV] at Ha <;> omega
      · rcases Hvis0 with Hmo | ⟨_, Hk, _⟩
        · exact gmoLtIrrefl _ _ (gmoLtTrans _ _ _ _ Hmo Hj12)
        · change 2 < 1 at Hk
          omega
      · simp only [lkZV, npZV] at Ha <;> omega
  · rw [List.getElem?_eq_none (by rw [wbytesLength]; omega),
      List.getElem?_eq_none (by rw [wbytesLength]; omega)]

/-- THE TWO READ VALUES DIFFER. -/
theorem uDistinct (GD : Gdexec) (Hcons : rvwmoCatConsistent GD) (A B : Agent) (HAB : A ≠ B)
    (Hharts : ∀ e, e ∈ GD.gdG.gxGmo → e.1 = A ∨ e.1 = B)
    (tA tB : Nat) (tsA tsB : List Nat) (wA wB : BitVec 32)
    (HrA : AxOpsem.grow GD A = uRow tA tsA wA) (HrB : AxOpsem.grow GD B = uRow tB tsB wB)
    (HnA : wA.toNat + 1 < 2 ^ 32) (HnB : wB.toNat + 1 < 2 ^ 32) :
    wA ≠ wB := by
  have HharB : ∀ e, e ∈ GD.gdG.gxGmo → e.1 = B ∨ e.1 = A := fun e He => (Hharts e He).symm
  rcases tB with _ | nB
  · rcases tA with _ | nA
    · exfalso
      obtain ⟨HrdA, HwrA, _⟩ := uClaimFacts GD Hcons A 0 tsA wA HrA
      obtain ⟨HrdB, HwrB, _⟩ := uClaimFacts GD Hcons B 0 tsB wB HrB
      have Heq := catRmwUniqueReader GD (paZ lkpa) 0 (A, 0) (B, 0) b0 b0 b1 b1 Hcons
        HrdA HwrA HrdB HwrB
      exact HAB (congrArg Prod.fst Heq)
    · have Hs := uSrcOther GD Hcons B A HharB 0 (nA + 1) tsB tsA wB wA HrB HrA nA rfl
      have Hv := uHandoff GD Hcons B A (Ne.symm HAB) HharB 0 (nA + 1) tsB tsA wB wA HrB HrA Hs
      intro Heq
      rw [Heq] at Hv
      exact bvAddOneNe wB HnB Hv.symm
  · have Hs := uSrcOther GD Hcons A B Hharts tA (nB + 1) tsA tsB wA wB HrA HrB nB rfl
    have Hv := uHandoff GD Hcons A B HAB Hharts tA (nB + 1) tsA tsB wA wB HrA HrB Hs
    intro Heq
    rw [← Heq] at Hv
    exact bvAddOneNe wA HnA Hv.symm

end Weak
