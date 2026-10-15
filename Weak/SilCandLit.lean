/-
Weak: **(c) [OWN.100], increment 1b — the CROSS-SPIN shape IS a twin run** (`PROGRESS-W10N2p.md`).
Lean-only, no Rocq twin.

The positive litmus beside `CertZ35.crossSpinNo`: two harts, lock bytes `0` and `1` (image zero), each
hart acquires its own lock (`amoswap.aq` reading 0), releases it (a plain store of 0), and then FAILS an
acquire of the other's lock, reading 1 — realized by the twin step `SilCand.stepS` with both failed AMOs
SILENT (at position 2).  **`SilCandLit.crossSpinYes`**.
-/
import Weak.SilCand

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std

namespace SilCandLit

def img0 : Image := fun a => if a = 0 ∨ a = 1 then some 0#8 else none

def lA1 : Lbl := .LRmw true false 0 [0] [0#8] [1#8] .WCexcl
def lA2 : Lbl := .LRmw true false 1 [0] [0#8] [1#8] .WCexcl
def lR1 : Lbl := .LStore false 0 [0#8] .WCrel
def lR2 : Lbl := .LStore false 1 [0#8] .WCrel
def lF2 : Lbl := .LRmw true false 1 [2] [1#8] [1#8] .WCexcl
def lF1 : Lbl := .LRmw true false 0 [1] [1#8] [1#8] .WCexcl

def tr : List Estep := [⟨0, lA1⟩, ⟨1, lA2⟩, ⟨0, lR1⟩, ⟨1, lR2⟩, ⟨0, lF2⟩, ⟨1, lF1⟩]

def oldNext (S : SilCand.St) (i : Nat) (l : Lbl) : SilCand.St :=
  ⟨mnext S.ms i l, SilCand.aqwPost S.ms S.aqw i l⟩

def silNext (S : SilCand.St) (i : Nat) (base : Int) (ts : List Nat) (wvs : List (BitVec 8))
    (q : Nat) : SilCand.St :=
  ⟨⟨S.ms.msImg, S.ms.msLog,
      updWs S.ms.msWs i (SilCand.silentPost (S.ms.msWs i) true base ts wvs.length q)⟩,
    SilCand.updAqw S.aqw i q⟩

def S0 : SilCand.St := ⟨⟨img0, [], fun _ => wsInit⟩, fun _ => 0⟩
def S1 : SilCand.St := oldNext S0 0 lA1
def S2 : SilCand.St := oldNext S1 1 lA2
def S3 : SilCand.St := oldNext S2 0 lR1
def S4 : SilCand.St := oldNext S3 1 lR2
def S5 : SilCand.St := silNext S4 0 1 [2] [1#8] 2
def S6 : SilCand.St := silNext S5 1 0 [1] [1#8] 2

theorem log4 : S4.ms.msLog =
    [⟨0, [1#8], some 0, .WCexcl⟩, ⟨1, [1#8], some 1, .WCexcl⟩, ⟨0, [0#8], some 0, .WCrel⟩,
     ⟨1, [0#8], some 1, .WCrel⟩] := rfl

theorem img4 : S4.ms.msImg = img0 := rfl

/-- The views of hart 0 before its failed AMO, and of hart 1 before its. -/
theorem ws0 : S4.ms.msWs 0 = (S3.ms.msWs 0) := by
  simp [S4, oldNext, mnext, lR2, updWs]

theorem ws1 : S5.ms.msWs 1 = (S4.ms.msWs 1) := by
  simp [S5, silNext, updWs]

theorem fv0 : fulfilVpre (S4.ms.msWs 0) false ≤ 2 := by
  simp [S4, S3, S2, S1, S0, oldNext, mnext, lA1, lA2, lR1, lR2, updWs, storePostRun, storePostBytes,
    storePost, loadPostRun, loadPostBytes, loadPostAt, ctrlPost, fwdView, loadVpre, wsInit, fulfilVpre]

theorem coh01 : coh (S4.ms.msWs 0) 1 = 0 := by
  simp [S4, S3, S2, S1, S0, oldNext, mnext, lA1, lA2, lR1, lR2, updWs, storePostRun, storePostBytes,
    storePost, loadPostRun, loadPostBytes, loadPostAt, ctrlPost, fwdView, loadVpre, wsInit, coh,
    lookupInsertNe, lookupEmpty]

theorem noW (log : List Wmsg) (a : Int) (lo hi : Nat) :
    writesInb log a lo hi = false → ¬ writesIn log a lo hi := by
  intro h hw
  rw [writesInbSpec, h] at hw
  cases hw

theorem vpre0 : max (loadVpre (S4.ms.msWs 0) true) (coh (S4.ms.msWs 0) 1) = 0 := by
  simp [S4, S3, S2, S1, S0, oldNext, mnext, lA1, lA2, lR1, lR2, updWs, storePostRun, storePostBytes,
    storePost, loadPostRun, loadPostBytes, loadPostAt, ctrlPost, fwdView, loadVpre, wsInit, coh,
    lookupInsertNe, lookupEmpty]

theorem vpre1 : max (loadVpre (S4.ms.msWs 1) true) (coh (S4.ms.msWs 1) 0) = 0 := by
  simp [S4, S3, S2, S1, S0, oldNext, mnext, lA1, lA2, lR1, lR2, updWs, storePostRun, storePostBytes,
    storePost, loadPostRun, loadPostBytes, loadPostAt, ctrlPost, fwdView, loadVpre, wsInit, coh,
    lookupInsertNe, lookupEmpty]

theorem fv1 : fulfilVpre (S4.ms.msWs 1) false ≤ 2 := by
  simp [S4, S3, S2, S1, S0, oldNext, mnext, lA1, lA2, lR1, lR2, updWs, storePostRun, storePostBytes,
    storePost, loadPostRun, loadPostBytes, loadPostAt, ctrlPost, fwdView, loadVpre, wsInit, fulfilVpre]

theorem coh10 : coh (S4.ms.msWs 1) 0 = 0 := by
  simp [S4, S3, S2, S1, S0, oldNext, mnext, lA1, lA2, lR1, lR2, updWs, storePostRun, storePostBytes,
    storePost, loadPostRun, loadPostBytes, loadPostAt, ctrlPost, fwdView, loadVpre, wsInit, coh,
    lookupInsertNe, lookupEmpty]

theorem aqw40 : S4.aqw 0 = 1 := by
  simp [S4, S3, S2, S1, S0, oldNext, SilCand.aqwPost, lA1, lA2, lR1, lR2, SilCand.updAqw, mnext]

theorem aqw51 : S5.aqw 1 = 2 := by
  simp [S5, silNext, S4, S3, S2, S1, S0, oldNext, SilCand.aqwPost, lA1, lA2, lR1, lR2,
    SilCand.updAqw, mnext]

theorem sil5 : SilCand.silentOk S4.ms S4.aqw 0 true 1 [2] [1#8] [1#8] 2 := by
  refine ⟨rfl, by simp, rfl, ⟨rfl, fun j t v hj hv => ?_⟩, by rw [log4]; simp, fun j t hj => ?_,
    fun j hj => ?_, by rw [show (2 : Nat) = 2 from rfl]; exact fv0, by rw [aqw40]; omega⟩
  · cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj hv
      subst hj hv
      refine ⟨by rw [log4, img4]; rfl, by rw [log4, img4]; rfl, ?_⟩
      rw [show accAddr 1 0 = 1 from rfl, vpre0]
      exact noW _ _ _ _ (by rw [log4]; rfl)
    | succ j => simp at hj
  · cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst hj
      exact ⟨Nat.le_refl _, noW _ _ _ _ (by rw [log4]; rfl)⟩
    | succ j => simp at hj
  · have : j = 0 := by simp at hj; omega
    subst this
    rw [show accAddr 1 0 = 1 from rfl, coh01]
    omega

theorem log5 : S5.ms.msLog = S4.ms.msLog := rfl
theorem ws51 : S5.ms.msWs 1 = S4.ms.msWs 1 := by simp [S5, silNext, updWs]

theorem sil6 : SilCand.silentOk S5.ms S5.aqw 1 true 0 [1] [1#8] [1#8] 2 := by
  refine ⟨rfl, by simp, rfl, ⟨rfl, fun j t v hj hv => ?_⟩, by rw [log5, log4]; simp,
    fun j t hj => ?_, fun j hj => ?_, by rw [ws51]; exact fv1, by rw [aqw51]; exact Nat.le_refl _⟩
  · cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj hv
      subst hj hv
      refine ⟨by rw [log5, log4]; rfl, by rw [log5, log4]; rfl, ?_⟩
      rw [ws51, show accAddr 0 0 = 0 from rfl, vpre1]
      exact noW _ _ _ _ (by rw [log5, log4]; rfl)
    | succ j => simp at hj
  · cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst hj
      exact ⟨by omega, noW _ _ _ _ (by rw [log5, log4]; rfl)⟩
    | succ j => simp at hj
  · have : j = 0 := by simp at hj; omega
    subst this
    rw [ws51, show accAddr 0 0 = 0 from rfl, coh10]
    omega

theorem ok1 : mstepOk S0.ms 0 lA1 := by
  refine ⟨by simp, rfl, ⟨rfl, fun j t v hj hv => ?_⟩, fun j t hj => ?_⟩
  · cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj hv
      subst hj hv
      exact ⟨rfl, rfl, noW _ _ _ _ rfl⟩
    | succ j => simp at hj
  · cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst hj
      exact ⟨rfl, noW _ _ _ _ rfl⟩
    | succ j => simp at hj

theorem ws11 : S1.ms.msWs 1 = wsInit := by simp [S1, S0, oldNext, mnext, lA1, updWs]

theorem ok2 : mstepOk S1.ms 1 lA2 := by
  refine ⟨by simp, rfl, ⟨rfl, fun j t v hj hv => ?_⟩, fun j t hj => ?_⟩
  · cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj hv
      subst hj hv
      refine ⟨rfl, rfl, ?_⟩
      rw [ws11]
      exact noW _ _ _ _ rfl
    | succ j => simp at hj
  · cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst hj
      exact ⟨rfl, noW _ _ _ _ rfl⟩
    | succ j => simp at hj

/-- **THE CROSS-SPIN IS A TWIN RUN.** -/
theorem crossSpinYes : SilCand.execWfS ⟨[S0, S1, S2, S3, S4, S5, S6], tr⟩ := by
  refine ⟨rfl, fun S h => ?_, fun k s S S' hs hS hS' => ?_⟩
  · simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    exact ⟨rfl, fun _ => rfl, fun _ => rfl⟩
  · match k, hs, hS, hS' with
    | 0, hs, hS, hS' =>
      simp only [tr, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at hs hS hS'
      subst hs hS hS'
      exact .old lA1 _ (mstepOkStep _ _ _ ok1)
    | 1, hs, hS, hS' =>
      simp only [tr, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at hs hS hS'
      subst hs hS hS'
      exact .old lA2 _ (mstepOkStep _ _ _ ok2)
    | 2, hs, hS, hS' =>
      simp only [tr, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at hs hS hS'
      subst hs hS hS'
      exact .old lR1 _ (mstepOkStep _ _ _ (by simp [mstepOk, lR1]))
    | 3, hs, hS, hS' =>
      simp only [tr, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at hs hS hS'
      subst hs hS hS'
      exact .old lR2 _ (mstepOkStep _ _ _ (by simp [mstepOk, lR2]))
    | 4, hs, hS, hS' =>
      simp only [tr, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at hs hS hS'
      subst hs hS hS'
      exact .silent true 1 [2] [1#8] [1#8] .WCexcl 2 sil5
    | 5, hs, hS, hS' =>
      simp only [tr, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at hs hS hS'
      subst hs hS hS'
      exact .silent true 0 [1] [1#8] [1#8] .WCexcl 2 sil6
    | k + 6, hs, _, _ => simp [tr] at hs

end SilCandLit

end Weak
