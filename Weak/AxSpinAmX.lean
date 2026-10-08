/-
Weak: **acquire's AMOSWAP write flow at ANY RMW write class** — `AxSpinAmX.fstAcqNh`, the
class-generic form of `AxSpinAm4.FstAcqNh`.

Lean-only (no Rocq source).  Rocq's `FstAcq_nh` (ported as `AxSpinAm4.FstAcqNh`) and
`AxSpinU.wpdAcquireX` state the acquire RMW's label at class `WCplain`; the hardware stamps a
fused RMW with `WCexcl` (`AxClsStep.pclsEv`, `AxCert.wclsLatest`/`wclsRmw`; certificates end in
`CRmw … WCexcl`), and `AxSpinRl1.rowClsHonest` demands `WCexcl` of every RMW.  So the Theorem-2
spin chain (`AxSpinAq1`) must be stated at `WCexcl`.

## Why the class is irrelevant (the analysis)

Nothing in the flow reads the class: the label is consumed only by `gwbRmwn` (AxSpinX3, generic
in `cls`), `lblOfRow`, and `OAcq` (AxSpinAm4, matches the class with `_`); the protocol rules
`fxClaim`/`fxNeutral` (AxSpinX2 "RULES, by class" — the "class" there is the BYTE class: lock
word / lk->cpu / nextpid / private / read-only, not the write class) are stated on
`greadsByte`/`gwritesByte`/`lkClaim`, which are class-free; the lock-word policy (`lwSide`,
`wrsOk`) is class-free too.  The amoswap leaf (`AxSpinAm3.XxAmoswap`) produces a row fact with an
existential class (`wcls akXc r`, AxSpinAm).  Hence the proof of `FstAcqNh` goes through verbatim
for an arbitrary `cls`.

## How

The proof of `AxSpinAm4.FstAcqNh`, with the label's class a parameter.  `AxSpinAm4` is merged and
left untouched (its statement stays; it is the `cls := .WCplain` instance).

## Deviations / honesty

None: a pure generalization (one extra explicit argument `cls` after `rvs`).

**Reused** (by name): `dflowOPlain2`, `OAcq` (AxSpinAm4); `dflowOPlain` (AxSpinHdB); `fxClaim`,
`fxNeutral` (AxSpinX2); `gwbRmwn` (AxSpinX3); `lblOfRow`, `HGX` (AxSpinE5); `FstRmwW` (AxSpinAm2).

**Lean-only declarations:** `AxSpinAmX.fstAcqNh`.
-/
import Weak.AxSpinAm4

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

section flowsAmX
variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF] [AxannotGS GF]
  [AxSpinX.Xv6G GF]
variable (L : Xlay) (GT : GdexecT) (nm : Xv6N)

/-- `AxSpinAm4.FstAcqNh` at ANY write class `cls` of the RMW label (`FstAcqNh` is the
`cls := .WCplain` instance): the acquire write flow from `notheld` in hand: success
(`rvs = z4`) by `fxClaim`, failure (low byte read ≠ 0) by `fxNeutral`, `notheld` handed back. -/
theorem AxSpinAmX.fstAcqNh (HL : xlayOk L) (Hcons : rvwmoCatConsistent (gtAdGd GT))
    (i : Agent) (kA t : Nat) (rvs : List (BitVec 8)) (cls : WmClass) (R1 R2 : IProp GF)
    (lo hi : Nat) :
    (AxOpsem.grow (gtAdGd GT) i)[kA]? =
      some (Lbl.LRmw true false L.xlLk [t, t, t, t] rvs AxSpinX4.o4 cls) →
    (rvs = AxSpinX4.z4 ∨ ∃ b0', rvs[0]? = some b0' ∧ b0' ≠ b0) →
    (∀ a, L.xlLk ≤ a ∧ a < L.xlLk + 4 → a ∈ lwb L) →
    (∀ (k' : Nat) (data : List (BitVec 8)), lo ≤ k' ∧ k' < hi →
      graphData (gtAdGd GT) (i, k') = some data →
      rowWr i (gtAdGd GT) k' L.xlLk data.length → k' = kA) →
    (iprop(locked nm.xnReg L.xlLk i (i, kA) ∗ RPid L nm.xnH nm.xnM nm.xnI (gtAdGd GT) (i, kA)) ⊢
      iprop(R1 ∗ R2)) →
    ⊢ isLock nm.xnReg L.xlLk (RPid L nm.xnH nm.xnM nm.xnI (gtAdGd GT)) -∗
      notheld nm.xnReg L.xlLk i -∗
      @FstRmwW hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent
        (dokAtP L.xlLk 4) i (OAcq L GT nm i R1 R2) lo hi := by
  intro Hrow Hcase Hlwb Huniq Hsplit
  iintro #Hil Hnh
  unfold FstRmwW
  iintro %GD %ls %k %data %base %n %Hc #Hg _Hloc %Hgd %Hd %Hw
  ihave %Heq := (HGX L GT nm GD Hc) $$ Hg
  subst Heq
  obtain ⟨⟨rfl, rfl⟩, Hwr⟩ := Hd
  have hk := Huniq k data Hw Hgd Hwr
  subst hk
  have Hl := lblOfRow _ _ _ _ Hrow
  obtain ⟨Hr, Hwb, Hsg, -⟩ := gwbRmwn _ _ _ _ _ _ _ Hl
  have Hlw : ∀ a v', gwritesByte (gtAdGd GT).gdG (i, k) a v' → a ∈ lwb L := by
    intro a v' Hw'
    obtain ⟨j, Hj, rfl⟩ := Hsg a v' Hw'
    have hj := (List.getElem?_eq_some_iff.1 Hj).1
    simp only [AxSpinX4.o4, wbytesLength] at hj
    exact Hlwb _ ⟨by omega, by omega⟩
  have HB1 : gwritesByte (gtAdGd GT).gdG (i, k) L.xlLk b1 := by
    have H := Hwb 0 b1 (by decide +kernel)
    rw [AxSpinX5.addZero] at H
    exact H
  simp only [OAcq, Hrow]
  rcases Hcase with rfl | ⟨b0', Hb0, Hnz⟩
  · rw [if_pos rfl]
    have Hcl : lkClaim L.xlLk (gtAdGd GT).gdG (i, k) (gwriteAt (gtAdGd GT).gdG t) := by
      refine ⟨t, ?_, rfl, HB1⟩
      have H := Hr 0 t b0 rfl (by decide +kernel)
      rw [AxSpinX5.addZero] at H
      exact H
    ihave Hfe := (fxClaim (hlc := hlc) L GT nm HL Hcons (i, k) (gwriteAt (gtAdGd GT).gdG t)
      Hcl Hlw) $$ Hnh Hil
    have Hs : ⊢ iprop(locked (GF := GF) nm.xnReg L.xlLk ((i, k) : Geid).1 (i, k) ∗
        RPid L nm.xnH nm.xnM nm.xnI (gtAdGd GT) (i, k)) -∗ iprop(R1 ∗ R2) :=
      BI.wand_intro (BI.emp_sep.1.trans Hsplit)
    iapply (dflowOPlain2 L GT nm i k R1 R2 _) $$ [Hfe]
    · iapply (@flowEqDynMono hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) (gtAdGd GT) (i, k) _
        (∅ : Mea GF)
        iprop(locked nm.xnReg L.xlLk ((i, k) : Geid).1 (i, k) ∗
          RPid L nm.xnH nm.xnM nm.xnI (gtAdGd GT) (i, k))
        iprop(R1 ∗ R2)) $$ [] Hfe
      inext
      ihave H := Hs
      iexact H
    · iintro H1 H2
      isplitl [H1]
      · iexact H1
      · iexact H2
  · have Hne : rvs ≠ AxSpinX4.z4 := by
      intro h
      subst h
      have hz : (AxSpinX4.z4)[0]? = some b0 := by decide +kernel
      rw [hz] at Hb0
      exact Hnz (Option.some.inj Hb0).symm
    rw [if_neg Hne]
    have Hrd : greadsByte (gtAdGd GT).gdG (i, k) L.xlLk t b0' := by
      have H := Hr 0 t b0' rfl Hb0
      rw [AxSpinX5.addZero] at H
      exact H
    ihave Hfe := fxNeutral (hlc := hlc) L GT nm HL Hcons (i, k) t b0' Hrd Hnz HB1 Hlw
    iapply (dflowOPlain L GT nm i k iprop(True) _) $$ Hfe
    iintro -
    iexact Hnh

end flowsAmX

end Weak
