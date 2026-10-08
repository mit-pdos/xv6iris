/-
Weak: **acquire's AMOSWAP on the POSITIONAL ENGINE, part 4**: the window-restricted WRITE FLOW
`FstRmwW` for `AxSpinAm3`'s `XxAmoswap` at Ixv6, built from AxSpinX2's lock-word rules — where
the protocol facts of a successful / failed spin come from (step3-plan [ID-5]).

Rocq: `iris/AxSpinAm4.v` @ xxvzwolszwmp.

## The Rocq header, in substance

* `OAcq L GT nm i R1 R2 kA _`: read off GD0's label at `kA`: an RMW whose read bytes are
  `AxSpinX4.z4` (the claim) yields the claim annotation pre-split, `(i,kA) ↦ₐ R1 ∗ (i,kA) ↦ₐ R2`;
  any other RMW (the failed spin) hands `notheld` back.
* `FstAcqNh`: from `isLock` and `notheld` in hand, the flow at the RMW `(i, kA)` — success by
  `fxClaim` (split along `LK ∗ RP ⊢ R1 ∗ R2`, `dflowOPlain2` = `AxSpinHdB`'s `dflowOPlain` with
  `annotSplit`), failure by `fxNeutral`.

Premises are the ROW's (the graph `GD0` is pinned): the label of `(i,kA)` (acquire's
`LRmw true false lk [t;t;t;t] rvs o4 WCplain`, as in `AxSpinU.wpdAcquireX`); `rvs = z4` or its low
byte ≠ 0 (the lock word is only ever 0 / 1 — a graph fact the leaf does not derive, so the client
states it from the row; `AxSpinU`'s acquire-fail leaf takes the same); `[lk, lk+4) ⊆ lwb L`;
`Huniq`: inside the window the only row item writing the lock word is `kA`.
NOT HERE (as Rocq): `FstAcq_h` (notheld drawn from the hart's own earlier release annotation) —
deferred by the plan (not needed for allocpid).

## Deviations from Rocq

1. O2 Stage C: nothing to change — the file states no row positions of its own (the window
   `lo hi` and the RMW position `kA` are parameters; `AxSpinAm3.XxAmoswap` instantiates
   `lo = kA = k`, `hi = k + 1`).  No fetch premises occur.  No kernel words occur (nothing to
   cross-check against `Xv6/KernelImage.lean`).
2. TYPES / INSTANCES (as `AxSpinAm3` deviation 2): `invGS_gen HasNoLc Σ` ↦ `[InvGS_gen hlc GF]`
   (any `hlc`); `xv6G Σ` ↦ `[AxSpinX.Xv6G GF]`; the local instances `am_pol` / `am_G` are
   inlined as `xv6Pol GT` / `AxSpinX2.xG L GT nm`, passed with `@`.  The Rocq notations
   `LK`/`NH`/`RP`/`ISL` are unfolded (`locked nm.xnReg L.xlLk`, `notheld nm.xnReg L.xlLk`,
   `RPid L nm.xnH nm.xnM nm.xnI (gtAdGd GT)`, `isLock nm.xnReg L.xlLk RP`).  Section variables
   are explicit leading arguments: `dflowOPlain2 L GT nm`, `OAcq L GT nm`, `FstAcqNh L GT nm HL
   Hcons` (Rocq `Proof using HL Hcons`).  `B0`/`B1` ↦ `b0`/`b1`, `z4`/`o4` ↦ `AxSpinX4.z4`/`o4`,
   `l !! k` ↦ `l[k]?`, `decide (rvs = z4)` ↦ `if rvs = AxSpinX4.z4`, `xl_lk L ≤ a < xl_lk L + 4`
   ↦ `L.xlLk ≤ a ∧ a < L.xlLk + 4`, `lo ≤ k' < hi` ↦ `lo ≤ k' ∧ k' < hi`.
3. The trailing `Print Assumptions` line is not ported (the lint's axiom check covers it).

**Rocq → Lean name map.**  `dflowO_plain2` `dflowOPlain2`, `OAcq` `OAcq`, `FstAcq_nh`
`FstAcqNh`.  None is in the duplicated-name table (grepped at the tip: no clash); no Lean-only
helpers.

**Dropped:** nothing (Rocq 3 definitions/lemmas + 2 local instances, inlined; Lean 3).
-/
import Weak.AxSpinAm3
import Weak.AxSpinHdB

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

section flowsAm
variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF] [AxannotGS GF]
  [AxSpinX.Xv6G GF]
variable (L : Xlay) (GT : GdexecT) (nm : Xv6N)

/-- Rocq `dflowO_plain2`: a flow with no draw whose output annotation is split in two. -/
theorem dflowOPlain2 (i : Agent) (k : Nat) (R1 R2 O : IProp GF) :
    ⊢ @flowEqDyn hlc GF _ (AxSpinX2.xG L GT nm) (gtAdGd GT) (i, k)
        (@Axpol.sPol (xv6Pol GT) (gtAdGd GT) (i, k)) (∅ : Mea GF) iprop(R1 ∗ R2) -∗
      (AxAnnot.annotOwn (i, k) R1 -∗ AxAnnot.annotOwn (i, k) R2 -∗ O) -∗
      @dflowO hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) i (gtAdGd GT) k O := by
  iintro Hfe HO
  unfold dflowO
  iintro %na ⟨Hpg, Hannot⟩
  ihave %Hnin := naAtProgressNotElemOf (gtAdGd GT) i k na $$ Hpg
  imod annotAlloc na (i, k) iprop(R1 ∗ R2) Hnin $$ Hannot with ⟨Hannot, Hh⟩
  imod (annotSplit (i, k) R1 R2) $$ Hh %_ Hannot with ⟨⟨Hf1, Hf2⟩, Hannot⟩
  imodintro
  inext
  imodintro
  iexists iprop(R1 ∗ R2), (∅ : Mea GF), (∅ : Mea GF), (() : Unit)
  isplitr
  · iapply (naWfEmpty L GT nm (i, k) na)
  isplitl [Hfe]
  · iexact Hfe
  isplitl [Hannot]
  · rw [AxLockWp.annotInsertEq na (i, k) iprop(R1 ∗ R2)]
    iexact Hannot
  isplitr
  · iapply (AxSpinWit.localTrue (gtAdGd GT) Xv6N Unit (protXv6 L) nm (gtAdGd GT) i (k + 1) ())
  · iapply HO $$ Hf1 Hf2

/-- Rocq `OAcq` ([ID-5]): the acquire RMW's output, claim / fail read off GD0's label. -/
def OAcq (i : Agent) (R1 R2 : IProp GF) (kA : Nat) (_v : List (BitVec 8)) : IProp GF :=
  match (AxOpsem.grow (gtAdGd GT) i)[kA]? with
  | some (Lbl.LRmw _ _ _ _ rvs _ _) =>
      if rvs = AxSpinX4.z4 then
        iprop(AxAnnot.annotOwn (i, kA) R1 ∗ AxAnnot.annotOwn (i, kA) R2)
      else notheld nm.xnReg L.xlLk i
  | _ => iprop(True)

/-- Rocq `FstAcq_nh` ([ID-5]): the acquire write flow from `notheld` in hand: success
(`rvs = z4`) by `fxClaim`, failure (low byte read ≠ 0) by `fxNeutral`, `notheld` handed back. -/
theorem FstAcqNh (HL : xlayOk L) (Hcons : rvwmoCatConsistent (gtAdGd GT))
    (i : Agent) (kA t : Nat) (rvs : List (BitVec 8)) (R1 R2 : IProp GF) (lo hi : Nat) :
    (AxOpsem.grow (gtAdGd GT) i)[kA]? =
      some (Lbl.LRmw true false L.xlLk [t, t, t, t] rvs AxSpinX4.o4 .WCplain) →
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

end flowsAm

end Weak
