/-
Weak: **Phase 2, part 2 of the spinlock plan -- the handle-based ACQUIRE / RELEASE CONTRACTS** at
`spinOb5 ya x Cl cv` / `splPol` (lock byte at `ya`, any owned byte `x`, any lk->cpu range `Cl`;
`R = spinR5 = RL [x] ∗ RL Cl`) on the hand lock instructions of `AxSpinProt7` (`acqRmw` =
`amoswap.aq lk ← 1; branch on old = 0`, `fenceM` = `fence rw,w`, `relM` = `sw lk ← 0` (WCrel)).
Instruction-level; NOT real xv6 acquire/release code (no fetch/decode, one-byte lock).

Rocq: `iris/AxSpinH2.v` @ xxvzwolszwmp.

## The Rocq header, in substance

PROVED
  `wpdAcquire` -- THE LITERAL CONTRACT: `isLock R ∗ notheld i ⊢ WPd {{ ∃ c, ⌜c = (i,k) ∧
    lkClaim c⌝ ∗ c ↦ₐ (locked i c ∗ R c) }}` (continuation form) -- `fe5Claim`.
  `wpdAcquireH` -- THE HANDLE FORM a critical section consumes: `c ↦ₐ (locked i c ∗ RL Cl c)` ∗
    `x ↦ₕ{c} none`; the claim's annotation is allocated ALREADY SPLIT (`wpdAcquireGen`'s
    `Hsplit`): an annotation can only be split inside a step.
  `wpdReacquireH`/`wpdReacquireGen`: `notheld` drawn from the hart's own earlier release
    annotation `w ↦ₐ notheld i` (`relClaimLobp`, rule 1).
  `wpdAcquireFail`: the failed spin (`fe5Neutral`), frame passed on.
  `wpdReleaseGen` -- THE RELEASE CONTRACT: `isLock R ∗ [∗map] e ↦ P ∈ m, e ↦ₐ P` with a wand
    producing `locked i c` and EACH component of `R` at some anchor in `dom m` (all po-before the
    fence: `fenceLobp` / `fenceGob`; `fe5Release'`) ⊢ WPd {{ w ↦ₐ notheld i }}.
  `wpdReleaseH`: the two-handle instance `c ↦ₐ (locked ∗ RL Cl c)` ∗ `x ↦ₕ{ex} mv`, `ex ≠ c`.
FINDING (unchanged by the port): the `ex ≠ c` premise is real -- one draw map has one entry per
event; an `annot_merge` step would be needed; not done.

## Deviations from Rocq

1. VOCABULARY (as `AxSpinH` deviation 1): `grow GD i !! k` ↦ `(AxOpsem.grow (gtAdGd GT) i)[k]?`,
   `S k` ↦ `k + 1`, `dom m` ↦ `FiniteMap.dom_set m : GSet Geid`, `B0`/`B1` ↦ `b0`/`b1`,
   `M unit` ↦ `SailM Unit`, `athread` ↦ `Athread`.
2. CONTEXTS (as `AxSpinH` deviation 2): Rocq's section variables are explicit leading arguments
   in Rocq's order `x Cl cv GT nm cpu Hcons HlkX` (every lemma is `Proof using Hcons HlkX`);
   `invGS_gen HasNoLc Σ` ↦ `[InvGS_gen hlc GF]` for any `hlc`.  O2 STAGE C: Rocq's `Tf` argument
   of `AxGA2`/`tierA_wpd` is gone.  The local instances `c_pol` ↦ `splPol GT` and `c_G` ↦
   `shG (gtAdGd GT) spinN Unit (spinOb5 ya x Cl cv) nm` (= `AxSpinProt6.s5G`) are passed
   explicitly; the notations `GD`/`G`/`OB`/`R5`/`TW`/`LK`/`NH`/`hdl5` are unfolded
   (`hdl5 a e mv` ↦ `hdl (Rbo nm.1 (gtAdGd GT)) a e mv`).
3. STATEMENT SHAPES (as `AxSpinH` deviation 3): Rocq's wand chains `A -∗ B -∗ …` ↦ `⊢ A -∗ B -∗ …`,
   pure premises stay `→`.  lean-sail hand nodes as `AxSpinProt7` (`acqRmw`, `fenceM`, `relM`;
   the success/fail branch is `if b0 = b0 …` / `if v = b0 …` -- Rocq `bool_decide`).

**Rocq → Lean name map.**  `wpd_acquire_gen` `wpdAcquireGen`, `wpd_reacquire_gen`
`wpdReacquireGen`, `wpd_acquire` `wpdAcquire`, `wpd_acquire_h` `wpdAcquireH`, `wpd_reacquire_h`
`wpdReacquireH`, `wpd_acquire_fail` `wpdAcquireFail`, `wpd_release_gen` `wpdReleaseGen`,
`wpd_release_h` `wpdReleaseH`.

**Dropped:** none (10 Rocq decls incl. the 2 local instances `c_pol`/`c_G` (inlined); 8 Lean).
-/
import Weak.AxSpinH

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D

section contracts
variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF] [AxannotGS GF]
  [AxlogG GF Hent] [SpinlockG GF]

/-! # 1. ACQUIRE -- the successful `amoswap.aq lk ← 1` (reads 0) -/

/-- The generic success leaf: the claim's flow equation deposits `locked i c ∗ R c`; the event's
annotation is allocated already SPLIT along any `Hsplit`.  `notheld` in hand. -/
theorem wpdAcquireGen (x : Int) (Cl : List Int) (cv : Agent → List (BitVec 8)) (GT : GdexecT)
    (nm : spinN) (cpu : CPU) (Hcons : rvwmoCatConsistent (gtAdGd GT)) (HlkX : ya ∉ X5 x Cl)
    (i : Agent) (k t : Nat) (kok kf : SailM Unit) (R1 R2 : IProp GF) (Φ : Athread → IProp GF) :
    k ≠ (AxOpsem.grow (gtAdGd GT) i).length →
    (AxOpsem.grow (gtAdGd GT) i)[k]? = some (.LRmw true false ya [t] [b0] [b1] .WCplain) →
    (iprop(locked nm.2 ya i (i, k) ∗ spinR5 x Cl nm (gtAdGd GT) (i, k)) ⊢ iprop(R1 ∗ R2)) →
    ⊢ isLock nm.2 ya (spinR5 x Cl nm (gtAdGd GT)) -∗ notheld nm.2 ya i -∗
      (⌜lkClaim ya (gtAdGd GT).gdG (i, k) (gwriteAt (gtAdGd GT).gdG t)⌝ -∗
        AxAnnot.annotOwn (i, k) R1 -∗ AxAnnot.annotOwn (i, k) R2 -∗
        ∀ rs : RegFile, @tierAWpd GF hlc _ _ (splPol GT) (gtAdGd GT) spinN Unit
          (spinOb5 ya x Cl cv) nm ⟨hp cpu kok rs, k + 1⟩ .MaybeStuck i Φ) -∗
      ∀ rs : RegFile, @tierAWpd GF hlc _ _ (splPol GT) (gtAdGd GT) spinN Unit
        (spinOb5 ya x Cl cv) nm ⟨hp cpu (acqRmw kok kf) rs, k⟩ .MaybeStuck i Φ := by
  intro Hne Hrow Hsplit
  have Hl : gxLbl (gtAdGd GT).gdG (i, k) = some (.LRmw true false ya [t] [b0] [b1] .WCplain) := by
    rw [gxLblGrow]; exact Hrow
  obtain ⟨Hrd, Hw, Hsg, -⟩ := gwbRmw _ _ _ _ _ _ _ Hl
  have Hcl : lkClaim ya (gtAdGd GT).gdG (i, k) (gwriteAt (gtAdGd GT).gdG t) := ⟨t, Hrd, rfl, Hw⟩
  have Hval : graphData (gtAdGd GT) (i, k) = some (WeakInterpProj.wbytes 1 b1) := by
    unfold graphData; rw [Hl]; simp [lblData, l3pWbytes1]
  have Hs : ⊢ iprop(locked (GF := GF) nm.2 ya i (i, k) ∗ spinR5 x Cl nm (gtAdGd GT) (i, k)) -∗
      iprop(R1 ∗ R2) := BI.wand_intro (BI.emp_sep.1.trans Hsplit)
  have HW := shRmwWrite (hlc := hlc) (pol := splPol GT) (gtAdGd GT) spinN Unit
    (spinOb5 ya x Cl cv) nm cpu i Φ ypaM ypaMRam (if b0 = b0 then kok else kf) k Hne
    iprop(isLock (GF := GF) nm.2 ya (spinR5 x Cl nm (gtAdGd GT)) ∗ notheld nm.2 ya i ∗
      (⌜lkClaim ya (gtAdGd GT).gdG (i, k) (gwriteAt (gtAdGd GT).gdG t)⌝ -∗
        AxAnnot.annotOwn (i, k) R1 -∗ AxAnnot.annotOwn (i, k) R2 -∗
        ∀ rs : RegFile, @tierAWpd GF hlc _ _ (splPol GT) (gtAdGd GT) spinN Unit
          (spinOb5 ya x Cl cv) nm ⟨hp cpu kok rs, k + 1⟩ .MaybeStuck i Φ))
    (fun rs => by
      iintro ⟨#Hil, Hnh, HΨ⟩
      ihave Hfe := (fe5Claim (hlc := hlc) ya x Cl cv GT nm Hcons HlkX (i, k)
        (gwriteAt (gtAdGd GT).gdG t) Hcl (fun a v H => (Hsg a v H).1)) $$ Hnh Hil
      ihave Hfe := (@flowEqDynMono hlc GF _ (shG (gtAdGd GT) spinN Unit (spinOb5 ya x Cl cv) nm)
        (splPol GT) (gtAdGd GT) (i, k) _ (∅ : Mea GF)
        iprop(locked nm.2 ya i (i, k) ∗ spinR5 x Cl nm (gtAdGd GT) (i, k))
        iprop(R1 ∗ R2)) $$ [] Hfe
      · inext
        ihave H := Hs
        iexact H
      iapply (evPlain (hlc := hlc) (pol := splPol GT) (gtAdGd GT) spinN Unit
        (spinOb5 ya x Cl cv) nm i k R1 R2 _ _ Hval) $$ Hfe
      iintro H1 H2
      rw [if_pos rfl]
      iapply HΨ $$ %Hcl H1 H2 %rs)
  have HR := shRmwRead (hlc := hlc) (pol := splPol GT) (gtAdGd GT) spinN Unit
    (spinOb5 ya x Cl cv) nm cpu i Φ ypaM ypaMRam (acqK kok kf) k t b0 .WCplain Hne Hrow
    iprop(isLock (GF := GF) nm.2 ya (spinR5 x Cl nm (gtAdGd GT)) ∗ notheld nm.2 ya i ∗
      (⌜lkClaim ya (gtAdGd GT).gdG (i, k) (gwriteAt (gtAdGd GT).gdG t)⌝ -∗
        AxAnnot.annotOwn (i, k) R1 -∗ AxAnnot.annotOwn (i, k) R2 -∗
        ∀ rs : RegFile, @tierAWpd GF hlc _ _ (splPol GT) (gtAdGd GT) spinN Unit
          (spinOb5 ya x Cl cv) nm ⟨hp cpu kok rs, k + 1⟩ .MaybeStuck i Φ))
    (fun rs => by
      iintro ⟨#Hil, Hnh, HΨ⟩
      rw [AxSpinProt7.acqKOk]
      iapply HW $$ [$Hil $Hnh $HΨ] %rs)
  iintro #Hil Hnh HΨ
  iapply HR $$ [$Hil $Hnh $HΨ]

/-- RE-ACQUIRE: `notheld` is the phase-2 resource `w ↦ₐ notheld i` of the hart's own earlier
release `w` (ppo rule 1: `sw lk` → `amoswap lk` puts `w` in `lobp`). -/
theorem wpdReacquireGen (x : Int) (Cl : List Int) (cv : Agent → List (BitVec 8)) (GT : GdexecT)
    (nm : spinN) (cpu : CPU) (Hcons : rvwmoCatConsistent (gtAdGd GT)) (HlkX : ya ∉ X5 x Cl)
    (i : Agent) (kw k t : Nat) (kok kf : SailM Unit) (cls : WmClass) (R1 R2 : IProp GF)
    (Φ : Athread → IProp GF) :
    k ≠ (AxOpsem.grow (gtAdGd GT) i).length →
    (AxOpsem.grow (gtAdGd GT) i)[kw]? = some (.LStore false ya [b0] cls) → kw < k →
    (AxOpsem.grow (gtAdGd GT) i)[k]? = some (.LRmw true false ya [t] [b0] [b1] .WCplain) →
    (iprop(locked nm.2 ya i (i, k) ∗ spinR5 x Cl nm (gtAdGd GT) (i, k)) ⊢ iprop(R1 ∗ R2)) →
    ⊢ isLock nm.2 ya (spinR5 x Cl nm (gtAdGd GT)) -∗
      AxAnnot.annotOwn (i, kw) (notheld nm.2 ya i) -∗
      (⌜lkClaim ya (gtAdGd GT).gdG (i, k) (gwriteAt (gtAdGd GT).gdG t)⌝ -∗
        AxAnnot.annotOwn (i, k) R1 -∗ AxAnnot.annotOwn (i, k) R2 -∗
        ∀ rs : RegFile, @tierAWpd GF hlc _ _ (splPol GT) (gtAdGd GT) spinN Unit
          (spinOb5 ya x Cl cv) nm ⟨hp cpu kok rs, k + 1⟩ .MaybeStuck i Φ) -∗
      ∀ rs : RegFile, @tierAWpd GF hlc _ _ (splPol GT) (gtAdGd GT) spinN Unit
        (spinOb5 ya x Cl cv) nm ⟨hp cpu (acqRmw kok kf) rs, k⟩ .MaybeStuck i Φ := by
  intro Hne Hroww Hlt Hrow Hsplit
  have Hl : gxLbl (gtAdGd GT).gdG (i, k) = some (.LRmw true false ya [t] [b0] [b1] .WCplain) := by
    rw [gxLblGrow]; exact Hrow
  have Hlw : gxLbl (gtAdGd GT).gdG (i, kw) = some (.LStore false ya [b0] cls) := by
    rw [gxLblGrow]; exact Hroww
  obtain ⟨Hrd, Hw, Hsg, -⟩ := gwbRmw _ _ _ _ _ _ _ Hl
  have Hcl : lkClaim ya (gtAdGd GT).gdG (i, k) (gwriteAt (gtAdGd GT).gdG t) := ⟨t, Hrd, rfl, Hw⟩
  have Hin : ((i, kw) : Geid) ∈ @Axpol.lobp (splPol GT) (gtAdGd GT) (i, k) := by
    obtain ⟨Hz, -⟩ := gwbStore _ _ _ _ _ Hlw
    exact relClaimLobp (gtAdGd GT) Hcons ya (i, kw) (i, k) _ _ Hlw rfl Hz
      (gpoRow (gtAdGd GT) i kw k _ _ Hlw Hl Hlt) Hcl
  have Hval : graphData (gtAdGd GT) (i, k) = some (WeakInterpProj.wbytes 1 b1) := by
    unfold graphData; rw [Hl]; simp [lblData, l3pWbytes1]
  have Hs : ⊢ iprop((locked (GF := GF) nm.2 ya i (i, k) ∗ spinR5 x Cl nm (gtAdGd GT) (i, k)) ∗
      True) -∗ iprop(R1 ∗ R2) := by
    iintro ⟨H, _⟩
    iapply Hsplit
    iexact H
  have Hsing : ⊢ ([∗map] Rin ∈ ({[((i, kw) : Geid) := notheld (GF := GF) nm.2 ya i]} :
      Mea GF), Rin) -∗ iprop(notheld (GF := GF) nm.2 ya i ∗ True) := by
    iintro H
    ihave H := (BigSepM.bigSepM_singleton (M := GMapF Geid)).1 $$ H
    isplitl [H]
    · iexact H
    · itrivial
  have HW := shRmwWrite (hlc := hlc) (pol := splPol GT) (gtAdGd GT) spinN Unit
    (spinOb5 ya x Cl cv) nm cpu i Φ ypaM ypaMRam (if b0 = b0 then kok else kf) k Hne
    iprop(isLock (GF := GF) nm.2 ya (spinR5 x Cl nm (gtAdGd GT)) ∗
      AxAnnot.annotOwn (i, kw) (notheld nm.2 ya i) ∗
      (⌜lkClaim ya (gtAdGd GT).gdG (i, k) (gwriteAt (gtAdGd GT).gdG t)⌝ -∗
        AxAnnot.annotOwn (i, k) R1 -∗ AxAnnot.annotOwn (i, k) R2 -∗
        ∀ rs : RegFile, @tierAWpd GF hlc _ _ (splPol GT) (gtAdGd GT) spinN Unit
          (spinOb5 ya x Cl cv) nm ⟨hp cpu kok rs, k + 1⟩ .MaybeStuck i Φ))
    (fun rs => by
      iintro ⟨#Hil, Hnh, HΨ⟩
      ihave Hw := Hsing
      ihave Hfe := (fe5Claim' (hlc := hlc) ya x Cl cv GT nm Hcons HlkX (i, k)
        (gwriteAt (gtAdGd GT).gdG t) iprop(True)
        ({[((i, kw) : Geid) := notheld (GF := GF) nm.2 ya i]} : Mea GF) Hcl
        (fun a v H => (Hsg a v H).1)) $$ Hil Hw
      ihave Hfe := (@flowEqDynMono hlc GF _ (shG (gtAdGd GT) spinN Unit (spinOb5 ya x Cl cv) nm)
        (splPol GT) (gtAdGd GT) (i, k) _ _
        iprop((locked nm.2 ya i (i, k) ∗ spinR5 x Cl nm (gtAdGd GT) (i, k)) ∗ True)
        iprop(R1 ∗ R2)) $$ [] Hfe
      · inext
        ihave H := Hs
        iexact H
      iapply (evDraw (hlc := hlc) (pol := splPol GT) (gtAdGd GT) spinN Unit
        (spinOb5 ya x Cl cv) nm (splAxpolWf GT) i k (i, kw) _ R1 R2 _ _ Hval Hin) $$ Hnh Hfe
      iintro H1 H2
      rw [if_pos rfl]
      iapply HΨ $$ %Hcl H1 H2 %rs)
  have HR := shRmwRead (hlc := hlc) (pol := splPol GT) (gtAdGd GT) spinN Unit
    (spinOb5 ya x Cl cv) nm cpu i Φ ypaM ypaMRam (acqK kok kf) k t b0 .WCplain Hne Hrow
    iprop(isLock (GF := GF) nm.2 ya (spinR5 x Cl nm (gtAdGd GT)) ∗
      AxAnnot.annotOwn (i, kw) (notheld nm.2 ya i) ∗
      (⌜lkClaim ya (gtAdGd GT).gdG (i, k) (gwriteAt (gtAdGd GT).gdG t)⌝ -∗
        AxAnnot.annotOwn (i, k) R1 -∗ AxAnnot.annotOwn (i, k) R2 -∗
        ∀ rs : RegFile, @tierAWpd GF hlc _ _ (splPol GT) (gtAdGd GT) spinN Unit
          (spinOb5 ya x Cl cv) nm ⟨hp cpu kok rs, k + 1⟩ .MaybeStuck i Φ))
    (fun rs => by
      iintro ⟨#Hil, Hnh, HΨ⟩
      rw [AxSpinProt7.acqKOk]
      iapply HW $$ [$Hil $Hnh $HΨ] %rs)
  iintro #Hil Hnh HΨ
  iapply HR $$ [$Hil $Hnh $HΨ]

/-- THE ACQUIRE CONTRACT, LITERAL FORM: `∃ c, ⌜lkClaim c⌝ ∗ c ↦ₐ (locked i c ∗ R c)` with
`c = (i, k)`. -/
theorem wpdAcquire (x : Int) (Cl : List Int) (cv : Agent → List (BitVec 8)) (GT : GdexecT)
    (nm : spinN) (cpu : CPU) (Hcons : rvwmoCatConsistent (gtAdGd GT)) (HlkX : ya ∉ X5 x Cl)
    (i : Agent) (k t : Nat) (kok kf : SailM Unit) (Φ : Athread → IProp GF) :
    k ≠ (AxOpsem.grow (gtAdGd GT) i).length →
    (AxOpsem.grow (gtAdGd GT) i)[k]? = some (.LRmw true false ya [t] [b0] [b1] .WCplain) →
    ⊢ isLock nm.2 ya (spinR5 x Cl nm (gtAdGd GT)) -∗ notheld nm.2 ya i -∗
      ((∃ (c : Geid), ⌜c = (i, k) ∧ lkClaim ya (gtAdGd GT).gdG c (gwriteAt (gtAdGd GT).gdG t)⌝ ∗
          AxAnnot.annotOwn c iprop(locked nm.2 ya i c ∗ spinR5 x Cl nm (gtAdGd GT) c)) -∗
        ∀ rs : RegFile, @tierAWpd GF hlc _ _ (splPol GT) (gtAdGd GT) spinN Unit
          (spinOb5 ya x Cl cv) nm ⟨hp cpu kok rs, k + 1⟩ .MaybeStuck i Φ) -∗
      ∀ rs : RegFile, @tierAWpd GF hlc _ _ (splPol GT) (gtAdGd GT) spinN Unit
        (spinOb5 ya x Cl cv) nm ⟨hp cpu (acqRmw kok kf) rs, k⟩ .MaybeStuck i Φ := by
  intro Hne Hrow
  have Hsplit : iprop(locked (GF := GF) nm.2 ya i (i, k) ∗ spinR5 x Cl nm (gtAdGd GT) (i, k)) ⊢
      iprop((locked nm.2 ya i (i, k) ∗ spinR5 x Cl nm (gtAdGd GT) (i, k)) ∗ True) := by
    iintro H
    isplitl [H]
    · iexact H
    · itrivial
  iintro #Hil Hnh HΨ
  iapply (wpdAcquireGen (hlc := hlc) (GF := GF) x Cl cv GT nm cpu Hcons HlkX i k t kok kf
    iprop(locked nm.2 ya i (i, k) ∗ spinR5 x Cl nm (gtAdGd GT) (i, k)) iprop(True) Φ
    Hne Hrow Hsplit) $$ Hil Hnh
  iintro %Hcl H _
  iapply HΨ
  iexists (i, k)
  isplitr
  · ipureintro
    exact ⟨rfl, Hcl⟩
  · iexact H

/-- THE ACQUIRE CONTRACT, HANDLE FORM (what a critical section consumes): the lock's `x`
component as a HANDLE `x ↦ₕ{c} none`, `locked` travelling with the lk->cpu component at `c`. -/
theorem wpdAcquireH (x : Int) (Cl : List Int) (cv : Agent → List (BitVec 8)) (GT : GdexecT)
    (nm : spinN) (cpu : CPU) (Hcons : rvwmoCatConsistent (gtAdGd GT)) (HlkX : ya ∉ X5 x Cl)
    (i : Agent) (k t : Nat) (kok kf : SailM Unit) (Φ : Athread → IProp GF) :
    k ≠ (AxOpsem.grow (gtAdGd GT) i).length →
    (AxOpsem.grow (gtAdGd GT) i)[k]? = some (.LRmw true false ya [t] [b0] [b1] .WCplain) →
    ⊢ isLock nm.2 ya (spinR5 x Cl nm (gtAdGd GT)) -∗ notheld nm.2 ya i -∗
      (⌜lkClaim ya (gtAdGd GT).gdG (i, k) (gwriteAt (gtAdGd GT).gdG t)⌝ -∗
        AxAnnot.annotOwn (i, k) iprop(locked nm.2 ya i (i, k) ∗ RL nm.1 (gtAdGd GT) Cl (i, k)) -∗
        hdl (Rbo nm.1 (gtAdGd GT)) x (i, k) none -∗
        ∀ rs : RegFile, @tierAWpd GF hlc _ _ (splPol GT) (gtAdGd GT) spinN Unit
          (spinOb5 ya x Cl cv) nm ⟨hp cpu kok rs, k + 1⟩ .MaybeStuck i Φ) -∗
      ∀ rs : RegFile, @tierAWpd GF hlc _ _ (splPol GT) (gtAdGd GT) spinN Unit
        (spinOb5 ya x Cl cv) nm ⟨hp cpu (acqRmw kok kf) rs, k⟩ .MaybeStuck i Φ := by
  intro Hne Hrow
  have Hsplit : iprop(locked (GF := GF) nm.2 ya i (i, k) ∗ spinR5 x Cl nm (gtAdGd GT) (i, k)) ⊢
      iprop((locked nm.2 ya i (i, k) ∗ RL nm.1 (gtAdGd GT) Cl (i, k)) ∗
        Rbo nm.1 (gtAdGd GT) x (i, k) none) := by
    unfold spinR5
    iintro ⟨Hlk, Hx, HC⟩
    isplitl [Hlk HC]
    · isplitl [Hlk]
      · iexact Hlk
      · iexact HC
    · iapply (RL1Rbo nm.1 (gtAdGd GT) x (i, k)) $$ Hx
  unfold hdl
  iintro #Hil Hnh HΨ
  iapply (wpdAcquireGen (hlc := hlc) (GF := GF) x Cl cv GT nm cpu Hcons HlkX i k t kok kf
    iprop(locked nm.2 ya i (i, k) ∗ RL nm.1 (gtAdGd GT) Cl (i, k))
    (Rbo nm.1 (gtAdGd GT) x (i, k) none) Φ Hne Hrow Hsplit) $$ Hil Hnh HΨ

theorem wpdReacquireH (x : Int) (Cl : List Int) (cv : Agent → List (BitVec 8)) (GT : GdexecT)
    (nm : spinN) (cpu : CPU) (Hcons : rvwmoCatConsistent (gtAdGd GT)) (HlkX : ya ∉ X5 x Cl)
    (i : Agent) (kw k t : Nat) (kok kf : SailM Unit) (cls : WmClass) (Φ : Athread → IProp GF) :
    k ≠ (AxOpsem.grow (gtAdGd GT) i).length →
    (AxOpsem.grow (gtAdGd GT) i)[kw]? = some (.LStore false ya [b0] cls) → kw < k →
    (AxOpsem.grow (gtAdGd GT) i)[k]? = some (.LRmw true false ya [t] [b0] [b1] .WCplain) →
    ⊢ isLock nm.2 ya (spinR5 x Cl nm (gtAdGd GT)) -∗
      AxAnnot.annotOwn (i, kw) (notheld nm.2 ya i) -∗
      (⌜lkClaim ya (gtAdGd GT).gdG (i, k) (gwriteAt (gtAdGd GT).gdG t)⌝ -∗
        AxAnnot.annotOwn (i, k) iprop(locked nm.2 ya i (i, k) ∗ RL nm.1 (gtAdGd GT) Cl (i, k)) -∗
        hdl (Rbo nm.1 (gtAdGd GT)) x (i, k) none -∗
        ∀ rs : RegFile, @tierAWpd GF hlc _ _ (splPol GT) (gtAdGd GT) spinN Unit
          (spinOb5 ya x Cl cv) nm ⟨hp cpu kok rs, k + 1⟩ .MaybeStuck i Φ) -∗
      ∀ rs : RegFile, @tierAWpd GF hlc _ _ (splPol GT) (gtAdGd GT) spinN Unit
        (spinOb5 ya x Cl cv) nm ⟨hp cpu (acqRmw kok kf) rs, k⟩ .MaybeStuck i Φ := by
  intro Hne Hroww Hlt Hrow
  have Hsplit : iprop(locked (GF := GF) nm.2 ya i (i, k) ∗ spinR5 x Cl nm (gtAdGd GT) (i, k)) ⊢
      iprop((locked nm.2 ya i (i, k) ∗ RL nm.1 (gtAdGd GT) Cl (i, k)) ∗
        Rbo nm.1 (gtAdGd GT) x (i, k) none) := by
    unfold spinR5
    iintro ⟨Hlk, Hx, HC⟩
    isplitl [Hlk HC]
    · isplitl [Hlk]
      · iexact Hlk
      · iexact HC
    · iapply (RL1Rbo nm.1 (gtAdGd GT) x (i, k)) $$ Hx
  unfold hdl
  iintro #Hil Hnh HΨ
  iapply (wpdReacquireGen (hlc := hlc) (GF := GF) x Cl cv GT nm cpu Hcons HlkX i kw k t kok kf
    cls iprop(locked nm.2 ya i (i, k) ∗ RL nm.1 (gtAdGd GT) Cl (i, k))
    (Rbo nm.1 (gtAdGd GT) x (i, k) none) Φ Hne Hroww Hlt Hrow Hsplit) $$ Hil Hnh HΨ

/-- ACQUIRE-FAIL (`amoswap` reads `v ≠ 0`): nothing drawn, nothing handed out; the frame `P`
passes to the retry. -/
theorem wpdAcquireFail (x : Int) (Cl : List Int) (cv : Agent → List (BitVec 8)) (GT : GdexecT)
    (nm : spinN) (cpu : CPU) (Hcons : rvwmoCatConsistent (gtAdGd GT)) (HlkX : ya ∉ X5 x Cl)
    (i : Agent) (k t : Nat) (v : BitVec 8) (kok kf : SailM Unit) (P : IProp GF)
    (Φ : Athread → IProp GF) :
    k ≠ (AxOpsem.grow (gtAdGd GT) i).length →
    (AxOpsem.grow (gtAdGd GT) i)[k]? = some (.LRmw true false ya [t] [v] [b1] .WCplain) →
    v ≠ b0 →
    ⊢ P -∗ (P -∗ ∀ rs : RegFile, @tierAWpd GF hlc _ _ (splPol GT) (gtAdGd GT) spinN Unit
          (spinOb5 ya x Cl cv) nm ⟨hp cpu kf rs, k + 1⟩ .MaybeStuck i Φ) -∗
      ∀ rs : RegFile, @tierAWpd GF hlc _ _ (splPol GT) (gtAdGd GT) spinN Unit
        (spinOb5 ya x Cl cv) nm ⟨hp cpu (acqRmw kok kf) rs, k⟩ .MaybeStuck i Φ := by
  intro Hne Hrow Hv
  have Hl : gxLbl (gtAdGd GT).gdG (i, k) = some (.LRmw true false ya [t] [v] [b1] .WCplain) := by
    rw [gxLblGrow]; exact Hrow
  obtain ⟨Hrd, Hw, Hsg, -⟩ := gwbRmw _ _ _ _ _ _ _ Hl
  have Hval : graphData (gtAdGd GT) (i, k) = some (WeakInterpProj.wbytes 1 b1) := by
    unfold graphData; rw [Hl]; simp [lblData, l3pWbytes1]
  have HW := shRmwWrite (hlc := hlc) (pol := splPol GT) (gtAdGd GT) spinN Unit
    (spinOb5 ya x Cl cv) nm cpu i Φ ypaM ypaMRam (if v = b0 then kok else kf) k Hne
    iprop(P ∗ (P -∗ ∀ rs : RegFile, @tierAWpd GF hlc _ _ (splPol GT) (gtAdGd GT) spinN Unit
          (spinOb5 ya x Cl cv) nm ⟨hp cpu kf rs, k + 1⟩ .MaybeStuck i Φ))
    (fun rs => by
      iintro ⟨HP, HΨ⟩
      ihave Hfe := fe5Neutral (hlc := hlc) (GF := GF) ya x Cl cv GT nm Hcons HlkX (i, k) t v Hrd
        Hv Hw (fun a v' H => (Hsg a v' H).1)
      iapply (evPlain (hlc := hlc) (pol := splPol GT) (gtAdGd GT) spinN Unit
        (spinOb5 ya x Cl cv) nm i k iprop(True) iprop(True) _ _ Hval) $$ [Hfe]
      · iapply (@flowEqDynMono hlc GF _ (shG (gtAdGd GT) spinN Unit (spinOb5 ya x Cl cv) nm)
          (splPol GT) (gtAdGd GT) (i, k) _ (∅ : Mea GF) iprop(True) iprop(True ∗ True)) $$ [] Hfe
        inext
        iintro _
        isplitl []
        · itrivial
        · itrivial
      iintro _ _
      rw [if_neg Hv]
      iapply HΨ $$ HP %rs)
  have HR := shRmwRead (hlc := hlc) (pol := splPol GT) (gtAdGd GT) spinN Unit
    (spinOb5 ya x Cl cv) nm cpu i Φ ypaM ypaMRam (acqK kok kf) k t v .WCplain Hne Hrow
    iprop(P ∗ (P -∗ ∀ rs : RegFile, @tierAWpd GF hlc _ _ (splPol GT) (gtAdGd GT) spinN Unit
          (spinOb5 ya x Cl cv) nm ⟨hp cpu kf rs, k + 1⟩ .MaybeStuck i Φ))
    (fun rs => by
      iintro ⟨HP, HΨ⟩
      rw [AxSpinProt7.acqKOk]
      iapply HW $$ [$HP $HΨ] %rs)
  iintro HP HΨ
  iapply HR $$ [$HP $HΨ]

/-! # 2. RELEASE -- `fence rw,w; sw lk ← 0` -/

/-- THE RELEASE CONTRACT, GENERIC FORM: the release store draws a FAMILY of annotations `m`
(each at a po-earlier memory event, hence a lob-predecessor through the fence, and gob-before the
store), from which `locked i c` and the two components of `R` are produced; deposits
`notheld i` at the store. -/
theorem wpdReleaseGen (x : Int) (Cl : List Int) (cv : Agent → List (BitVec 8)) (GT : GdexecT)
    (nm : spinN) (cpu : CPU) (Hcons : rvwmoCatConsistent (gtAdGd GT)) (HlkX : ya ∉ X5 x Cl)
    (i : Agent) (kf : Nat) (m' : SailM Unit) (c : Geid) (m : Mea GF) (Φ : Athread → IProp GF) :
    kf ≠ (AxOpsem.grow (gtAdGd GT) i).length → kf + 1 ≠ (AxOpsem.grow (gtAdGd GT) i).length →
    (AxOpsem.grow (gtAdGd GT) i)[kf]? = some (.LFence true true false true) →
    (AxOpsem.grow (gtAdGd GT) i)[kf + 1]? = some (.LStore false ya [b0] .WCrel) →
    (∀ e, e ∈ (FiniteMap.dom_set m : GSet Geid) → e.1 = i ∧ e.2 < kf ∧
      ∃ l, (AxOpsem.grow (gtAdGd GT) i)[e.2]? = some l ∧ lbIsMem l = true) →
    ⊢ isLock nm.2 ya (spinR5 x Cl nm (gtAdGd GT)) -∗
      ([∗map] e ↦ P ∈ m, AxAnnot.annotOwn e P) -∗
      (([∗map] P ∈ m, P) -∗
        locked nm.2 ya i c ∗
        (∃ (a : Geid), ⌜a ∈ (FiniteMap.dom_set m : GSet Geid)⌝ ∗ RL nm.1 (gtAdGd GT) [x] a) ∗
        (∃ (a : Geid), ⌜a ∈ (FiniteMap.dom_set m : GSet Geid)⌝ ∗ RL nm.1 (gtAdGd GT) Cl a)) -∗
      (AxAnnot.annotOwn (i, kf + 1) (notheld nm.2 ya i) -∗
        ∀ rs : RegFile, @tierAWpd GF hlc _ _ (splPol GT) (gtAdGd GT) spinN Unit
          (spinOb5 ya x Cl cv) nm ⟨hp cpu m' rs, kf + 1 + 1⟩ .MaybeStuck i Φ) -∗
      ∀ rs : RegFile, @tierAWpd GF hlc _ _ (splPol GT) (gtAdGd GT) spinN Unit
        (spinOb5 ya x Cl cv) nm ⟨hp cpu (fenceM (relM m')) rs, kf⟩ .MaybeStuck i Φ := by
  intro Hne1 Hne2 Hf Hst Hdom
  have Hlf : gxLbl (gtAdGd GT).gdG (i, kf) = some (.LFence true true false true) := by
    rw [gxLblGrow]; exact Hf
  have Hls : gxLbl (gtAdGd GT).gdG (i, kf + 1) = some (.LStore false ya [b0] .WCrel) := by
    rw [gxLblGrow]; exact Hst
  have Hgob : ∀ e, e ∈ (FiniteMap.dom_set m : GSet Geid) →
      gobCat (gtAdGd GT) e (i, kf + 1) ∧
        e ∈ @Axpol.lobp (splPol GT) (gtAdGd GT) (i, kf + 1) := by
    rintro ⟨ei, ek⟩ He
    obtain ⟨Hi, Hlt, l, Hl, Hmem⟩ := Hdom _ He
    dsimp only at Hi Hlt Hl
    rw [show ((ei, ek) : Geid) = (i, ek) from by rw [Hi]]
    have Hl' : gxLbl (gtAdGd GT).gdG (i, ek) = some l := by rw [gxLblGrow]; exact Hl
    exact ⟨fenceGob (gtAdGd GT) i ek kf (kf + 1) l ya [b0] .WCrel Hl' (WeakRvwmoGraph.gwfMemRW _ _ _ Hcons.1 Hl' Hmem) Hlf Hls Hlt
        (by omega),
      fenceLobp (gtAdGd GT) Hcons i ek kf (kf + 1) l ya [b0] .WCrel Hl' Hmem Hlf Hls Hlt
        (by omega)⟩
  have HS := shPos (hlc := hlc) (pol := splPol GT) (gtAdGd GT) spinN Unit (spinOb5 ya x Cl cv)
    nm cpu i Φ
    iprop(isLock (GF := GF) nm.2 ya (spinR5 x Cl nm (gtAdGd GT)) ∗
      ([∗map] e ↦ P ∈ m, AxAnnot.annotOwn e P) ∗
      (([∗map] P ∈ m, P) -∗
        locked nm.2 ya i c ∗
        (∃ (a : Geid), ⌜a ∈ (FiniteMap.dom_set m : GSet Geid)⌝ ∗ RL nm.1 (gtAdGd GT) [x] a) ∗
        (∃ (a : Geid), ⌜a ∈ (FiniteMap.dom_set m : GSet Geid)⌝ ∗ RL nm.1 (gtAdGd GT) Cl a)) ∗
      (AxAnnot.annotOwn (i, kf + 1) (notheld nm.2 ya i) -∗
        ∀ rs : RegFile, @tierAWpd GF hlc _ _ (splPol GT) (gtAdGd GT) spinN Unit
          (spinOb5 ya x Cl cv) nm ⟨hp cpu m' rs, kf + 1 + 1⟩ .MaybeStuck i Φ))
    (kf + 1) (relM m') Hne2
    (fun rs id K => noReadAtWrite cpu _ ypaM ypaMRam b0 m' rs (kf + 1) id K)
    (fun rs l s' Hst' => by
      obtain ⟨rfl, Hs', -⟩ := writeInv2 cpu _ ypaM ypaMRam b0 m' rs (kf + 1) l s' Hst'
      simp only [wlWdata]
      subst Hs'
      obtain ⟨Hzw, Hsg⟩ := gwbStore _ _ _ _ _ Hls
      have Hval : graphData (gtAdGd GT) (i, kf + 1) = some (WeakInterpProj.wbytes 1 b0) := by
        unfold graphData; rw [Hls]; simp [lblData, l3pWbytes1]
      have Hsub : (FiniteMap.dom_set m : GSet Geid) ⊆
          @Axpol.lobp (splPol GT) (gtAdGd GT) (i, kf + 1) := fun e He => (Hgob e He).2
      have HF : ∀ Rj, Rj ∈ [RL (GF := GF) nm.1 (gtAdGd GT) [x], RL nm.1 (gtAdGd GT) Cl] →
          lkTransportable (gtAdGd GT) Rj := by
        intro Rj H
        simp only [List.mem_cons, List.not_mem_nil, or_false] at H
        rcases H with rfl | rfl <;> exact RLTransportable _ _ _ Hcons
      have HRs : ([∗list] Rj ∈ [RL (GF := GF) nm.1 (gtAdGd GT) [x], RL nm.1 (gtAdGd GT) Cl],
          Rj (i, kf + 1)) ⊢ spinR5 x Cl nm (gtAdGd GT) (i, kf + 1) := by
        unfold spinR5
        iintro ⟨H1, H2⟩
        ihave H2 := BigSepL.bigSepL_singleton.1 $$ H2
        isplitl [H1]
        · iexact H1
        · iexact H2
      iintro ⟨#Hil, Hm, Hw, HΨ⟩
      ihave Hfe := (fe5Release' (hlc := hlc) ya x Cl cv GT nm Hcons HlkX (i, kf + 1) i c
        (spinR5 x Cl nm (gtAdGd GT))
        [RL (GF := GF) nm.1 (gtAdGd GT) [x], RL nm.1 (gtAdGd GT) Cl] m Hzw
        (fun t v => storeNoRead _ _ _ _ _ _ _ _ Hls) (fun a v H => (Hsg a v H).1) HF HRs)
        $$ Hil [Hw]
      · iintro Hin
        icases Hw $$ Hin with ⟨Hlk, ⟨%a1, %Ha1, H1⟩, ⟨%a2, %Ha2, H2⟩⟩
        isplitl [Hlk]
        · iexact Hlk
        isplitl [H1]
        · iexists a1
          isplitr
          · ipureintro
            exact (Hgob a1 Ha1).1
          · iexact H1
        · iapply BigSepL.bigSepL_singleton.2
          iexists a2
          isplitr
          · ipureintro
            exact (Hgob a2 Ha2).1
          · iexact H2
      iapply (evDrawM (hlc := hlc) (pol := splPol GT) (gtAdGd GT) spinN Unit
        (spinOb5 ya x Cl cv) nm (splAxpolWf GT) i (kf + 1) m (notheld nm.2 ya i) iprop(True) _ _
        Hval Hsub) $$ Hm [Hfe]
      · iapply (@flowEqDynMono hlc GF _ (shG (gtAdGd GT) spinN Unit (spinOb5 ya x Cl cv) nm)
          (splPol GT) (gtAdGd GT) (i, kf + 1) _ _ (notheld nm.2 ya i)
          iprop(notheld nm.2 ya i ∗ True)) $$ [] Hfe
        inext
        iintro H
        isplitl [H]
        · iexact H
        · itrivial
      iintro H _
      iapply HΨ $$ H %rs)
  have H := shPos (hlc := hlc) (pol := splPol GT) (gtAdGd GT) spinN Unit (spinOb5 ya x Cl cv)
    nm cpu i Φ
    iprop(isLock (GF := GF) nm.2 ya (spinR5 x Cl nm (gtAdGd GT)) ∗
      ([∗map] e ↦ P ∈ m, AxAnnot.annotOwn e P) ∗
      (([∗map] P ∈ m, P) -∗
        locked nm.2 ya i c ∗
        (∃ (a : Geid), ⌜a ∈ (FiniteMap.dom_set m : GSet Geid)⌝ ∗ RL nm.1 (gtAdGd GT) [x] a) ∗
        (∃ (a : Geid), ⌜a ∈ (FiniteMap.dom_set m : GSet Geid)⌝ ∗ RL nm.1 (gtAdGd GT) Cl a)) ∗
      (AxAnnot.annotOwn (i, kf + 1) (notheld nm.2 ya i) -∗
        ∀ rs : RegFile, @tierAWpd GF hlc _ _ (splPol GT) (gtAdGd GT) spinN Unit
          (spinOb5 ya x Cl cv) nm ⟨hp cpu m' rs, kf + 1 + 1⟩ .MaybeStuck i Φ))
    kf (fenceM (relM m')) Hne1
    (fun rs id K => noReadAtFence cpu _ (relM m') rs kf id K)
    (fun rs l s' Hst' => by
      obtain ⟨rfl, Hs', -⟩ := fenceInv2 cpu _ (relM m') rs kf l s' Hst'
      simp only [wlWdata]
      subst Hs'
      iintro ⟨#Hil, Hm, Hw, HΨ⟩
      iapply (shSkip2 (GF := GF) (gtAdGd GT) spinN Unit (spinOb5 ya x Cl cv) nm i _ _)
      inext
      iapply HS $$ [$Hil $Hm $Hw $HΨ] %rs)
  iintro #Hil Hm Hw HΨ
  iapply H $$ [$Hil $Hm $Hw $HΨ]

/-- THE RELEASE CONTRACT, HANDLE FORM: `c ↦ₐ (locked i c ∗ lk->cpu component)` and the `x`
HANDLE at any anchor `ex ≠ c` po-before the fence; post `w ↦ₐ notheld i`. -/
theorem wpdReleaseH (x : Int) (Cl : List Int) (cv : Agent → List (BitVec 8)) (GT : GdexecT)
    (nm : spinN) (cpu : CPU) (Hcons : rvwmoCatConsistent (gtAdGd GT)) (HlkX : ya ∉ X5 x Cl)
    (i : Agent) (kf : Nat) (m' : SailM Unit) (c ex : Geid) (mv : Option (BitVec 8))
    (Φ : Athread → IProp GF) :
    kf ≠ (AxOpsem.grow (gtAdGd GT) i).length → kf + 1 ≠ (AxOpsem.grow (gtAdGd GT) i).length →
    (AxOpsem.grow (gtAdGd GT) i)[kf]? = some (.LFence true true false true) →
    (AxOpsem.grow (gtAdGd GT) i)[kf + 1]? = some (.LStore false ya [b0] .WCrel) →
    c ≠ ex →
    (∀ e, e = c ∨ e = ex → e.1 = i ∧ e.2 < kf ∧
      ∃ l, (AxOpsem.grow (gtAdGd GT) i)[e.2]? = some l ∧ lbIsMem l = true) →
    ⊢ isLock nm.2 ya (spinR5 x Cl nm (gtAdGd GT)) -∗
      AxAnnot.annotOwn c iprop(locked nm.2 ya i c ∗ RL nm.1 (gtAdGd GT) Cl c) -∗
      hdl (Rbo nm.1 (gtAdGd GT)) x ex mv -∗
      (AxAnnot.annotOwn (i, kf + 1) (notheld nm.2 ya i) -∗
        ∀ rs : RegFile, @tierAWpd GF hlc _ _ (splPol GT) (gtAdGd GT) spinN Unit
          (spinOb5 ya x Cl cv) nm ⟨hp cpu m' rs, kf + 1 + 1⟩ .MaybeStuck i Φ) -∗
      ∀ rs : RegFile, @tierAWpd GF hlc _ _ (splPol GT) (gtAdGd GT) spinN Unit
        (spinOb5 ya x Cl cv) nm ⟨hp cpu (fenceM (relM m')) rs, kf⟩ .MaybeStuck i Φ := by
  intro Hne1 Hne2 Hf Hst Hce Hev
  have hnone : get? ({[ex := Rbo (GF := GF) nm.1 (gtAdGd GT) x ex mv]} : Mea GF) c = none :=
    lookupSingletonNe (Ne.symm Hce)
  have Hdom : ∀ e, e ∈ (FiniteMap.dom_set (insert
      ({[ex := Rbo (GF := GF) nm.1 (gtAdGd GT) x ex mv]} : Mea GF) c
      iprop(locked nm.2 ya i c ∗ RL nm.1 (gtAdGd GT) Cl c)) : GSet Geid) →
      e.1 = i ∧ e.2 < kf ∧
        ∃ l, (AxOpsem.grow (gtAdGd GT) i)[e.2]? = some l ∧ lbIsMem l = true := by
    intro e He
    rw [domInsert, domSingleton] at He
    apply Hev
    rcases elemOfUnion.1 He with h | h
    · exact Or.inl (elemOfSingleton.1 h)
    · exact Or.inr (elemOfSingleton.1 h)
  have HexIn : ex ∈ (FiniteMap.dom_set (insert
      ({[ex := Rbo (GF := GF) nm.1 (gtAdGd GT) x ex mv]} : Mea GF) c
      iprop(locked nm.2 ya i c ∗ RL nm.1 (gtAdGd GT) Cl c)) : GSet Geid) := by
    rw [domInsert, domSingleton]
    exact elemOfUnionR (elemOfSingleton.2 rfl)
  have HcIn : c ∈ (FiniteMap.dom_set (insert
      ({[ex := Rbo (GF := GF) nm.1 (gtAdGd GT) x ex mv]} : Mea GF) c
      iprop(locked nm.2 ya i c ∗ RL nm.1 (gtAdGd GT) Cl c)) : GSet Geid) := by
    rw [domInsert, domSingleton]
    exact elemOfUnionL (elemOfSingleton.2 rfl)
  have Hmk : ⊢ AxAnnot.annotOwn (GF := GF) c
        iprop(locked nm.2 ya i c ∗ RL nm.1 (gtAdGd GT) Cl c) -∗
      AxAnnot.annotOwn ex (Rbo nm.1 (gtAdGd GT) x ex mv) -∗
      [∗map] e ↦ P ∈ (insert ({[ex := Rbo (GF := GF) nm.1 (gtAdGd GT) x ex mv]} : Mea GF) c
        iprop(locked nm.2 ya i c ∗ RL nm.1 (gtAdGd GT) Cl c)), AxAnnot.annotOwn e P := by
    iintro Ha Hb
    iapply (BigSepM.bigSepM_insert hnone).2
    isplitl [Ha]
    · iexact Ha
    · iapply BigSepM.bigSepM_singleton.2
      iexact Hb
  have Hsplit : ⊢ ([∗map] Rin ∈ (insert
      ({[ex := Rbo (GF := GF) nm.1 (gtAdGd GT) x ex mv]} : Mea GF) c
      iprop(locked nm.2 ya i c ∗ RL nm.1 (gtAdGd GT) Cl c)), Rin) -∗
      iprop(locked nm.2 ya i c ∗
        (∃ (a : Geid), ⌜a ∈ (FiniteMap.dom_set (insert
          ({[ex := Rbo (GF := GF) nm.1 (gtAdGd GT) x ex mv]} : Mea GF) c
          iprop(locked nm.2 ya i c ∗ RL nm.1 (gtAdGd GT) Cl c)) : GSet Geid)⌝ ∗
          RL nm.1 (gtAdGd GT) [x] a) ∗
        (∃ (a : Geid), ⌜a ∈ (FiniteMap.dom_set (insert
          ({[ex := Rbo (GF := GF) nm.1 (gtAdGd GT) x ex mv]} : Mea GF) c
          iprop(locked nm.2 ya i c ∗ RL nm.1 (gtAdGd GT) Cl c)) : GSet Geid)⌝ ∗
          RL nm.1 (gtAdGd GT) Cl a)) := by
    iintro H
    icases (BigSepM.bigSepM_insert hnone).1 $$ H with ⟨⟨Hlk, HC⟩, HX⟩
    ihave HX := (BigSepM.bigSepM_singleton (M := GMapF Geid)).1 $$ HX
    isplitl [Hlk]
    · iexact Hlk
    isplitl [HX]
    · iexists ex
      isplitr
      · ipureintro
        exact HexIn
      · iapply (RboRL1 nm.1 (gtAdGd GT) x ex mv) $$ HX
    · iexists c
      isplitr
      · ipureintro
        exact HcIn
      · iexact HC
  unfold hdl
  iintro #Hil Hc Hx HΨ
  ihave Hm := Hmk $$ Hc Hx
  ihave Hw := Hsplit
  iapply (wpdReleaseGen (hlc := hlc) (GF := GF) x Cl cv GT nm cpu Hcons HlkX i kf m' c _ Φ
    Hne1 Hne2 Hf Hst Hdom) $$ Hil Hm Hw HΨ

end contracts

end Weak
