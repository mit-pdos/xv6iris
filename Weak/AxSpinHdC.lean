/-
Weak: **holding's TWO CALL SITES WITHOUT the lock-word leaf premise** — the leaf is built from the
window-restricted load leaf `AxSpinXP2.XxLdW` and window-restricted flow resources
(`AxCertP3.FldMW`).

Rocq: `iris/AxSpinHdC.v` @ xxvzwolszwmp.

## The Rocq header, in substance

`AxSpinHdB.holdingFromAcquire` / `holdingFromRelease` take the lock-word leaf
(`XLd k (pch 0x00) … 4 …`) as a premise, because the position-generic `FldM` for `(lk, 4)` needs
"no RMW of hart `i` on `(lk, 4)` at ANY row position" — false on any row with acquire's
`amoswap.w.aq lk`.  `XxLdW` demands the flow only in the load's window; inside it there is no RMW
item (`holdWin`).
§1 `rdPlain1` (positional `AxSpinHdB.rdPlain`); `FldMWFrame` / `FldMWLkheld` = `FldMFrame` /
   `FldMLkheld` restricted to a window whose positions carry no RMW on the bytes (same proofs).
§2 `holdWin`: the row fact of the load's window from `RowHolding`.
§3 `holdingFromAcquire'` / `holdingFromRelease'` = HdB's corollaries with the leaf premise
   replaced by the load's address translation (`dataAtS … 4 Plk`, `¬ xlText`) and, for release,
   the `FldMLkheld` ingredients (the claim `kc`'s row item, `kc < k`, `nolk`, the claim's
   annotation).

## Stage 2 P-FORM (Lean-only; notes/weak-lb-thm2-stage2.md §B, §C, §D Q-S2-9)

Both call sites on PREFIX rows (`RowHoldingP`, AxSpinHd8), built DIRECTLY on
`AxSpinHdA.wpdHoldingP` (not through AxSpinHdB's full-row call sites; HdB's `XCpuOf`, `FldMRacy`,
`FldMCpuOwn`, `OHeld`, `OOwn`, `ORacy` reused): `holdWinP`/`winNormwP`/`XLkOfWP` are the
prefix twins of `holdWin`/`winNormw`/`XLkOfW`.  Hook: the windowed resource-free `HΨend` over
`[k, if hb then k + 11 else k]` (as `AxSpinE8.wpdMycpuP`).  Designated cuts are handed to the
caller WITH their readback deposits, in the continuations (not dropped as affine):
  * `holdingFromAcquireP`: long arm `KLong ∧ KLongEnd` with `Ocpu = ORacy … (k + 4)` — the
    `lk->cpu` read's `rdFact (clb L) cvx G (i, k + 4)` deposit, the `aq` readback
    (`AxSpinT2g.racyNotMine`); short arm `KShort ∧ KShortEnd` (not a cut for acquire).
  * `holdingFromReleaseP` — GENERALIZED to the branch bit `hb` (Q-S2-9, Rec): long arm
    `KLong ∧ KLongEnd` with `OHeld … k` (lock word, ⌜bytes ≠ 0⌝ — `AxSpinT2g.heldNonzero`) and
    `OOwn … (k + 4)` (⌜bytes read = val's bytes⌝ — `AxSpinT2g.ownIsMine`, the `rlL` readback);
    SHORT arm (`rlS`: `wpdHoldingP`'s short path with the same `OHeld` lock-word leaf)
    `KShort ∧ KShortEnd` whose output is `OHeld … k vlk ∗` the UNUSED last-value handle at `kw`
    (no `lk->cpu` read on that path; handed back, not dropped).  The return pin is split on
    `hb` as in `holdingFromAcquire'` (short arm: `jalrTgt 0 ra = release+0x10`).
`holdingFromAcquire'` / `holdingFromRelease'` keep their exact statements as corollaries (now of
the P-forms; full row ⇒ hook and end continuations vacuous).

## P1 GATE FORM (Lean-only; notes/weak-lb-thm2-pins.md §P1)

`holdingFromAcquireG` / `holdingFromReleaseG` = `holdingFromAcquireP` / `holdingFromReleaseP` on
`AxSpinHdA.wpdHoldingG`: the pin block (`if hb then guarded pins at k + 7 / k + 9 against
acquire + 0x16 / release + 0x10 else jalrTgt 0 ra = …`) becomes `wpdHoldingG`'s
`(hb = true → Gate (k + 7) (pch 0x1a) ∧ Gate (k + 9) (gprVal rs0 r1) ∧ Gate (k + 11) (gprVal rs0
r9)) → jalrTgt 0#12 (gprVal rs0 r1) = gprVal rs0 r1 →` (in the slot of the old pin; all other
premises in the same order), the literal return address becomes `gprVal rs0 r1` in `KShort`, and
the long main continuation is `KLongG` (`KLongEnd`/`KShortEnd` unchanged).  Old forms untouched.

## Deviations from Rocq

1. O2 STAGE C / Q20' (provisional Option V; as `AxSpinXP2` deviation 1 and `AxSpinHdB`
   deviation 1): a fetch consumes no row item, so the lw's window is the single row item `k`
   (the lw's data read) — Rocq `[k, k + 2)` (the 2-byte fetch at `k`, the lw at `k + 1`).
   * `holdWin` / `winNormw` range over `k ≤ k' ∧ k' < k + 1` (Rocq `k ≤ k' < k + 2`); with
     `RowHolding` they drop `pretm`/`pret`/`nret` (AxSpinHd8 deviation 1).
   * `XLkOfW` consumes `FldMW … Out k (k + 1)` and concludes `XLd … (Out k)` (Rocq
     `k (k + 2)`, `Out (S k)`).
   * The call sites follow `AxSpinHdB`'s Lean statements (no `pretm`/`pret`, no
     `Him`/`Hsm`/`Hi`/`Hs`, no section `stv`/`va_first_read`; the graph-value pins instead;
     `ORacy … (k + 4)`, `OOwn … (k + 4)`, `kw < k + 4`, `Hnoint` at `(i, k + 4)`).  Release:
     the claim premises are `kc < k` and `nolk … (i, kc) (i, k)` (Rocq `kc < k + 1`,
     `(i, k + 1)`), the output `OHeld L GT nm i kc k Qc k` (Rocq `… (k+1) Qc (k+1)`).
2. TYPES / INSTANCES (as `AxSpinHdB` deviation 2): `[InvGS_gen hlc GF]` (any `hlc`),
   `[AxSpinX.Xv6G GF]`; the local instances `hC_pol`/`hC_G`/`hC2_pol`/`hC2_G` are inlined as
   `xv6Pol GT` / `AxSpinX2.xG L GT nm`.  `(lo ≤ k' < hi)%nat` ↦ `lo ≤ k' ∧ k' < hi`.
   Section variables are explicit leading arguments (`rdPlain1 GT`, the `FldMW*` rules
   `L GT nm HL Hcons`, §3 as `AxSpinHdB`'s call sites).  `holdWin` is stated with the window
   bound first (`∀ k', k ≤ k' ∧ k' < k + 1 → …`), as Rocq.
3. `XLkOfW` concludes `AxSpinHd7.XLd` from `AxSpinXP2.XxLdW`'s `AxSpinXP.XLdP` (Rocq's verbatim
   primed copy) by definitional unfolding, as Rocq's `iApply`.
4. The trailing `Print Assumptions` lines are not ported (the lint's axiom check covers them).

**Rocq → Lean name map.**  `rd_plain1` `rdPlain1`, `FldMW_frame` `FldMWFrame`, `FldMW_lkheld`
`FldMWLkheld`, `hold_win` `holdWin`, `XLk_ofW` `XLkOfW`, `win_normw` `winNormw`,
`holding_from_acquire'` `holdingFromAcquire'`, `holding_from_release'` `holdingFromRelease'`.
None is in the duplicated-name table.  Stage-2 P-form (Lean-only, unqualified, grepped unique):
`holdWinP`, `XLkOfWP`, `winNormwP`, `holdingFromAcquireP`, `holdingFromReleaseP`; P1 (grepped unique): `holdingFromAcquireG`, `holdingFromReleaseG`.

**Dropped:** `hold_fetch0` (row item `k` is a 2-byte FETCH: under Stage C there is no fetch row
item — row item `k` is the lw's own 4-byte read, so the statement is false; its only use was
`Xx_ldW`'s fetch premise `Hnrk`, dropped in `AxSpinXP2.XxLdW`; no other weak file uses it).
Rocq 9 lemmas (+ 4 local instances, inlined); Lean 8.
-/
import Weak.AxSpinHdB
import Weak.AxSpinXP2

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-! # 1. Window-restricted flow resources -/

section callsW
variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF] [AxannotGS GF]
  [AxSpinX.Xv6G GF]
variable (L : Xlay) (GT : GdexecT) (nm : Xv6N)
variable (HL : xlayOk L) (Hcons : rvwmoCatConsistent (gtAdGd GT))

/-- Rocq `rd_plain1`: the positional `rdPlain` — no RMW of hart `i` on `(pa, n)` at row item
`k` makes the item a plain load. -/
theorem rdPlain1 (i : Agent) (pa : Int) (n k : Nat) :
    (∀ (lb : Lbl) (aq rl : Bool) (m : Nat),
      (AxOpsem.grow (gtAdGd GT) i)[k]? = some lb → aident lb = .IRmw aq rl pa m → m ≠ n) →
    rowRd i (gtAdGd GT) k pa n →
    ∃ aq ts vs, (AxOpsem.grow (gtAdGd GT) i)[k]? = some (Lbl.LLoad aq pa ts vs) ∧
      vs.length = n := by
  rintro Hnormw ⟨lb, aq, Hlb, Hid⟩
  cases lb with
  | LLoad aq' b ts vs =>
    simp only [aident, aidentRd, Option.some.injEq, Prod.mk.injEq] at Hid
    obtain ⟨rfl, rfl, rfl⟩ := Hid
    exact ⟨aq', ts, vs, Hlb, rfl⟩
  | LStore _ _ _ _ => simp [aident, aidentRd] at Hid
  | LFence _ _ _ _ => simp [aident, aidentRd] at Hid
  | LRmw aq' rl b ts rvs wvs cls =>
    simp only [aident, aidentRd, Option.some.injEq, Prod.mk.injEq] at Hid
    obtain ⟨rfl, rfl, Hn⟩ := Hid
    exact absurd Hn (Hnormw _ aq' rl wvs.length Hlb rfl)

include HL Hcons in
/-- Rocq `FldMW_frame`: `FldMFrame` on a window without RMW on the bytes. -/
theorem FldMWFrame (i : Agent) (pa : Int) (n lo hi : Nat) :
    (∀ k' : Nat, lo ≤ k' ∧ k' < hi → ∀ (lb : Lbl) (aq rl : Bool) (m : Nat),
      (AxOpsem.grow (gtAdGd GT) i)[k']? = some lb → aident lb = .IRmw aq rl pa m → m ≠ n) →
    ⊢ @FldMW hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent (dokAtP pa n) i
        (fun _ _ => iprop(True)) lo hi := by
  intro Hnormw
  unfold FldMW
  iintro %GD %ls %k %v %base %n' %Hc #Hg _ %Hgv %Hd %Hw
  ihave %Heq := (HGX L GT nm GD Hc) $$ Hg
  subst Heq
  obtain ⟨⟨rfl, rfl⟩, Hrd⟩ := Hd
  obtain ⟨aq, ts, vs, Hlb, -⟩ := rdPlain1 GT i _ _ k (Hnormw k Hw) Hrd
  ihave Hfe := fxRead L GT nm HL Hcons (i, k) (nwOfLoad GT i k _ _ _ _ Hlb)
  iapply (dflowOPlain L GT nm i k iprop(True) iprop(True)) $$ Hfe
  iintro -
  itrivial

include HL Hcons in
/-- Rocq `FldMW_lkheld`: `FldMLkheld` on a window without RMW on the bytes. -/
theorem FldMWLkheld (i : Agent) (pa : Int) (kc kr : Nat) (rvs wvs : List (BitVec 8))
    (ts : List Nat) (cls : WmClass) (Q : IProp GF) (lo hi : Nat) :
    (∀ k' : Nat, lo ≤ k' ∧ k' < hi → ∀ (lb : Lbl) (aq rl : Bool) (m : Nat),
      (AxOpsem.grow (gtAdGd GT) i)[k']? = some lb → aident lb = .IRmw aq rl pa m → m ≠ 4) →
    (AxOpsem.grow (gtAdGd GT) i)[kc]? = some (Lbl.LRmw true false L.xlLk ts rvs wvs cls) →
    kc < kr →
    nolk L.xlLk (gtAdGd GT).gdG (i, kc) (i, kr) →
    ⊢ AxAnnot.annotOwn (i, kc) iprop(locked nm.xnReg L.xlLk i (i, kc) ∗ Q) -∗
      @FldMW hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent (dokAtP pa 4) i
        (OHeld L GT nm i kc kr Q) lo hi := by
  intro Hnormw Hc Hlt Hnl
  iintro Hh
  unfold FldMW
  iintro %GD %ls %k %v %base %n' %Hcs #Hg _ %Hgv %Hd %Hw
  ihave %Heq := (HGX L GT nm GD Hcs) $$ Hg
  subst Heq
  obtain ⟨⟨rfl, rfl⟩, Hrd⟩ := Hd
  obtain ⟨aq, ts', vs, Hlb, -⟩ := rdPlain1 GT i _ _ k (Hnormw k Hw) Hrd
  have Hnw := nwOfLoad GT i k _ _ _ _ Hlb
  by_cases hk : k = kr
  · subst hk
    rw [OHeld, if_pos rfl]
    have Hlc := lblOfRow _ _ _ _ Hc
    have Hl := lblOfRow _ _ _ _ Hlb
    have Hin : (i, kc) ∈ @Axpol.lobp (xv6Pol GT) (gtAdGd GT) (i, k) :=
      acqLobp (gtAdGd GT) Hcons i kc k _ _ _ _ _ _ Hlc Hl rfl Hlt
    have Hpo := gpoRow (gtAdGd GT) i kc k _ _ Hlc Hl Hlt
    have Hsing : ⊢ ([∗map] Rin ∈ ({[(i, kc) := iprop(locked nm.xnReg L.xlLk i (i, kc) ∗ Q)]} :
        Mea GF), Rin) -∗ iprop(locked nm.xnReg L.xlLk i (i, kc) ∗ Q) := by
      iintro H
      ihave H2 := (BigSepM.bigSepM_singleton (M := GMapF Geid)).1 $$ H
      iexact H2
    have Hfe0 := fxLkreadHeld L GT nm HL Hcons (i, k) i (i, kc) Q
      ({[(i, kc) := iprop(locked nm.xnReg L.xlLk i (i, kc) ∗ Q)]} : Mea GF) Hnw Hpo Hnl
    ihave Hw := Hsing
    ihave Hfe1 := Hfe0
    ihave Hfe := Hfe1 $$ Hw
    iapply (dflowODraw L GT nm HL Hcons i k (i, kc) _
      iprop(locked nm.xnReg L.xlLk i (i, kc) ∗ Q)
      iprop(⌜∀ t b, greadsByte (gtAdGd GT).gdG (i, k) L.xlLk t b → b ≠ b0⌝) _ Hin) $$ Hh Hfe
    iintro H1 H2
    isplitl [H1]
    · iexact H1
    · iexact H2
  · rw [OHeld, if_neg hk]
    ihave Hfe := fxRead L GT nm HL Hcons (i, k) Hnw
    iapply (dflowOPlain L GT nm i k iprop(True) _) $$ Hfe
    iintro -
    iexact Hh

end callsW

/-! # 2. Row facts of the lock-word load's window -/

/-- Rocq `hold_win`: the lw's window carries no RMW item (deviation 1: the window is the single
item `k`, the lw itself). -/
theorem holdWin (k : Nat) (row : List Lbl) (hb : Bool) (plk pcl pra ps0 ps1 pram ps0m : Int) :
    RowHolding k row hb plk pcl pra ps0 ps1 pram ps0m →
    ∀ k' : Nat, k ≤ k' ∧ k' < k + 1 → ∀ (lb : Lbl) (aq rl : Bool) (b : Int) (m : Nat),
      row[k']? = some lb → aident lb = .IRmw aq rl b m → False := by
  intro HR k' Hk' lb aq rl b m Hlb Hid
  rw [show k' = k by omega] at Hlb
  have Hs : ∃ lb0, row[k + 0]? = some lb0 ∧ ∃ aq', aident lb0 = .IRead aq' plk 4 := by
    unfold RowHolding at HR
    cases hb with
    | true =>
      obtain ⟨_, _, Hsh, _⟩ := HR
      exact Hsh 0 (by omega) (by omega)
    | false =>
      obtain ⟨_, _, Hsh⟩ := HR
      exact Hsh 0 (by omega)
  obtain ⟨lb0, Hlb0, aq', Hs⟩ := Hs
  rw [Nat.add_zero, Hlb] at Hlb0
  cases Hlb0
  rw [Hid] at Hs
  cases Hs

/-- (Lean-only, stage 2) `holdWin` on a PREFIX window (`RowHoldingP`): a present item at `k`
is the lw. -/
theorem holdWinP (k : Nat) (row : List Lbl) (hb : Bool) (plk pcl pra ps0 ps1 pram ps0m : Int) :
    RowHoldingP k row hb plk pcl pra ps0 ps1 pram ps0m →
    ∀ k' : Nat, k ≤ k' ∧ k' < k + 1 → ∀ (lb : Lbl) (aq rl : Bool) (b : Int) (m : Nat),
      row[k']? = some lb → aident lb = .IRmw aq rl b m → False := by
  intro HR k' Hk' lb aq rl b m Hlb Hid
  rw [show k' = k by omega] at Hlb
  have Hin : k + 0 < row.length := by
    have := (List.getElem?_eq_some_iff.1 Hlb).1
    omega
  have Hs : ∃ lb0, row[k + 0]? = some lb0 ∧ ∃ aq', aident lb0 = .IRead aq' plk 4 := by
    unfold RowHoldingP at HR
    cases hb with
    | true =>
      obtain ⟨_, Hsh, _⟩ := HR
      exact Hsh 0 (by omega) (by omega) Hin
    | false =>
      obtain ⟨_, Hsh⟩ := HR
      exact Hsh 0 (by omega) Hin
  obtain ⟨lb0, Hlb0, aq', Hs⟩ := Hs
  rw [Nat.add_zero, Hlb] at Hlb0
  cases Hlb0
  rw [Hid] at Hs
  cases Hs

/-! # 3. The two call sites, lock-word leaf discharged -/

section callsC
variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF] [AxannotGS GF]
  [AxSpinX.Xv6G GF]
variable (L : Xlay) (GT : GdexecT) (nm : Xv6N)
variable (HL : xlayOk L) (Hcons : rvwmoCatConsistent (gtAdGd GT))
variable (σi : ExecSt) (T : PTree) (satp0 : BitVec 64)
variable (hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = 8#4)
variable (hasid : zero_extend (m := 16) (satp_to_asid satp0) = 0#16)
variable (hppn : BitVec.setWidth 44 (satp_to_ppn satp0) = T.base)
variable (i : Agent) (cpu : CPU)
variable (Hfix : textFixed (gtAdGd GT) i (imgS σi))
variable (Htxm : mycpuText σi T) (Htxh : holdingText σi T)
variable (Ψ : Athread → IProp GF)
variable (HΨmid : ∀ s, midState s → s.atK = (AxOpsem.grow (gtAdGd GT) i).length →
  ⊢ @postLifting GF (AxSpinX2.xG L GT nm) Ψ i s)

include HL Hcons hmode hasid hppn Hfix Htxh HΨmid in
/-- Rocq `XLk_ofW`: the lock-word leaf from a WINDOW flow resource (deviation 1: window
`[k, k + 1)`, output `Out k`). -/
theorem XLkOfW (k : Nat) (hb : Bool) (plk pcl pra ps0 ps1 pram ps0m : Int) (a0v Plk : BitVec 64)
    (Out : Nat → List (BitVec 8) → IProp GF) :
    RowHolding k (AxOpsem.grow (gtAdGd GT) i) hb plk pcl pra ps0 ps1 pram ps0m →
    dataAtS σi T (.Load .Data) (a0v + sign_extend (m := 64) (0#12)) 4 Plk →
    ¬ L.xlText (paZ Plk) →
    ⊢ @FldMW hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent (dokAtP (paZ Plk) 4)
        i Out k (k + 1) -∗
      XLd (hlc := hlc) L GT nm T satp0 i cpu Ψ k (pch 0x00) 10#5 15#5 0#12 4 a0v (Out k) := by
  intro HR Hda Hnt
  exact XxLdW L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Ψ HΨmid k (pch 0x00) 0#12
    10#5 15#5 4 a0v Plk Out (htok00 σi T satp0 Htxh) (by decide) AxSpinHd7.vw4 (by omega)
    (by omega) Hda Hnt
    (fun lb aq rl m Hlb Hid => (holdWin _ _ _ _ _ _ _ _ _ _ HR k ⟨Nat.le_refl k, by omega⟩
      lb aq rl _ m Hlb Hid).elim)

/-- Rocq `win_normw`: no RMW item in the lw's window (deviation 1: `[k, k + 1)`). -/
theorem winNormw (k : Nat) (hb : Bool) (plk pcl pra ps0 ps1 pram ps0m : Int) (pa : Int)
    (n : Nat) :
    RowHolding k (AxOpsem.grow (gtAdGd GT) i) hb plk pcl pra ps0 ps1 pram ps0m →
    ∀ k' : Nat, k ≤ k' ∧ k' < k + 1 → ∀ (lb : Lbl) (aq rl : Bool) (m : Nat),
      (AxOpsem.grow (gtAdGd GT) i)[k']? = some lb → aident lb = .IRmw aq rl pa m → m ≠ n :=
  fun HR k' Hk' lb aq rl m Hlb Hid =>
    (holdWin _ _ _ _ _ _ _ _ _ _ HR k' Hk' lb aq rl _ m Hlb Hid).elim

include HL Hcons hmode hasid hppn Hfix Htxh HΨmid in
/-- (Lean-only, stage 2) `XLkOfW` on a PREFIX window (`RowHoldingP`). -/
theorem XLkOfWP (k : Nat) (hb : Bool) (plk pcl pra ps0 ps1 pram ps0m : Int) (a0v Plk : BitVec 64)
    (Out : Nat → List (BitVec 8) → IProp GF) :
    RowHoldingP k (AxOpsem.grow (gtAdGd GT) i) hb plk pcl pra ps0 ps1 pram ps0m →
    dataAtS σi T (.Load .Data) (a0v + sign_extend (m := 64) (0#12)) 4 Plk →
    ¬ L.xlText (paZ Plk) →
    ⊢ @FldMW hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent (dokAtP (paZ Plk) 4)
        i Out k (k + 1) -∗
      XLd (hlc := hlc) L GT nm T satp0 i cpu Ψ k (pch 0x00) 10#5 15#5 0#12 4 a0v (Out k) := by
  intro HR Hda Hnt
  exact XxLdW L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Ψ HΨmid k (pch 0x00) 0#12
    10#5 15#5 4 a0v Plk Out (htok00 σi T satp0 Htxh) (by decide) AxSpinHd7.vw4 (by omega)
    (by omega) Hda Hnt
    (fun lb aq rl m Hlb Hid => (holdWinP _ _ _ _ _ _ _ _ _ _ HR k ⟨Nat.le_refl k, by omega⟩
      lb aq rl _ m Hlb Hid).elim)

/-- (Lean-only, stage 2) `winNormw` on a PREFIX window (`RowHoldingP`). -/
theorem winNormwP (k : Nat) (hb : Bool) (plk pcl pra ps0 ps1 pram ps0m : Int) (pa : Int)
    (n : Nat) :
    RowHoldingP k (AxOpsem.grow (gtAdGd GT) i) hb plk pcl pra ps0 ps1 pram ps0m →
    ∀ k' : Nat, k ≤ k' ∧ k' < k + 1 → ∀ (lb : Lbl) (aq rl : Bool) (m : Nat),
      (AxOpsem.grow (gtAdGd GT) i)[k']? = some lb → aident lb = .IRmw aq rl pa m → m ≠ n :=
  fun HR k' Hk' lb aq rl m Hlb Hid =>
    (holdWinP _ _ _ _ _ _ _ _ _ _ HR k' Hk' lb aq rl _ m Hlb Hid).elim

set_option maxHeartbeats 1000000 in
include HL Hcons hmode hasid hppn Hfix Htxm Htxh HΨmid in
/-- (Lean-only, stage 2) THE P-FORM of `holdingFromAcquire'` (acquire's call of holding) on a
PREFIX row: `AxSpinHdA.wpdHoldingP` with the lock-word leaf (`XLkOfWP` + `FldMWFrame`) and the
`lk->cpu` leaf (`XCpuOf` + `FldMRacy`) built here.  Row ends: the windowed resource-free hook
`HΨend` (`[k, if hb then k + 11 else k]`); the designated-cut boundaries are the END
continuations: `KLongEnd` at `k + 12` RECEIVES the `lk->cpu` read's `ORacy` deposit
(`rdFact (clb L) cvx G (i, k + 4)`, the `aq` cut's readback — `AxSpinT2g.racyNotMine`),
`KShortEnd` at `k + 1` (acquire's short arm is not a cut; the caller closes it by its hook). -/
theorem holdingFromAcquireP (k : Nat) (rs0 : RegFile) (ib0 : Ibch) (hb : Bool)
    (plk pcl : Int) (Pra Ps0 Ps1 Pram Ps0m Pcl Plk : BitVec 64) :
    RowHoldingP k (AxOpsem.grow (gtAdGd GT) i) hb plk pcl (paZ Pra) (paZ Ps0) (paZ Ps1)
      (paZ Pram) (paZ Ps0m) →
    rowW8 (AxOpsem.grow (gtAdGd GT) i) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Pra) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Ps0) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Ps1) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Pram) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Ps0m) →
    ctrlOkSW T satp0 rs0 → rs0 .PC = pch 0 → hitW rs0 (pch 0) → hitW rs0 (pcm 0) →
    hitW rs0 (gprVal rs0 AxSpinE8.r10 + sign_extend (m := 64) (0#12)) →
    hitW rs0 (gprVal rs0 AxSpinE8.r10 + sign_extend (m := 64) (16#12)) →
    dataAtS σi T (.Store .Data) (AxSpinHd9.hsp1 rs0 + sign_extend (m := 64) AxSpinHd8.imm24) 8 Pra →
    dataAtS σi T (.Load .Data) (AxSpinHd9.hsp1 rs0 + sign_extend (m := 64) AxSpinHd8.imm24) 8 Pra →
    hitW rs0 (AxSpinHd9.hsp1 rs0 + sign_extend (m := 64) AxSpinHd8.imm24) →
    dataAtS σi T (.Store .Data) (AxSpinHd9.hsp1 rs0 + sign_extend (m := 64) AxSpinHd8.imm16) 8 Ps0 →
    dataAtS σi T (.Load .Data) (AxSpinHd9.hsp1 rs0 + sign_extend (m := 64) AxSpinHd8.imm16) 8 Ps0 →
    hitW rs0 (AxSpinHd9.hsp1 rs0 + sign_extend (m := 64) AxSpinHd8.imm16) →
    dataAtS σi T (.Store .Data) (AxSpinHd9.hsp1 rs0 + sign_extend (m := 64) AxSpinHd8.imm8) 8 Ps1 →
    dataAtS σi T (.Load .Data) (AxSpinHd9.hsp1 rs0 + sign_extend (m := 64) AxSpinHd8.imm8) 8 Ps1 →
    hitW rs0 (AxSpinHd9.hsp1 rs0 + sign_extend (m := 64) AxSpinHd8.imm8) →
    dataAtS σi T (.Store .Data)
      (AxSpinE8.sp1Of (AxSpinHd9.hsp1 rs0) + sign_extend (m := 64) AxSpinE8.immRa) 8 Pram →
    dataAtS σi T (.Load .Data)
      (AxSpinE8.sp1Of (AxSpinHd9.hsp1 rs0) + sign_extend (m := 64) AxSpinE8.immRa) 8 Pram →
    hitW rs0 (AxSpinE8.sp1Of (AxSpinHd9.hsp1 rs0) + sign_extend (m := 64) AxSpinE8.immRa) →
    dataAtS σi T (.Store .Data)
      (AxSpinE8.sp1Of (AxSpinHd9.hsp1 rs0) + sign_extend (m := 64) AxSpinE8.immS0) 8 Ps0m →
    dataAtS σi T (.Load .Data)
      (AxSpinE8.sp1Of (AxSpinHd9.hsp1 rs0) + sign_extend (m := 64) AxSpinE8.immS0) 8 Ps0m →
    hitW rs0 (AxSpinE8.sp1Of (AxSpinHd9.hsp1 rs0) + sign_extend (m := 64) AxSpinE8.immS0) →
    (∀ j : Nat, j < 8 → priv L (paZ Pra + (j : Int)) i) → ¬ L.xlText (paZ Pra) →
    (∀ j : Nat, j < 8 → priv L (paZ Ps0 + (j : Int)) i) → ¬ L.xlText (paZ Ps0) →
    (∀ j : Nat, j < 8 → priv L (paZ Ps1 + (j : Int)) i) → ¬ L.xlText (paZ Ps1) →
    (∀ j : Nat, j < 8 → priv L (paZ Pram + (j : Int)) i) → ¬ L.xlText (paZ Pram) →
    (∀ j : Nat, j < 8 → priv L (paZ Ps0m + (j : Int)) i) → ¬ L.xlText (paZ Ps0m) →
    slotsDisj [paZ Pra, paZ Ps0, paZ Ps1, paZ Pram, paZ Ps0m] →
    -- the return addresses (Q20': graph-value pins; deviation 1)
    (if hb then
        (k + 7 < (AxOpsem.grow (gtAdGd GT) i).length →
          graphValue (gtAdGd GT) (i, k + 7) = some (stBytes 8 (pch 0x1a))) ∧
        (k + 9 < (AxOpsem.grow (gtAdGd GT) i).length →
          graphValue (gtAdGd GT) (i, k + 9) = some (stBytes 8 (AxSpinHdB.pac 0x16)))
      else jalrTgt 0#12 (gprVal rs0 AxSpinE8.r1) = AxSpinHdB.pac 0x16) →
    -- the lk->cpu read
    dataAtS σi T (.Load .Data) (gprVal rs0 AxSpinE8.r10 + sign_extend (m := 64) (16#12)) 8 Pcl →
    ¬ L.xlText (paZ Pcl) →
    (∀ (k' : Nat) (lb : Lbl) (aq rl : Bool) (m : Nat),
      (AxOpsem.grow (gtAdGd GT) i)[k']? = some lb → aident lb = .IRmw aq rl (paZ Pcl) m →
      m ≠ 8) →
    -- the lock-word read: only its address translation
    dataAtS σi T (.Load .Data) (gprVal rs0 AxSpinE8.r10 + sign_extend (m := 64) (0#12)) 4 Plk →
    ¬ L.xlText (paZ Plk) →
    -- the row-end hook (stage 2, design §B / Q-S2-2)
    (∀ k' : Nat, k ≤ k' → k' ≤ (if hb then k + 11 else k) →
      (AxOpsem.grow (gtAdGd GT) i).length ≤ k' → ∀ pr : Pexv6,
        ⊢ @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
          ⟨pr, k'⟩ Ψ) →
    ⊢ (if hb then
          KLong (hlc := hlc) L GT nm T satp0 i cpu Ψ k rs0 (AxSpinHdB.pac 0x16) Pra Ps0 Ps1 Pram
            Ps0m (fun _ => iprop(True)) (ORacy L GT i (k + 4)) ∧
          KLongEnd (hlc := hlc) L GT nm i Ψ k rs0 Pra Ps0 Ps1 Pram Ps0m (fun _ => iprop(True))
            (ORacy L GT i (k + 4))
        else KShort (hlc := hlc) L GT nm T satp0 i cpu Ψ k rs0 (AxSpinHdB.pac 0x16)
            (fun _ => iprop(True)) ∧
          KShortEnd (hlc := hlc) L GT nm i Ψ k (fun _ => iprop(True))) -∗
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
        ⟨.PHart cpu (.pure ()) rs0 none ib0, k⟩ Ψ := by
  intro HR Hw8 H1 H2 H3 H4 H5 Hc0 HPC0 Hh0 Hhm Hhlk Hhlc
    Hd1 Hd2 Hd3 Hd4 Hd5 Hd6 Hd7 Hd8 Hd9 Hd10 Hd11 Hd12 Hd13 Hd14 Hd15
    Hp1 Hn1 Hp2 Hn2 Hp3 Hn3 Hp4 Hn4 Hp5 Hn5 Hdisj Hpin Hdcl Hntcl Hnrcl Hdlk Hntlk HΨend
  have Hlk : ⊢ @FldMW hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent
        (dokAtP (paZ Plk) 4) i (fun _ _ => iprop(True)) k (k + 1) -∗
      XLd (hlc := hlc) L GT nm T satp0 i cpu Ψ k (pch 0x00) 10#5 15#5 0#12 4
        (gprVal rs0 AxSpinE8.r10) (fun _ => iprop(True)) :=
    XLkOfWP L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Htxh Ψ HΨmid k hb plk pcl
      (paZ Pra) (paZ Ps0) (paZ Ps1) (paZ Pram) (paZ Ps0m) (gprVal rs0 AxSpinE8.r10) Plk
      (fun _ _ => iprop(True)) HR Hdlk Hntlk
  have Hfr := FldMWFrame (hlc := hlc) (GF := GF) L GT nm HL Hcons i (paZ Plk) 4 k (k + 1)
    (winNormwP GT i k hb plk pcl _ _ _ _ _ (paZ Plk) 4 HR)
  cases hb
  · simp only [Bool.false_eq_true, ↓reduceIte] at Hpin ⊢
    have W := wpdHoldingP L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Htxm Htxh Ψ
      HΨmid k rs0 ib0 false (AxSpinHdB.pac 0x16) plk pcl Pra Ps0 Ps1 Pram Ps0m
      (fun _ => iprop(True)) (ORacy L GT i (k + 4)) HR Hw8 H1 H2 H3 H4 H5 Hc0 HPC0 Hh0 Hhm
      Hhlk Hhlc Hd1 Hd2 Hd3 Hd4 Hd5 Hd6 Hd7 Hd8 Hd9 Hd10 Hd11 Hd12 Hd13 Hd14 Hd15
      Hp1 Hn1 Hp2 Hn2 Hp3 Hn3 Hp4 Hn4 Hp5 Hn5 Hdisj
      (by simp only [Bool.false_eq_true, ↓reduceIte]; exact Hpin) HΨend
    simp only [Bool.false_eq_true, ↓reduceIte] at W
    iintro C
    ihave F := Hfr
    ihave X0 := Hlk
    ihave X := X0 $$ F
    ihave W0 := W
    iapply W0 $$ X C
  · simp only [↓reduceIte] at Hpin ⊢
    obtain ⟨Hvm, Hv⟩ := Hpin
    have W := wpdHoldingP L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Htxm Htxh Ψ
      HΨmid k rs0 ib0 true (AxSpinHdB.pac 0x16) plk pcl Pra Ps0 Ps1 Pram Ps0m
      (fun _ => iprop(True)) (ORacy L GT i (k + 4)) HR Hw8 H1 H2 H3 H4 H5 Hc0 HPC0 Hh0 Hhm
      Hhlk Hhlc Hd1 Hd2 Hd3 Hd4 Hd5 Hd6 Hd7 Hd8 Hd9 Hd10 Hd11 Hd12 Hd13 Hd14 Hd15
      Hp1 Hn1 Hp2 Hn2 Hp3 Hn3 Hp4 Hn4 Hp5 Hn5 Hdisj
      (by simp only [↓reduceIte]; exact ⟨Hvm, Hv, by decide +kernel⟩) HΨend
    simp only [↓reduceIte] at W
    have Hcpu := XCpuOf L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Htxh Ψ HΨmid k
      (gprVal rs0 AxSpinE8.r10) Pcl (ORacy L GT i) Hdcl Hntcl Hnrcl
    have Hfc := FldMRacy (hlc := hlc) (GF := GF) L GT nm HL Hcons i (paZ Pcl) 8 Hnrcl
    iintro C
    ihave F := Hfr
    ihave X0 := Hlk
    ihave X := X0 $$ F
    ihave Hf := Hfc
    ihave Hc0 := Hcpu
    ihave Hc := Hc0 $$ Hf
    ihave W0 := W
    iapply W0 $$ X [Hc C]
    isplitl [Hc]
    · iexact Hc
    · iexact C

set_option maxHeartbeats 1000000 in
include HL Hcons hmode hasid hppn Hfix Htxm Htxh HΨmid in
/-- Rocq `holding_from_acquire'`: `holdingFromAcquire` with the lock-word leaf built here
(`XLkOfW` + `FldMWFrame`); only the load's address translation remains (deviation 1).  Stage 2:
the full-row corollary of `holdingFromAcquireP` (hook and end continuations vacuous). -/
theorem holdingFromAcquire' (k : Nat) (rs0 : RegFile) (ib0 : Ibch) (hb : Bool)
    (plk pcl : Int) (Pra Ps0 Ps1 Pram Ps0m Pcl Plk : BitVec 64) :
    RowHolding k (AxOpsem.grow (gtAdGd GT) i) hb plk pcl (paZ Pra) (paZ Ps0) (paZ Ps1)
      (paZ Pram) (paZ Ps0m) →
    rowW8 (AxOpsem.grow (gtAdGd GT) i) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Pra) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Ps0) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Ps1) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Pram) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Ps0m) →
    ctrlOkSW T satp0 rs0 → rs0 .PC = pch 0 → hitW rs0 (pch 0) → hitW rs0 (pcm 0) →
    hitW rs0 (gprVal rs0 AxSpinE8.r10 + sign_extend (m := 64) (0#12)) →
    hitW rs0 (gprVal rs0 AxSpinE8.r10 + sign_extend (m := 64) (16#12)) →
    dataAtS σi T (.Store .Data) (AxSpinHd9.hsp1 rs0 + sign_extend (m := 64) AxSpinHd8.imm24) 8 Pra →
    dataAtS σi T (.Load .Data) (AxSpinHd9.hsp1 rs0 + sign_extend (m := 64) AxSpinHd8.imm24) 8 Pra →
    hitW rs0 (AxSpinHd9.hsp1 rs0 + sign_extend (m := 64) AxSpinHd8.imm24) →
    dataAtS σi T (.Store .Data) (AxSpinHd9.hsp1 rs0 + sign_extend (m := 64) AxSpinHd8.imm16) 8 Ps0 →
    dataAtS σi T (.Load .Data) (AxSpinHd9.hsp1 rs0 + sign_extend (m := 64) AxSpinHd8.imm16) 8 Ps0 →
    hitW rs0 (AxSpinHd9.hsp1 rs0 + sign_extend (m := 64) AxSpinHd8.imm16) →
    dataAtS σi T (.Store .Data) (AxSpinHd9.hsp1 rs0 + sign_extend (m := 64) AxSpinHd8.imm8) 8 Ps1 →
    dataAtS σi T (.Load .Data) (AxSpinHd9.hsp1 rs0 + sign_extend (m := 64) AxSpinHd8.imm8) 8 Ps1 →
    hitW rs0 (AxSpinHd9.hsp1 rs0 + sign_extend (m := 64) AxSpinHd8.imm8) →
    dataAtS σi T (.Store .Data)
      (AxSpinE8.sp1Of (AxSpinHd9.hsp1 rs0) + sign_extend (m := 64) AxSpinE8.immRa) 8 Pram →
    dataAtS σi T (.Load .Data)
      (AxSpinE8.sp1Of (AxSpinHd9.hsp1 rs0) + sign_extend (m := 64) AxSpinE8.immRa) 8 Pram →
    hitW rs0 (AxSpinE8.sp1Of (AxSpinHd9.hsp1 rs0) + sign_extend (m := 64) AxSpinE8.immRa) →
    dataAtS σi T (.Store .Data)
      (AxSpinE8.sp1Of (AxSpinHd9.hsp1 rs0) + sign_extend (m := 64) AxSpinE8.immS0) 8 Ps0m →
    dataAtS σi T (.Load .Data)
      (AxSpinE8.sp1Of (AxSpinHd9.hsp1 rs0) + sign_extend (m := 64) AxSpinE8.immS0) 8 Ps0m →
    hitW rs0 (AxSpinE8.sp1Of (AxSpinHd9.hsp1 rs0) + sign_extend (m := 64) AxSpinE8.immS0) →
    (∀ j : Nat, j < 8 → priv L (paZ Pra + (j : Int)) i) → ¬ L.xlText (paZ Pra) →
    (∀ j : Nat, j < 8 → priv L (paZ Ps0 + (j : Int)) i) → ¬ L.xlText (paZ Ps0) →
    (∀ j : Nat, j < 8 → priv L (paZ Ps1 + (j : Int)) i) → ¬ L.xlText (paZ Ps1) →
    (∀ j : Nat, j < 8 → priv L (paZ Pram + (j : Int)) i) → ¬ L.xlText (paZ Pram) →
    (∀ j : Nat, j < 8 → priv L (paZ Ps0m + (j : Int)) i) → ¬ L.xlText (paZ Ps0m) →
    slotsDisj [paZ Pra, paZ Ps0, paZ Ps1, paZ Pram, paZ Ps0m] →
    -- the return addresses (Q20': graph-value pins; deviation 1)
    (if hb then
        graphValue (gtAdGd GT) (i, k + 7) = some (stBytes 8 (pch 0x1a)) ∧
        graphValue (gtAdGd GT) (i, k + 9) = some (stBytes 8 (AxSpinHdB.pac 0x16))
      else jalrTgt 0#12 (gprVal rs0 AxSpinE8.r1) = AxSpinHdB.pac 0x16) →
    -- the lk->cpu read
    dataAtS σi T (.Load .Data) (gprVal rs0 AxSpinE8.r10 + sign_extend (m := 64) (16#12)) 8 Pcl →
    ¬ L.xlText (paZ Pcl) →
    (∀ (k' : Nat) (lb : Lbl) (aq rl : Bool) (m : Nat),
      (AxOpsem.grow (gtAdGd GT) i)[k']? = some lb → aident lb = .IRmw aq rl (paZ Pcl) m →
      m ≠ 8) →
    -- the lock-word read: only its address translation
    dataAtS σi T (.Load .Data) (gprVal rs0 AxSpinE8.r10 + sign_extend (m := 64) (0#12)) 4 Plk →
    ¬ L.xlText (paZ Plk) →
    ⊢ (if hb then
          KLong (hlc := hlc) L GT nm T satp0 i cpu Ψ k rs0 (AxSpinHdB.pac 0x16) Pra Ps0 Ps1 Pram
            Ps0m (fun _ => iprop(True)) (ORacy L GT i (k + 4))
        else KShort (hlc := hlc) L GT nm T satp0 i cpu Ψ k rs0 (AxSpinHdB.pac 0x16)
          (fun _ => iprop(True))) -∗
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
        ⟨.PHart cpu (.pure ()) rs0 none ib0, k⟩ Ψ := by
  intro HR Hw8 H1 H2 H3 H4 H5 Hc0 HPC0 Hh0 Hhm Hhlk Hhlc
    Hd1 Hd2 Hd3 Hd4 Hd5 Hd6 Hd7 Hd8 Hd9 Hd10 Hd11 Hd12 Hd13 Hd14 Hd15
    Hp1 Hn1 Hp2 Hn2 Hp3 Hn3 Hp4 Hn4 Hp5 Hn5 Hdisj Hpin Hdcl Hntcl Hnrcl Hdlk Hntlk
  have HRP := AxSpinHd8.rowHoldingPOfFull _ _ _ _ _ _ _ _ _ _ HR
  obtain ⟨_, HRp⟩ := HR
  cases hb
  · have Hlen : k + 1 < (AxOpsem.grow (gtAdGd GT) i).length := HRp.1
    have W := holdingFromAcquireP L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Htxm
      Htxh Ψ HΨmid k rs0 ib0 false plk pcl Pra Ps0 Ps1 Pram Ps0m Pcl Plk HRP Hw8 H1 H2 H3 H4 H5
      Hc0 HPC0 Hh0 Hhm Hhlk Hhlc Hd1 Hd2 Hd3 Hd4 Hd5 Hd6 Hd7 Hd8 Hd9 Hd10 Hd11 Hd12 Hd13 Hd14
      Hd15 Hp1 Hn1 Hp2 Hn2 Hp3 Hn3 Hp4 Hn4 Hp5 Hn5 Hdisj
      (by simp only [Bool.false_eq_true, ↓reduceIte] at Hpin ⊢; exact Hpin) Hdcl Hntcl Hnrcl
      Hdlk Hntlk
      (fun _ _ h2 h3 => absurd h3 (by simp only [Bool.false_eq_true, ↓reduceIte] at h2; omega))
    simp only [Bool.false_eq_true, ↓reduceIte] at W ⊢
    iintro C
    iapply W
    isplit
    · iexact C
    · unfold KShortEnd
      iintro %vlk %pr %Hp
      exact absurd Hp.1 (by omega)
  · have Hlen : k + 12 < (AxOpsem.grow (gtAdGd GT) i).length := HRp.1
    simp only [↓reduceIte] at Hpin
    obtain ⟨Hvm, Hv⟩ := Hpin
    have W := holdingFromAcquireP L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Htxm
      Htxh Ψ HΨmid k rs0 ib0 true plk pcl Pra Ps0 Ps1 Pram Ps0m Pcl Plk HRP Hw8 H1 H2 H3 H4 H5
      Hc0 HPC0 Hh0 Hhm Hhlk Hhlc Hd1 Hd2 Hd3 Hd4 Hd5 Hd6 Hd7 Hd8 Hd9 Hd10 Hd11 Hd12 Hd13 Hd14
      Hd15 Hp1 Hn1 Hp2 Hn2 Hp3 Hn3 Hp4 Hn4 Hp5 Hn5 Hdisj
      (by simp only [↓reduceIte]; exact ⟨fun _ => Hvm, fun _ => Hv⟩) Hdcl Hntcl Hnrcl
      Hdlk Hntlk (fun _ _ h2 h3 => absurd h3 (by simp only [↓reduceIte] at h2; omega))
    simp only [↓reduceIte] at W ⊢
    iintro C
    iapply W
    isplit
    · iexact C
    · unfold KLongEnd
      iintro %vlk %vcpu %vram %vs0m %vra %vs0 %vs1 %pr %Hp
      exact absurd Hp.1 (by omega)

set_option maxHeartbeats 1000000 in
include HL Hcons hmode hasid hppn Hfix Htxm Htxh HΨmid in
/-- (Lean-only, stage 2; design Q-S2-9) THE P-FORM of `holdingFromRelease'` (release's call of
holding) on a PREFIX row, GENERALIZED to the branch bit `hb`: `AxSpinHdA.wpdHoldingP` with the
holder's lock-word leaf (`XLkOfWP` + `FldMWLkheld`, output `OHeld`) and, on the long arm, the
OWNED `lk->cpu` leaf (`XCpuOf` + `FldMCpuOwn`, output `OOwn`) built here.  SHORT arm (`hb =
false`, the lw read 0 — `rlS`): `KShort`/`KShortEnd` with output `OHeld … k vlk` (at the read
`k`: `locked ∗ Qc` plus ⌜every byte read ≠ 0⌝) TOGETHER WITH the unused last-value handle at
`kw` (no `lk->cpu` read happened).  LONG arm: `KLong`/`KLongEnd` with `OHeld` and `OOwn … (k + 4)`
(⌜bytes read = val's bytes⌝ — the `rlL` readback, `AxSpinT2g.ownIsMine`).  Row ends: the
windowed resource-free hook `HΨend` (`[k, if hb then k + 11 else k]`), the designated-cut
boundaries `k + 1` / `k + 12` the END continuations (deposits handed over, not dropped). -/
theorem holdingFromReleaseP (k : Nat) (rs0 : RegFile) (ib0 : Ibch) (hb : Bool)
    (plk : Int) (Pra Ps0 Ps1 Pram Ps0m Pcl Plk : BitVec 64)
    (kc kw : Nat) (val : BitVec 64) (cls : WmClass) (Qc Qw : IProp GF)
    (tsc : List Nat) (rvsc wvsc : List (BitVec 8)) (clsc : WmClass) :
    RowHoldingP k (AxOpsem.grow (gtAdGd GT) i) hb plk (paZ Pcl) (paZ Pra) (paZ Ps0) (paZ Ps1)
      (paZ Pram) (paZ Ps0m) →
    rowW8 (AxOpsem.grow (gtAdGd GT) i) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Pra) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Ps0) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Ps1) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Pram) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Ps0m) →
    ctrlOkSW T satp0 rs0 → rs0 .PC = pch 0 → hitW rs0 (pch 0) → hitW rs0 (pcm 0) →
    hitW rs0 (gprVal rs0 AxSpinE8.r10 + sign_extend (m := 64) (0#12)) →
    hitW rs0 (gprVal rs0 AxSpinE8.r10 + sign_extend (m := 64) (16#12)) →
    dataAtS σi T (.Store .Data) (AxSpinHd9.hsp1 rs0 + sign_extend (m := 64) AxSpinHd8.imm24) 8 Pra →
    dataAtS σi T (.Load .Data) (AxSpinHd9.hsp1 rs0 + sign_extend (m := 64) AxSpinHd8.imm24) 8 Pra →
    hitW rs0 (AxSpinHd9.hsp1 rs0 + sign_extend (m := 64) AxSpinHd8.imm24) →
    dataAtS σi T (.Store .Data) (AxSpinHd9.hsp1 rs0 + sign_extend (m := 64) AxSpinHd8.imm16) 8 Ps0 →
    dataAtS σi T (.Load .Data) (AxSpinHd9.hsp1 rs0 + sign_extend (m := 64) AxSpinHd8.imm16) 8 Ps0 →
    hitW rs0 (AxSpinHd9.hsp1 rs0 + sign_extend (m := 64) AxSpinHd8.imm16) →
    dataAtS σi T (.Store .Data) (AxSpinHd9.hsp1 rs0 + sign_extend (m := 64) AxSpinHd8.imm8) 8 Ps1 →
    dataAtS σi T (.Load .Data) (AxSpinHd9.hsp1 rs0 + sign_extend (m := 64) AxSpinHd8.imm8) 8 Ps1 →
    hitW rs0 (AxSpinHd9.hsp1 rs0 + sign_extend (m := 64) AxSpinHd8.imm8) →
    dataAtS σi T (.Store .Data)
      (AxSpinE8.sp1Of (AxSpinHd9.hsp1 rs0) + sign_extend (m := 64) AxSpinE8.immRa) 8 Pram →
    dataAtS σi T (.Load .Data)
      (AxSpinE8.sp1Of (AxSpinHd9.hsp1 rs0) + sign_extend (m := 64) AxSpinE8.immRa) 8 Pram →
    hitW rs0 (AxSpinE8.sp1Of (AxSpinHd9.hsp1 rs0) + sign_extend (m := 64) AxSpinE8.immRa) →
    dataAtS σi T (.Store .Data)
      (AxSpinE8.sp1Of (AxSpinHd9.hsp1 rs0) + sign_extend (m := 64) AxSpinE8.immS0) 8 Ps0m →
    dataAtS σi T (.Load .Data)
      (AxSpinE8.sp1Of (AxSpinHd9.hsp1 rs0) + sign_extend (m := 64) AxSpinE8.immS0) 8 Ps0m →
    hitW rs0 (AxSpinE8.sp1Of (AxSpinHd9.hsp1 rs0) + sign_extend (m := 64) AxSpinE8.immS0) →
    (∀ j : Nat, j < 8 → priv L (paZ Pra + (j : Int)) i) → ¬ L.xlText (paZ Pra) →
    (∀ j : Nat, j < 8 → priv L (paZ Ps0 + (j : Int)) i) → ¬ L.xlText (paZ Ps0) →
    (∀ j : Nat, j < 8 → priv L (paZ Ps1 + (j : Int)) i) → ¬ L.xlText (paZ Ps1) →
    (∀ j : Nat, j < 8 → priv L (paZ Pram + (j : Int)) i) → ¬ L.xlText (paZ Pram) →
    (∀ j : Nat, j < 8 → priv L (paZ Ps0m + (j : Int)) i) → ¬ L.xlText (paZ Ps0m) →
    slotsDisj [paZ Pra, paZ Ps0, paZ Ps1, paZ Pram, paZ Ps0m] →
    -- the return addresses (Q20': graph-value pins; deviation 1)
    (if hb then
        (k + 7 < (AxOpsem.grow (gtAdGd GT) i).length →
          graphValue (gtAdGd GT) (i, k + 7) = some (stBytes 8 (pch 0x1a))) ∧
        (k + 9 < (AxOpsem.grow (gtAdGd GT) i).length →
          graphValue (gtAdGd GT) (i, k + 9) = some (stBytes 8 (AxSpinHdB.prl 0x10)))
      else jalrTgt 0#12 (gprVal rs0 AxSpinE8.r1) = AxSpinHdB.prl 0x10) →
    -- the owned lk->cpu read
    dataAtS σi T (.Load .Data) (gprVal rs0 AxSpinE8.r10 + sign_extend (m := 64) (16#12)) 8 Pcl →
    paZ Pcl = L.xlLk + 16 → ¬ L.xlText (paZ Pcl) →
    (∀ (k' : Nat) (lb : Lbl) (aq rl : Bool) (m : Nat),
      (AxOpsem.grow (gtAdGd GT) i)[k']? = some lb → aident lb = .IRmw aq rl (paZ Pcl) m →
      m ≠ 8) →
    (AxOpsem.grow (gtAdGd GT) i)[kw]? =
      some (Lbl.LStore false (L.xlLk + 16) (WeakInterpProj.wbytes 8 val) cls) →
    kw < k + 4 →
    (∀ w a v', a ∈ clb L → gwritesByte (gtAdGd GT).gdG w a v' →
      WeakRvwmoGraph.gpo (gtAdGd GT).gdG (i, kw) w →
      WeakRvwmoGraph.gpo (gtAdGd GT).gdG w (i, k + 4) → False) →
    -- the holder's lock-word read: address translation + the claim at `kc`
    dataAtS σi T (.Load .Data) (gprVal rs0 AxSpinE8.r10 + sign_extend (m := 64) (0#12)) 4 Plk →
    ¬ L.xlText (paZ Plk) →
    (AxOpsem.grow (gtAdGd GT) i)[kc]? = some (Lbl.LRmw true false L.xlLk tsc rvsc wvsc clsc) →
    kc < k →
    nolk L.xlLk (gtAdGd GT).gdG (i, kc) (i, k) →
    -- the row-end hook (stage 2, design §B / Q-S2-2)
    (∀ k' : Nat, k ≤ k' → k' ≤ (if hb then k + 11 else k) →
      (AxOpsem.grow (gtAdGd GT) i).length ≤ k' → ∀ pr : Pexv6,
        ⊢ @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
          ⟨pr, k'⟩ Ψ) →
    ⊢ AxAnnot.annotOwn (i, kc) iprop(locked nm.xnReg L.xlLk i (i, kc) ∗ Qc) -∗
      AxAnnot.annotOwn (i, kw)
        iprop(Qw ∗ RVL nm.xnH (gtAdGd GT) (clb L) (i, kw) (WeakInterpProj.wbytes 8 val)) -∗
      (if hb then
          KLong (hlc := hlc) L GT nm T satp0 i cpu Ψ k rs0 (AxSpinHdB.prl 0x10) Pra Ps0 Ps1 Pram
            Ps0m (OHeld L GT nm i kc k Qc k) (OOwn L GT nm i kw (k + 4) val Qw (k + 4)) ∧
          KLongEnd (hlc := hlc) L GT nm i Ψ k rs0 Pra Ps0 Ps1 Pram Ps0m
            (OHeld L GT nm i kc k Qc k) (OOwn L GT nm i kw (k + 4) val Qw (k + 4))
        else
          KShort (hlc := hlc) L GT nm T satp0 i cpu Ψ k rs0 (AxSpinHdB.prl 0x10)
            (fun v => iprop(OHeld L GT nm i kc k Qc k v ∗ AxAnnot.annotOwn (i, kw)
              iprop(Qw ∗ RVL nm.xnH (gtAdGd GT) (clb L) (i, kw) (WeakInterpProj.wbytes 8 val)))) ∧
          KShortEnd (hlc := hlc) L GT nm i Ψ k
            (fun v => iprop(OHeld L GT nm i kc k Qc k v ∗ AxAnnot.annotOwn (i, kw)
              iprop(Qw ∗ RVL nm.xnH (gtAdGd GT) (clb L) (i, kw) (WeakInterpProj.wbytes 8 val))))) -∗
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
        ⟨.PHart cpu (.pure ()) rs0 none ib0, k⟩ Ψ := by
  intro HR Hw8 H1 H2 H3 H4 H5 Hc0 HPC0 Hh0 Hhm Hhlk Hhlc
    Hd1 Hd2 Hd3 Hd4 Hd5 Hd6 Hd7 Hd8 Hd9 Hd10 Hd11 Hd12 Hd13 Hd14 Hd15
    Hp1 Hn1 Hp2 Hn2 Hp3 Hn3 Hp4 Hn4 Hp5 Hn5 Hdisj Hpin Hdcl Hpcl Hntcl Hnrcl Hw Hkw Hnoint
    Hdlk Hntlk Hkc Hkck Hnl HΨend
  have Hlk := XLkOfWP L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Htxh Ψ HΨmid k hb
    plk (paZ Pcl) (paZ Pra) (paZ Ps0) (paZ Ps1) (paZ Pram) (paZ Ps0m) (gprVal rs0 AxSpinE8.r10)
    Plk (OHeld L GT nm i kc k Qc) HR Hdlk Hntlk
  have Hfl := FldMWLkheld (hlc := hlc) (GF := GF) L GT nm HL Hcons i (paZ Plk) kc k rvsc wvsc
    tsc clsc Qc k (k + 1) (winNormwP GT i k hb plk (paZ Pcl) _ _ _ _ _ (paZ Plk) 4 HR)
    Hkc Hkck Hnl
  cases hb
  · -- SHORT arm (rlS): the lw's `OHeld` output and the unused handle go to the continuation
    simp only [Bool.false_eq_true, ↓reduceIte] at Hpin ⊢
    have W := wpdHoldingP L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Htxm Htxh Ψ
      HΨmid k rs0 ib0 false (AxSpinHdB.prl 0x10) plk (paZ Pcl) Pra Ps0 Ps1 Pram Ps0m
      (OHeld L GT nm i kc k Qc k) (OOwn L GT nm i kw (k + 4) val Qw (k + 4)) HR Hw8 H1 H2 H3 H4
      H5 Hc0 HPC0 Hh0 Hhm Hhlk Hhlc Hd1 Hd2 Hd3 Hd4 Hd5 Hd6 Hd7 Hd8 Hd9 Hd10 Hd11 Hd12 Hd13 Hd14
      Hd15 Hp1 Hn1 Hp2 Hn2 Hp3 Hn3 Hp4 Hn4 Hp5 Hn5 Hdisj
      (by simp only [Bool.false_eq_true, ↓reduceIte]; exact Hpin) HΨend
    simp only [Bool.false_eq_true, ↓reduceIte] at W
    unfold KShort KShortEnd at W ⊢
    iintro Hc Hh C
    ihave F0 := Hfl
    ihave F := F0 $$ Hc
    ihave X0 := Hlk
    ihave X := X0 $$ F
    ihave W0 := W
    iapply W0 $$ X
    isplit
    · iintro %vlk %rs' %ib' %Hp Ho
      icases C with ⟨C, -⟩
      iapply C $$ %vlk %rs' %ib' %Hp
      isplitl [Ho]
      · iexact Ho
      · iexact Hh
    · iintro %vlk %pr %Hp Ho
      icases C with ⟨-, C⟩
      iapply C $$ %vlk %pr %Hp
      isplitl [Ho]
      · iexact Ho
      · iexact Hh
  · -- LONG arm (rlL): `OHeld` and the owned read's `OOwn`
    simp only [↓reduceIte] at Hpin ⊢
    obtain ⟨Hvm, Hv⟩ := Hpin
    have W := wpdHoldingP L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Htxm Htxh Ψ
      HΨmid k rs0 ib0 true (AxSpinHdB.prl 0x10) plk (paZ Pcl) Pra Ps0 Ps1 Pram Ps0m
      (OHeld L GT nm i kc k Qc k) (OOwn L GT nm i kw (k + 4) val Qw (k + 4)) HR Hw8 H1 H2 H3 H4
      H5 Hc0 HPC0 Hh0 Hhm Hhlk Hhlc Hd1 Hd2 Hd3 Hd4 Hd5 Hd6 Hd7 Hd8 Hd9 Hd10 Hd11 Hd12 Hd13 Hd14
      Hd15 Hp1 Hn1 Hp2 Hn2 Hp3 Hn3 Hp4 Hn4 Hp5 Hn5 Hdisj
      (by simp only [↓reduceIte]; exact ⟨Hvm, Hv, by decide +kernel⟩) HΨend
    simp only [↓reduceIte] at W
    have Hcpu := XCpuOf L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Htxh Ψ HΨmid k
      (gprVal rs0 AxSpinE8.r10) Pcl (OOwn L GT nm i kw (k + 4) val Qw) Hdcl Hntcl Hnrcl
    have Hfo := FldMCpuOwn (hlc := hlc) (GF := GF) L GT nm HL Hcons i kw (k + 4) val cls Qw
      (by rw [← Hpcl]; exact Hnrcl) Hw Hkw Hnoint
    rw [← Hpcl] at Hfo
    iintro Hc Hh C
    ihave F0 := Hfl
    ihave F := F0 $$ Hc
    ihave X0 := Hlk
    ihave X := X0 $$ F
    ihave Hfo0 := Hfo
    ihave Hf := Hfo0 $$ Hh
    ihave Hcc0 := Hcpu
    ihave Hcc := Hcc0 $$ Hf
    ihave W0 := W
    iapply W0 $$ X [Hcc C]
    isplitl [Hcc]
    · iexact Hcc
    · iexact C

set_option maxHeartbeats 1000000 in
include HL Hcons hmode hasid hppn Hfix Htxm Htxh HΨmid in
/-- Rocq `holding_from_release'`: `holdingFromRelease` with the holder's lock-word leaf built
here (`XLkOfW` + `FldMWLkheld`, the claim at `kc`; deviation 1).  Stage 2: the full-row,
`hb = true` corollary of `holdingFromReleaseP` (hook and end continuation vacuous). -/
theorem holdingFromRelease' (k : Nat) (rs0 : RegFile) (ib0 : Ibch)
    (plk : Int) (Pra Ps0 Ps1 Pram Ps0m Pcl Plk : BitVec 64)
    (kc kw : Nat) (val : BitVec 64) (cls : WmClass) (Qc Qw : IProp GF)
    (tsc : List Nat) (rvsc wvsc : List (BitVec 8)) (clsc : WmClass) :
    RowHolding k (AxOpsem.grow (gtAdGd GT) i) true plk (paZ Pcl) (paZ Pra) (paZ Ps0) (paZ Ps1)
      (paZ Pram) (paZ Ps0m) →
    rowW8 (AxOpsem.grow (gtAdGd GT) i) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Pra) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Ps0) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Ps1) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Pram) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Ps0m) →
    ctrlOkSW T satp0 rs0 → rs0 .PC = pch 0 → hitW rs0 (pch 0) → hitW rs0 (pcm 0) →
    hitW rs0 (gprVal rs0 AxSpinE8.r10 + sign_extend (m := 64) (0#12)) →
    hitW rs0 (gprVal rs0 AxSpinE8.r10 + sign_extend (m := 64) (16#12)) →
    dataAtS σi T (.Store .Data) (AxSpinHd9.hsp1 rs0 + sign_extend (m := 64) AxSpinHd8.imm24) 8 Pra →
    dataAtS σi T (.Load .Data) (AxSpinHd9.hsp1 rs0 + sign_extend (m := 64) AxSpinHd8.imm24) 8 Pra →
    hitW rs0 (AxSpinHd9.hsp1 rs0 + sign_extend (m := 64) AxSpinHd8.imm24) →
    dataAtS σi T (.Store .Data) (AxSpinHd9.hsp1 rs0 + sign_extend (m := 64) AxSpinHd8.imm16) 8 Ps0 →
    dataAtS σi T (.Load .Data) (AxSpinHd9.hsp1 rs0 + sign_extend (m := 64) AxSpinHd8.imm16) 8 Ps0 →
    hitW rs0 (AxSpinHd9.hsp1 rs0 + sign_extend (m := 64) AxSpinHd8.imm16) →
    dataAtS σi T (.Store .Data) (AxSpinHd9.hsp1 rs0 + sign_extend (m := 64) AxSpinHd8.imm8) 8 Ps1 →
    dataAtS σi T (.Load .Data) (AxSpinHd9.hsp1 rs0 + sign_extend (m := 64) AxSpinHd8.imm8) 8 Ps1 →
    hitW rs0 (AxSpinHd9.hsp1 rs0 + sign_extend (m := 64) AxSpinHd8.imm8) →
    dataAtS σi T (.Store .Data)
      (AxSpinE8.sp1Of (AxSpinHd9.hsp1 rs0) + sign_extend (m := 64) AxSpinE8.immRa) 8 Pram →
    dataAtS σi T (.Load .Data)
      (AxSpinE8.sp1Of (AxSpinHd9.hsp1 rs0) + sign_extend (m := 64) AxSpinE8.immRa) 8 Pram →
    hitW rs0 (AxSpinE8.sp1Of (AxSpinHd9.hsp1 rs0) + sign_extend (m := 64) AxSpinE8.immRa) →
    dataAtS σi T (.Store .Data)
      (AxSpinE8.sp1Of (AxSpinHd9.hsp1 rs0) + sign_extend (m := 64) AxSpinE8.immS0) 8 Ps0m →
    dataAtS σi T (.Load .Data)
      (AxSpinE8.sp1Of (AxSpinHd9.hsp1 rs0) + sign_extend (m := 64) AxSpinE8.immS0) 8 Ps0m →
    hitW rs0 (AxSpinE8.sp1Of (AxSpinHd9.hsp1 rs0) + sign_extend (m := 64) AxSpinE8.immS0) →
    (∀ j : Nat, j < 8 → priv L (paZ Pra + (j : Int)) i) → ¬ L.xlText (paZ Pra) →
    (∀ j : Nat, j < 8 → priv L (paZ Ps0 + (j : Int)) i) → ¬ L.xlText (paZ Ps0) →
    (∀ j : Nat, j < 8 → priv L (paZ Ps1 + (j : Int)) i) → ¬ L.xlText (paZ Ps1) →
    (∀ j : Nat, j < 8 → priv L (paZ Pram + (j : Int)) i) → ¬ L.xlText (paZ Pram) →
    (∀ j : Nat, j < 8 → priv L (paZ Ps0m + (j : Int)) i) → ¬ L.xlText (paZ Ps0m) →
    slotsDisj [paZ Pra, paZ Ps0, paZ Ps1, paZ Pram, paZ Ps0m] →
    -- the return addresses (Q20': graph-value pins; deviation 1)
    graphValue (gtAdGd GT) (i, k + 7) = some (stBytes 8 (pch 0x1a)) →
    graphValue (gtAdGd GT) (i, k + 9) = some (stBytes 8 (AxSpinHdB.prl 0x10)) →
    -- the owned lk->cpu read
    dataAtS σi T (.Load .Data) (gprVal rs0 AxSpinE8.r10 + sign_extend (m := 64) (16#12)) 8 Pcl →
    paZ Pcl = L.xlLk + 16 → ¬ L.xlText (paZ Pcl) →
    (∀ (k' : Nat) (lb : Lbl) (aq rl : Bool) (m : Nat),
      (AxOpsem.grow (gtAdGd GT) i)[k']? = some lb → aident lb = .IRmw aq rl (paZ Pcl) m →
      m ≠ 8) →
    (AxOpsem.grow (gtAdGd GT) i)[kw]? =
      some (Lbl.LStore false (L.xlLk + 16) (WeakInterpProj.wbytes 8 val) cls) →
    kw < k + 4 →
    (∀ w a v', a ∈ clb L → gwritesByte (gtAdGd GT).gdG w a v' →
      WeakRvwmoGraph.gpo (gtAdGd GT).gdG (i, kw) w →
      WeakRvwmoGraph.gpo (gtAdGd GT).gdG w (i, k + 4) → False) →
    -- the holder's lock-word read: address translation + the claim at `kc`
    dataAtS σi T (.Load .Data) (gprVal rs0 AxSpinE8.r10 + sign_extend (m := 64) (0#12)) 4 Plk →
    ¬ L.xlText (paZ Plk) →
    (AxOpsem.grow (gtAdGd GT) i)[kc]? = some (Lbl.LRmw true false L.xlLk tsc rvsc wvsc clsc) →
    kc < k →
    nolk L.xlLk (gtAdGd GT).gdG (i, kc) (i, k) →
    ⊢ AxAnnot.annotOwn (i, kc) iprop(locked nm.xnReg L.xlLk i (i, kc) ∗ Qc) -∗
      AxAnnot.annotOwn (i, kw)
        iprop(Qw ∗ RVL nm.xnH (gtAdGd GT) (clb L) (i, kw) (WeakInterpProj.wbytes 8 val)) -∗
      KLong (hlc := hlc) L GT nm T satp0 i cpu Ψ k rs0 (AxSpinHdB.prl 0x10) Pra Ps0 Ps1 Pram Ps0m
        (OHeld L GT nm i kc k Qc k) (OOwn L GT nm i kw (k + 4) val Qw (k + 4)) -∗
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
        ⟨.PHart cpu (.pure ()) rs0 none ib0, k⟩ Ψ := by
  intro HR Hw8 H1 H2 H3 H4 H5 Hc0 HPC0 Hh0 Hhm Hhlk Hhlc
    Hd1 Hd2 Hd3 Hd4 Hd5 Hd6 Hd7 Hd8 Hd9 Hd10 Hd11 Hd12 Hd13 Hd14 Hd15
    Hp1 Hn1 Hp2 Hn2 Hp3 Hn3 Hp4 Hn4 Hp5 Hn5 Hdisj Hvm Hv Hdcl Hpcl Hntcl Hnrcl Hw Hkw Hnoint
    Hdlk Hntlk Hkc Hkck Hnl
  have Hlen : k + 12 < (AxOpsem.grow (gtAdGd GT) i).length := HR.2.1
  have W := holdingFromReleaseP L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Htxm Htxh
    Ψ HΨmid k rs0 ib0 true plk Pra Ps0 Ps1 Pram Ps0m Pcl Plk kc kw val cls Qc Qw tsc rvsc wvsc
    clsc (AxSpinHd8.rowHoldingPOfFull _ _ _ _ _ _ _ _ _ _ HR) Hw8 H1 H2 H3 H4 H5
    Hc0 HPC0 Hh0 Hhm Hhlk Hhlc Hd1 Hd2 Hd3 Hd4 Hd5 Hd6 Hd7 Hd8 Hd9 Hd10 Hd11 Hd12 Hd13 Hd14 Hd15
    Hp1 Hn1 Hp2 Hn2 Hp3 Hn3 Hp4 Hn4 Hp5 Hn5 Hdisj
    (by simp only [↓reduceIte]; exact ⟨fun _ => Hvm, fun _ => Hv⟩) Hdcl Hpcl Hntcl Hnrcl Hw Hkw
    Hnoint Hdlk Hntlk Hkc Hkck Hnl
    (fun _ _ h2 h3 => absurd h3 (by simp only [↓reduceIte] at h2; omega))
  simp only [↓reduceIte] at W
  iintro Hc Hh C
  iapply W $$ Hc Hh
  isplit
  · iexact C
  · unfold KLongEnd
    iintro %vlk %vcpu %vram %vs0m %vra %vs0 %vs1 %pr %Hp
    exact absurd Hp.1 (by omega)
set_option maxHeartbeats 1000000 in
include HL Hcons hmode hasid hppn Hfix Htxm Htxh HΨmid in
/-- (Lean-only, P1) THE GATE FORM of acquire's call of holding on a PREFIX row:
`holdingFromAcquireP` on `AxSpinHdA.wpdHoldingG` — the long arm's reload pins (AllocPins2
`hdRets`, `hdS1`) replaced by the three `AxSpinT2i.Gate`s, the return address `acquire + 0x16`
replaced by the entry ra `gprVal rs0 ra` (acquire knows it from its `jal`), `Hret` its
2-alignment; long continuation `KLongG` (receives the three reload values past `k + 12`),
`KLongEnd` / `KShortEnd` unchanged. -/
theorem holdingFromAcquireG (k : Nat) (rs0 : RegFile) (ib0 : Ibch) (hb : Bool)
    (plk pcl : Int) (Pra Ps0 Ps1 Pram Ps0m Pcl Plk : BitVec 64) :
    RowHoldingP k (AxOpsem.grow (gtAdGd GT) i) hb plk pcl (paZ Pra) (paZ Ps0) (paZ Ps1)
      (paZ Pram) (paZ Ps0m) →
    rowW8 (AxOpsem.grow (gtAdGd GT) i) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Pra) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Ps0) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Ps1) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Pram) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Ps0m) →
    ctrlOkSW T satp0 rs0 → rs0 .PC = pch 0 → hitW rs0 (pch 0) → hitW rs0 (pcm 0) →
    hitW rs0 (gprVal rs0 AxSpinE8.r10 + sign_extend (m := 64) (0#12)) →
    hitW rs0 (gprVal rs0 AxSpinE8.r10 + sign_extend (m := 64) (16#12)) →
    dataAtS σi T (.Store .Data) (AxSpinHd9.hsp1 rs0 + sign_extend (m := 64) AxSpinHd8.imm24) 8 Pra →
    dataAtS σi T (.Load .Data) (AxSpinHd9.hsp1 rs0 + sign_extend (m := 64) AxSpinHd8.imm24) 8 Pra →
    hitW rs0 (AxSpinHd9.hsp1 rs0 + sign_extend (m := 64) AxSpinHd8.imm24) →
    dataAtS σi T (.Store .Data) (AxSpinHd9.hsp1 rs0 + sign_extend (m := 64) AxSpinHd8.imm16) 8 Ps0 →
    dataAtS σi T (.Load .Data) (AxSpinHd9.hsp1 rs0 + sign_extend (m := 64) AxSpinHd8.imm16) 8 Ps0 →
    hitW rs0 (AxSpinHd9.hsp1 rs0 + sign_extend (m := 64) AxSpinHd8.imm16) →
    dataAtS σi T (.Store .Data) (AxSpinHd9.hsp1 rs0 + sign_extend (m := 64) AxSpinHd8.imm8) 8 Ps1 →
    dataAtS σi T (.Load .Data) (AxSpinHd9.hsp1 rs0 + sign_extend (m := 64) AxSpinHd8.imm8) 8 Ps1 →
    hitW rs0 (AxSpinHd9.hsp1 rs0 + sign_extend (m := 64) AxSpinHd8.imm8) →
    dataAtS σi T (.Store .Data)
      (AxSpinE8.sp1Of (AxSpinHd9.hsp1 rs0) + sign_extend (m := 64) AxSpinE8.immRa) 8 Pram →
    dataAtS σi T (.Load .Data)
      (AxSpinE8.sp1Of (AxSpinHd9.hsp1 rs0) + sign_extend (m := 64) AxSpinE8.immRa) 8 Pram →
    hitW rs0 (AxSpinE8.sp1Of (AxSpinHd9.hsp1 rs0) + sign_extend (m := 64) AxSpinE8.immRa) →
    dataAtS σi T (.Store .Data)
      (AxSpinE8.sp1Of (AxSpinHd9.hsp1 rs0) + sign_extend (m := 64) AxSpinE8.immS0) 8 Ps0m →
    dataAtS σi T (.Load .Data)
      (AxSpinE8.sp1Of (AxSpinHd9.hsp1 rs0) + sign_extend (m := 64) AxSpinE8.immS0) 8 Ps0m →
    hitW rs0 (AxSpinE8.sp1Of (AxSpinHd9.hsp1 rs0) + sign_extend (m := 64) AxSpinE8.immS0) →
    (∀ j : Nat, j < 8 → priv L (paZ Pra + (j : Int)) i) → ¬ L.xlText (paZ Pra) →
    (∀ j : Nat, j < 8 → priv L (paZ Ps0 + (j : Int)) i) → ¬ L.xlText (paZ Ps0) →
    (∀ j : Nat, j < 8 → priv L (paZ Ps1 + (j : Int)) i) → ¬ L.xlText (paZ Ps1) →
    (∀ j : Nat, j < 8 → priv L (paZ Pram + (j : Int)) i) → ¬ L.xlText (paZ Pram) →
    (∀ j : Nat, j < 8 → priv L (paZ Ps0m + (j : Int)) i) → ¬ L.xlText (paZ Ps0m) →
    slotsDisj [paZ Pra, paZ Ps0, paZ Ps1, paZ Pram, paZ Ps0m] →
    -- P1: the long arm's three reload GATES (mycpu's ra, holding's ra, holding's s1)
    (hb = true →
      AxSpinT2i.Gate GT i (k + 7) (stBytes 8 (pch 0x1a)) ∧
      AxSpinT2i.Gate GT i (k + 9) (stBytes 8 (gprVal rs0 AxSpinE8.r1)) ∧
      AxSpinT2i.Gate GT i (k + 11) (stBytes 8 (gprVal rs0 AxSpinHd8.r9))) →
    -- the return address is the entry ra (the caller's `jal` link; 2-aligned)
    jalrTgt 0#12 (gprVal rs0 AxSpinE8.r1) = gprVal rs0 AxSpinE8.r1 →
    -- the lk->cpu read
    dataAtS σi T (.Load .Data) (gprVal rs0 AxSpinE8.r10 + sign_extend (m := 64) (16#12)) 8 Pcl →
    ¬ L.xlText (paZ Pcl) →
    (∀ (k' : Nat) (lb : Lbl) (aq rl : Bool) (m : Nat),
      (AxOpsem.grow (gtAdGd GT) i)[k']? = some lb → aident lb = .IRmw aq rl (paZ Pcl) m →
      m ≠ 8) →
    -- the lock-word read: only its address translation
    dataAtS σi T (.Load .Data) (gprVal rs0 AxSpinE8.r10 + sign_extend (m := 64) (0#12)) 4 Plk →
    ¬ L.xlText (paZ Plk) →
    -- the row-end hook (stage 2, design §B / Q-S2-2)
    (∀ k' : Nat, k ≤ k' → k' ≤ (if hb then k + 11 else k) →
      (AxOpsem.grow (gtAdGd GT) i).length ≤ k' → ∀ pr : Pexv6,
        ⊢ @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
          ⟨pr, k'⟩ Ψ) →
    ⊢ (if hb then
          KLongG (hlc := hlc) L GT nm T satp0 i cpu Ψ k rs0 Pra Ps0 Ps1 Pram
            Ps0m (fun _ => iprop(True)) (ORacy L GT i (k + 4)) ∧
          KLongEnd (hlc := hlc) L GT nm i Ψ k rs0 Pra Ps0 Ps1 Pram Ps0m (fun _ => iprop(True))
            (ORacy L GT i (k + 4))
        else KShort (hlc := hlc) L GT nm T satp0 i cpu Ψ k rs0 (gprVal rs0 AxSpinE8.r1)
            (fun _ => iprop(True)) ∧
          KShortEnd (hlc := hlc) L GT nm i Ψ k (fun _ => iprop(True))) -∗
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
        ⟨.PHart cpu (.pure ()) rs0 none ib0, k⟩ Ψ := by
  intro HR Hw8 H1 H2 H3 H4 H5 Hc0 HPC0 Hh0 Hhm Hhlk Hhlc
    Hd1 Hd2 Hd3 Hd4 Hd5 Hd6 Hd7 Hd8 Hd9 Hd10 Hd11 Hd12 Hd13 Hd14 Hd15
    Hp1 Hn1 Hp2 Hn2 Hp3 Hn3 Hp4 Hn4 Hp5 Hn5 Hdisj Hg Hret Hdcl Hntcl Hnrcl Hdlk Hntlk HΨend
  have Hlk : ⊢ @FldMW hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent
        (dokAtP (paZ Plk) 4) i (fun _ _ => iprop(True)) k (k + 1) -∗
      XLd (hlc := hlc) L GT nm T satp0 i cpu Ψ k (pch 0x00) 10#5 15#5 0#12 4
        (gprVal rs0 AxSpinE8.r10) (fun _ => iprop(True)) :=
    XLkOfWP L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Htxh Ψ HΨmid k hb plk pcl
      (paZ Pra) (paZ Ps0) (paZ Ps1) (paZ Pram) (paZ Ps0m) (gprVal rs0 AxSpinE8.r10) Plk
      (fun _ _ => iprop(True)) HR Hdlk Hntlk
  have Hfr := FldMWFrame (hlc := hlc) (GF := GF) L GT nm HL Hcons i (paZ Plk) 4 k (k + 1)
    (winNormwP GT i k hb plk pcl _ _ _ _ _ (paZ Plk) 4 HR)
  cases hb
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have W := wpdHoldingG L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Htxm Htxh Ψ
      HΨmid k rs0 ib0 false plk pcl Pra Ps0 Ps1 Pram Ps0m
      (fun _ => iprop(True)) (ORacy L GT i (k + 4)) HR Hw8 H1 H2 H3 H4 H5 Hc0 HPC0 Hh0 Hhm
      Hhlk Hhlc Hd1 Hd2 Hd3 Hd4 Hd5 Hd6 Hd7 Hd8 Hd9 Hd10 Hd11 Hd12 Hd13 Hd14 Hd15
      Hp1 Hn1 Hp2 Hn2 Hp3 Hn3 Hp4 Hn4 Hp5 Hn5 Hdisj
      Hg Hret HΨend
    simp only [Bool.false_eq_true, ↓reduceIte] at W
    iintro C
    ihave F := Hfr
    ihave X0 := Hlk
    ihave X := X0 $$ F
    ihave W0 := W
    iapply W0 $$ X C
  · simp only [↓reduceIte]
    have W := wpdHoldingG L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Htxm Htxh Ψ
      HΨmid k rs0 ib0 true plk pcl Pra Ps0 Ps1 Pram Ps0m
      (fun _ => iprop(True)) (ORacy L GT i (k + 4)) HR Hw8 H1 H2 H3 H4 H5 Hc0 HPC0 Hh0 Hhm
      Hhlk Hhlc Hd1 Hd2 Hd3 Hd4 Hd5 Hd6 Hd7 Hd8 Hd9 Hd10 Hd11 Hd12 Hd13 Hd14 Hd15
      Hp1 Hn1 Hp2 Hn2 Hp3 Hn3 Hp4 Hn4 Hp5 Hn5 Hdisj
      Hg Hret HΨend
    simp only [↓reduceIte] at W
    have Hcpu := XCpuOf L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Htxh Ψ HΨmid k
      (gprVal rs0 AxSpinE8.r10) Pcl (ORacy L GT i) Hdcl Hntcl Hnrcl
    have Hfc := FldMRacy (hlc := hlc) (GF := GF) L GT nm HL Hcons i (paZ Pcl) 8 Hnrcl
    iintro C
    ihave F := Hfr
    ihave X0 := Hlk
    ihave X := X0 $$ F
    ihave Hf := Hfc
    ihave Hc0 := Hcpu
    ihave Hc := Hc0 $$ Hf
    ihave W0 := W
    iapply W0 $$ X [Hc C]
    isplitl [Hc]
    · iexact Hc
    · iexact C

set_option maxHeartbeats 1000000 in
include HL Hcons hmode hasid hppn Hfix Htxm Htxh HΨmid in
/-- (Lean-only, P1) THE GATE FORM of release's call of holding on a PREFIX row (any `hb`):
`holdingFromReleaseP` on `AxSpinHdA.wpdHoldingG` — the long arm's reload pins (AllocPins2
`rhRets`, `rhS1`) replaced by the three `AxSpinT2i.Gate`s, the return address `release + 0x10`
replaced by the entry ra `gprVal rs0 ra` (release knows it from its `jal`), `Hret` its
2-alignment; long continuation `KLongG` (receives the three reload values past `k + 12`),
`KLongEnd` / `KShortEnd` unchanged. -/
theorem holdingFromReleaseG (k : Nat) (rs0 : RegFile) (ib0 : Ibch) (hb : Bool)
    (plk : Int) (Pra Ps0 Ps1 Pram Ps0m Pcl Plk : BitVec 64)
    (kc kw : Nat) (val : BitVec 64) (cls : WmClass) (Qc Qw : IProp GF)
    (tsc : List Nat) (rvsc wvsc : List (BitVec 8)) (clsc : WmClass) :
    RowHoldingP k (AxOpsem.grow (gtAdGd GT) i) hb plk (paZ Pcl) (paZ Pra) (paZ Ps0) (paZ Ps1)
      (paZ Pram) (paZ Ps0m) →
    rowW8 (AxOpsem.grow (gtAdGd GT) i) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Pra) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Ps0) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Ps1) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Pram) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Ps0m) →
    ctrlOkSW T satp0 rs0 → rs0 .PC = pch 0 → hitW rs0 (pch 0) → hitW rs0 (pcm 0) →
    hitW rs0 (gprVal rs0 AxSpinE8.r10 + sign_extend (m := 64) (0#12)) →
    hitW rs0 (gprVal rs0 AxSpinE8.r10 + sign_extend (m := 64) (16#12)) →
    dataAtS σi T (.Store .Data) (AxSpinHd9.hsp1 rs0 + sign_extend (m := 64) AxSpinHd8.imm24) 8 Pra →
    dataAtS σi T (.Load .Data) (AxSpinHd9.hsp1 rs0 + sign_extend (m := 64) AxSpinHd8.imm24) 8 Pra →
    hitW rs0 (AxSpinHd9.hsp1 rs0 + sign_extend (m := 64) AxSpinHd8.imm24) →
    dataAtS σi T (.Store .Data) (AxSpinHd9.hsp1 rs0 + sign_extend (m := 64) AxSpinHd8.imm16) 8 Ps0 →
    dataAtS σi T (.Load .Data) (AxSpinHd9.hsp1 rs0 + sign_extend (m := 64) AxSpinHd8.imm16) 8 Ps0 →
    hitW rs0 (AxSpinHd9.hsp1 rs0 + sign_extend (m := 64) AxSpinHd8.imm16) →
    dataAtS σi T (.Store .Data) (AxSpinHd9.hsp1 rs0 + sign_extend (m := 64) AxSpinHd8.imm8) 8 Ps1 →
    dataAtS σi T (.Load .Data) (AxSpinHd9.hsp1 rs0 + sign_extend (m := 64) AxSpinHd8.imm8) 8 Ps1 →
    hitW rs0 (AxSpinHd9.hsp1 rs0 + sign_extend (m := 64) AxSpinHd8.imm8) →
    dataAtS σi T (.Store .Data)
      (AxSpinE8.sp1Of (AxSpinHd9.hsp1 rs0) + sign_extend (m := 64) AxSpinE8.immRa) 8 Pram →
    dataAtS σi T (.Load .Data)
      (AxSpinE8.sp1Of (AxSpinHd9.hsp1 rs0) + sign_extend (m := 64) AxSpinE8.immRa) 8 Pram →
    hitW rs0 (AxSpinE8.sp1Of (AxSpinHd9.hsp1 rs0) + sign_extend (m := 64) AxSpinE8.immRa) →
    dataAtS σi T (.Store .Data)
      (AxSpinE8.sp1Of (AxSpinHd9.hsp1 rs0) + sign_extend (m := 64) AxSpinE8.immS0) 8 Ps0m →
    dataAtS σi T (.Load .Data)
      (AxSpinE8.sp1Of (AxSpinHd9.hsp1 rs0) + sign_extend (m := 64) AxSpinE8.immS0) 8 Ps0m →
    hitW rs0 (AxSpinE8.sp1Of (AxSpinHd9.hsp1 rs0) + sign_extend (m := 64) AxSpinE8.immS0) →
    (∀ j : Nat, j < 8 → priv L (paZ Pra + (j : Int)) i) → ¬ L.xlText (paZ Pra) →
    (∀ j : Nat, j < 8 → priv L (paZ Ps0 + (j : Int)) i) → ¬ L.xlText (paZ Ps0) →
    (∀ j : Nat, j < 8 → priv L (paZ Ps1 + (j : Int)) i) → ¬ L.xlText (paZ Ps1) →
    (∀ j : Nat, j < 8 → priv L (paZ Pram + (j : Int)) i) → ¬ L.xlText (paZ Pram) →
    (∀ j : Nat, j < 8 → priv L (paZ Ps0m + (j : Int)) i) → ¬ L.xlText (paZ Ps0m) →
    slotsDisj [paZ Pra, paZ Ps0, paZ Ps1, paZ Pram, paZ Ps0m] →
    -- P1: the long arm's three reload GATES (mycpu's ra, holding's ra, holding's s1)
    (hb = true →
      AxSpinT2i.Gate GT i (k + 7) (stBytes 8 (pch 0x1a)) ∧
      AxSpinT2i.Gate GT i (k + 9) (stBytes 8 (gprVal rs0 AxSpinE8.r1)) ∧
      AxSpinT2i.Gate GT i (k + 11) (stBytes 8 (gprVal rs0 AxSpinHd8.r9))) →
    -- the return address is the entry ra (the caller's `jal` link; 2-aligned)
    jalrTgt 0#12 (gprVal rs0 AxSpinE8.r1) = gprVal rs0 AxSpinE8.r1 →
    -- the owned lk->cpu read
    dataAtS σi T (.Load .Data) (gprVal rs0 AxSpinE8.r10 + sign_extend (m := 64) (16#12)) 8 Pcl →
    paZ Pcl = L.xlLk + 16 → ¬ L.xlText (paZ Pcl) →
    (∀ (k' : Nat) (lb : Lbl) (aq rl : Bool) (m : Nat),
      (AxOpsem.grow (gtAdGd GT) i)[k']? = some lb → aident lb = .IRmw aq rl (paZ Pcl) m →
      m ≠ 8) →
    (AxOpsem.grow (gtAdGd GT) i)[kw]? =
      some (Lbl.LStore false (L.xlLk + 16) (WeakInterpProj.wbytes 8 val) cls) →
    kw < k + 4 →
    (∀ w a v', a ∈ clb L → gwritesByte (gtAdGd GT).gdG w a v' →
      WeakRvwmoGraph.gpo (gtAdGd GT).gdG (i, kw) w →
      WeakRvwmoGraph.gpo (gtAdGd GT).gdG w (i, k + 4) → False) →
    -- the holder's lock-word read: address translation + the claim at `kc`
    dataAtS σi T (.Load .Data) (gprVal rs0 AxSpinE8.r10 + sign_extend (m := 64) (0#12)) 4 Plk →
    ¬ L.xlText (paZ Plk) →
    (AxOpsem.grow (gtAdGd GT) i)[kc]? = some (Lbl.LRmw true false L.xlLk tsc rvsc wvsc clsc) →
    kc < k →
    nolk L.xlLk (gtAdGd GT).gdG (i, kc) (i, k) →
    -- the row-end hook (stage 2, design §B / Q-S2-2)
    (∀ k' : Nat, k ≤ k' → k' ≤ (if hb then k + 11 else k) →
      (AxOpsem.grow (gtAdGd GT) i).length ≤ k' → ∀ pr : Pexv6,
        ⊢ @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
          ⟨pr, k'⟩ Ψ) →
    ⊢ AxAnnot.annotOwn (i, kc) iprop(locked nm.xnReg L.xlLk i (i, kc) ∗ Qc) -∗
      AxAnnot.annotOwn (i, kw)
        iprop(Qw ∗ RVL nm.xnH (gtAdGd GT) (clb L) (i, kw) (WeakInterpProj.wbytes 8 val)) -∗
      (if hb then
          KLongG (hlc := hlc) L GT nm T satp0 i cpu Ψ k rs0 Pra Ps0 Ps1 Pram
            Ps0m (OHeld L GT nm i kc k Qc k) (OOwn L GT nm i kw (k + 4) val Qw (k + 4)) ∧
          KLongEnd (hlc := hlc) L GT nm i Ψ k rs0 Pra Ps0 Ps1 Pram Ps0m
            (OHeld L GT nm i kc k Qc k) (OOwn L GT nm i kw (k + 4) val Qw (k + 4))
        else
          KShort (hlc := hlc) L GT nm T satp0 i cpu Ψ k rs0 (gprVal rs0 AxSpinE8.r1)
            (fun v => iprop(OHeld L GT nm i kc k Qc k v ∗ AxAnnot.annotOwn (i, kw)
              iprop(Qw ∗ RVL nm.xnH (gtAdGd GT) (clb L) (i, kw) (WeakInterpProj.wbytes 8 val)))) ∧
          KShortEnd (hlc := hlc) L GT nm i Ψ k
            (fun v => iprop(OHeld L GT nm i kc k Qc k v ∗ AxAnnot.annotOwn (i, kw)
              iprop(Qw ∗ RVL nm.xnH (gtAdGd GT) (clb L) (i, kw) (WeakInterpProj.wbytes 8 val))))) -∗
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
        ⟨.PHart cpu (.pure ()) rs0 none ib0, k⟩ Ψ := by
  intro HR Hw8 H1 H2 H3 H4 H5 Hc0 HPC0 Hh0 Hhm Hhlk Hhlc
    Hd1 Hd2 Hd3 Hd4 Hd5 Hd6 Hd7 Hd8 Hd9 Hd10 Hd11 Hd12 Hd13 Hd14 Hd15
    Hp1 Hn1 Hp2 Hn2 Hp3 Hn3 Hp4 Hn4 Hp5 Hn5 Hdisj Hg Hret Hdcl Hpcl Hntcl Hnrcl Hw Hkw Hnoint
    Hdlk Hntlk Hkc Hkck Hnl HΨend
  have Hlk := XLkOfWP L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Htxh Ψ HΨmid k hb
    plk (paZ Pcl) (paZ Pra) (paZ Ps0) (paZ Ps1) (paZ Pram) (paZ Ps0m) (gprVal rs0 AxSpinE8.r10)
    Plk (OHeld L GT nm i kc k Qc) HR Hdlk Hntlk
  have Hfl := FldMWLkheld (hlc := hlc) (GF := GF) L GT nm HL Hcons i (paZ Plk) kc k rvsc wvsc
    tsc clsc Qc k (k + 1) (winNormwP GT i k hb plk (paZ Pcl) _ _ _ _ _ (paZ Plk) 4 HR)
    Hkc Hkck Hnl
  cases hb
  · -- SHORT arm (rlS): the lw's `OHeld` output and the unused handle go to the continuation
    simp only [Bool.false_eq_true, ↓reduceIte]
    have W := wpdHoldingG L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Htxm Htxh Ψ
      HΨmid k rs0 ib0 false plk (paZ Pcl) Pra Ps0 Ps1 Pram Ps0m
      (OHeld L GT nm i kc k Qc k) (OOwn L GT nm i kw (k + 4) val Qw (k + 4)) HR Hw8 H1 H2 H3 H4
      H5 Hc0 HPC0 Hh0 Hhm Hhlk Hhlc Hd1 Hd2 Hd3 Hd4 Hd5 Hd6 Hd7 Hd8 Hd9 Hd10 Hd11 Hd12 Hd13 Hd14
      Hd15 Hp1 Hn1 Hp2 Hn2 Hp3 Hn3 Hp4 Hn4 Hp5 Hn5 Hdisj
      Hg Hret HΨend
    simp only [Bool.false_eq_true, ↓reduceIte] at W
    unfold KShort KShortEnd at W ⊢
    iintro Hc Hh C
    ihave F0 := Hfl
    ihave F := F0 $$ Hc
    ihave X0 := Hlk
    ihave X := X0 $$ F
    ihave W0 := W
    iapply W0 $$ X
    isplit
    · iintro %vlk %rs' %ib' %Hp Ho
      icases C with ⟨C, -⟩
      iapply C $$ %vlk %rs' %ib' %Hp
      isplitl [Ho]
      · iexact Ho
      · iexact Hh
    · iintro %vlk %pr %Hp Ho
      icases C with ⟨-, C⟩
      iapply C $$ %vlk %pr %Hp
      isplitl [Ho]
      · iexact Ho
      · iexact Hh
  · -- LONG arm (rlL): `OHeld` and the owned read's `OOwn`
    simp only [↓reduceIte]
    have W := wpdHoldingG L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Htxm Htxh Ψ
      HΨmid k rs0 ib0 true plk (paZ Pcl) Pra Ps0 Ps1 Pram Ps0m
      (OHeld L GT nm i kc k Qc k) (OOwn L GT nm i kw (k + 4) val Qw (k + 4)) HR Hw8 H1 H2 H3 H4
      H5 Hc0 HPC0 Hh0 Hhm Hhlk Hhlc Hd1 Hd2 Hd3 Hd4 Hd5 Hd6 Hd7 Hd8 Hd9 Hd10 Hd11 Hd12 Hd13 Hd14
      Hd15 Hp1 Hn1 Hp2 Hn2 Hp3 Hn3 Hp4 Hn4 Hp5 Hn5 Hdisj
      Hg Hret HΨend
    simp only [↓reduceIte] at W
    have Hcpu := XCpuOf L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Htxh Ψ HΨmid k
      (gprVal rs0 AxSpinE8.r10) Pcl (OOwn L GT nm i kw (k + 4) val Qw) Hdcl Hntcl Hnrcl
    have Hfo := FldMCpuOwn (hlc := hlc) (GF := GF) L GT nm HL Hcons i kw (k + 4) val cls Qw
      (by rw [← Hpcl]; exact Hnrcl) Hw Hkw Hnoint
    rw [← Hpcl] at Hfo
    iintro Hc Hh C
    ihave F0 := Hfl
    ihave F := F0 $$ Hc
    ihave X0 := Hlk
    ihave X := X0 $$ F
    ihave Hfo0 := Hfo
    ihave Hf := Hfo0 $$ Hh
    ihave Hcc0 := Hcpu
    ihave Hcc := Hcc0 $$ Hf
    ihave W0 := W
    iapply W0 $$ X [Hcc C]
    isplitl [Hcc]
    · iexact Hcc
    · iexact C
end callsC

end Weak
