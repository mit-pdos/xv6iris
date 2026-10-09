/-
Weak: **the inlined allocpid's FLOW RESOURCES at the joint instance Ixv6 (any layout `L`): the
nextpid read and write, the value-agnostic flow of the 64 `proc[j].pid` scan reads, and a
POSITIONAL STORE LEAF over an arbitrary store flow resource.**

Rocq: `iris/AxSpinAp8.v` @ xxvzwolszwmp (owner ruling Q18: RETARGETED to the allocpid copy that
this tree's kernel INLINES into `allocproc`, `allocproc + 0x44 .. + 0x94`; code and mapping in
`Weak/AxSpinAp.lean`'s header, "Design"; the plan is `PROGRESS-Q18.md`, "AxSpinAp8").

## The Rocq header, in substance

§1 `FldMWNp` — the CS's nextpid read (Rocq `c.lw s1,0(a5)`; here `lw a3,1998(a3)`, +0x48),
   window-restricted (for `AxSpinXP2.XxLdW`): at the read position `kr` the flow is
   `AxSpinU.fxuNpRead` drawing `RNp` from the anchor `e` (a lob-predecessor of the read — the
   claim, ppo rule 5); it deposits at `(i, kr)` the VALUE handle `NPh` (value = the word of the
   graph value) and the SOURCE fact `npSrc` (no nextpid write lands gmo-between the anchor and the
   read).  Any other window position that reads 4 bytes is excluded by the premise `Hoth`.
§2 `FstMNp` — the CS's nextpid write (Rocq `c.sw a4,0(a5)`; here `sw a1,1936(a5)`, +0x86),
   position-generic `FstM`: at the store position `ks` (the ONLY row position writing nextpid — a
   row premise), IF the graph data is `w8 + 1`'s bytes the flow is `AxSpinU.fxuNpIncr` drawing the
   value handle from the read (ppo rule 1: same-address R→W), depositing `RNp` and the minted
   ◯{v} (`FRAG`) at the store; any OTHER data (refuted by the caller from the register value,
   `AxSpinAp7.npBytes`) is still a legal owned write (`AxSpinX2.fxRVLWrite` with the drawn
   handle's last-value bytes), output dropped.
§3 `XxStF` — `AxSpinE6.XxSt` with the private-slot flow replaced by ANY `FstM` (width `w`); the
   continuation learns the store's row position, its graph data (= the register's bytes) and the
   flow output there.  Used by Ap9 twice: `sw a1,1936(a5)` (+0x86, nextpid, with `FstMNp`) and
   `c.sw a3,48(s1)` (+0x8a, `p->pid`, with the caller's store flow — ruling Q18c).
NEW (Lean-only, ruling Q18a): `AxSpinAp8.FldMWFrame` — a VALUE-AGNOSTIC read flow (no ownership,
   nothing deposited: `AxSpinX2.fxRead` via `AxSpinHdB.dflowOPlain`) for any plain read in a
   window; `AxSpinAp8.FldMWScan` — its instance at the `j`-th scan read `c.lw a4,48(a5)` (+0x74)
   of `proc[j].pid`, positioned by `AxSpinAp7.RowAllocpidBody`.  The scan reads are racy (other
   harts write `proc[j].pid` under `p->lock`, not under `pid_lock`), so no ownership is used.

## Deviations from Rocq

1. KERNEL INLINING (Q18) + O2 STAGE C.  The flows are about the same events (one nextpid read,
   one nextpid write), at the inlined code's instructions.
   * `FldMWNp`: statement as Rocq (window `[lo, hi)`, `Hoth` for the window's other positions).
     Under Stage C a 4-byte `lw` has its data event exactly at its first row position, so the Ap9
     caller uses the window `[kr, kr + 1)` (`AxSpinXP2.XxLdW`), where `Hoth` is vacuous; Rocq's
     window `[k + 2, k + 4)` also covered the `c.lw`'s 2-byte fetch item.
   * `FstMNp`: statement as Rocq; the Ap9 caller has `ks = kr + 65` (Rocq `kr + 3`).
   * `XxStF` (as `AxSpinE6.XxSt`, its deviation 3): the store is AT `k` (Rocq `S k`), the
     continuation at `k + 1` (Rocq `k + 2`), premise `k + 1 ≤ LEN` (Rocq `k + 2 ≤ LEN`); the facts
     are `graphData (i, k)` and `Out k`.  Rocq's `Hnw` ("row item `k` — the fetch — is not a
     write") is DROPPED: row item `k` IS the store, so the premise would be unsatisfiable; its one
     use (ruling out `kd = k`) is now arithmetic.
   * NEW `AxSpinAp8.FldMWFrame` / `AxSpinAp8.FldMWScan` (provisional ruling Q18a; Rocq's allocpid
     makes no scan).
2. TYPES / INSTANCES (as `AxSpinHdB` deviation 2, `AxSpinXP2` deviation 2): `invGS_gen HasNoLc
   Σ` ↦ `[InvGS_gen hlc GF]` (any `hlc`); `xv6G Σ` ↦ `[AxSpinX.Xv6G GF]`; the local instances
   `a8_pol`/`a8_G` and `a8s_pol`/`a8s_G` are inlined as `xv6Pol GT` / `AxSpinX2.xG L GT nm`,
   passed with `@`.  `Z` widths ↦ `Nat` (`Z.to_nat w` ↦ `w`, `1 ≤ w ≤ 8` ↦ `1 ≤ w → w ≤ 8`),
   `uint pa` ↦ `paZ pa`, `bv_unsigned w8 + 1 < 2 ^ 32` ↦ `w8.toNat + 1 < 2 ^ 32`, `bv_add w8 one32`
   ↦ `w8 + one32`, `word_of_bytes` ↦ `wordOfBytes`, `st_bytes` ↦ `stBytes`, `decide (P)` ↦
   `if P`, `(i, k) ↦ₐ P` ↦ `AxAnnot.annotOwn (i, k) P`, `l !! k` ↦ `l[k]?`.  Section variables
   are explicit leading arguments where Rocq's section mechanism includes them: `a8Gmo GT`;
   `OLd L GT nm`, `OSt L GT nm`; `FldMWNp`/`FstMNp` `L GT nm HL Hcons`; `OutW GT i`;
   `FstMRowW L GT nm i`; `XxStF L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Ψ HΨmid`.
   Rocq's `Q := True` + `flow_eq_dyn_mono` (drop the `True`) is kept.
3. The trailing `Print Assumptions` lines are not ported (the lint's axiom check covers them).

**Rocq → Lean name map.**  `a8_gmo` `a8Gmo`, `OLd` `OLd`, `FldMW_np` `FldMWNp`, `OSt` `OSt`,
`FstM_np` `FstMNp`, `OutW` `OutW`, `FstM_rowW` `FstMRowW`, `Xx_stF` `XxStF`.  None is in the
duplicated-name table.  Lean-only (file-qualified): `AxSpinAp8.FldMWFrame`,
`AxSpinAp8.FldMWScan`.

**Dropped:** nothing (Rocq 8 definitions/lemmas + 4 local instances, inlined; Lean 10 = 8 + 2
Lean-only).
-/
import Weak.AxSpinHdB
import Weak.AxSpinXP2
import Weak.AxSpinE6
import Weak.AxSpinAp7

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-- Rocq `a8_gmo`: a lob-predecessor is gmo-before. -/
theorem a8Gmo (GT : GdexecT) (e r : Geid) :
    e ∈ @Axpol.lobp (xv6Pol GT) (gtAdGd GT) r → gmoLt (gtAdGd GT).gdG e r :=
  fun He => ((elemOfSplLobp _ _ _).1 He).2.2.2

section flows
variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF] [AxannotGS GF]
  [AxSpinX.Xv6G GF]
variable (L : Xlay) (GT : GdexecT) (nm : Xv6N)
variable (HL : xlayOk L) (Hcons : rvwmoCatConsistent (gtAdGd GT))

/-! # 1. The nextpid read -/

/-- Rocq `OLd`: at the read `kr`, the value handle and the source fact. -/
def OLd (i : Agent) (e : Geid) (kr k : Nat) (v : List (BitVec 8)) : IProp GF :=
  if k = kr then
    iprop(AxAnnot.annotOwn (i, kr) (NPh L GT nm (i, kr) (wordOfBytes 4 v)) ∗
      AxAnnot.annotOwn (i, kr) iprop(⌜npSrc (gtAdGd GT).gdG L (i, kr) e⌝))
  else iprop(True)

include HL Hcons in
/-- Rocq `FldMW_np`: the CS's nextpid read at `kr`, `RNp` drawn from the anchor `e`. -/
theorem FldMWNp (i : Agent) (e : Geid) (kr lo hi : Nat) :
    (∀ k', lo ≤ k' ∧ k' < hi → k' ≠ kr → ∀ (lb : Lbl) (aq : Bool) (b : Int) (n : Nat),
      (AxOpsem.grow (gtAdGd GT) i)[k']? = some lb → aidentRd (aident lb) = some (aq, b, n) →
      n ≠ 4) →
    (∀ lb, (AxOpsem.grow (gtAdGd GT) i)[kr]? = some lb → aident lb = .IRead false L.xlNp 4) →
    e ∈ @Axpol.lobp (xv6Pol GT) (gtAdGd GT) (i, kr) →
    (∀ w a v', a ∈ npb L → gwritesByte (gtAdGd GT).gdG w a v' →
      WeakRvwmoGraph.gpo (gtAdGd GT).gdG w (i, kr) → gmoLt (gtAdGd GT).gdG w (i, kr)) →
    ⊢ AxAnnot.annotOwn e (RNp L nm.xnH nm.xnM nm.xnI (gtAdGd GT) e) -∗
      @FldMW hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent (dokAtP L.xlNp 4) i
        (OLd L GT nm i e kr) lo hi := by
  intro Hoth Hkr Hin Hpo
  iintro He
  unfold FldMW
  iintro %GD %ls %k %v %base %n' %Hcs #Hg _ %Hgv %Hd %Hw
  ihave %Heq := (HGX L GT nm GD Hcs) $$ Hg
  subst Heq
  obtain ⟨⟨rfl, rfl⟩, lb, aq, Hlb, Hid⟩ := Hd
  by_cases hk : k = kr
  case neg => exact absurd rfl (Hoth k Hw hk lb aq _ _ Hlb Hid)
  subst hk
  rw [OLd, if_pos rfl]
  have Hlb' := Hkr lb Hlb
  cases lb with
  | LStore _ _ _ _ => simp [aident] at Hlb'
  | LFence _ _ _ _ => simp [aident] at Hlb'
  | LRmw _ _ _ _ _ _ _ => simp [aident] at Hlb'
  | LLoad aq' b ts vs =>
    simp only [aident, AidentT.IRead.injEq] at Hlb'
    obtain ⟨rfl, rfl, Hlen⟩ := Hlb'
    have Hl := lblOfRow _ _ _ _ Hlb
    have Hv : vs = v := by
      rw [graphValue, Hl] at Hgv
      simpa [lblValue] using Hgv
    subst Hv
    have Hl' : gxLbl (gtAdGd GT).gdG (i, k) =
        some (.LLoad false L.xlNp ts (WeakInterpProj.wbytes 4 (wordOfBytes 4 vs))) := by
      rw [wbytesWordOfBytes 4 vs Hlen]
      exact Hl
    have Hsing : ⊢ ([∗map] Rin ∈ ({[e := RNp L nm.xnH nm.xnM nm.xnI (gtAdGd GT) e]} : Mea GF),
        Rin) -∗ iprop(True ∗ RNp L nm.xnH nm.xnM nm.xnI (gtAdGd GT) e) := by
      iintro H
      ihave H2 := (BigSepM.bigSepM_singleton (M := GMapF Geid)).1 $$ H
      isplitr
      · itrivial
      · iexact H2
    have Hfe0 := fxuNpRead L GT nm HL Hcons (i, k) e ts (wordOfBytes 4 vs) iprop(True)
      ({[e := RNp L nm.xnH nm.xnM nm.xnI (gtAdGd GT) e]} : Mea GF) Hl' (a8Gmo GT e (i, k) Hin)
      Hpo
    have Hmono : ⊢ ▷ (iprop(True ∗ NPh (GF := GF) L GT nm (i, k) (wordOfBytes 4 vs) ∗
          ⌜npSrc (gtAdGd GT).gdG L (i, k) e⌝) -∗
        iprop(NPh L GT nm (i, k) (wordOfBytes 4 vs) ∗ ⌜npSrc (gtAdGd GT).gdG L (i, k) e⌝)) := by
      inext
      iintro ⟨-, H1, H2⟩
      isplitl [H1]
      · iexact H1
      · iexact H2
    ihave Hw0 := Hsing
    ihave Hfe1 := Hfe0
    ihave Hfe2 := Hfe1 $$ Hw0
    ihave Hm := Hmono
    ihave Hmn := (@flowEqDynMono hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) (gtAdGd GT) (i, k)
      (@Axpol.sPol (xv6Pol GT) (gtAdGd GT) (i, k))
      ({[e := RNp L nm.xnH nm.xnM nm.xnI (gtAdGd GT) e]} : Mea GF)
      iprop(True ∗ NPh L GT nm (i, k) (wordOfBytes 4 vs) ∗ ⌜npSrc (gtAdGd GT).gdG L (i, k) e⌝)
      iprop(NPh L GT nm (i, k) (wordOfBytes 4 vs) ∗ ⌜npSrc (gtAdGd GT).gdG L (i, k) e⌝))
    ihave Hfe := Hmn $$ Hm Hfe2
    iapply (dflowODraw L GT nm HL Hcons i k e _ (NPh L GT nm (i, k) (wordOfBytes 4 vs))
      iprop(⌜npSrc (gtAdGd GT).gdG L (i, k) e⌝) _ Hin) $$ He Hfe
    iintro H1 H2
    isplitl [H1]
    · iexact H1
    · iexact H2

/-! # 2. The nextpid write -/

/-- Rocq `OSt`: at the store `ks` with data `w8 + 1`, `RNp` and the minted fragment. -/
def OSt (i : Agent) (ks : Nat) (w8 : BitVec 32) (k : Nat) (data : List (BitVec 8)) : IProp GF :=
  if k = ks ∧ data = WeakInterpProj.wbytes 4 (w8 + one32) then
    iprop(AxAnnot.annotOwn (i, ks) (RNp L nm.xnH nm.xnM nm.xnI (gtAdGd GT) (i, ks)) ∗
      AxAnnot.annotOwn (i, ks) (FRAG nm w8))
  else iprop(True)

include HL Hcons in
/-- Rocq `FstM_np`: the CS's nextpid write at `ks`, the value handle drawn from the read `kr`. -/
theorem FstMNp (i : Agent) (kr ks : Nat) (w8 : BitVec 32) :
    kr < ks →
    (∃ ts, (AxOpsem.grow (gtAdGd GT) i)[kr]? =
      some (.LLoad false L.xlNp ts (WeakInterpProj.wbytes 4 w8))) →
    (∀ (k' : Nat) (lb : Lbl) (rl : Bool) (m : Nat), (AxOpsem.grow (gtAdGd GT) i)[k']? = some lb →
      aidentWr (aident lb) = some (rl, L.xlNp, m) → k' = ks) →
    (∃ vw cls, (AxOpsem.grow (gtAdGd GT) i)[ks]? = some (.LStore false L.xlNp vw cls) ∧
      vw.length = 4) →
    w8.toNat + 1 < 2 ^ 32 →
    ⊢ AxAnnot.annotOwn (i, kr) (NPh L GT nm (i, kr) w8) -∗
      @FstM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent (dokAtP L.xlNp 4) i
        (OSt L GT nm i ks w8) := by
  rintro Hlt ⟨ts, Hrd⟩ Hone ⟨vw, cls, Hst, Hl4⟩ Hnwr
  iintro Hh
  unfold FstM
  iintro %GD %ls %k %data %base %n %Hcs #Hg _ %Hgd %Hd
  ihave %Heq := (HGX L GT nm GD Hcs) $$ Hg
  subst Heq
  obtain ⟨⟨rfl, -⟩, lb, rl, Hlb, Hid⟩ := Hd
  obtain rfl : k = ks := Hone k lb rl _ Hlb Hid
  have Hls := lblOfRow _ _ _ _ Hst
  have Hvw : data = vw := by
    rw [graphData, Hls] at Hgd
    simpa [lblData] using Hgd.symm
  subst Hvw
  have Hlr := lblOfRow _ _ _ _ Hrd
  -- the read is a lob-predecessor of the store (ppo rule 1, same address)
  have Hin : (i, kr) ∈ @Axpol.lobp (xv6Pol GT) (gtAdGd GT) (i, k) := by
    obtain ⟨t0, Ht0⟩ := loadnReads (gtAdGd GT).gdG Hcons.1 (i, kr) L.xlNp ts 4 w8 0 Hlr
      (by omega)
    have Hw2 := (gwbStoren _ _ _ _ _ Hls).1
    have hb : data[0]? = some (data[0]'(by omega)) := List.getElem?_eq_getElem _
    exact locLobp (gtAdGd GT) Hcons (i, kr) (i, k) _ _ _ Hlr rfl
      (gpoRow (gtAdGd GT) i kr k _ _ Hlr Hls Hlt) (Or.inr ⟨t0, _, Ht0⟩) (Hw2 0 _ hb)
  by_cases hd : data = WeakInterpProj.wbytes 4 (w8 + one32)
  · subst hd
    rw [OSt, if_pos ⟨rfl, rfl⟩]
    have Hsing : ⊢ ([∗map] Rin ∈ ({[(i, kr) := NPh L GT nm (i, kr) w8]} : Mea GF), Rin) -∗
        iprop(True ∗ NPh L GT nm (i, kr) w8) := by
      iintro H
      ihave H2 := (BigSepM.bigSepM_singleton (M := GMapF Geid)).1 $$ H
      isplitr
      · itrivial
      · iexact H2
    have Hfe0 := fxuNpIncr L GT nm HL Hcons (i, k) (i, kr) w8 cls iprop(True)
      ({[(i, kr) := NPh L GT nm (i, kr) w8]} : Mea GF) Hls (a8Gmo GT _ _ Hin) Hnwr
    have Hmono : ⊢ ▷ (iprop(True ∗ RNp (GF := GF) L nm.xnH nm.xnM nm.xnI (gtAdGd GT) (i, k) ∗ FRAG nm w8) -∗
        iprop(RNp L nm.xnH nm.xnM nm.xnI (gtAdGd GT) (i, k) ∗ FRAG nm w8)) := by
      inext
      iintro ⟨-, H1, H2⟩
      isplitl [H1]
      · iexact H1
      · iexact H2
    ihave Hw0 := Hsing
    ihave Hfe1 := Hfe0
    ihave Hfe2 := Hfe1 $$ Hw0
    ihave Hm := Hmono
    ihave Hmn := (@flowEqDynMono hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) (gtAdGd GT) (i, k)
      (@Axpol.sPol (xv6Pol GT) (gtAdGd GT) (i, k))
      ({[(i, kr) := NPh L GT nm (i, kr) w8]} : Mea GF)
      iprop(True ∗ RNp L nm.xnH nm.xnM nm.xnI (gtAdGd GT) (i, k) ∗ FRAG nm w8)
      iprop(RNp L nm.xnH nm.xnM nm.xnI (gtAdGd GT) (i, k) ∗ FRAG nm w8))
    ihave Hfe := Hmn $$ Hm Hfe2
    iapply (dflowODraw L GT nm HL Hcons i k (i, kr) _
      (RNp L nm.xnH nm.xnM nm.xnI (gtAdGd GT) (i, k)) (FRAG nm w8) _ Hin) $$ Hh Hfe
    iintro H1 H2
    isplitl [H1]
    · iexact H1
    · iexact H2
  · rw [OSt, if_neg (fun h => hd h.2)]
    obtain ⟨Hwb, Hsg⟩ := gwbStoren _ _ _ _ _ Hls
    have Hlen : data.length = (npb L).length := by simp [npb, clRange, Hl4]
    have Honly : ∀ a v', gwritesByte (gtAdGd GT).gdG (i, k) a v' → a ∈ npb L := by
      intro a v' Hw
      obtain ⟨j, Hj, rfl⟩ := Hsg a v' Hw
      have hj := (List.getElem?_eq_some_iff.1 Hj).1
      unfold npb
      rw [inClr]
      omega
    have Hall : ∀ (j : Nat) a v, (npb L)[j]? = some a → data[j]? = some v →
        gwritesByte (gtAdGd GT).gdG (i, k) a v := by
      intro j a v Hj Hv
      have Hj' : (clRange L.xlNp 4)[j]? = some a := Hj
      obtain ⟨rfl, -⟩ := AxSpinX4.clRangeLookup _ _ _ _ Hj'
      exact Hwb j v Hv
    have Hok : cpuOk (clb L) cvx (gtAdGd GT).gdG (i, k) := by
      apply cpuOkNw
      intro a v Ha Hw
      exact clbNpbDisj L HL a Ha (Honly a v Hw)
    have Hisw : gisW (gtAdGd GT).gdG (i, k) = true := by unfold gisW; rw [Hls]; rfl
    have Hsing : ⊢ ([∗map] Rin ∈ ({[(i, kr) := NPh L GT nm (i, kr) w8]} : Mea GF), Rin) -∗
        iprop(True ∗ ∃ vold, RVL nm.xnH (gtAdGd GT) (npb L) (i, kr) vold) := by
      iintro H
      ihave H2 := (BigSepM.bigSepM_singleton (M := GMapF Geid)).1 $$ H
      unfold NPh RNpv
      icases H2 with ⟨%v, ⟨%_, HR, _, _⟩, _⟩
      isplitr
      · itrivial
      · iexists _
        iexact HR
    have Hfe0 := fxRVLWrite L GT nm HL Hcons (i, k) (i, kr) (npb L) data iprop(True)
      ({[(i, kr) := NPh L GT nm (i, kr) w8]} : Mea GF) Hisw (a8Gmo GT _ _ Hin) Hlen Hall Honly
      (npbXO L) Hok (AxSpinX2.clFullNpb L HL _ (i, k) Honly)
    ihave Hw0 := Hsing
    ihave Hfe1 := Hfe0
    ihave Hfe := Hfe1 $$ Hw0
    iapply (dflowODraw L GT nm HL Hcons i k (i, kr) _ iprop(True)
      (RVL nm.xnH (gtAdGd GT) (npb L) (i, k) data) _ Hin) $$ Hh Hfe
    iintro - -
    itrivial

/-! # NEW (Q18a): the value-agnostic read flow of the scan -/

include HL Hcons in
/-- (Lean-only, ruling Q18a) A VALUE-AGNOSTIC read flow for any plain read in the window
`[lo, hi)`: no ownership drawn, nothing deposited (`fxRead`).  Window form of
`AxSpinHdB.FldMFrame` (the no-RMW premise only on the window). -/
theorem AxSpinAp8.FldMWFrame (i : Agent) (pa : Int) (n lo hi : Nat) :
    (∀ (k' : Nat) (lb : Lbl) (aq rl : Bool) (m : Nat), lo ≤ k' ∧ k' < hi →
      (AxOpsem.grow (gtAdGd GT) i)[k']? = some lb → aident lb = .IRmw aq rl pa m → m ≠ n) →
    ⊢ @FldMW hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent (dokAtP pa n) i
        (fun _ _ => iprop(True)) lo hi := by
  intro Hnormw
  unfold FldMW
  iintro %GD %ls %k %v %base %n' %Hc #Hg _ %Hgv %Hd %Hw
  ihave %Heq := (HGX L GT nm GD Hc) $$ Hg
  subst Heq
  obtain ⟨⟨rfl, rfl⟩, lb, aq, Hlb, Hid⟩ := Hd
  have Hnw : gisW (gtAdGd GT).gdG (i, k) = false := by
    cases lb with
    | LLoad aq' b ts vs => exact nwOfLoad GT i k aq' b ts vs Hlb
    | LStore _ _ _ _ => simp [aident, aidentRd] at Hid
    | LFence _ _ _ _ => simp [aident, aidentRd] at Hid
    | LRmw aq' rl b ts rvs wvs cls =>
      simp only [aident, aidentRd, Option.some.injEq, Prod.mk.injEq] at Hid
      obtain ⟨rfl, rfl, Hn⟩ := Hid
      exact absurd Hn (Hnormw k _ aq' rl wvs.length Hw Hlb rfl)
  ihave Hfe := fxRead L GT nm HL Hcons (i, k) Hnw
  iapply (dflowOPlain L GT nm i k iprop(True) iprop(True)) $$ Hfe
  iintro -
  itrivial

include HL Hcons in
/-- (Lean-only, ruling Q18a) The flow of the `j`-th scan read (`c.lw a4,48(a5)`, +0x74, of
`proc[j].pid`) at its row position `k + 1 + j` of `AxSpinAp7.RowAllocpidBody`, window
`[k + 1 + j, k + 1 + j + 1)` (as `AxSpinXP2.XxLdW` consumes it). -/
theorem AxSpinAp8.FldMWScan (i : Agent) (k : Nat) (pnp ppid : Int)
    (HR : RowAllocpidBody k (AxOpsem.grow (gtAdGd GT) i) pnp ppid) (j : Nat) (hj : j < 64) :
    ⊢ @FldMW hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent
        (dokAtP (AxSpinAp7.scanAddr j) 4) i (fun _ _ => iprop(True)) (k + 1 + j) (k + 1 + j + 1) :=
  AxSpinAp8.FldMWFrame L GT nm HL Hcons i _ 4 _ _ (by
    intro k' lb aq rl m Hw Hlb Hid
    obtain rfl : k' = k + 1 + j := by omega
    rw [HR.2.2 j hj lb Hlb] at Hid
    cases Hid)

end flows

/-! # 3. The positional store leaf over any `FstM` -/

section stF
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
variable (Ψ : Athread → IProp GF)
variable (HΨmid : ∀ s, midState s → s.atK = (AxOpsem.grow (gtAdGd GT) i).length →
  ⊢ @postLifting GF (AxSpinX2.xG L GT nm) Ψ i s)

/-- Rocq `OutW`: the store's output, with the row facts that locate the event. -/
def OutW (pa : Int) (Out : Nat → List (BitVec 8) → IProp GF) (k : Nat)
    (data : List (BitVec 8)) : IProp GF :=
  iprop(⌜graphData (gtAdGd GT) (i, k) = some data ∧
    ∃ lb rl, (AxOpsem.grow (gtAdGd GT) i)[k]? = some lb ∧
      aidentWr (aident lb) = some (rl, pa, data.length)⌝ ∗ Out k data)

/-- Rocq `FstM_rowW`. -/
theorem FstMRowW (pa : Int) (n : Nat) (Out : Nat → List (BitVec 8) → IProp GF) :
    ⊢ @FstM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent (dokAtP pa n) i Out -∗
      @FstM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent (dokAtP pa n) i
        (OutW GT i pa Out) := by
  iintro F
  unfold FstM
  iintro %GD %ls %k %data %base %n' %Hc #Hg Hloc %Hgd %Hd
  ihave %Heq := (HGX L GT nm GD Hc) $$ Hg
  subst Heq
  obtain ⟨⟨rfl, rfl⟩, Hrw⟩ := Hd
  ihave F2 := F $$ %(gtAdGd GT) %ls %k %data %base %n' %Hc Hg Hloc %Hgd %⟨⟨rfl, rfl⟩, Hrw⟩
  iapply (dflowOMonoP L GT nm i (gtAdGd GT) k _ _) $$ [] F2
  iintro HO
  unfold OutW
  isplitr
  · ipureintro
    exact ⟨Hgd, Hrw⟩
  · iexact HO

include HL Hcons hmode hasid hppn Hfix HΨmid in
/-- Rocq `Xx_stF`: `XxSt` over any store flow `FstM` (width `w`).  Stage C: the store is AT `k`
(Rocq `S k`), the continuation at `k + 1` (Rocq `k + 2`), premise `k + 1 ≤ LEN`; Rocq's `Hnw`
is DROPPED (deviation 1). -/
theorem XxStF (s : Athread) (rs : RegFile) (k : Nat) (pc : BitVec 64) (is_rvc : Bool)
    (imm : BitVec 12) (rs2 rs1 : BitVec 5) (w : Nat) (va pa : BitVec 64)
    (Out : Nat → List (BitVec 8) → IProp GF) :
    RetX cpu rs k s → ctrlOkSW T satp0 rs → rs .PC = pc → hitW rs pc →
    textOkB σi T satp0 pc is_rvc (.STORE (imm, .Regidx rs2, .Regidx rs1, w)) →
    vmemWidth w → 1 ≤ w → w ≤ 8 →
    va = gprVal rs rs1 + sign_extend (m := 64) imm →
    dataAtS σi T (.Store .Data) va w pa → hitW rs va →
    k + 1 ≤ (AxOpsem.grow (gtAdGd GT) i).length →
    ⊢ @FstM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent (dokAtP (paZ pa) w) i
        Out -∗
      (∀ (rs' : RegFile) (ib' : Ibch), ⌜GoodB T satp0 rs pc is_rvc none none rs'⌝ -∗
        ⌜graphData (gtAdGd GT) (i, k) = some (stBytes w (gprVal rs rs2))⌝ -∗
        Out k (stBytes w (gprVal rs rs2)) -∗
        @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
          ⟨.PHart cpu (.pure ()) rs' none ib', k + 1⟩ Ψ) -∗
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i s Ψ := by
  intro HRet Hc HPC Hhit Htx Hvw Hw1 Hw8 Hva Hda Hhv Hle
  have H := @XBk hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) σi T satp0 hmode hasid hppn i cpu
    (fun GD => GD = gtAdGd GT) (HGX L GT nm) (AxOpsem.grow (gtAdGd GT) i).length (HL0 GT i)
    (HGex0 GT) Ψ (AxSpinE6.Hmid0 L GT nm i Ψ HΨmid) (HtextX L GT nm (imgS σi) i Hfix)
    (HflowX L GT nm HL Hcons (imgS σi) i) (HlocX L GT nm i)
    (dokAtP (paZ pa) w) .DKSt (by intro h; cases h) (by intro h; cases h)
    (OutW GT i (paZ pa) Out)
    s rs k pc is_rvc _ 1 none (fun _ => none) .CPend false _
    HRet Hc HPC Hhit Htx (fun _ _ _ => trivial)
    (CertBStoreS σi T satp0 hmode hasid hppn (dokAtP (paZ pa) w) rs pc is_rvc imm rs2 rs1 w va pa
      false Hvw Hw1 Hw8 Hva Hda Hhv ⟨rfl, rfl⟩)
    (by omega) Hle
  iintro F C
  iapply H $$ [F] [C]
  · simp only [CResK, CFkM]
    iapply (FstMRowW L GT nm i (paZ pa) w Out)
    iexact F
  · iintro %d %r %rs' %ib' %HPX %HGB HO
    obtain ⟨rfl, rfl⟩ := HPX
    simp only [CResK]
    icases HO with ⟨%kd, %Hkd, HO⟩
    obtain rfl : kd = k := by omega
    unfold OutW
    icases HO with ⟨%Hgd, HO⟩
    iapply C $$ %rs' %ib' %HGB %Hgd.1 HO

end stF

end Weak
