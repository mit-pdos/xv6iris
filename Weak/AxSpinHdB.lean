/-
Weak: **PHASE 5, stage 3: holding's TWO CALL SITES** as two instantiations of the one theorem
`AxSpinHdA.wpdHolding`, and the PROTOCOL READ RULES of the two shared loads as flow resources
(`AxSymMem.FldM`) at the joint instance Ixv6.

Rocq: `iris/AxSpinHdB.v` @ xxvzwolszwmp.

## The Rocq header, in substance

§1 FLOW RESOURCES (each a rule of AxSpinX2 packaged for `AxSpinHd7.XxLdO`; `Hnormw`: no RMW row
item of hart `i` at the read's address and width — the ROW item is then a plain load, hence not a
write, `rdPlain` / `nwOfLoad`):
* `FldMFrame` — any plain read, nothing deposited (`fxRead`): the NON-HOLDER's lw of
  `lk->locked` (acquire);
* `FldMRacy` — the NON-HOLDER's ld of `lk->cpu` (`fxCpuRacy`): deposits Φ_cpu's `rdFact` at the
  read (`ORacy`; Lean-only, Q-S2-B: `AxSpinX2.fxCpuRacyS`, also `clSrcFull` — see deviation 4);
* `FldMLkheld` — the HOLDER's lw of `lk->locked` (`fxLkreadHeld`, `locked` drawn from the claim's
  annotation, ppo rule 5): deposits `locked ∗ Q` back and ⌜every byte read at lk ≠ 0⌝ at the read
  (`OHeld`);
* `FldMCpuOwn` — the HOLDER's ld of `lk->cpu` after its own `sd lk->cpu ← val` (the gmo split
  inside: `fxOwnedRead` drawing the last-value handle, or `fxFwdRead` forwarding): deposits ⌜the
  bytes read = val's bytes⌝ at the read (`OOwn`).
Each is position-generic (a `FldM` holds at every row position) with the real rule at the
designated read position `kr` and the frame rule elsewhere.  The plumbing: `dflowOPlain` (a flow
with no draw) and `dflowODraw` (a flow drawing a lob-predecessor's annotation, split in two).

§2 THE CALL SITES.  `holdingFromAcquire` — acquire+0x12 `jal holding`, return to `pac 0x16`, ANY
path `hb`; the lk->cpu leaf is BUILT here from `XxLdO` + `FldMRacy` (`XCpuOf`); the lock-word
leaf (output: frame) is a PREMISE.  `holdingFromRelease` — release+0x0c `jal holding`, return to
`prl 0x10`, the holder's path `hb = true`; the lk->cpu leaf is BUILT from `XxLdO` +
`FldMCpuOwn`; the lock-word leaf (output: `OHeld`) is a PREMISE.  `XLkOf` builds the lock-word
leaf from any flow resource UNDER the engine's global no-RMW premise (false on real rows, which
contain acquire's `amoswap.w.aq lk`: the OPEN ENGINE ISSUE of the Rocq header; the positional
fix is AxSpinXP / AxSpinHdC).

## Deviations from Rocq

1. O2 STAGE C / Q20' (provisional Option V; as `AxSpinHd7` deviation 1 and `AxSpinHdA`
   deviation 1): a fetch consumes no row item.
   * `XLkOf` concludes `XLd … k … (Out k)` (Rocq `Out (S k)`); `XCpuOf` is the leaf at
     `k + 4` with `Out (k + 4)` (Rocq `k + 11`, `Out (k + 12)`).  Rocq's fetch premise `Hnrk`
     of both is DROPPED (as `AxSpinHd7.XxLdO`).
   * The call sites: `ORacy L GT i (k + 4)` (Rocq `k + 12`), `OHeld … kc k Qc k` (Rocq
     `kc (k+1) Qc (k+1)`), `OOwn … kw (k + 4) val Qw (k + 4)` (Rocq `k + 12`), `kw < k + 4`
     and `Hnoint` at `(i, k + 4)` (Rocq `k + 12`).
   * The call sites drop the parameters `pretm`/`pret` and the premises `Hinjm`/`Hstvm`/`Hinj`/
     `Hstv` (+ the section context `stv` / `va_first_read`), as `wpdHolding`; NEW premise (the
     graph-value pin of `wpdHolding`, its `jalrTgt 0#12 ret = ret` conjunct discharged by
     `decide` at the literal return address): acquire `if hb then graphValue GD0 (i, k + 7) =
     some (stBytes 8 (pch 0x1a)) ∧ graphValue GD0 (i, k + 9) = some (stBytes 8 (pac 0x16))
     else jalrTgt 0#12 (gprVal rs0 ra) = pac 0x16`; release the two long-path conjuncts at
     `prl 0x10`.  Rocq's `nret` argument (2) is gone with `RowHolding`'s.
2. TYPES / INSTANCES (as `AxSpinHdA` deviations 2–3): `invGS_gen HasNoLc Σ` ↦
   `[InvGS_gen hlc GF]` (any `hlc`); `xv6G Σ` ↦ `[AxSpinX.Xv6G GF]`; the local instances
   `hB_pol`/`hB_G` are inlined as `xv6Pol GT` / `AxSpinX2.xG L GT nm`; `mword_of_int` ↦
   `BitVec.ofInt`, `uint` ↦ `paZ`, `B0` ↦ `b0`, `l !! k` ↦ `l[k]?`, `decide (k = kr)` ↦
   `if k = kr`.  Section variables are explicit leading arguments where Rocq's section mechanism
   includes them (`rdPlain GT`, `nwOfLoad GT`, `dflowOPlain L GT nm`, `dflowODraw L GT nm HL
   Hcons`, `ORacy L GT`, `OHeld L GT nm`, `OOwn L GT nm`, the `FldM*` rules `L GT nm HL Hcons`,
   §2 as `AxSpinHdA.wpdHolding`).
3. The trailing `Print Assumptions` lines are not ported (the lint's axiom check covers them).
4. Q-S2-B (owner ruling 2026-10-08, protocol full-width lk->cpu writes): `ORacy` deposits
   `rdFact ∧ clSrcFull L G (i, k)` (Rocq: `rdFact` only); `FldMRacy` runs
   `AxSpinX2.fxCpuRacyS` (Rocq `fx_cpu_racy`).  `clSrcFull` comes from `protXv6`'s new σ
   conjunct `CLFULL` (AxSpinX deviation 8).

**Rocq → Lean name map.**  `pac` `AxSpinHdB.pac`, `prl` `AxSpinHdB.prl` (short generic names:
file-qualified; not in the duplicated-name table), `rd_plain` `rdPlain`, `nw_of_load`
`nwOfLoad`, `dflowO_plain` `dflowOPlain`, `dflowO_draw` `dflowODraw`, `FldM_frame` `FldMFrame`,
`ORacy` `ORacy`, `FldM_racy` `FldMRacy`, `OHeld` `OHeld`, `FldM_lkheld` `FldMLkheld`, `OOwn`
`OOwn`, `FldM_cpu_own` `FldMCpuOwn`, `XLk_of` `XLkOf`, `XCpu_of` `XCpuOf`, `holding_from_acquire`
`holdingFromAcquire`, `holding_from_release` `holdingFromRelease`.  No Lean-only declarations.

**Dropped:** `fetch11` (the row item at `k+11` is a 2-byte FETCH — Stage C: no fetch row item;
its only use was `XCpu_of`'s `Hnrk`, dropped with it; no other weak file uses it).  Rocq 18
definitions/lemmas (+ 2 local instances, inlined); Lean 17.
-/
import Weak.AxSpinHdA
import Weak.AxSpinHd2b
import Weak.AxSpinHd3
import Weak.AxSpinHd7
import Weak.AxSpinU
import Weak.AxGraphDec

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-- Rocq `pac`: an address in `acquire`. -/
def AxSpinHdB.pac (off : Int) : BitVec 64 :=
  BitVec.ofInt 64 ((KernelSyms.«acquire» : Int) + off)
/-- Rocq `prl`: an address in `release`. -/
def AxSpinHdB.prl (off : Int) : BitVec 64 :=
  BitVec.ofInt 64 ((KernelSyms.«release» : Int) + off)

/-! # 1. Flow resources -/

section flows
variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF] [AxannotGS GF]
  [AxSpinX.Xv6G GF]
variable (L : Xlay) (GT : GdexecT) (nm : Xv6N)
variable (HL : xlayOk L) (Hcons : rvwmoCatConsistent (gtAdGd GT))

/-- Rocq `rd_plain`: the row item of a `FldM` read is a plain load when no RMW of hart `i`
targets its (address, width). -/
theorem rdPlain (i : Agent) (pa : Int) (n k : Nat) :
    (∀ (k' : Nat) (lb : Lbl) (aq rl : Bool) (m : Nat),
      (AxOpsem.grow (gtAdGd GT) i)[k']? = some lb → aident lb = .IRmw aq rl pa m → m ≠ n) →
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
    exact absurd Hn (Hnormw k _ aq' rl wvs.length Hlb rfl)

/-- Rocq `nw_of_load`. -/
theorem nwOfLoad (i : Agent) (k : Nat) (aq : Bool) (pa : Int) (ts : List Nat)
    (vs : List (BitVec 8)) :
    (AxOpsem.grow (gtAdGd GT) i)[k]? = some (Lbl.LLoad aq pa ts vs) →
    gisW (gtAdGd GT).gdG (i, k) = false := by
  intro Hlb
  unfold gisW
  rw [lblOfRow _ _ _ _ Hlb]
  rfl

/-- Rocq `dflowO_plain`: a flow with no draw (the frame rule's shape for any flow equation). -/
theorem dflowOPlain (i : Agent) (k : Nat) (R O : IProp GF) :
    ⊢ @flowEqDyn hlc GF _ (AxSpinX2.xG L GT nm) (gtAdGd GT) (i, k)
        (@Axpol.sPol (xv6Pol GT) (gtAdGd GT) (i, k)) (∅ : Mea GF) R -∗
      (AxAnnot.annotOwn (i, k) R -∗ O) -∗
      @dflowO hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) i (gtAdGd GT) k O := by
  iintro Hfe HO
  unfold dflowO
  iintro %na ⟨Hpg, Hannot⟩
  ihave %Hnin := naAtProgressNotElemOf (gtAdGd GT) i k na $$ Hpg
  imod annotAlloc na (i, k) R Hnin $$ Hannot with ⟨Hannot, Hh⟩
  imodintro
  inext
  imodintro
  iexists R, (∅ : Mea GF), (∅ : Mea GF), (() : Unit)
  isplitr
  · iapply (naWfEmpty L GT nm (i, k) na)
  isplitl [Hfe]
  · iexact Hfe
  isplitl [Hannot]
  · rw [AxLockWp.annotInsertEq na (i, k) R]
    iexact Hannot
  isplitr
  · iapply (AxSpinWit.localTrue (gtAdGd GT) Xv6N Unit (protXv6 L) nm (gtAdGd GT) i (k + 1) ())
  · iapply HO $$ Hh

set_option linter.unusedSectionVars false in
include HL Hcons in
/-- Rocq `dflowO_draw` (`HL Hcons` kept in the signature, as Rocq's `Proof using`): a flow DRAWING a lob-predecessor's annotation (`AxSpinProt3.evDraw`'s
plumbing, in `dflowO` form); the new annotation is split in two. -/
theorem dflowODraw (i : Agent) (k : Nat) (e' : Geid) (P R1 R2 O : IProp GF) :
    e' ∈ @Axpol.lobp (xv6Pol GT) (gtAdGd GT) (i, k) →
    ⊢ AxAnnot.annotOwn e' P -∗
      @flowEqDyn hlc GF _ (AxSpinX2.xG L GT nm) (gtAdGd GT) (i, k)
        (@Axpol.sPol (xv6Pol GT) (gtAdGd GT) (i, k)) ({[e' := P]} : Mea GF) iprop(R1 ∗ R2) -∗
      (AxAnnot.annotOwn (i, k) R1 -∗ AxAnnot.annotOwn (i, k) R2 -∗ O) -∗
      @dflowO hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) i (gtAdGd GT) k O := by
  intro Hin
  iintro Hp Hfe HO
  unfold dflowO naAtProgress
  iintro %na ⟨%Hprog, Hannot⟩
  have Hb := xv6AxpolWf GT (gtAdGd GT) i k e' Hin
  have Hdom : e' ∈ (FiniteMap.dom_set na : GSet Geid) := by
    rw [← Hprog] at Hb
    exact (elemOfFilter.1 Hb).2
  have Hnin : (i, k) ∉ (FiniteMap.dom_set na : GSet Geid) := by
    intro Hd
    have Hf : (i, k) ∈ FiniteSet.filter (fun e : Geid => decide (e.1 = i))
        (FiniteMap.dom_set na : GSet Geid) := elemOfFilter.2 ⟨by simp, Hd⟩
    rw [Hprog, elemOfEidsBefore] at Hf
    exact Nat.lt_irrefl _ Hf.2.1
  obtain ⟨P0, HP0⟩ := Option.isSome_iff_exists.1 (elemOfDom.1 Hdom)
  have Hdet : ⊢ AxAnnot.annotInterp na -∗ AxAnnot.annotOwn e' P ==∗
      ∃ Rr, AxAnnot.annotInterp (insert na e' Rr) ∗ iprop(▷ □ (P0 -∗ P ∗ Rr)) := by
    have h := annotDetach na e' P
    rw [HP0] at h
    exact h
  imod Hdet $$ Hannot Hp with ⟨%Rr, Hannot, #Hwand⟩
  have Hnin' : (i, k) ∉ (FiniteMap.dom_set (insert na e' Rr) : GSet Geid) := by
    rw [domInsert, elemOfUnion, elemOfSingleton]
    rintro (Heq | Hik)
    · subst Heq
      exact Hnin (elemOfDom.2 (by rw [HP0]; rfl))
    · exact Hnin Hik
  imod annotAlloc (insert na e' Rr) (i, k) iprop(R1 ∗ R2) Hnin' $$ Hannot with ⟨Hannot, Hfrag⟩
  imod (annotSplit (i, k) R1 R2) $$ Hfrag %_ Hannot with ⟨⟨Hf1, Hf2⟩, Hannot⟩
  imodintro
  inext
  imodintro
  iexists iprop(R1 ∗ R2), ({[e' := P]} : Mea GF), ({[e' := Rr]} : Mea GF), (() : Unit)
  isplitr
  · unfold naSplittingWf
    isplitr
    · ipureintro
      rw [domSingleton]
      exact singletonSubseteqL.2 Hin
    · iapply (BigSepM2.bigSepM2_singleton _ e' P Rr).2
      simp only [HP0, AxWp.fromOption]
      iexact Hwand
  isplitl [Hfe]
  · iexact Hfe
  isplitl [Hannot]
  · rw [← AxSpinProt3.annotEq]
    iexact Hannot
  isplitr
  · iapply (AxSpinWit.localTrue (gtAdGd GT) Xv6N Unit (protXv6 L) nm (gtAdGd GT) i (k + 1) ())
  · iapply HO $$ Hf1 Hf2

include HL Hcons in
/-- Rocq `FldM_frame`: nothing deposited. -/
theorem FldMFrame (i : Agent) (pa : Int) (n : Nat) :
    (∀ (k' : Nat) (lb : Lbl) (aq rl : Bool) (m : Nat),
      (AxOpsem.grow (gtAdGd GT) i)[k']? = some lb → aident lb = .IRmw aq rl pa m → m ≠ n) →
    ⊢ @FldM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent (dokAt pa n) i
        (fun _ _ => iprop(True)) := by
  intro Hnormw
  unfold FldM
  iintro %GD %ls %k %v %base %n' %Hc #Hg _ %Hgv %Hd
  ihave %Heq := (HGX L GT nm GD Hc) $$ Hg
  subst Heq
  obtain ⟨⟨rfl, rfl⟩, Hrd⟩ := Hd
  obtain ⟨aq, ts, vs, Hlb, -⟩ := rdPlain GT i _ _ k Hnormw Hrd
  ihave Hfe := fxRead L GT nm HL Hcons (i, k) (nwOfLoad GT i k _ _ _ _ Hlb)
  iapply (dflowOPlain L GT nm i k iprop(True) iprop(True)) $$ Hfe
  iintro -
  itrivial

/-- Rocq `ORacy`: the racy read's deposit, Φ_cpu's `rdFact` at the read — and (Lean-only,
Q-S2-B) `clSrcFull`: its gmo-earlier lk->cpu sources are full-width (`AxSpinX2.fxCpuRacyS`). -/
def ORacy (i : Agent) (k : Nat) (_v : List (BitVec 8)) : IProp GF :=
  AxAnnot.annotOwn (i, k)
    iprop(⌜rdFact (clb L) cvx (gtAdGd GT).gdG (i, k) ∧ clSrcFull L (gtAdGd GT).gdG (i, k)⌝)

include HL Hcons in
/-- Rocq `FldM_racy`: the non-holder's lk->cpu read deposits Φ_cpu's `rdFact` (and, Lean-only,
`clSrcFull`). -/
theorem FldMRacy (i : Agent) (pa : Int) (n : Nat) :
    (∀ (k' : Nat) (lb : Lbl) (aq rl : Bool) (m : Nat),
      (AxOpsem.grow (gtAdGd GT) i)[k']? = some lb → aident lb = .IRmw aq rl pa m → m ≠ n) →
    ⊢ @FldM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent (dokAt pa n) i
        (ORacy L GT i) := by
  intro Hnormw
  unfold FldM
  iintro %GD %ls %k %v %base %n' %Hc #Hg _ %Hgv %Hd
  ihave %Heq := (HGX L GT nm GD Hc) $$ Hg
  subst Heq
  obtain ⟨⟨rfl, rfl⟩, Hrd⟩ := Hd
  obtain ⟨aq, ts, vs, Hlb, -⟩ := rdPlain GT i _ _ k Hnormw Hrd
  ihave Hfe := AxSpinX2.fxCpuRacyS L GT nm HL Hcons (i, k) (nwOfLoad GT i k _ _ _ _ Hlb)
  iapply (dflowOPlain L GT nm i k _ _) $$ Hfe
  iintro H
  unfold ORacy
  iexact H

/-- Rocq `OHeld`: the holder's lock-word read output — at `kr` the claim's `locked ∗ Q` moved
to the read plus ⌜every byte read ≠ 0⌝; elsewhere the claim annotation handed back. -/
def OHeld (i : Agent) (kc kr : Nat) (Q : IProp GF) (k : Nat) (_v : List (BitVec 8)) :
    IProp GF :=
  if k = kr then
    iprop(AxAnnot.annotOwn (i, kr) iprop(locked nm.xnReg L.xlLk i (i, kc) ∗ Q) ∗
      AxAnnot.annotOwn (i, kr)
        iprop(⌜∀ t b, greadsByte (gtAdGd GT).gdG (i, kr) L.xlLk t b → b ≠ b0⌝))
  else AxAnnot.annotOwn (i, kc) iprop(locked nm.xnReg L.xlLk i (i, kc) ∗ Q)

include HL Hcons in
/-- Rocq `FldM_lkheld`: the holder's lock-word read at `kr`, `locked` drawn from the claim
`kc`. -/
theorem FldMLkheld (i : Agent) (pa : Int) (kc kr : Nat) (rvs wvs : List (BitVec 8))
    (ts : List Nat) (cls : WmClass) (Q : IProp GF) :
    (∀ (k' : Nat) (lb : Lbl) (aq rl : Bool) (m : Nat),
      (AxOpsem.grow (gtAdGd GT) i)[k']? = some lb → aident lb = .IRmw aq rl pa m → m ≠ 4) →
    (AxOpsem.grow (gtAdGd GT) i)[kc]? = some (Lbl.LRmw true false L.xlLk ts rvs wvs cls) →
    kc < kr →
    nolk L.xlLk (gtAdGd GT).gdG (i, kc) (i, kr) →
    ⊢ AxAnnot.annotOwn (i, kc) iprop(locked nm.xnReg L.xlLk i (i, kc) ∗ Q) -∗
      @FldM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent (dokAt pa 4) i
        (OHeld L GT nm i kc kr Q) := by
  intro Hnormw Hc Hlt Hnl
  iintro Hh
  unfold FldM
  iintro %GD %ls %k %v %base %n' %Hcs #Hg _ %Hgv %Hd
  ihave %Heq := (HGX L GT nm GD Hcs) $$ Hg
  subst Heq
  obtain ⟨⟨rfl, rfl⟩, Hrd⟩ := Hd
  obtain ⟨aq, ts', vs, Hlb, -⟩ := rdPlain GT i _ _ k Hnormw Hrd
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

/-- Rocq `OOwn`: the holder's owned lk->cpu read output — at `kr` the last-value handle (at the
store `kw` or moved to the read) plus ⌜the bytes read = val's bytes⌝; elsewhere the handle back. -/
def OOwn (i : Agent) (kw kr : Nat) (val : BitVec 64) (Q : IProp GF) (k : Nat)
    (_v : List (BitVec 8)) : IProp GF :=
  if k = kr then
    iprop((∃ e' : Geid, ⌜e' = (i, kw) ∨ e' = (i, kr)⌝ ∗
        AxAnnot.annotOwn e'
          iprop(Q ∗ RVL nm.xnH (gtAdGd GT) (clb L) e' (WeakInterpProj.wbytes 8 val))) ∗
      AxAnnot.annotOwn (i, kr)
        iprop(⌜∀ (j : Nat) a t b, (clb L)[j]? = some a →
          greadsByte (gtAdGd GT).gdG (i, kr) a t b →
          (WeakInterpProj.wbytes 8 val)[j]? = some b⌝))
  else AxAnnot.annotOwn (i, kw)
    iprop(Q ∗ RVL nm.xnH (gtAdGd GT) (clb L) (i, kw) (WeakInterpProj.wbytes 8 val))

include HL Hcons in
/-- Rocq `FldM_cpu_own`: the holder's lk->cpu read at `kr` after its own `sd lk->cpu ← val` at
`kw`. -/
theorem FldMCpuOwn (i : Agent) (kw kr : Nat) (val : BitVec 64) (cls : WmClass) (Q : IProp GF) :
    (∀ (k' : Nat) (lb : Lbl) (aq rl : Bool) (m : Nat),
      (AxOpsem.grow (gtAdGd GT) i)[k']? = some lb →
      aident lb = .IRmw aq rl (L.xlLk + 16) m → m ≠ 8) →
    (AxOpsem.grow (gtAdGd GT) i)[kw]? =
      some (Lbl.LStore false (L.xlLk + 16) (WeakInterpProj.wbytes 8 val) cls) →
    kw < kr →
    (∀ w a v', a ∈ clb L → gwritesByte (gtAdGd GT).gdG w a v' →
      WeakRvwmoGraph.gpo (gtAdGd GT).gdG (i, kw) w →
      WeakRvwmoGraph.gpo (gtAdGd GT).gdG w (i, kr) → False) →
    ⊢ AxAnnot.annotOwn (i, kw)
        iprop(Q ∗ RVL nm.xnH (gtAdGd GT) (clb L) (i, kw) (WeakInterpProj.wbytes 8 val)) -∗
      @FldM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent
        (dokAt (L.xlLk + 16) 8) i (OOwn L GT nm i kw kr val Q) := by
  intro Hnormw Hw Hlt Hnoint
  iintro Hh
  unfold FldM
  iintro %GD %ls %k %v %base %n' %Hcs #Hg _ %Hgv %Hd
  ihave %Heq := (HGX L GT nm GD Hcs) $$ Hg
  subst Heq
  obtain ⟨⟨rfl, rfl⟩, Hrd⟩ := Hd
  obtain ⟨aq, ts, vs, Hlb, -⟩ := rdPlain GT i _ _ k Hnormw Hrd
  have Hnw := nwOfLoad GT i k _ _ _ _ Hlb
  by_cases hk : k = kr
  · subst hk
    rw [OOwn, if_pos rfl]
    have Hlw := lblOfRow _ _ _ _ Hw
    have Hl := lblOfRow _ _ _ _ Hlb
    have Hpo := gpoRow (gtAdGd GT) i kw k _ _ Hlw Hl Hlt
    have Hww := (gwbStoren _ _ _ _ _ Hlw).1
    cases Hb : gmoLtB (gtAdGd GT).gdG (i, kw) (i, k) with
    | true =>
      -- ordered: the OWNED last-value read, the handle moves to the read
      have Hb' := (gmoLtBSpec _ _ _).1 Hb
      have Hin : (i, kw) ∈ @Axpol.lobp (xv6Pol GT) (gtAdGd GT) (i, k) :=
        lobpIntro (gtAdGd GT) (i, kw) (i, k) _ Hlw rfl Hpo Hb'
      have Hpo' : ∀ w a v', a ∈ clb L → gwritesByte (gtAdGd GT).gdG w a v' →
          WeakRvwmoGraph.gpo (gtAdGd GT).gdG w (i, k) → gmoLt (gtAdGd GT).gdG w (i, k) := by
        intro w a v' Ha Hw' Hpo'
        refine poWritesGmoBeforeN (gtAdGd GT) Hcons i kw k (L.xlLk + 16)
          (WeakInterpProj.wbytes 8 val) cls a Hlw ?_ ?_ Hb' w v' Hw' Hpo'
        · rw [wbytesLength]
          exact Ha
        · intro w'' v'' Hw'' H1 H2
          exact Hnoint w'' a v'' Ha Hw'' H1 H2
      have Hsing : ⊢ ([∗map] Rin ∈ ({[(i, kw) := iprop(Q ∗ RVL nm.xnH (gtAdGd GT) (clb L) (i, kw)
          (WeakInterpProj.wbytes 8 val))]} : Mea GF), Rin) -∗
          iprop(Q ∗ RVL nm.xnH (gtAdGd GT) (clb L) (i, kw) (WeakInterpProj.wbytes 8 val)) := by
        iintro H
        ihave H2 := (BigSepM.bigSepM_singleton (M := GMapF Geid)).1 $$ H
        iexact H2
      have Hmono : ⊢ ▷ (iprop((Q ∗ RVL nm.xnH (gtAdGd GT) (clb L) (i, kw)
            (WeakInterpProj.wbytes 8 val)) ∗
          ⌜∀ (j : Nat) a t b, (clb L)[j]? = some a → greadsByte (gtAdGd GT).gdG (i, k) a t b →
            (WeakInterpProj.wbytes 8 val)[j]? = some b⌝) -∗
          iprop((Q ∗ RVL nm.xnH (gtAdGd GT) (clb L) (i, k) (WeakInterpProj.wbytes 8 val)) ∗
          ⌜∀ (j : Nat) a t b, (clb L)[j]? = some a → greadsByte (gtAdGd GT).gdG (i, k) a t b →
            (WeakInterpProj.wbytes 8 val)[j]? = some b⌝)) := by
        inext
        iintro ⟨⟨HQ, HR⟩, HF⟩
        ihave HR2 := (RVLRetie nm.xnH (gtAdGd GT) (clb L) (i, kw) (i, k)
          (WeakInterpProj.wbytes 8 val) Hb') $$ HR
        isplitl [HQ HR2]
        · isplitl [HQ]
          · iexact HQ
          · iexact HR2
        · iexact HF
      have Hfe0 := fxOwnedRead L GT nm HL Hcons (i, k) (i, kw) (clb L)
        (WeakInterpProj.wbytes 8 val) Q
        ({[(i, kw) := iprop(Q ∗ RVL nm.xnH (gtAdGd GT) (clb L) (i, kw)
          (WeakInterpProj.wbytes 8 val))]} : Mea GF) Hnw (clbXO L) Hb' Hpo'
      ihave Hw0 := Hsing
      ihave Hfe1 := Hfe0
      ihave Hfe2 := Hfe1 $$ Hw0
      ihave Hm := Hmono
      ihave Hmn := (@flowEqDynMono hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) (gtAdGd GT) (i, k)
        (@Axpol.sPol (xv6Pol GT) (gtAdGd GT) (i, k))
        ({[(i, kw) := iprop(Q ∗ RVL nm.xnH (gtAdGd GT) (clb L) (i, kw)
          (WeakInterpProj.wbytes 8 val))]} : Mea GF)
        iprop((Q ∗ RVL nm.xnH (gtAdGd GT) (clb L) (i, kw) (WeakInterpProj.wbytes 8 val)) ∗
          ⌜∀ (j : Nat) a t b, (clb L)[j]? = some a → greadsByte (gtAdGd GT).gdG (i, k) a t b →
            (WeakInterpProj.wbytes 8 val)[j]? = some b⌝)
        iprop((Q ∗ RVL nm.xnH (gtAdGd GT) (clb L) (i, k) (WeakInterpProj.wbytes 8 val)) ∗
          ⌜∀ (j : Nat) a t b, (clb L)[j]? = some a → greadsByte (gtAdGd GT).gdG (i, k) a t b →
            (WeakInterpProj.wbytes 8 val)[j]? = some b⌝))
      ihave Hfe := Hmn $$ Hm Hfe2
      iapply (dflowODraw L GT nm HL Hcons i k (i, kw) _
        iprop(Q ∗ RVL nm.xnH (gtAdGd GT) (clb L) (i, k) (WeakInterpProj.wbytes 8 val))
        iprop(⌜∀ (j : Nat) a t b, (clb L)[j]? = some a →
          greadsByte (gtAdGd GT).gdG (i, k) a t b →
          (WeakInterpProj.wbytes 8 val)[j]? = some b⌝) _ Hin) $$ Hh Hfe
      iintro H1 H2
      isplitl [H1]
      · iexists (i, k)
        isplitr
        · ipureintro
          exact Or.inr rfl
        · iexact H1
      · iexact H2
    | false =>
      -- not ordered: FORWARDING, nothing drawn
      have Hnlt : ¬ gmoLt (gtAdGd GT).gdG (i, kw) (i, k) := by
        intro Hx
        rw [(gmoLtBSpec _ _ _).2 Hx] at Hb
        cases Hb
      have Hall : ∀ (j : Nat) a v, (clb L)[j]? = some a →
          (WeakInterpProj.wbytes 8 val)[j]? = some v →
          gwritesByte (gtAdGd GT).gdG (i, kw) a v := by
        intro j a v Hj Hv
        obtain ⟨rfl, -⟩ := AxSpinX4.clRangeLookup _ _ _ _ Hj
        exact Hww j v Hv
      have Hlen : (WeakInterpProj.wbytes 8 val).length = (clb L).length := by
        simp [clb, clRange, wbytesLength]
      ihave Hfe := fxFwdRead L GT nm HL Hcons (i, k) (i, kw) (clb L)
        (WeakInterpProj.wbytes 8 val) Hnw Hpo Hnlt Hall Hlen Hnoint
      iapply (dflowOPlain L GT nm i k _ _) $$ Hfe
      iintro H
      isplitl [Hh]
      · iexists (i, kw)
        isplitr
        · ipureintro
          exact Or.inl rfl
        · iexact Hh
      · iexact H
  · rw [OOwn, if_neg hk]
    ihave Hfe := fxRead L GT nm HL Hcons (i, k) Hnw
    iapply (dflowOPlain L GT nm i k iprop(True) _) $$ Hfe
    iintro -
    iexact Hh

end flows

/-! # 2. The two call sites -/

section calls
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
/-- Rocq `XLk_of`: the lock-word leaf from a flow resource — UNDER the engine's global no-RMW
premise (false on real rows; deviation 1: `Out k`, `Hnrk` dropped). -/
theorem XLkOf (k : Nat) (a0v Plk : BitVec 64) (Out : Nat → List (BitVec 8) → IProp GF) :
    dataAtS σi T (.Load .Data) (a0v + sign_extend (m := 64) (0#12)) 4 Plk →
    ¬ L.xlText (paZ Plk) →
    (∀ (k' : Nat) (lb : Lbl) (aq rl : Bool) (m : Nat),
      (AxOpsem.grow (gtAdGd GT) i)[k']? = some lb → aident lb = .IRmw aq rl (paZ Plk) m →
      m ≠ 4) →
    ⊢ @FldM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent (dokAt (paZ Plk) 4) i
        Out -∗
      XLd (hlc := hlc) L GT nm T satp0 i cpu Ψ k (pch 0x00) 10#5 15#5 0#12 4 a0v (Out k) := by
  intro Hda Hnt Hnormw
  exact XxLdO L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Ψ HΨmid k (pch 0x00) 0#12
    10#5 15#5 4 a0v Plk Out (htok00 σi T satp0 Htxh) (by decide) AxSpinHd7.vw4 (by omega)
    (by omega) Hda Hnt Hnormw

include HL Hcons hmode hasid hppn Hfix Htxh HΨmid in
/-- Rocq `XCpu_of`: the lk->cpu leaf from a flow resource (the global no-RMW premise holds for
lk->cpu in xv6; deviation 1: the leaf at `k + 4`, `Out (k + 4)`, `Hnrk` dropped). -/
theorem XCpuOf (k : Nat) (a0v Pcl : BitVec 64) (Out : Nat → List (BitVec 8) → IProp GF) :
    dataAtS σi T (.Load .Data) (a0v + sign_extend (m := 64) (16#12)) 8 Pcl →
    ¬ L.xlText (paZ Pcl) →
    (∀ (k' : Nat) (lb : Lbl) (aq rl : Bool) (m : Nat),
      (AxOpsem.grow (gtAdGd GT) i)[k']? = some lb → aident lb = .IRmw aq rl (paZ Pcl) m →
      m ≠ 8) →
    ⊢ @FldM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent (dokAt (paZ Pcl) 8) i
        Out -∗
      XLd (hlc := hlc) L GT nm T satp0 i cpu Ψ (k + 4) (pch 0x12) 10#5 15#5 16#12 8 a0v
        (Out (k + 4)) := by
  intro Hda Hnt Hnormw
  exact XxLdO L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Ψ HΨmid (k + 4) (pch 0x12)
    16#12 10#5 15#5 8 a0v Pcl Out (htok12 σi T satp0 Htxh) (by decide) vw8 (by omega)
    (by omega) Hda Hnt Hnormw

set_option maxHeartbeats 1000000 in
include HL Hcons hmode hasid hppn Hfix Htxm Htxh HΨmid in
/-- Rocq `holding_from_acquire`: ACQUIRE's call (acquire+0x12 `jal holding`, return to
acquire+0x16), the non-holder — lock word: frame; lk->cpu: Φ_cpu's `rdFact` (deviation 1). -/
theorem holdingFromAcquire (k : Nat) (rs0 : RegFile) (ib0 : Ibch) (hb : Bool)
    (plk pcl : Int) (Pra Ps0 Ps1 Pram Ps0m Pcl : BitVec 64) :
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
    ⊢ XLd (hlc := hlc) L GT nm T satp0 i cpu Ψ k (pch 0x00) 10#5 15#5 0#12 4
        (gprVal rs0 AxSpinE8.r10) (fun _ => iprop(True)) -∗
      (if hb then
          KLong (hlc := hlc) L GT nm T satp0 i cpu Ψ k rs0 (AxSpinHdB.pac 0x16) Pra Ps0 Ps1 Pram
            Ps0m (fun _ => iprop(True)) (ORacy L GT i (k + 4))
        else KShort (hlc := hlc) L GT nm T satp0 i cpu Ψ k rs0 (AxSpinHdB.pac 0x16)
          (fun _ => iprop(True))) -∗
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
        ⟨.PHart cpu (.pure ()) rs0 none ib0, k⟩ Ψ := by
  intro HR Hw8 H1 H2 H3 H4 H5 Hc0 HPC0 Hh0 Hhm Hhlk Hhlc
    Hd1 Hd2 Hd3 Hd4 Hd5 Hd6 Hd7 Hd8 Hd9 Hd10 Hd11 Hd12 Hd13 Hd14 Hd15
    Hp1 Hn1 Hp2 Hn2 Hp3 Hn3 Hp4 Hn4 Hp5 Hn5 Hdisj Hpin Hdcl Hntcl Hnrcl
  cases hb
  · simp only [Bool.false_eq_true, ↓reduceIte] at Hpin ⊢
    have W := wpdHolding L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Htxm Htxh Ψ
      HΨmid k rs0 ib0 false (AxSpinHdB.pac 0x16) plk pcl Pra Ps0 Ps1 Pram Ps0m
      (fun _ => iprop(True)) (ORacy L GT i (k + 4)) HR Hw8 H1 H2 H3 H4 H5 Hc0 HPC0 Hh0 Hhm
      Hhlk Hhlc Hd1 Hd2 Hd3 Hd4 Hd5 Hd6 Hd7 Hd8 Hd9 Hd10 Hd11 Hd12 Hd13 Hd14 Hd15
      Hp1 Hn1 Hp2 Hn2 Hp3 Hn3 Hp4 Hn4 Hp5 Hn5 Hdisj
      (by simp only [Bool.false_eq_true, ↓reduceIte]; exact Hpin)
    simp only [Bool.false_eq_true, ↓reduceIte] at W
    exact W
  · simp only [↓reduceIte] at Hpin ⊢
    obtain ⟨Hvm, Hv⟩ := Hpin
    have W := wpdHolding L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Htxm Htxh Ψ
      HΨmid k rs0 ib0 true (AxSpinHdB.pac 0x16) plk pcl Pra Ps0 Ps1 Pram Ps0m
      (fun _ => iprop(True)) (ORacy L GT i (k + 4)) HR Hw8 H1 H2 H3 H4 H5 Hc0 HPC0 Hh0 Hhm
      Hhlk Hhlc Hd1 Hd2 Hd3 Hd4 Hd5 Hd6 Hd7 Hd8 Hd9 Hd10 Hd11 Hd12 Hd13 Hd14 Hd15
      Hp1 Hn1 Hp2 Hn2 Hp3 Hn3 Hp4 Hn4 Hp5 Hn5 Hdisj
      (by simp only [↓reduceIte]; exact ⟨Hvm, Hv, by decide +kernel⟩)
    simp only [↓reduceIte] at W
    have Hcpu := XCpuOf L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Htxh Ψ HΨmid k
      (gprVal rs0 AxSpinE8.r10) Pcl (ORacy L GT i) Hdcl Hntcl Hnrcl
    have Hfr := FldMRacy (hlc := hlc) (GF := GF) L GT nm HL Hcons i (paZ Pcl) 8 Hnrcl
    iintro Hlk C
    ihave Hf := Hfr
    ihave Hc0 := Hcpu
    ihave Hc := Hc0 $$ Hf
    ihave W0 := W
    iapply W0 $$ Hlk [Hc C]
    isplitl [Hc]
    · iexact Hc
    · iexact C

set_option maxHeartbeats 1000000 in
include HL Hcons hmode hasid hppn Hfix Htxm Htxh HΨmid in
/-- Rocq `holding_from_release`: RELEASE's call (release+0x0c `jal holding`, return to
release+0x10), the holder's path — lock word: `fxLkreadHeld`'s output; lk->cpu: the OWNED read of
the hart's own `sd lk->cpu ← val` at `kw` (deviation 1). -/
theorem holdingFromRelease (k : Nat) (rs0 : RegFile) (ib0 : Ibch)
    (plk : Int) (Pra Ps0 Ps1 Pram Ps0m Pcl : BitVec 64)
    (kc kw : Nat) (val : BitVec 64) (cls : WmClass) (Qc Qw : IProp GF) :
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
    ⊢ XLd (hlc := hlc) L GT nm T satp0 i cpu Ψ k (pch 0x00) 10#5 15#5 0#12 4
        (gprVal rs0 AxSpinE8.r10) (OHeld L GT nm i kc k Qc k) -∗
      AxAnnot.annotOwn (i, kw)
        iprop(Qw ∗ RVL nm.xnH (gtAdGd GT) (clb L) (i, kw) (WeakInterpProj.wbytes 8 val)) -∗
      KLong (hlc := hlc) L GT nm T satp0 i cpu Ψ k rs0 (AxSpinHdB.prl 0x10) Pra Ps0 Ps1 Pram Ps0m
        (OHeld L GT nm i kc k Qc k) (OOwn L GT nm i kw (k + 4) val Qw (k + 4)) -∗
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
        ⟨.PHart cpu (.pure ()) rs0 none ib0, k⟩ Ψ := by
  intro HR Hw8 H1 H2 H3 H4 H5 Hc0 HPC0 Hh0 Hhm Hhlk Hhlc
    Hd1 Hd2 Hd3 Hd4 Hd5 Hd6 Hd7 Hd8 Hd9 Hd10 Hd11 Hd12 Hd13 Hd14 Hd15
    Hp1 Hn1 Hp2 Hn2 Hp3 Hn3 Hp4 Hn4 Hp5 Hn5 Hdisj Hvm Hv Hdcl Hpcl Hntcl Hnrcl Hw Hkw Hnoint
  have W := wpdHolding L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Htxm Htxh Ψ
    HΨmid k rs0 ib0 true (AxSpinHdB.prl 0x10) plk (paZ Pcl) Pra Ps0 Ps1 Pram Ps0m
    (OHeld L GT nm i kc k Qc k) (OOwn L GT nm i kw (k + 4) val Qw (k + 4)) HR Hw8 H1 H2 H3 H4
    H5 Hc0 HPC0 Hh0 Hhm Hhlk Hhlc Hd1 Hd2 Hd3 Hd4 Hd5 Hd6 Hd7 Hd8 Hd9 Hd10 Hd11 Hd12 Hd13 Hd14
    Hd15 Hp1 Hn1 Hp2 Hn2 Hp3 Hn3 Hp4 Hn4 Hp5 Hn5 Hdisj
    (by simp only [↓reduceIte]; exact ⟨Hvm, Hv, by decide +kernel⟩)
  simp only [↓reduceIte] at W
  have Hcpu := XCpuOf L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Htxh Ψ HΨmid k
    (gprVal rs0 AxSpinE8.r10) Pcl (OOwn L GT nm i kw (k + 4) val Qw) Hdcl Hntcl Hnrcl
  have Hfo := FldMCpuOwn (hlc := hlc) (GF := GF) L GT nm HL Hcons i kw (k + 4) val cls Qw
    (by rw [← Hpcl]; exact Hnrcl) Hw Hkw Hnoint
  rw [← Hpcl] at Hfo
  iintro Hlk Hh C
  ihave Hfo0 := Hfo
  ihave Hf := Hfo0 $$ Hh
  ihave Hc0 := Hcpu
  ihave Hc := Hc0 $$ Hf
  ihave W0 := W
  iapply W0 $$ Hlk [Hc C]
  isplitl [Hc]
  · iexact Hc
  · iexact C

end calls

end Weak
