/-
Weak: **THEOREM 2, STAGE 2 — the two 4-byte private-field load leaves WITH a read-back
annotation** (stage-2 design `notes/weak-lb-thm2-stage2.md` §C; the need was found by
`AxSpinT2g`, its header "RISK 2" and `PROGRESS-AxSpinT2g.md`).  NEW Lean file (no Rocq source).

## Why

Every 4-byte `struct cpu` field load of push_off / pop_off (push_off's noff loads PO1:395 and
PO3:284, pop_off's noff load PO5:395, pop_off's intena load PO6:180) runs `AxSpinPOx.XxLd4`,
whose data flow is the FRAME rule (`fxRead`): it deposits NOTHING about the bytes read, so the
pop_off panic arms cannot be refuted by D4 readback at a row end.  This file supplies the two
leaves the P lane swaps in, the width-4 counterparts of `AxSpinE5.FldSlot` / `AxSpinE6.XxLd`:

* **RELOAD** `AxSpinLd4P.XxLd4R` — a 4-byte load at `k` of hart `i`'s private field at `pa`,
  whose po-latest own store is the row item `kw < k` (`.LStore false (paZ pa) vw cls`, no write of
  the row to `[pa, pa + 4)` strictly between: `nowr row kw k (paZ pa) 4`).  Flow:
  `fxPrivReadn L GT nm HL Hcons (i, k) (i, kw) (clRange (paZ pa) 4) vw` (AxSpinX2).  The
  continuation additionally receives
  `annotOwn (i, k) ⌜AxSpinLd4P.rlFact4 GT i (paZ pa) k vw⌝`,
  `rlFact4 … := ∀ j a t v, (clRange pa 4)[j]? = some a → greadsByte (i, k) a t v → vw[j]? = some v`.
  Uses: pop_off's noff load (kw = push_off's `sw noff`, `vw = stBytes 4 (addiw1 …)`, PO4) and
  pop_off's intena load (kw = push_off's `sw intena`, `vw = stBytes 4 0`, PO4).
* **GENESIS** `AxSpinLd4P.XxLd4G` — a 4-byte load at `k` of private bytes the row has NOT written
  before `k` (`AxSpinLd4P.noWrBefore row k (paZ pa) 4`).  Flow: `fxReadFact` + `privReadImg` per
  byte (= `fxPrivRead0` (AxSpinX2:952) for all four bytes at once; `AxSpinLd4P.fxPrivRead0n`).
  The continuation additionally receives
  `annotOwn (i, k) ⌜AxSpinLd4P.genFact4 GT i (paZ pa) k⌝`,
  `genFact4 … := ∀ a ∈ clRange pa 4, ∀ t v, greadsByte (i, k) a t v → t = 0 ∧ gxImg a = some v`.
  Uses: push_off's two noff loads.

The annotations are handed to the continuation as `annotOwn` resources (NOT dropped): a WPd
cannot branch on them mid-row; they surface at the row end (`AxSpinApA.wpdEndAnn`, design §B),
where `rlFact4` / `genFact4` UNFOLD to exactly the per-byte hypotheses of `AxSpinT2g.privReadEq`
(`tgt := vw`, `n := 4`) resp. `AxSpinT2g.imgReadEq` (`n := 4`) — the pure readback to
"graph value = stored bytes / image bytes".  (Those lemmas are not re-proved here: `AxSpinT2g`
imports `AxSpinPO1`, which will import this file.)

## THE SWAP (for P-lane workers)

Register effect: the new leaves' continuations get EXACTLY `XxLd4`'s arguments
(`vs`, `rs'`, `ib'`, `⌜vs.length = 4⌝`, `⌜GoodB … none (some (rd, ldRes false 4 vs)) rs'⌝`,
`⌜graphValue (gtAdGd GT) (i, k) = some vs⌝`, continuation state `⟨.PHart cpu (.pure ()) rs' none ib', k + 1⟩`)
plus ONE trailing annotation.  `AxSpinLd4P.XxLd4RAsLd4` / `AxSpinLd4P.XxLd4GAsLd4` prove the
`XxLd4` statement verbatim from each new leaf (the register effect agrees).  Mechanically:
1. `have XL4 := XxLd4 L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Ψ HΨmid` ↦
   `have XL4R := AxSpinLd4P.XxLd4R L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Ψ HΨmid`
   (resp. `XxLd4G`) — same section arguments, same order.
2. The call `XL4 s rs k pc is_rvc imm rs1 rd va pa HRet Hc HPC Hhit Htx Hrd Hva Hda Hhv Hnt Hnr Hle`
   keeps every argument and APPENDS (after `Hle`):
   * reload: `kw vw cls Hpriv Hkw_lbl Hvwlen Hkw_lt Hnowr` with
     `Hpriv : ∀ j < 4, priv L (paZ pa + j) i`,
     `Hkw_lbl : row[kw]? = some (.LStore false (paZ pa) vw cls)`, `Hvwlen : vw.length = 4`,
     `Hkw_lt : kw < k`, `Hnowr : nowr row kw k (paZ pa) 4`;
   * genesis: `Hpriv Hnone` with `Hnone : AxSpinLd4P.noWrBefore row k (paZ pa) 4`.
3. The continuation intro `iintro %vs %rs' %ib' %Hvs %HG %Hgv` gets one more spatial name, e.g.
   `iintro %vs %rs' %ib' %Hvs %HG %Hgv Hann`, to be carried to the row end (or `-` to drop it).

## Deviations / pins / honesty

* No Rocq source.  The leaves are `AxSpinPOx.XxLd4` with the field flow `FldFld` replaced by
  `FldFld4R` / `FldFld4G` (which differ from `FldFld` only at the designated position `k = kr`;
  at every other position they are the frame rule, as `AxSpinE5.FldSlot`).
* The extra premises are ROW facts (labels / positions of hart `i`'s own row) plus `priv` of the
  four bytes — the same kind `XxSt4` / `AxSpinE6.XxLd` already take.  No new scope premise.
* `XxLd4`'s unused `¬ L.xlText (paZ pa)` premise is kept (swap parity).

Reused: `XBk` (AxSpinE4), `CertBLoadS`, `HGX`, `HtextX`, `HflowX`, `HlocX`, `naWfEmpty`,
`lblOfRow`, `lblRow`, `gwbIdent` (AxSpinE5), `fxPrivReadn`, `fxReadFact`, `privReadImg`, `fxRead`
(AxSpinX2), `gwbStoren` (AxSpinX3), `AxSpinX4.clRangeLookup`, `inClr` (AxSpinX4),
`HL0p`/`HGex0p`/`Hmid0p`/`noRmwn`/`dokFld`/`XxLd4` (AxSpinPOx), `nowr`/`dj` (AxSpinPOr),
`AxLockWp.annotInsertEq`, `naAtProgressNotElemOf`, `annotAlloc`, `AxSpinWit.localTrue`.
All declarations are Lean-only and file-qualified `AxSpinLd4P.*`.
-/
import Weak.AxSpinPOx
import Weak.AxSpinE5

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-! # 1. Row premise and the two read-back facts -/

/-- No write of the row BEFORE position `k` touches `[pa, pa + w)` (the genesis premise). -/
def AxSpinLd4P.noWrBefore (row : List Lbl) (k : Nat) (pa : Int) (w : Nat) : Prop :=
  ∀ (k' : Nat) (lb : Lbl) (rl : Bool) (b : Int) (m : Nat), k' < k →
    row[k']? = some lb → aidentWr (aident lb) = some (rl, b, m) → dj b m pa w

/-- The 4-byte reload's annotation: byte `j` read at `(i, kr)` is `vw[j]`. -/
def AxSpinLd4P.rlFact4 (GT : GdexecT) (i : Agent) (pa : Int) (kr : Nat) (vw : List (BitVec 8)) :
    Prop :=
  ∀ (j : Nat) a t v, (clRange pa 4)[j]? = some a → greadsByte (gtAdGd GT).gdG (i, kr) a t v →
    vw[j]? = some v

/-- The 4-byte genesis load's annotation: every byte read at `(i, kg)` is the image byte. -/
def AxSpinLd4P.genFact4 (GT : GdexecT) (i : Agent) (pa : Int) (kg : Nat) : Prop :=
  ∀ a, a ∈ clRange pa 4 → ∀ t v, greadsByte (gtAdGd GT).gdG (i, kg) a t v →
    t = 0 ∧ (gtAdGd GT).gdG.gxImg a = some v

section fld
variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF] [AxannotGS GF]
  [AxSpinX.Xv6G GF]

def AxSpinLd4P.rlAnn4 (GT : GdexecT) (i : Agent) (pa : Int) (kr : Nat) (vw : List (BitVec 8))
    (k : Nat) : IProp GF :=
  if k = kr then iprop(⌜AxSpinLd4P.rlFact4 GT i pa kr vw⌝) else iprop(True)

def AxSpinLd4P.genAnn4 (GT : GdexecT) (i : Agent) (pa : Int) (kg : Nat) (k : Nat) : IProp GF :=
  if k = kg then iprop(⌜AxSpinLd4P.genFact4 GT i pa kg⌝) else iprop(True)

/-- The reload's output: `OutLdF` at width 4 plus the annotation. -/
def AxSpinLd4P.outLd4R (GT : GdexecT) (i : Agent) (pa : Int) (kr : Nat) (vw : List (BitVec 8))
    (k : Nat) (v : List (BitVec 8)) : IProp GF :=
  iprop(⌜graphValue (gtAdGd GT) (i, k) = some v ∧
    ∃ lb aq, (AxOpsem.grow (gtAdGd GT) i)[k]? = some lb ∧
      aidentRd (aident lb) = some (aq, pa, 4)⌝ ∗
    AxAnnot.annotOwn (i, k) (AxSpinLd4P.rlAnn4 GT i pa kr vw k))

/-- The genesis load's output: `OutLdF` at width 4 plus the annotation. -/
def AxSpinLd4P.outLd4G (GT : GdexecT) (i : Agent) (pa : Int) (kg : Nat)
    (k : Nat) (v : List (BitVec 8)) : IProp GF :=
  iprop(⌜graphValue (gtAdGd GT) (i, k) = some v ∧
    ∃ lb aq, (AxOpsem.grow (gtAdGd GT) i)[k]? = some lb ∧
      aidentRd (aident lb) = some (aq, pa, 4)⌝ ∗
    AxAnnot.annotOwn (i, k) (AxSpinLd4P.genAnn4 GT i pa kg k))

/-- `fxPrivRead0` for a whole byte range at once. -/
theorem AxSpinLd4P.fxPrivRead0n (L : Xlay) (GT : GdexecT) (nm : Xv6N) (HL : xlayOk L)
    (Hcons : rvwmoCatConsistent (gtAdGd GT)) (r : Geid) (Cw : List Int) :
    gisW (gtAdGd GT).gdG r = false → (∀ a, a ∈ Cw → priv L a r.1) →
    (∀ w' a v', a ∈ Cw → gwritesByte (gtAdGd GT).gdG w' a v' →
      WeakRvwmoGraph.gpo (gtAdGd GT).gdG w' r → False) →
    ⊢ @flowEqDyn hlc GF _ (AxSpinX2.xG L GT nm) (gtAdGd GT) r
        (@Axpol.sPol (xv6Pol GT) (gtAdGd GT) r) (∅ : Mea GF)
        iprop(⌜∀ a, a ∈ Cw → ∀ t v, greadsByte (gtAdGd GT).gdG r a t v →
          t = 0 ∧ (gtAdGd GT).gdG.gxImg a = some v⌝) := by
  intro Hnw Hpr Hnone
  exact fxReadFact L GT nm HL Hcons r _ Hnw (fun s _ Hwp _ Hwok _ a Ha t v Hrd =>
    privReadImg L HL (gtAdGd GT) Hcons s r a Hwok Hwp (Hpr a Ha) Hnw
      (fun w' v' => Hnone w' a v' Ha) t v Hrd)

/-- The noRmwn row fact rules out an RMW at the designated 4-byte read. -/
theorem AxSpinLd4P.ldOfRd (GT : GdexecT) (i : Agent) (pa : Int) (k : Nat) (lb : Lbl) (aq : Bool)
    (Hnr : noRmwn (AxOpsem.grow (gtAdGd GT) i) pa 4)
    (Hlb : (AxOpsem.grow (gtAdGd GT) i)[k]? = some lb)
    (Hid : aidentRd (aident lb) = some (aq, pa, 4)) :
    ∃ ts vs, lb = .LLoad aq pa ts vs := by
  cases lb with
  | LLoad aq' b ts vs =>
    simp only [aident, aidentRd, Option.some.injEq, Prod.mk.injEq] at Hid
    obtain ⟨rfl, rfl, -⟩ := Hid
    exact ⟨ts, vs, rfl⟩
  | LStore _ _ _ _ => simp [aident, aidentRd] at Hid
  | LFence _ _ _ _ => simp [aident, aidentRd] at Hid
  | LRmw aq' rl b ts rvs wvs cls' =>
    simp only [aident, aidentRd, Option.some.injEq, Prod.mk.injEq] at Hid
    obtain ⟨rfl, rfl, Hn⟩ := Hid
    exact absurd Hn (Hnr k _ aq' rl wvs.length Hlb rfl)

/-- The privacy premise, at `clRange`. -/
theorem AxSpinLd4P.privClr (L : Xlay) (i : Agent) (pa : Int)
    (Hpriv : ∀ j : Nat, j < 4 → priv L (pa + (j : Int)) i) :
    ∀ a, a ∈ clRange pa 4 → priv L a i := by
  intro a Ha
  rw [inClr] at Ha
  have h := Hpriv (a - pa).toNat (by omega)
  rwa [show pa + (((a - pa).toNat : Nat) : Int) = a by omega] at h

/-- The 4-byte field RELOAD flow: `fxPrivReadn` at `kr` against the store at `kw`, the frame
rule elsewhere. -/
theorem AxSpinLd4P.FldFld4R (L : Xlay) (GT : GdexecT) (nm : Xv6N) (HL : xlayOk L)
    (Hcons : rvwmoCatConsistent (gtAdGd GT)) (i : Agent) (pa : Int) (kr kw : Nat)
    (vw : List (BitVec 8)) (cls : WmClass)
    (Hpriv : ∀ j : Nat, j < 4 → priv L (pa + (j : Int)) i)
    (Hnr : noRmwn (AxOpsem.grow (gtAdGd GT) i) pa 4)
    (Hw : (AxOpsem.grow (gtAdGd GT) i)[kw]? = some (.LStore false pa vw cls))
    (Hlen : vw.length = 4) (Hkw : kw < kr)
    (Hbetween : nowr (AxOpsem.grow (gtAdGd GT) i) kw kr pa 4) :
    ⊢ @FldM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent (dokFld pa 4) i
        (AxSpinLd4P.outLd4R GT i pa kr vw) := by
  unfold FldM
  iintro %GD %ls %k %v %base %n %Hc #Hg _ %Hgv %Hd
  ihave %Heq := (HGX L GT nm GD Hc) $$ Hg
  subst Heq
  obtain ⟨⟨Hb, Hn⟩, lb, aq, Hlb, Hid⟩ := Hd
  rw [Hb, Hn] at Hid
  obtain ⟨ts, vs, rfl⟩ := AxSpinLd4P.ldOfRd GT i pa k lb aq Hnr Hlb Hid
  have Hnw : gisW (gtAdGd GT).gdG (i, k) = false := by
    unfold gisW
    rw [lblOfRow _ _ _ _ Hlb]
    rfl
  have Hflow : ⊢ @flowEqDyn hlc GF _ (AxSpinX2.xG L GT nm) (gtAdGd GT) (i, k)
      (@Axpol.sPol (xv6Pol GT) (gtAdGd GT) (i, k)) (∅ : Mea GF)
      (AxSpinLd4P.rlAnn4 GT i pa kr vw k) := by
    unfold AxSpinLd4P.rlAnn4
    by_cases hk : k = kr
    · subst hk
      rw [if_pos rfl]
      have H2 : ∀ (j : Nat) a v', (clRange pa 4)[j]? = some a → vw[j]? = some v' →
          gwritesByte (gtAdGd GT).gdG (i, kw) a v' := by
        intro j a v' Hj Hv'
        obtain ⟨rfl, -⟩ := AxSpinX4.clRangeLookup _ _ _ _ Hj
        exact (gwbStoren _ _ _ _ _ (lblOfRow _ _ _ _ Hw)).1 j v' Hv'
      have H3 : vw.length = (clRange pa 4).length := by
        simp [clRange, Hlen]
      have H4 : WeakRvwmoGraph.gpo (gtAdGd GT).gdG (i, kw) (i, k) := by
        refine ⟨rfl, Hkw, ?_, ?_⟩
        · rw [lblOfRow _ _ _ _ Hw]; rfl
        · rw [lblOfRow _ _ _ _ Hlb]; rfl
      have H5 : ∀ w' a v', a ∈ clRange pa 4 → gwritesByte (gtAdGd GT).gdG w' a v' →
          WeakRvwmoGraph.gpo (gtAdGd GT).gdG w' (i, k) →
          w' = (i, kw) ∨ WeakRvwmoGraph.gpo (gtAdGd GT).gdG w' (i, kw) := by
        rintro ⟨i', k'⟩ a v' Ha Hw' ⟨Hh, Hlt, Hl', -⟩
        simp only at Hh Hlt
        subst Hh
        by_cases hkw : k' = kw
        · left
          rw [hkw]
        by_cases hlt : k' < kw
        · right
          refine ⟨rfl, hlt, Hl', ?_⟩
          rw [lblOfRow _ _ _ _ Hw]; rfl
        · exfalso
          rw [inClr] at Ha
          obtain ⟨l', Hl''⟩ := Option.isSome_iff_exists.1 Hl'
          obtain ⟨rl, b, m, j, Hid', Hj, rfl⟩ := gwbIdent _ _ _ _ _ Hl'' Hw'
          have := Hbetween k' l' rl b m ⟨by omega, by omega⟩ (lblRow _ _ _ _ Hl'') Hid'
          unfold dj at this
          omega
      exact fxPrivReadn L GT nm HL Hcons (i, k) (i, kw) (clRange pa 4) vw Hnw
        (AxSpinLd4P.privClr L i pa Hpriv) H2 H3 H4 H5
    · rw [if_neg hk]
      exact fxRead L GT nm HL Hcons (i, k) Hnw
  unfold dflowO
  iintro %na ⟨Hpg, Hannot⟩
  ihave %Hnin := naAtProgressNotElemOf (gtAdGd GT) i k na $$ Hpg
  imod annotAlloc na (i, k) (AxSpinLd4P.rlAnn4 GT i pa kr vw k) Hnin $$ Hannot with ⟨Hannot, Hh⟩
  imodintro
  inext
  imodintro
  iexists (AxSpinLd4P.rlAnn4 GT i pa kr vw k), (∅ : Mea GF), (∅ : Mea GF), (() : Unit)
  isplitr
  · iapply (naWfEmpty L GT nm (i, k) na)
  isplitr
  · iapply Hflow
  isplitl [Hannot]
  · rw [AxLockWp.annotInsertEq na (i, k) (AxSpinLd4P.rlAnn4 GT i pa kr vw k)]
    iexact Hannot
  isplitr
  · iapply (AxSpinWit.localTrue (gtAdGd GT) Xv6N Unit (protXv6 L) nm (gtAdGd GT) i (k + 1) ())
  · unfold AxSpinLd4P.outLd4R
    isplitr
    · ipureintro
      exact ⟨Hgv, _, aq, Hlb, Hid⟩
    · iexact Hh

/-- The 4-byte field GENESIS flow: `fxPrivRead0` on all four bytes at `kg`, the frame rule
elsewhere. -/
theorem AxSpinLd4P.FldFld4G (L : Xlay) (GT : GdexecT) (nm : Xv6N) (HL : xlayOk L)
    (Hcons : rvwmoCatConsistent (gtAdGd GT)) (i : Agent) (pa : Int) (kg : Nat)
    (Hpriv : ∀ j : Nat, j < 4 → priv L (pa + (j : Int)) i)
    (Hnr : noRmwn (AxOpsem.grow (gtAdGd GT) i) pa 4)
    (Hnone : AxSpinLd4P.noWrBefore (AxOpsem.grow (gtAdGd GT) i) kg pa 4) :
    ⊢ @FldM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent (dokFld pa 4) i
        (AxSpinLd4P.outLd4G GT i pa kg) := by
  unfold FldM
  iintro %GD %ls %k %v %base %n %Hc #Hg _ %Hgv %Hd
  ihave %Heq := (HGX L GT nm GD Hc) $$ Hg
  subst Heq
  obtain ⟨⟨Hb, Hn⟩, lb, aq, Hlb, Hid⟩ := Hd
  rw [Hb, Hn] at Hid
  obtain ⟨ts, vs, rfl⟩ := AxSpinLd4P.ldOfRd GT i pa k lb aq Hnr Hlb Hid
  have Hnw : gisW (gtAdGd GT).gdG (i, k) = false := by
    unfold gisW
    rw [lblOfRow _ _ _ _ Hlb]
    rfl
  have Hflow : ⊢ @flowEqDyn hlc GF _ (AxSpinX2.xG L GT nm) (gtAdGd GT) (i, k)
      (@Axpol.sPol (xv6Pol GT) (gtAdGd GT) (i, k)) (∅ : Mea GF)
      (AxSpinLd4P.genAnn4 GT i pa kg k) := by
    unfold AxSpinLd4P.genAnn4
    by_cases hk : k = kg
    · subst hk
      rw [if_pos rfl]
      have H3 : ∀ w' a v', a ∈ clRange pa 4 → gwritesByte (gtAdGd GT).gdG w' a v' →
          WeakRvwmoGraph.gpo (gtAdGd GT).gdG w' (i, k) → False := by
        rintro ⟨i', k'⟩ a v' Ha Hw' ⟨Hh, Hlt, Hl', -⟩
        simp only at Hh Hlt
        subst Hh
        rw [inClr] at Ha
        obtain ⟨l', Hl''⟩ := Option.isSome_iff_exists.1 Hl'
        obtain ⟨rl, b, m, j, Hid', Hj, rfl⟩ := gwbIdent _ _ _ _ _ Hl'' Hw'
        have := Hnone k' l' rl b m Hlt (lblRow _ _ _ _ Hl'') Hid'
        unfold dj at this
        omega
      exact AxSpinLd4P.fxPrivRead0n L GT nm HL Hcons (i, k) (clRange pa 4) Hnw
        (AxSpinLd4P.privClr L i pa Hpriv) H3
    · rw [if_neg hk]
      exact fxRead L GT nm HL Hcons (i, k) Hnw
  unfold dflowO
  iintro %na ⟨Hpg, Hannot⟩
  ihave %Hnin := naAtProgressNotElemOf (gtAdGd GT) i k na $$ Hpg
  imod annotAlloc na (i, k) (AxSpinLd4P.genAnn4 GT i pa kg k) Hnin $$ Hannot with ⟨Hannot, Hh⟩
  imodintro
  inext
  imodintro
  iexists (AxSpinLd4P.genAnn4 GT i pa kg k), (∅ : Mea GF), (∅ : Mea GF), (() : Unit)
  isplitr
  · iapply (naWfEmpty L GT nm (i, k) na)
  isplitr
  · iapply Hflow
  isplitl [Hannot]
  · rw [AxLockWp.annotInsertEq na (i, k) (AxSpinLd4P.genAnn4 GT i pa kg k)]
    iexact Hannot
  isplitr
  · iapply (AxSpinWit.localTrue (gtAdGd GT) Xv6N Unit (protXv6 L) nm (gtAdGd GT) i (k + 1) ())
  · unfold AxSpinLd4P.outLd4G
    isplitr
    · ipureintro
      exact ⟨Hgv, _, aq, Hlb, Hid⟩
    · iexact Hh

end fld

/-! # 2. The leaves at Ixv6 -/

section ixleaves
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

/-- `XBk`'s no-RMW premise at the field, from the row fact `noRmwn`. -/
theorem AxSpinLd4P.noRmwPrem (pa : Int) (Hnr : noRmwn (AxOpsem.grow (gtAdGd GT) i) pa 4) :
    Dkind.DKLd = .DKLd → ∀ GD, rvwmoCatConsistent GD →
      @AxirisG.gconstInterp GF (AxSpinX2.xG L GT nm) GD ⊢
      ⌜∀ (k' : Nat) (lb : Lbl) (aq rl : Bool) (base : Int) (n : Nat),
        (AxOpsem.grow GD i)[k']? = some lb → aident lb = .IRmw aq rl base n →
        ¬ dokFld pa 4 base n⌝ := by
  intro _ GD Hc'
  iintro Hg
  ihave %Heq := (HGX L GT nm GD Hc') $$ Hg
  subst Heq
  ipureintro
  rintro k' lb aq rl base n Hlb Hid ⟨rfl, rfl⟩
  exact Hnr k' lb aq rl 4 Hlb Hid rfl

include HL Hcons hmode hasid hppn Hfix HΨmid in
/-- THE 4-BYTE RELOAD LEAF: `XxLd4` with the reload flow `FldFld4R`; the continuation also
receives the annotation `rlFact4` ("byte `j` read = `vw[j]`") at `(i, k)`.  Premises: `XxLd4`'s,
then (after the length premise) the store at `kw` and the row facts. -/
theorem AxSpinLd4P.XxLd4R (s : Athread) (rs : RegFile) (k : Nat) (pc : BitVec 64) (is_rvc : Bool)
    (imm : BitVec 12) (rs1 rd : BitVec 5) (va pa : BitVec 64) :
    RetX cpu rs k s → ctrlOkSW T satp0 rs → rs .PC = pc → hitW rs pc →
    textOkB σi T satp0 pc is_rvc (.LOAD (imm, .Regidx rs1, .Regidx rd, false, 4)) →
    rd.toNat ≠ 0 →
    va = gprVal rs rs1 + sign_extend (m := 64) imm →
    dataAtS σi T (.Load .Data) va 4 pa → hitW rs va → ¬ L.xlText (paZ pa) →
    noRmwn (AxOpsem.grow (gtAdGd GT) i) (paZ pa) 4 →
    k + 1 ≤ (AxOpsem.grow (gtAdGd GT) i).length →
    ∀ (kw : Nat) (vw : List (BitVec 8)) (cls : WmClass),
    (∀ j : Nat, j < 4 → priv L (paZ pa + (j : Int)) i) →
    (AxOpsem.grow (gtAdGd GT) i)[kw]? = some (.LStore false (paZ pa) vw cls) → vw.length = 4 →
    kw < k → nowr (AxOpsem.grow (gtAdGd GT) i) kw k (paZ pa) 4 →
    ⊢ (∀ (vs : List (BitVec 8)) (rs' : RegFile) (ib' : Ibch), ⌜vs.length = 4⌝ -∗
        ⌜GoodB T satp0 rs pc is_rvc none (some (rd, ldRes false 4 vs)) rs'⌝ -∗
        ⌜graphValue (gtAdGd GT) (i, k) = some vs⌝ -∗
        AxAnnot.annotOwn (GF := GF) (i, k) iprop(⌜AxSpinLd4P.rlFact4 GT i (paZ pa) k vw⌝) -∗
        @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
          ⟨.PHart cpu (.pure ()) rs' none ib', k + 1⟩ Ψ) -∗
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i s Ψ := by
  intro HRet Hc HPC Hhit Htx Hrd Hva Hda Hhv _ Hnr Hle kw vw cls Hpriv Hw Hlen Hkw Hbw
  have H := @XBk hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) σi T satp0 hmode hasid hppn i cpu
    (fun GD => GD = gtAdGd GT) (HGX L GT nm) (AxOpsem.grow (gtAdGd GT) i).length (HL0p GT i)
    (HGex0p GT) Ψ (Hmid0p L GT nm i Ψ HΨmid) (HtextX L GT nm (imgS σi) i Hfix)
    (HflowX L GT nm HL Hcons (imgS σi) i) (HlocX L GT nm i)
    (dokFld (paZ pa) 4) .DKLd (AxSpinLd4P.noRmwPrem L GT nm i (paZ pa) Hnr)
    (by intro h; cases h) (AxSpinLd4P.outLd4R GT i (paZ pa) k vw)
    s rs k pc is_rvc _ 1 none (owLdB rd false 4) .CPend false _
    HRet Hc HPC Hhit Htx (by rintro d r ⟨vs, rfl, -, -⟩; exact Hrd)
    (CertBLoadS σi T satp0 hmode hasid hppn (dokFld (paZ pa) 4) rs pc is_rvc imm rs1 rd false 4 va
      pa false Hrd AxSpinPOx.vw4 (by omega) (by omega) Hva Hda Hhv ⟨rfl, rfl⟩)
    (by omega) Hle
  iintro C
  iapply H $$ [] [C]
  · simp only [CResK, CFkM]
    iapply (AxSpinLd4P.FldFld4R L GT nm HL Hcons i (paZ pa) k kw vw cls Hpriv Hnr Hw Hlen Hkw Hbw)
  · iintro %d %r %rs' %ib' %HPX %HGB HO
    obtain ⟨vs, rfl, Hvs, rfl⟩ := HPX
    simp only [CResK]
    icases HO with ⟨%kd, %Hkd, HO⟩
    obtain rfl : kd = k := by omega
    unfold AxSpinLd4P.outLd4R
    rw [show AxSpinLd4P.rlAnn4 (GF := GF) GT i (paZ pa) kd vw kd =
      iprop(⌜AxSpinLd4P.rlFact4 GT i (paZ pa) kd vw⌝) from if_pos rfl]
    icases HO with ⟨%Hgv, HO⟩
    iapply C $$ %vs %rs' %ib' %Hvs %HGB %Hgv.1 HO

include HL Hcons hmode hasid hppn Hfix HΨmid in
/-- THE 4-BYTE GENESIS LEAF: `XxLd4` with the genesis flow `FldFld4G`; the continuation also
receives the annotation `genFact4` ("every byte read is the image byte") at `(i, k)`.
Premises: `XxLd4`'s, then (after the length premise) privacy and "no own write before `k`". -/
theorem AxSpinLd4P.XxLd4G (s : Athread) (rs : RegFile) (k : Nat) (pc : BitVec 64) (is_rvc : Bool)
    (imm : BitVec 12) (rs1 rd : BitVec 5) (va pa : BitVec 64) :
    RetX cpu rs k s → ctrlOkSW T satp0 rs → rs .PC = pc → hitW rs pc →
    textOkB σi T satp0 pc is_rvc (.LOAD (imm, .Regidx rs1, .Regidx rd, false, 4)) →
    rd.toNat ≠ 0 →
    va = gprVal rs rs1 + sign_extend (m := 64) imm →
    dataAtS σi T (.Load .Data) va 4 pa → hitW rs va → ¬ L.xlText (paZ pa) →
    noRmwn (AxOpsem.grow (gtAdGd GT) i) (paZ pa) 4 →
    k + 1 ≤ (AxOpsem.grow (gtAdGd GT) i).length →
    (∀ j : Nat, j < 4 → priv L (paZ pa + (j : Int)) i) →
    AxSpinLd4P.noWrBefore (AxOpsem.grow (gtAdGd GT) i) k (paZ pa) 4 →
    ⊢ (∀ (vs : List (BitVec 8)) (rs' : RegFile) (ib' : Ibch), ⌜vs.length = 4⌝ -∗
        ⌜GoodB T satp0 rs pc is_rvc none (some (rd, ldRes false 4 vs)) rs'⌝ -∗
        ⌜graphValue (gtAdGd GT) (i, k) = some vs⌝ -∗
        AxAnnot.annotOwn (GF := GF) (i, k) iprop(⌜AxSpinLd4P.genFact4 GT i (paZ pa) k⌝) -∗
        @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
          ⟨.PHart cpu (.pure ()) rs' none ib', k + 1⟩ Ψ) -∗
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i s Ψ := by
  intro HRet Hc HPC Hhit Htx Hrd Hva Hda Hhv _ Hnr Hle Hpriv Hnone
  have H := @XBk hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) σi T satp0 hmode hasid hppn i cpu
    (fun GD => GD = gtAdGd GT) (HGX L GT nm) (AxOpsem.grow (gtAdGd GT) i).length (HL0p GT i)
    (HGex0p GT) Ψ (Hmid0p L GT nm i Ψ HΨmid) (HtextX L GT nm (imgS σi) i Hfix)
    (HflowX L GT nm HL Hcons (imgS σi) i) (HlocX L GT nm i)
    (dokFld (paZ pa) 4) .DKLd (AxSpinLd4P.noRmwPrem L GT nm i (paZ pa) Hnr)
    (by intro h; cases h) (AxSpinLd4P.outLd4G GT i (paZ pa) k)
    s rs k pc is_rvc _ 1 none (owLdB rd false 4) .CPend false _
    HRet Hc HPC Hhit Htx (by rintro d r ⟨vs, rfl, -, -⟩; exact Hrd)
    (CertBLoadS σi T satp0 hmode hasid hppn (dokFld (paZ pa) 4) rs pc is_rvc imm rs1 rd false 4 va
      pa false Hrd AxSpinPOx.vw4 (by omega) (by omega) Hva Hda Hhv ⟨rfl, rfl⟩)
    (by omega) Hle
  iintro C
  iapply H $$ [] [C]
  · simp only [CResK, CFkM]
    iapply (AxSpinLd4P.FldFld4G L GT nm HL Hcons i (paZ pa) k Hpriv Hnr Hnone)
  · iintro %d %r %rs' %ib' %HPX %HGB HO
    obtain ⟨vs, rfl, Hvs, rfl⟩ := HPX
    simp only [CResK]
    icases HO with ⟨%kd, %Hkd, HO⟩
    obtain rfl : kd = k := by omega
    unfold AxSpinLd4P.outLd4G
    rw [show AxSpinLd4P.genAnn4 (GF := GF) GT i (paZ pa) kd kd =
      iprop(⌜AxSpinLd4P.genFact4 GT i (paZ pa) kd⌝) from if_pos rfl]
    icases HO with ⟨%Hgv, HO⟩
    iapply C $$ %vs %rs' %ib' %Hvs %HGB %Hgv.1 HO

/-! # 3. Register-effect agreement with `XxLd4` (the swap is sound) -/

include HL Hcons hmode hasid hppn Hfix HΨmid in
/-- The reload leaf yields `XxLd4`'s statement VERBATIM (same continuation, same register
effect `GoodB … (some (rd, ldRes false 4 vs))`, same `graphValue`, same position `k + 1`). -/
theorem AxSpinLd4P.XxLd4RAsLd4 (s : Athread) (rs : RegFile) (k : Nat) (pc : BitVec 64)
    (is_rvc : Bool) (imm : BitVec 12) (rs1 rd : BitVec 5) (va pa : BitVec 64) :
    RetX cpu rs k s → ctrlOkSW T satp0 rs → rs .PC = pc → hitW rs pc →
    textOkB σi T satp0 pc is_rvc (.LOAD (imm, .Regidx rs1, .Regidx rd, false, 4)) →
    rd.toNat ≠ 0 →
    va = gprVal rs rs1 + sign_extend (m := 64) imm →
    dataAtS σi T (.Load .Data) va 4 pa → hitW rs va → ¬ L.xlText (paZ pa) →
    noRmwn (AxOpsem.grow (gtAdGd GT) i) (paZ pa) 4 →
    k + 1 ≤ (AxOpsem.grow (gtAdGd GT) i).length →
    ∀ (kw : Nat) (vw : List (BitVec 8)) (cls : WmClass),
    (∀ j : Nat, j < 4 → priv L (paZ pa + (j : Int)) i) →
    (AxOpsem.grow (gtAdGd GT) i)[kw]? = some (.LStore false (paZ pa) vw cls) → vw.length = 4 →
    kw < k → nowr (AxOpsem.grow (gtAdGd GT) i) kw k (paZ pa) 4 →
    ⊢ (∀ (vs : List (BitVec 8)) (rs' : RegFile) (ib' : Ibch), ⌜vs.length = 4⌝ -∗
        ⌜GoodB T satp0 rs pc is_rvc none (some (rd, ldRes false 4 vs)) rs'⌝ -∗
        ⌜graphValue (gtAdGd GT) (i, k) = some vs⌝ -∗
        @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
          ⟨.PHart cpu (.pure ()) rs' none ib', k + 1⟩ Ψ) -∗
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i s Ψ := by
  intro HRet Hc HPC Hhit Htx Hrd Hva Hda Hhv Hnt Hnr Hle kw vw cls Hpriv Hw Hlen Hkw Hbw
  have H := AxSpinLd4P.XxLd4R L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Ψ HΨmid
    s rs k pc is_rvc imm rs1 rd va pa HRet Hc HPC Hhit Htx Hrd Hva Hda Hhv Hnt Hnr Hle
    kw vw cls Hpriv Hw Hlen Hkw Hbw
  iintro C
  iapply H
  iintro %vs %rs' %ib' %Hvs %HGB %Hgv -
  iapply C $$ %vs %rs' %ib' %Hvs %HGB %Hgv

include HL Hcons hmode hasid hppn Hfix HΨmid in
/-- The genesis leaf yields `XxLd4`'s statement VERBATIM. -/
theorem AxSpinLd4P.XxLd4GAsLd4 (s : Athread) (rs : RegFile) (k : Nat) (pc : BitVec 64)
    (is_rvc : Bool) (imm : BitVec 12) (rs1 rd : BitVec 5) (va pa : BitVec 64) :
    RetX cpu rs k s → ctrlOkSW T satp0 rs → rs .PC = pc → hitW rs pc →
    textOkB σi T satp0 pc is_rvc (.LOAD (imm, .Regidx rs1, .Regidx rd, false, 4)) →
    rd.toNat ≠ 0 →
    va = gprVal rs rs1 + sign_extend (m := 64) imm →
    dataAtS σi T (.Load .Data) va 4 pa → hitW rs va → ¬ L.xlText (paZ pa) →
    noRmwn (AxOpsem.grow (gtAdGd GT) i) (paZ pa) 4 →
    k + 1 ≤ (AxOpsem.grow (gtAdGd GT) i).length →
    (∀ j : Nat, j < 4 → priv L (paZ pa + (j : Int)) i) →
    AxSpinLd4P.noWrBefore (AxOpsem.grow (gtAdGd GT) i) k (paZ pa) 4 →
    ⊢ (∀ (vs : List (BitVec 8)) (rs' : RegFile) (ib' : Ibch), ⌜vs.length = 4⌝ -∗
        ⌜GoodB T satp0 rs pc is_rvc none (some (rd, ldRes false 4 vs)) rs'⌝ -∗
        ⌜graphValue (gtAdGd GT) (i, k) = some vs⌝ -∗
        @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
          ⟨.PHart cpu (.pure ()) rs' none ib', k + 1⟩ Ψ) -∗
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i s Ψ := by
  intro HRet Hc HPC Hhit Htx Hrd Hva Hda Hhv Hnt Hnr Hle Hpriv Hnone
  have H := AxSpinLd4P.XxLd4G L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Ψ HΨmid
    s rs k pc is_rvc imm rs1 rd va pa HRet Hc HPC Hhit Htx Hrd Hva Hda Hhv Hnt Hnr Hle Hpriv Hnone
  iintro C
  iapply H
  iintro %vs %rs' %ib' %Hvs %HGB %Hgv -
  iapply C $$ %vs %rs' %ib' %Hvs %HGB %Hgv

end ixleaves

end Weak
