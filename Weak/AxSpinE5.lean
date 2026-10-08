/-
Weak: **PHASE 5 POSITIONAL ENGINE, part 5: the engine at the JOINT INSTANCE Ixv6**
(`AxSpinX2.xG L GT nm` = `shG (gtAdGd GT) Xv6N Unit (protXv6 L) nm`, policy `xv6Pol GT`).

Rocq: `iris/AxSpinE5.v` @ xxvzwolszwmp.

## The Rocq header, in substance

§1 the bridge's instance premises at Ixv6: `HGX` (the graph is pinned:
`gconstInterp GD ⊢ ⌜GD = GD0⌝`), `HtextX` (from the GRAPH fact `textFixed GD0 i img`), `HflowX`
(a fetch's flow equation is the frame rule `fxRead` — the row item is a non-write event),
`HlocX`.
§2 the PRIVATE STACK SLOT data resources, through Phase 1c's row-indexed private rules:
`FstSlot` — a store to hart `i`'s private 8-byte slot at `pa`: the flow is `fxPrivWrite`
(writer = owner, WOK); the output records the row item's data (`graphData`) at the event;
`FldSlot` — a load of that slot: at the RELOAD position `kr` the flow is `fxPrivReadn` against
the SPILL at `kw` (the ROW fact "`kw` is the latest earlier store to the slot" supplied as
premises), depositing at `(i, kr)` the annotation `⌜the reload's bytes = the spill's row
bytes⌝`; at any other position the frame rule.  Out also records the read's `graphValue`.
ROW premises of the slot rules: every write of hart `i`'s row is at most 8 bytes (RV64); no
fused RMW of hart `i` targets the slot with 8 bytes.  (Rocq's header also announces §3 leaves
`Xx_reg`/`Xx_st`/`Xx_ld`; the Rocq file does not define them.)

## Deviations from Rocq

1. O2 STAGE C: NONE NEEDED IN THIS FILE.  The `AxSpinE3` WARNING (a TLB-hit fetch is not a first
   read, so the first graph read can be the instruction's own data read) concerns the off-row /
   `FirstRd` argument, which this file does not contain: AxSpinE5 only discharges the instance
   premises of `AxSpinE4.XBk` (`HG`, `Htext`, `Hflow`, `Hloc`) and the data flows `FstM`/`FldM`.
   `HflowX` is stated at `AxSpinE4`'s `Hflow` shape verbatim (a row item answered by image bytes
   is a plain `IRead`, hence not a write, hence `fxRead`); under Stage C that premise is no longer
   consumed by fetches, but `XBk` still takes it (image-answered data reads,
   `AxSymEngine3.wpdImgRead3M`), so the lemma keeps its meaning.
2. INSTANCES (as `AxSpinX2` deviation 2 / `AxSpinU`): the local instances `e_pol`/`e_G` are
   inlined as `xv6Pol GT` / `AxSpinX2.xG L GT nm`, passed with `@`.  Rocq's `AxGA2 GD0 (xl_text L)
   …` has no text argument in Lean (Stage C, `AxTierA2` deviation 2).  `invGS_gen HasNoLc Σ` ↦
   `[InvGS_gen hlc GF]` (any `hlc`); `xv6G Σ` ↦ `[AxSpinX.Xv6G GF]`; `axannotGS Σ` ↦
   `[AxannotGS GF]`.  Section variables are explicit leading arguments where Rocq's section
   mechanism includes them (`L GT nm`, then `HL Hcons` where `Proof using` names them; for
   `naWfEmpty` Rocq's `Proof using L GT nm` keeps `L`/`nm` as (unused) explicit arguments).
3. VOCABULARY: `Z` ↦ `Int`, `bv 8` ↦ `BitVec 8`, `gd_g GD` ↦ `GD.gdG`, `l !! j` ↦ `l[j]?`,
   `cl_range` ↦ `clRange` (`AxSpinProt5`), `in_clr` ↦ `inClr`, `cl_range_lookup` ↦
   `AxSpinX4.clRangeLookup`, `row_read_lbl` ↦ `rowReadLbl`, `row_read_not_w` ↦ `rowReadNotW`
   (`AxSymEngine3b`).  `Hbetween`'s `(kw < k' < kr)%nat` ↦ `kw < k' ∧ k' < kr`.
4. The trailing `Print Assumptions` lines are not ported (the lint's axiom check covers them).

**Rocq → Lean name map.**  `gwb_ident` `gwbIdent`, `lbl_of_row` `lblOfRow`, `lbl_row` `lblRow`,
`HG_x` `HGX`, `Htext_x` `HtextX`, `Hloc_x` `HlocX`, `na_wf_empty` `naWfEmpty`, `Hflow_x`
`HflowX`, `dok_slot` `dokSlot`, `OutSt` `OutSt`, `Fst_slot` `FstSlot`, `RLfact` `RLfact`,
`RLann` `RLann`, `OutLd` `OutLd`, `Fld_slot` `FldSlot`.  No duplicated Rocq names; no Lean-only
helpers.

**Dropped:** none (Rocq 15 definitions/lemmas + the 2 local instances `e_pol`/`e_G`, inlined;
Lean 15).
-/
import Weak.AxSpinE4
import Weak.AxSymEngine3b
import Weak.AxSpinX2
import Weak.AxSpinX3
import Weak.AxSpinX4
import Weak.AxLockWp

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-- The byte footprint of a labelled write. -/
theorem gwbIdent (G : Gexec) (e : Geid) (l : Lbl) (a : Int) (v : BitVec 8) :
    gxLbl G e = some l → gwritesByte G e a v →
    ∃ rl b m j, aidentWr (aident l) = some (rl, b, m) ∧ j < m ∧ a = b + (j : Int) := by
  rintro Hl ⟨l', b, vs, j, Hl', Hwr, Hv, Ha⟩
  rw [Hl] at Hl'
  cases Hl'
  have Hj : j < vs.length := (List.getElem?_eq_some_iff.1 Hv).1
  unfold accAddr at Ha
  cases l with
  | LLoad _ _ _ _ => simp [lbWr] at Hwr
  | LFence _ _ _ _ => simp [lbWr] at Hwr
  | LStore rl b0 vs0 cls =>
    simp only [lbWr, Option.some.injEq, Prod.mk.injEq] at Hwr
    obtain ⟨rfl, rfl⟩ := Hwr
    exact ⟨rl, b0, vs0.length, j, rfl, Hj, Ha.symm⟩
  | LRmw aq rl b0 ts rvs wvs cls =>
    simp only [lbWr, Option.some.injEq, Prod.mk.injEq] at Hwr
    obtain ⟨rfl, rfl⟩ := Hwr
    exact ⟨rl, b0, wvs.length, j, rfl, Hj, Ha.symm⟩

theorem lblOfRow (GD : Gdexec) (i : Agent) (k : Nat) (lb : Lbl) :
    (AxOpsem.grow GD i)[k]? = some lb → gxLbl GD.gdG (i, k) = some lb :=
  rowReadLbl GD i k lb

theorem lblRow (GD : Gdexec) (i : Agent) (k : Nat) (lb : Lbl) :
    gxLbl GD.gdG (i, k) = some lb → (AxOpsem.grow GD i)[k]? = some lb := by
  unfold gxLbl AxOpsem.grow growG
  cases hp : GD.gdG.gxProg[i]? with
  | none => simp
  | some p => simp

section ix
variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF] [AxannotGS GF]
  [AxSpinX.Xv6G GF]

/-! # 1. The bridge's instance premises -/

theorem HGX (L : Xlay) (GT : GdexecT) (nm : Xv6N) :
    ∀ GD, rvwmoCatConsistent GD →
      @AxirisG.gconstInterp GF (AxSpinX2.xG L GT nm) GD ⊢ ⌜GD = gtAdGd GT⌝ :=
  fun _ _ => .rfl

theorem HtextX (L : Xlay) (GT : GdexecT) (nm : Xv6N) (img : Image) (i : Agent) :
    textFixed (gtAdGd GT) i img →
    ∀ GD, rvwmoCatConsistent GD →
      @AxirisG.gconstInterp GF (AxSpinX2.xG L GT nm) GD ⊢ ⌜textFixed GD i img⌝ := by
  intro Hfix GD Hc
  iintro Hg
  ihave %Heq := (HGX L GT nm GD Hc) $$ Hg
  subst Heq
  ipureintro
  exact Hfix

theorem HlocX (L : Xlay) (GT : GdexecT) (nm : Xv6N) (i : Agent) :
    ∀ GD ls k, rvwmoCatConsistent GD →
      @AxirisG.gconstInterp GF (AxSpinX2.xG L GT nm) GD ∗
        @AxirisG.localInterp GF (AxSpinX2.xG L GT nm) GD i k ls ⊢
      |==> ∃ ls', @AxirisG.localInterp GF (AxSpinX2.xG L GT nm) GD i (k + 1) ls' := by
  intro GD ls k _
  iintro -
  imodintro
  iexists (() : Unit)
  iapply (AxSpinWit.localTrue (gtAdGd GT) Xv6N Unit (protXv6 L) nm GD i (k + 1) ())

theorem naWfEmpty (_L : Xlay) (GT : GdexecT) (_nm : Xv6N) (e : Geid) (na : Mea GF) :
    ⊢ naSplittingWf (@Axpol.lobp (xv6Pol GT) (gtAdGd GT) e) na (∅ : Mea GF) (∅ : Mea GF) :=
  AxSpinWit.naSplittingWfEmpty _ na

/-- A fetch is a non-write event: the frame rule. -/
theorem HflowX (L : Xlay) (GT : GdexecT) (nm : Xv6N) (HL : xlayOk L)
    (Hcons : rvwmoCatConsistent (gtAdGd GT)) (img : Image) (i : Agent) :
    ∀ GD ls k, rvwmoCatConsistent GD →
      (∃ lb aq base n vs, (AxOpsem.grow GD i)[k]? = some lb ∧ aident lb = .IRead aq base n ∧
         imgBytes img base n = some vs) →
      @AxirisG.gconstInterp GF (AxSpinX2.xG L GT nm) GD ∗
        @AxirisG.localInterp GF (AxSpinX2.xG L GT nm) GD i k ls ⊢
      @fetchFlow hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) GD i k := by
  intro GD ls k Hc ⟨lb, aq, base, n, vs, Hlb, Hid, _⟩
  iintro ⟨Hg, -⟩
  ihave %Heq := (HGX L GT nm GD Hc) $$ Hg
  subst Heq
  have Hnw := rowReadNotW (gtAdGd GT) i k lb aq base n Hlb Hid
  unfold fetchFlow
  iintro %na ⟨Hpg, Hannot⟩
  ihave %Hnin := naAtProgressNotElemOf (gtAdGd GT) i k na $$ Hpg
  imod annotAlloc na (i, k) iprop(True) Hnin $$ Hannot with ⟨Hannot, -⟩
  imodintro
  inext
  imodintro
  iexists iprop(True), (∅ : Mea GF), (∅ : Mea GF), (() : Unit)
  isplitr
  · iapply (naWfEmpty L GT nm (i, k) na)
  isplitr
  · iapply (fxRead L GT nm HL Hcons (i, k) Hnw)
  isplitl [Hannot]
  · rw [AxLockWp.annotInsertEq na (i, k) iprop(True)]
    iexact Hannot
  · iapply (AxSpinWit.localTrue (gtAdGd GT) Xv6N Unit (protXv6 L) nm (gtAdGd GT) i (k + 1) ())

/-! # 2. The private stack slot -/

def dokSlot (pa : Int) : Int → Nat → Prop := fun base n => base = pa ∧ n = 8

/-- The store's output: the row item's data at the event. -/
def OutSt (GT : GdexecT) (i : Agent) (pa : Int) (k : Nat) (data : List (BitVec 8)) :
    IProp GF :=
  iprop(⌜graphData (gtAdGd GT) (i, k) = some data ∧
    ∃ lb rl, (AxOpsem.grow (gtAdGd GT) i)[k]? = some lb ∧
      aidentWr (aident lb) = some (rl, pa, data.length)⌝)

theorem FstSlot (L : Xlay) (GT : GdexecT) (nm : Xv6N) (HL : xlayOk L)
    (Hcons : rvwmoCatConsistent (gtAdGd GT)) (i : Agent) (pa : Int)
    (Hpriv : ∀ j : Nat, j < 8 → priv L (pa + (j : Int)) i)
    (Hw8 : ∀ (k : Nat) (lb : Lbl) (rl : Bool) (b : Int) (m : Nat), (AxOpsem.grow (gtAdGd GT) i)[k]? = some lb →
      aidentWr (aident lb) = some (rl, b, m) → m ≤ 8) :
    ⊢ @FstM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent (dokSlot pa) i
        (OutSt GT i pa) := by
  unfold FstM
  iintro %GD %ls %k %data %base %n %Hc #Hg _ %Hgd %Hd
  ihave %Heq := (HGX L GT nm GD Hc) $$ Hg
  subst Heq
  obtain ⟨⟨Hb, -⟩, lb, rl, Hlb, Hid⟩ := Hd
  rw [Hb] at Hid
  have Hisw : gisW (gtAdGd GT).gdG (i, k) = true := by
    unfold gisW
    rw [lblOfRow _ _ _ _ Hlb]
    cases lb <;> simp [aident, aidentWr] at Hid ⊢ <;> rfl
  have Hsg : ∀ a v, gwritesByte (gtAdGd GT).gdG (i, k) a v → priv L a (i, k).1 := by
    intro a v Hw
    obtain ⟨rl', b, m, j, Hid', Hj, rfl⟩ := gwbIdent _ _ _ _ _ (lblOfRow _ _ _ _ Hlb) Hw
    rw [Hid] at Hid'
    simp only [Option.some.injEq, Prod.mk.injEq] at Hid'
    obtain ⟨rfl, rfl, rfl⟩ := Hid'
    have Hm := Hw8 k lb rl pa data.length Hlb Hid
    exact Hpriv j (by omega)
  unfold dflowO
  iintro %na ⟨Hpg, Hannot⟩
  ihave %Hnin := naAtProgressNotElemOf (gtAdGd GT) i k na $$ Hpg
  imod annotAlloc na (i, k) iprop(True) Hnin $$ Hannot with ⟨Hannot, -⟩
  imodintro
  inext
  imodintro
  iexists iprop(True), (∅ : Mea GF), (∅ : Mea GF), (() : Unit)
  isplitr
  · iapply (naWfEmpty L GT nm (i, k) na)
  isplitr
  · iapply (fxPrivWrite L GT nm HL Hcons (i, k) Hisw Hsg)
  isplitl [Hannot]
  · rw [AxLockWp.annotInsertEq na (i, k) iprop(True)]
    iexact Hannot
  isplitr
  · iapply (AxSpinWit.localTrue (gtAdGd GT) Xv6N Unit (protXv6 L) nm (gtAdGd GT) i (k + 1) ())
  · unfold OutSt
    ipureintro
    exact ⟨Hgd, lb, rl, Hlb, Hid⟩

/-- The reload's annotation. -/
def RLfact (GT : GdexecT) (i : Agent) (pa : Int) (kr : Nat) (vw : List (BitVec 8)) : Prop :=
  ∀ (j : Nat) a t v, (clRange pa 8)[j]? = some a → greadsByte (gtAdGd GT).gdG (i, kr) a t v →
    vw[j]? = some v

def RLann (GT : GdexecT) (i : Agent) (pa : Int) (kr : Nat) (vw : List (BitVec 8)) (k : Nat) :
    IProp GF :=
  if k = kr then iprop(⌜RLfact GT i pa kr vw⌝) else iprop(True)

def OutLd (GT : GdexecT) (i : Agent) (pa : Int) (kr : Nat) (vw : List (BitVec 8)) (k : Nat)
    (v : List (BitVec 8)) : IProp GF :=
  iprop(⌜graphValue (gtAdGd GT) (i, k) = some v ∧
    ∃ lb aq, (AxOpsem.grow (gtAdGd GT) i)[k]? = some lb ∧
      aidentRd (aident lb) = some (aq, pa, 8)⌝ ∗
    AxAnnot.annotOwn (i, k) (RLann GT i pa kr vw k))

theorem FldSlot (L : Xlay) (GT : GdexecT) (nm : Xv6N) (HL : xlayOk L)
    (Hcons : rvwmoCatConsistent (gtAdGd GT)) (i : Agent) (pa : Int) (kr kw : Nat)
    (vw : List (BitVec 8)) (cls : WmClass)
    (Hpriv : ∀ j : Nat, j < 8 → priv L (pa + (j : Int)) i)
    (Hnormw : ∀ (k : Nat) (lb : Lbl) (aq rl : Bool) (n : Nat), (AxOpsem.grow (gtAdGd GT) i)[k]? = some lb →
      aident lb = .IRmw aq rl pa n → n ≠ 8)
    (Hw : (AxOpsem.grow (gtAdGd GT) i)[kw]? = some (.LStore false pa vw cls))
    (Hlen : vw.length = 8) (Hkw : kw < kr)
    (Hbetween : ∀ (k' : Nat) (lb' : Lbl) (rl : Bool) (b : Int) (m : Nat), kw < k' ∧ k' < kr → (AxOpsem.grow (gtAdGd GT) i)[k']? = some lb' →
      aidentWr (aident lb') = some (rl, b, m) → b + (m : Int) ≤ pa ∨ pa + 8 ≤ b) :
    ⊢ @FldM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent (dokSlot pa) i
        (OutLd GT i pa kr vw) := by
  unfold FldM
  iintro %GD %ls %k %v %base %n %Hc #Hg _ %Hgv %Hd
  ihave %Heq := (HGX L GT nm GD Hc) $$ Hg
  subst Heq
  obtain ⟨⟨Hb, Hn⟩, lb, aq, Hlb, Hid⟩ := Hd
  rw [Hb, Hn] at Hid
  have Hld : ∃ ts vs, lb = .LLoad aq pa ts vs := by
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
      exact absurd Hn (Hnormw k _ aq' rl wvs.length Hlb rfl)
  obtain ⟨ts, vs, rfl⟩ := Hld
  have Hnw : gisW (gtAdGd GT).gdG (i, k) = false := by
    unfold gisW
    rw [lblOfRow _ _ _ _ Hlb]
    rfl
  have Hflow : ⊢ @flowEqDyn hlc GF _ (AxSpinX2.xG L GT nm) (gtAdGd GT) (i, k)
      (@Axpol.sPol (xv6Pol GT) (gtAdGd GT) (i, k)) (∅ : Mea GF) (RLann GT i pa kr vw k) := by
    unfold RLann
    by_cases hk : k = kr
    · subst hk
      rw [if_pos rfl]
      have H1 : ∀ a, a ∈ clRange pa 8 → priv L a (i, k).1 := by
        intro a Ha
        rw [inClr] at Ha
        have h := Hpriv (a - pa).toNat (by omega)
        rwa [show pa + (((a - pa).toNat : Nat) : Int) = a by omega] at h
      have H2 : ∀ (j : Nat) a v', (clRange pa 8)[j]? = some a → vw[j]? = some v' →
          gwritesByte (gtAdGd GT).gdG (i, kw) a v' := by
        intro j a v' Hj Hv'
        obtain ⟨rfl, -⟩ := AxSpinX4.clRangeLookup _ _ _ _ Hj
        exact (gwbStoren _ _ _ _ _ (lblOfRow _ _ _ _ Hw)).1 j v' Hv'
      have H3 : vw.length = (clRange pa 8).length := by
        simp [clRange, Hlen]
      have H4 : WeakRvwmoGraph.gpo (gtAdGd GT).gdG (i, kw) (i, k) := by
        refine ⟨rfl, Hkw, ?_, ?_⟩
        · rw [lblOfRow _ _ _ _ Hw]; rfl
        · rw [lblOfRow _ _ _ _ Hlb]; rfl
      have H5 : ∀ w' a v', a ∈ clRange pa 8 → gwritesByte (gtAdGd GT).gdG w' a v' →
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
          omega
      exact fxPrivReadn L GT nm HL Hcons (i, k) (i, kw) (clRange pa 8) vw Hnw H1 H2 H3 H4 H5
    · rw [if_neg hk]
      exact fxRead L GT nm HL Hcons (i, k) Hnw
  unfold dflowO
  iintro %na ⟨Hpg, Hannot⟩
  ihave %Hnin := naAtProgressNotElemOf (gtAdGd GT) i k na $$ Hpg
  imod annotAlloc na (i, k) (RLann GT i pa kr vw k) Hnin $$ Hannot with ⟨Hannot, Hh⟩
  imodintro
  inext
  imodintro
  iexists (RLann GT i pa kr vw k), (∅ : Mea GF), (∅ : Mea GF), (() : Unit)
  isplitr
  · iapply (naWfEmpty L GT nm (i, k) na)
  isplitr
  · iapply Hflow
  isplitl [Hannot]
  · rw [AxLockWp.annotInsertEq na (i, k) (RLann GT i pa kr vw k)]
    iexact Hannot
  isplitr
  · iapply (AxSpinWit.localTrue (gtAdGd GT) Xv6N Unit (protXv6 L) nm (gtAdGd GT) i (k + 1) ())
  · unfold OutLd
    isplitr
    · ipureintro
      exact ⟨Hgv, _, aq, Hlb, Hid⟩
    · iexact Hh

end ix

end Weak
