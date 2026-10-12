/-
Weak: **THEOREM 2, REDUCE PINS P1 — THE RELOAD CUT** (`notes/weak-lb-thm2-pins.md` §P1).  NEW
Lean file (no Rocq source).  The generic arm `cutReload` that refutes "a reload read a value other
than its spill" at the row end `kr + 1`, and the GATE premise shape `Hgate` the six leaf lanes
(AxSpinE8, AxSpinPO4, AxSpinHdA/Hd9, AxSpinAq2, AxSpinPO6, AxSpinRl4b) put in place of their
reload pins `Hval : graphValue (i, kr) = some vw`.

## API for the leaf lanes (read this)

Notation: `LEN := (AxOpsem.grow (gtAdGd GT) i).length`, `WPd s Ψ := @wpdM hlc GF _ (AxSpinX2.xG L
GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i s Ψ`, `vw` = the spill's bytes (pure at every
site), `pa` = the slot (`paZ pa` in `XxLd`), `kr` = the reload's row position.

* **`AxSpinT2i.Gate GT i kr vw : Prop := graphValue (gtAdGd GT) (i, kr) ≠ some vw → LEN ≤ kr + 1`**
  — the premise that REPLACES the pin (`Hgate : AxSpinT2i.Gate GT i kr vw`; unfold it or use it
  directly, it is a plain `def`).  "A row that continues past the reload read the spill."
* **`AxSpinT2i.gateOfPin : graphValue (gtAdGd GT) (i, kr) = some vw → AxSpinT2i.Gate GT i kr vw`**
  (old unguarded pin ⇒ gate: the stage-1/2 statements stay corollaries) and
  **`AxSpinT2i.gateOfPinG : (kr < LEN → graphValue … = some vw) → AxSpinT2i.Gate GT i kr vw`**
  (AllocPins2's GUARDED pin form ⇒ gate).
* **`cutReload L GT nm Hcons i kr pa vw vs Ψ Hrd Hvw Hgv Hne Hend pr :
  ⊢ AxAnnot.annotOwn (i, kr) iprop(⌜RLfact GT i pa kr vw⌝) -∗ WPd ⟨pr, kr + 1⟩ Ψ`**, with
  `Hcons : rvwmoCatConsistent (gtAdGd GT)`, `Hrd : AxSpinT2i.RdAt (AxOpsem.grow (gtAdGd GT) i) kr
  pa 8` (`∃ lb, row[kr]? = some lb ∧ ∃ aq, aident lb = .IRead aq pa 8`, definitionally `row[kr]? =
  some lb ∧ ishape (.RL pa 8) lb` — exactly what `RowSh`/`rowShPAt` give for the reload item; pass
  `⟨lb, Hlb, Hsh⟩`), `Hvw : vw.length = 8` (`XxLd`'s `Hlen`), `Hgv : graphValue (gtAdGd
  GT) (i, kr) = some vs` and `Hne : vs ≠ vw` (both from `XxLd`'s continuation / the `by_cases`),
  `Hend : LEN ≤ kr + 1`.  No knowledge of `Ψ` is needed: the arm is REFUTED (the annotation read
  back past the row end says the reload's bytes are `vw`, contradicting `Hne`).
* **`AxSpinT2i.cutReloadG`**: the same with `Hgate : AxSpinT2i.Gate GT i kr vw` in place of
  `Hend` (it derives `Hend` from `Hgv`, `Hne`, `Hgate`).  THE LEAF SCRIPT, in `XxLd`'s
  continuation (`iintro %vs %rs' %ib' %Hl %Hgood %Hgv Hann`):
  ```
  by_cases Hv : vs = vw
  · subst Hv  -- today's script (the pin's value is now `Hgv`)
    ...
  · iapply (AxSpinT2i.cutReloadG L GT nm Hcons i kr _ vw vs Ψ Hrd Hvw Hgv Hv Hgate _) $$ Hann
  ```
  (other hypotheses in the context are dropped: `IProp` is affine).  For the `aqS1`/`rlS1` sites
  (`graphValue … = graphData GD (i, kw)` pins) `vw` is the spill's own data — the store label at
  `kw` (`XxLd`'s `Hw`) gives `graphData GD (i, kw) = some vw`; the gate is stated against `vw`.
* Pure core: **`AxSpinT2i.rlFactEq`** (`RdAt` + `graphValue = some vs` + `RLfact … vw` +
  `vw.length = 8` ⇒ `vs = vw`), **`AxSpinT2i.lenOfGate`** (`Gate` + `graphValue = some vs` +
  `vs ≠ vw` ⇒ `LEN ≤ kr + 1`).

## How

`cutReload` = the local end lemma `AxSpinT2i.wpdEnd1` (at `k0 = kr + 1 ≥ LEN` every step is
administrative and AxWpD's row-end clause hands the hart's annotation back as a pure fact) with
`P := RLfact GT i pa kr vw`; the post is closed by contradiction via `AxSpinT2i.rlFactEq`
(`AxSpinT2i.ldOfRd`: the read item with a graph value is an `LLoad` carrying it; `AxSpinT2i.ldEq`:
a per-byte read fact over `clRange pa 8` pins a load's values — `RLfact` is literally that fact).

## Deviations / honesty

1. **Local copies** (same statements and proofs): `AxSpinT2i.rowEndShape` / `wpdEndAnn` /
   `wpdEnd1` (= `AxSpinT2h.*` = `AxSpinApA.*`) and `AxSpinT2i.RdAt`/`ldOfRd`/`ldReads`/`ldEq`
   (= `AxSpinT2h.*`).  AxSpinT2h imports AxSpinPO6 (and HdC → Aq2-level files), so importing it
   would make the leaf files unable to import this file (cycle); T2h is also under the Q-S2-B
   rework.  `AxSpinT2i.RdAt` is T2h's `RdAt` verbatim (it unfolds `ishape (.RL pa n)`: AxSpinPOr,
   where `ishape` lives, imports AxSpinE8, a leaf).
2. The design's `cutReload` takes the pure facts as `-∗ ⌜…⌝ →` premises; here they are Lean
   arguments (same content, easier to apply in a leaf script).
3. Nothing about the row family (AxSpinT2f) is used here: the gate is stated on `graphValue`, the
   family's `t2GateOk` reload clause (T2f, P1 step 1(a)) is bridged in ApB.

HONESTY.  Fully proved; the arm is a refutation, so no row with a wrong reload value at its end
`kr + 1` needs a post.  `Gate` is weaker than the guarded pin exactly at `LEN = kr + 1` (the row
stops right after a wrong reload): that row is now COVERED (refuted) instead of excluded.

**Reused:** `RLfact` (AxSpinE5), `graphValue`/`gxLbl`/`AxWp.growLookup`/
`annotAgreeBig` (AxWp), `lblTsLen` (AxSpinX5), `clRangeLookup2` (AxSpinX4), `AxSpinRow.lbAdminWdata`,
`shSkip`/`AxSpinWit.gconstEq` (AxSpinWit), `AxSpinProt7.readbackBig`, `progressOblMaybestuck`
(AxWp2), `AxWpD.wpdMUnfoldStep`, `postLifting`.  New unqualified name: `cutReload` (grepped
absent); every helper is `AxSpinT2i.*`.
-/
import Weak.AxSpinE6
import Weak.AxSpinProt7
import Weak.AxSpinX5

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-! # 1. Pure: the reload read and the gate -/

/-- Row item `k` is a read of `n` bytes at `pa` (the `RowSh` shape of a reload item). -/
def AxSpinT2i.RdAt (row : List Lbl) (k : Nat) (pa : Int) (n : Nat) : Prop :=
  ∃ lb, row[k]? = some lb ∧ ∃ aq, aident lb = .IRead aq pa n

/-- (= `AxSpinT2h.ldOfRd`) a read item with a graph value is a load label carrying that value. -/
theorem AxSpinT2i.ldOfRd (GD : Gdexec) (i k : Nat) (pa : Int) (n : Nat) (vs : List (BitVec 8)) :
    AxSpinT2i.RdAt (AxOpsem.grow GD i) k pa n → graphValue GD (i, k) = some vs →
    ∃ aq ts, gxLbl GD.gdG (i, k) = some (.LLoad aq pa ts vs) ∧ vs.length = n := by
  rintro ⟨lb, Hlb, aq, Hid⟩ Hgv
  have Hl := AxWp.growLookup GD i k lb Hlb
  unfold graphValue at Hgv
  rw [Hl] at Hgv
  cases lb with
  | LLoad aq' b ts vs' =>
    simp only [aident] at Hid
    injection Hid with h1 h2 h3
    subst h1 h2
    simp only [Option.bind, lblValue, Option.some.injEq] at Hgv
    subst Hgv
    exact ⟨aq', ts, Hl, h3⟩
  | LStore _ _ _ _ => simp [aident] at Hid
  | LFence _ _ _ _ => simp [aident] at Hid
  | LIo _ _ _ => simp [aident] at Hid
  | LRmw _ _ _ _ _ _ _ => simp [aident] at Hid

/-- (= `AxSpinT2h.ldReads`) every byte of a load label is read. -/
theorem AxSpinT2i.ldReads (G : Gexec) (Hwf : gwf G) (e : Geid) (aq : Bool) (base : Int)
    (ts : List Nat) (vs : List (BitVec 8)) (j : Nat) (v : BitVec 8) :
    gxLbl G e = some (.LLoad aq base ts vs) → vs[j]? = some v →
    ∃ t, greadsByte G e (base + (j : Int)) t v := by
  intro Hl Hv
  have Hlen := lblTsLen G Hwf e aq base ts vs Hl
  have Hj : j < ts.length := by
    have := (List.getElem?_eq_some_iff.1 Hv).1
    omega
  exact ⟨ts[j], _, base, ts, vs, j, Hl, rfl, List.getElem?_eq_getElem Hj, Hv, rfl⟩

/-- (= `AxSpinT2h.ldEq`) a per-byte read fact pins a load's values. -/
theorem AxSpinT2i.ldEq (G : Gexec) (Hwf : gwf G) (e : Geid) (aq : Bool) (base : Int)
    (ts : List Nat) (n : Nat) (vs tgt : List (BitVec 8)) :
    gxLbl G e = some (.LLoad aq base ts vs) → vs.length = n → tgt.length = n →
    (∀ (j : Nat) a t b, (clRange base n)[j]? = some a → greadsByte G e a t b →
      tgt[j]? = some b) →
    vs = tgt := by
  intro Hl Hvl Htl Hf
  apply List.ext_getElem?
  intro j
  by_cases Hj : j < n
  · have Hv : vs[j]? = some (vs[j]'(by omega)) := List.getElem?_eq_getElem (by omega)
    obtain ⟨t, Hr⟩ := AxSpinT2i.ldReads G Hwf e aq base ts vs j _ Hl Hv
    rw [Hv]
    exact (Hf j _ t _ (clRangeLookup2 base n j Hj) Hr).symm
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

/-- The reload's annotation pins the value it read to the spill's bytes. -/
theorem AxSpinT2i.rlFactEq (GT : GdexecT) (Hcons : rvwmoCatConsistent (gtAdGd GT)) (i : Agent)
    (kr : Nat) (pa : Int) (vw vs : List (BitVec 8))
    (Hrd : AxSpinT2i.RdAt (AxOpsem.grow (gtAdGd GT) i) kr pa 8) (Hvw : vw.length = 8)
    (Hgv : graphValue (gtAdGd GT) (i, kr) = some vs) (HF : RLfact GT i pa kr vw) : vs = vw := by
  obtain ⟨aq, ts, Hl, Hvl⟩ := AxSpinT2i.ldOfRd _ i kr pa 8 vs Hrd Hgv
  exact AxSpinT2i.ldEq _ Hcons.1 (i, kr) aq pa ts 8 vs vw Hl Hvl Hvw HF

/-- THE RELOAD GATE (replaces the pin `graphValue (i, kr) = some vw`): a row that continues past
the reload at `kr` read the spill `vw`. -/
def AxSpinT2i.Gate (GT : GdexecT) (i : Agent) (kr : Nat) (vw : List (BitVec 8)) : Prop :=
  graphValue (gtAdGd GT) (i, kr) ≠ some vw → (AxOpsem.grow (gtAdGd GT) i).length ≤ kr + 1

/-- The old (unguarded) pin implies the gate. -/
theorem AxSpinT2i.gateOfPin {GT : GdexecT} {i : Agent} {kr : Nat} {vw : List (BitVec 8)}
    (H : graphValue (gtAdGd GT) (i, kr) = some vw) : AxSpinT2i.Gate GT i kr vw :=
  fun h => absurd H h

/-- The guarded pin (`AllocPins2` form) implies the gate. -/
theorem AxSpinT2i.gateOfPinG {GT : GdexecT} {i : Agent} {kr : Nat} {vw : List (BitVec 8)}
    (H : kr < (AxOpsem.grow (gtAdGd GT) i).length → graphValue (gtAdGd GT) (i, kr) = some vw) :
    AxSpinT2i.Gate GT i kr vw := by
  intro h
  refine Nat.le_of_not_lt fun hl => h (H ?_)
  omega

/-- A wrong reload value under the gate puts the row end at `kr + 1`. -/
theorem AxSpinT2i.lenOfGate {GT : GdexecT} {i : Agent} {kr : Nat} {vw vs : List (BitVec 8)}
    (Hg : AxSpinT2i.Gate GT i kr vw) (Hgv : graphValue (gtAdGd GT) (i, kr) = some vs)
    (Hne : vs ≠ vw) : (AxOpsem.grow (gtAdGd GT) i).length ≤ kr + 1 :=
  Hg fun h => Hne (Option.some.inj (Hgv.symm.trans h))

/-! # 2. Past the row end (local copy of `AxSpinT2h.wpdEndAnn` / `wpdEnd1`, deviation 1) -/

/-- (= `AxSpinT2h.rowEndShape`) past the row end, a program step is administrative and keeps
the position. -/
theorem AxSpinT2i.rowEndShape (row : List Lbl) (s : Athread) (l : Wlabel) (s' : Athread)
    (Hnone : row[s.atK]? = none) :
    AxOpsem.astepProg row s l s' → AxOpsem.lbAdminAx true l ∧ s'.atK = s.atK := by
  intro h
  cases h with
  | AStepAdmin p k d l p' d' hadm hst => exact ⟨hadm, rfl⟩
  | AStepWrite p k d l lb p' d' hlk _ _ _ _ =>
    simp only at Hnone
    rw [hlk] at Hnone
    cases Hnone
  | AStepFence p k d l lb p' d' hlk _ _ _ =>
    simp only at Hnone
    rw [hlk] at Hnone
    cases Hnone

section rowend
open Iris.Std.PartialMap
variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF] [AxannotGS GF]
  [AxSpinX.Xv6G GF]

/-- (= `AxSpinT2h.wpdEndAnn`) PAST THE ROW END, an annotation readback. -/
theorem AxSpinT2i.wpdEndAnn (L : Xlay) (GT : GdexecT) (nm : Xv6N) (i : Agent) (k0 : Nat)
    (Hend : (AxOpsem.grow (gtAdGd GT) i).length ≤ k0) (m : Mea GF)
    (Hm : ∀ e, e ∈ (FiniteMap.dom_set m : GSet Geid) → e.1 = i) (Φ : Athread → IProp GF)
    (HRQ : ∀ s, ([∗map] R ∈ m, R) ⊢ Φ s) :
    ⊢ ([∗map] e ↦ R ∈ m, AxAnnot.annotOwn e R) -∗ ∀ pr : Pexv6,
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
        ⟨pr, k0⟩ Φ := by
  have Hnone : (AxOpsem.grow (gtAdGd GT) i)[k0]? = none := List.getElem?_eq_none Hend
  have H : ⊢ ∀ pr : Pexv6, ([∗map] e ↦ R ∈ m, AxAnnot.annotOwn e R) -∗
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
        ⟨pr, k0⟩ Φ := by
    iloeb as IH
    iintro %pr Hp
    iapply (@AxWpD.wpdMUnfoldStep hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT)
      rvwmoCatConsistent .MaybeStuck i _ _).2
    isplit
    · iapply (@progressOblMaybestuck GF (AxSpinX2.xG L GT nm) _ i _).2
      itrivial
    unfold wpdMPreStepDef
    iintro %GD' %ls ⟨%Hc, #Hg, -⟩
    ihave %Hg := (AxSpinWit.gconstEq (gtAdGd GT) Xv6N Unit (protXv6 L) nm GD') $$ Hg
    subst GD'
    isplit
    · iintro %id %K %Hst
      obtain ⟨lb, Hlb, -⟩ := Hst
      simp only at Hlb
      rw [Hnone] at Hlb
      cases Hlb
    isplit
    · iintro %l %s' %Hst %-
      obtain ⟨Hadm, Hk'⟩ := AxSpinT2i.rowEndShape _ _ l s' Hnone Hst
      rw [AxSpinRow.lbAdminWdata l Hadm]
      obtain ⟨p', k1⟩ := s'
      simp only at Hk'
      subst Hk'
      iapply (shSkip (gtAdGd GT) Xv6N Unit (protXv6 L) nm i)
      inext
      iapply IH $$ %p' Hp
    isplit
    · iintro %s' %Hw
      obtain ⟨p', k1⟩ := s'
      obtain ⟨Hk, -⟩ := Hw
      simp only at Hk
      subst Hk
      iapply (shSkip (gtAdGd GT) Xv6N Unit (protXv6 L) nm i)
      inext
      iapply IH $$ %p' Hp
    · iintro %-
      unfold postLifting
      iintro %na Hna
      ihave ⟨%Hdomi, #Hw⟩ := annotAgreeBig na m $$ Hna Hp
      imodintro
      isplitl [Hna]
      · iexact Hna
      iintro Hbig
      ihave HR := AxSpinProt7.readbackBig na m i Hdomi Hm $$ Hbig Hw
      inext
      imodintro
      iapply (HRQ _) $$ HR
  iintro Hp %pr
  iapply H $$ %pr Hp

/-- (= `AxSpinT2h.wpdEnd1`) ONE pure annotation of hart `i` read back past the row end. -/
theorem AxSpinT2i.wpdEnd1 (L : Xlay) (GT : GdexecT) (nm : Xv6N) (i : Agent) (k0 : Nat)
    (Hend : (AxOpsem.grow (gtAdGd GT) i).length ≤ k0) (e : Geid) (he : e.1 = i) (P : Prop)
    (Φ : Athread → IProp GF) (HRQ : P → ∀ s, ⊢ Φ s) (pr : Pexv6) :
    ⊢ AxAnnot.annotOwn e iprop(⌜P⌝) -∗
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
        ⟨pr, k0⟩ Φ := by
  have hn : get? (∅ : Mea GF) e = none := lookupEmpty
  have Hm : ∀ e', e' ∈ (FiniteMap.dom_set (insert (∅ : Mea GF) e iprop(⌜P⌝)) : GSet Geid) →
      e'.1 = i := by
    intro e' he'
    rw [domInsert, domEmpty] at he'
    rcases elemOfUnion.1 he' with h | h
    · rw [elemOfSingleton.1 h]; exact he
    · exact absurd h (fun h' => (elemOfEmpty (S := GSet Geid)).1 h')
  have HR : ∀ s, ([∗map] R ∈ insert (∅ : Mea GF) e iprop(⌜P⌝), R) ⊢ Φ s := by
    intro s
    iintro Hb
    icases (BigSepM.bigSepM_insert hn).1 $$ Hb with ⟨%HP, -⟩
    iapply (HRQ HP s)
  iintro A
  ihave W := (AxSpinT2i.wpdEndAnn L GT nm i k0 Hend _ Hm Φ HR) $$ [A]
  · iapply (BigSepM.bigSepM_insert hn).2
    isplitl [A]
    · iexact A
    iapply BigSepM.bigSepM_empty.2
    itrivial
  iapply W $$ %pr

/-! # 3. The reload cut -/

/-- THE RELOAD CUT: at the row end `kr + 1` right after a reload that read `vs ≠ vw` (the spill),
the reload's own annotation (`XxLd`'s `RLfact`) read back refutes the row: every post holds. -/
theorem cutReload (L : Xlay) (GT : GdexecT) (nm : Xv6N) (Hcons : rvwmoCatConsistent (gtAdGd GT))
    (i : Agent) (kr : Nat) (pa : Int) (vw vs : List (BitVec 8)) (Ψ : Athread → IProp GF)
    (Hrd : AxSpinT2i.RdAt (AxOpsem.grow (gtAdGd GT) i) kr pa 8) (Hvw : vw.length = 8)
    (Hgv : graphValue (gtAdGd GT) (i, kr) = some vs) (Hne : vs ≠ vw)
    (Hend : (AxOpsem.grow (gtAdGd GT) i).length ≤ kr + 1) (pr : Pexv6) :
    ⊢ AxAnnot.annotOwn (GF := GF) (i, kr) iprop(⌜RLfact GT i pa kr vw⌝) -∗
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
        ⟨pr, kr + 1⟩ Ψ :=
  AxSpinT2i.wpdEnd1 L GT nm i (kr + 1) Hend (i, kr) rfl _ Ψ
    (fun HF => absurd (AxSpinT2i.rlFactEq GT Hcons i kr pa vw vs Hrd Hvw Hgv HF) Hne) pr

/-- `cutReload` with the GATE premise (what the leaf lanes hold) in place of the row-end bound. -/
theorem AxSpinT2i.cutReloadG (L : Xlay) (GT : GdexecT) (nm : Xv6N)
    (Hcons : rvwmoCatConsistent (gtAdGd GT)) (i : Agent) (kr : Nat) (pa : Int)
    (vw vs : List (BitVec 8)) (Ψ : Athread → IProp GF)
    (Hrd : AxSpinT2i.RdAt (AxOpsem.grow (gtAdGd GT) i) kr pa 8) (Hvw : vw.length = 8)
    (Hgv : graphValue (gtAdGd GT) (i, kr) = some vs) (Hne : vs ≠ vw)
    (Hgate : AxSpinT2i.Gate GT i kr vw) (pr : Pexv6) :
    ⊢ AxAnnot.annotOwn (GF := GF) (i, kr) iprop(⌜RLfact GT i pa kr vw⌝) -∗
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
        ⟨pr, kr + 1⟩ Ψ :=
  cutReload L GT nm Hcons i kr pa vw vs Ψ Hrd Hvw Hgv Hne (AxSpinT2i.lenOfGate Hgate Hgv Hne) pr

end rowend

end Weak
