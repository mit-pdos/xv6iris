/-
Weak: **Phase 2b, part 2 of the spinlock plan -- the WORD HANDLE surface at `spinOb6`**: n-byte
owned leaves, FRACTIONAL read handles and their recombination, annotation split/merge ANYWHERE (not
only inside a step), and the acquire / release contracts incl. the release whose handle is
anchored AT THE CLAIM.  (Phase-2b files: `AxSpinH4` n-byte nodes/`RbN`/`spinOb6`; this one;
`AxSpinH6` certificate 1; `AxSpinH7` certificate 2.)

Rocq: `iris/AxSpinH5.v` @ xxvzwolszwmp.

## The Rocq header, in substance

DEFINITION `hdlw GT nm q a n e vs` = `e ↦ₐ RbN nm.1 GD q (clRange a n) e vs` -- "fraction `q` of
  the word `[a, a+n)` arrives at `e` in phase 2, value `vs`" (`vs = []`: unknown); `q = 1` is the
  full (write) handle.
PROVED
  §1 `wpdAnnotMerge`/`wpdAnnotSplit`/`wpdAnnotEntail` (any `axGA2` instance): two fragments at ONE
     event merge (and split, and weaken) at ANY point of a WPd proof, through `iupdWpd` +
     `annotMerge`/`annotSplit`/`annotEntail` (AxSpinH2's "split only inside a step" and its
     missing "annot_merge step" are both lifted).  `hdlwSplit`/`hdlwJoin`: fractions at one anchor.
  §2 leaves at `spinOb6 ya (clRange xw nw) Cl cv` / `splPol`, hand `memRead n`/`memWrite n` nodes,
     ANY width `n` (no alignment needed by the leaves, only by `nbSingleSource`):
     `wpdLdOwnN` FRACTIONAL owned load (`hdlw q` at `e ∈ lobp r` ⇒ `hdlw q` at `r` with the read
       value, the agreement with the old value deposited at `r`);
     `wpdSdOwnN` owned store, FULL handle at `e ∈ lobp w`;
     `wpdSdOwnN2` owned store RECOMBINING two fractions `q1 + q2 = 1` at two lob-predecessors --
       deposits at `w` that the two fractions' values AGREE (one history);
     `wpdReloadOwnN` store `w` then same-word load `r` (ordered ⇒ the handle moves `w → r`;
       forwarded ⇒ per-byte `ownedReadRuleFwd`, nothing drawn).
     Contracts: `wpdAcquireGen6`/`wpdAcquireH6` (the claim's word component as `hdlw 1 xw nw c []`),
     `wpdReleaseGen6` (any family of po-earlier anchors), `wpdReleaseH6` (two anchors),
     `wpdReleaseH6Same` -- THE CS NEVER TOUCHES THE WORD: the handle is still AT THE CLAIM, merged
     with the claim's `locked ∗ lk->cpu` fragment by `wpdAnnotMerge`, drawn as one anchor;
     `wpdLkreadHeld6`: the holder's `lw lk` (draws `locked`, deposits `v ≠ 0`).
USAGE NOTE (Rocq): every leaf/contract concludes `∀ rs, WPd …`; the split/merge lemmas conclude a
  plain WPd.  All leaves and contracts share ONE policy (`splPol GT`, Rocq `l6_pol`).
HONEST LIMITS (unchanged): the reload leaf is proved but not exercised by a certificate here;
  fractions recombine only at a drawing EVENT; the lock word stays ONE byte; hand nodes, no
  fetch/decode.

## Deviations from Rocq

1. VOCABULARY (as `AxSpinH2`/`AxSpinH4`): `grow GD i !! k` ↦ `(AxOpsem.grow (gtAdGd GT) i)[k]?`,
   `S k` ↦ `k + 1`, `N` widths ↦ `Nat` (`N.to_nat n` ↦ `n`, `Hn : n ≠ 0`), `pa_z` ↦ `paZ`,
   `cl_range` ↦ `clRange`, `dom m` ↦ `FiniteMap.dom_set m : GSet Geid`, `B0`/`B1` ↦ `b0`/`b1`,
   `M unit` ↦ `SailM Unit`, `l !! j` ↦ `l[j]?`.  lean-sail hand nodes as `AxSpinH4` (`.impure (.ok
   (.memRead n 64 (h4rreq n l3pAkP pa))) KK`, answers `.Ok (wordOfBytes n vs, none)`; `.memWrite`
   likewise) and `AxSpinProt7` (`acqRmw`, `fenceM`, `relM`).
2. CONTEXTS: Rocq section variables are explicit leading arguments in Rocq's order, only where
   Rocq's section mechanism includes them (§1 `GD N obSt0 obi nm [pol]`; §2 `xw nw Cl cv GT nm`,
   then `cpu` and `Hcons HlkX` where used / named by `Proof using`; `hdlw` takes `GT nm` only).
   O2 STAGE C: Rocq's `Tf` argument of `AxGA2`/`tierA_wpd` is gone.  `invGS_gen HasNoLc Σ` ↦
   `[InvGS_gen hlc GF]` for any `hlc`.  The local instances `mgG`/`l6_G` ↦ `axGA2`/`shG` (=
   `AxSpinH4.s6G`) and `l6_pol` ↦ `splPol GT`, passed explicitly; the notations `GD`/`G`/`XS`/
   `OB`/`TW`/`LK`/`NH`/`R6`/`HW` are unfolded.
3. STATEMENT SHAPES (as `AxSpinH2`): wand chains ↦ `⊢ A -∗ B -∗ …`, pure premises stay `→`.
   `hdlw` is an `abbrev` (Rocq `Definition`), so handles match annotation fragments in proof mode.
4. PROOF ROUTE (not statements): `wpdReloadOwnN` splits on `gmoLt w r` classically (Rocq: the
   boolean `gmo_lt_b`), as `AxSpinH.evReloadOwn`.

**Rocq → Lean name map.**  `wpd_annot_merge` `wpdAnnotMerge`, `wpd_annot_split` `wpdAnnotSplit`,
`wpd_annot_entail` `wpdAnnotEntail`, `po_writes_gmo_beforeN` `poWritesGmoBeforeN`, `hdlw` `hdlw`,
`hdlw_split` `hdlwSplit`, `hdlw_join` `hdlwJoin`, `wpd_ld_own_n` `wpdLdOwnN`, `wpd_sd_own_n`
`wpdSdOwnN`, `wpd_sd_own_n2` `wpdSdOwnN2`, `wpd_reload_own_n` `wpdReloadOwnN`, `RL_RbN_1`
`RLRbN1`, `wpd_acquire_gen6` `wpdAcquireGen6`, `wpd_acquire_h6` `wpdAcquireH6`,
`wpd_release_gen6` `wpdReleaseGen6`, `wpd_release_h6` `wpdReleaseH6`, `wpd_release_h6_same`
`wpdReleaseH6Same`, `wpd_lkread_held6` `wpdLkreadHeld6`.

**Dropped:** none (21 Rocq decls = 18 + the local instances `mgG`/`l6_pol`/`l6_G` (inlined);
18 Lean).

**W13 (I) (plan `notes/weak-allocproc-plan.md` §C W13 (I); [OWN.27]).** the release lemmas' anchor-domain premise is `(lbIsR l || lbIsW l) = true` (was `lbIsMem l = true`): `gwf` admits I/O events, which `fence rw,w` does not order (RVWMO; D48).
-/
import Weak.AxSpinH2
import Weak.AxSpinH4

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D

/-! # 1. Annotation split / merge / weakening at ANY point of a WPd -/

section merge
variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF] [AxannotGS GF]
  (GD : Gdexec) (N obSt0 : Type) (obi : N → Gdexec → obSt0 → GSet Geid → IProp GF) (nm : N)
  [pol : Axpol]

theorem wpdAnnotMerge (i : Agent) (Φ : Athread → IProp GF) (s : Athread) (e : Geid)
    (P Q : IProp GF) :
    ⊢ AxAnnot.annotOwn e P -∗ AxAnnot.annotOwn e Q -∗
      (AxAnnot.annotOwn e iprop(P ∗ Q) -∗
        tierAWpd (hlc := hlc) GD N obSt0 obi nm s .MaybeStuck i Φ) -∗
      tierAWpd (hlc := hlc) GD N obSt0 obi nm s .MaybeStuck i Φ := by
  iintro HP HQ HΨ
  unfold tierAWpd
  iapply (@iupdWpd hlc GF _ (axGA2 GD N obSt0 obi nm) pol .MaybeStuck i s Φ)
  unfold interpMod
  iintro %na Hna
  imod (annotMerge e P Q) $$ HP HQ %na Hna with ⟨H, Hna⟩
  imodintro
  isplitl [H HΨ]
  · iapply HΨ $$ H
  · iexact Hna

theorem wpdAnnotSplit (i : Agent) (Φ : Athread → IProp GF) (s : Athread) (e : Geid)
    (P Q : IProp GF) :
    ⊢ AxAnnot.annotOwn e iprop(P ∗ Q) -∗
      (AxAnnot.annotOwn e P -∗ AxAnnot.annotOwn e Q -∗
        tierAWpd (hlc := hlc) GD N obSt0 obi nm s .MaybeStuck i Φ) -∗
      tierAWpd (hlc := hlc) GD N obSt0 obi nm s .MaybeStuck i Φ := by
  iintro HPQ HΨ
  unfold tierAWpd
  iapply (@iupdWpd hlc GF _ (axGA2 GD N obSt0 obi nm) pol .MaybeStuck i s Φ)
  unfold interpMod
  iintro %na Hna
  imod (annotSplit e P Q) $$ HPQ %na Hna with ⟨⟨H1, H2⟩, Hna⟩
  imodintro
  isplitl [H1 H2 HΨ]
  · iapply HΨ $$ H1 H2
  · iexact Hna

theorem wpdAnnotEntail (i : Agent) (Φ : Athread → IProp GF) (s : Athread) (e : Geid)
    (P Q : IProp GF) :
    (P ⊢ Q) →
    ⊢ AxAnnot.annotOwn e P -∗
      (AxAnnot.annotOwn e Q -∗ tierAWpd (hlc := hlc) GD N obSt0 obi nm s .MaybeStuck i Φ) -∗
      tierAWpd (hlc := hlc) GD N obSt0 obi nm s .MaybeStuck i Φ := by
  intro HPQ
  iintro HP HΨ
  unfold tierAWpd
  iapply (@iupdWpd hlc GF _ (axGA2 GD N obSt0 obi nm) pol .MaybeStuck i s Φ)
  unfold interpMod
  iintro %na Hna
  imod (annotEntail e P Q HPQ) $$ HP %na Hna with ⟨H, Hna⟩
  imodintro
  isplitl [H HΨ]
  · iapply HΨ $$ H
  · iexact Hna

end merge

/-! # 2. The word handle and its leaves at `spinOb6` -/

/-- Every po-earlier write of a byte of the word `w` stored is gmo-before `r` once `r` is
gmo-after `w` (no same-byte write po-between): the others are po-before `w` ⇒ ppo rule 1. -/
theorem poWritesGmoBeforeN (GD : Gdexec) (Hcons : rvwmoCatConsistent GD) (i : Agent) (kw k : Nat)
    (a : Int) (bs : List (BitVec 8)) (cls : WmClass) (b : Int) :
    gxLbl GD.gdG (i, kw) = some (Lbl.LStore false a bs cls) → b ∈ clRange a bs.length →
    (∀ w v', gwritesByte GD.gdG w b v' → WeakRvwmoGraph.gpo GD.gdG (i, kw) w →
      WeakRvwmoGraph.gpo GD.gdG w (i, k) → False) →
    gmoLt GD.gdG (i, kw) (i, k) →
    ∀ w v', gwritesByte GD.gdG w b v' → WeakRvwmoGraph.gpo GD.gdG w (i, k) →
      gmoLt GD.gdG w (i, k) := by
  intro Hlw Hb Hnoint Hlt w v' Hw Hpo
  by_cases Hne : w = (i, kw)
  · subst Hne
    exact Hlt
  obtain ⟨wi, wk⟩ := w
  obtain ⟨Hh, Hk, Hs1, Hs2⟩ := Hpo
  have Hh' : wi = i := Hh
  subst wi
  obtain ⟨j, Hj⟩ := List.mem_iff_getElem?.1 Hb
  obtain ⟨vb, -, Hwb⟩ := (storeNBytes _ _ _ _ _ Hlw).1 j b Hj
  by_cases Hlk : wk < kw
  · refine gmoLtTrans _ _ _ _ (gobGmo GD Hcons _ _ ?_) Hlt
    exact ppo1Gob GD (i, wk) (i, kw) b vb ⟨rfl, Hlk, Hs1, by rw [Hlw]; rfl⟩ (.inl ⟨v', Hw⟩) Hwb
  · exfalso
    have Hne' : wk ≠ kw := fun h => Hne (by rw [h])
    exact Hnoint (i, wk) v' Hw ⟨rfl, by simp only; omega, by rw [Hlw]; rfl, Hs1⟩
      ⟨rfl, Hk, Hs1, Hs2⟩

section leaves6
variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF] [AxannotGS GF]
  [AxlogG GF Hent] [SpinlockG GF]

/-- THE WORD HANDLE. -/
abbrev hdlw (GT : GdexecT) (nm : spinN) (q : Qp) (a : Int) (n : Nat) (e : Geid)
    (vs : List (BitVec 8)) : IProp GF :=
  AxAnnot.annotOwn e (RbN nm.1 (gtAdGd GT) q (clRange a n) e vs)

theorem hdlwSplit (xw : Int) (nw : Nat) (Cl : List Int) (cv : Agent → List (BitVec 8))
    (GT : GdexecT) (nm : spinN) (i : Agent) (Φ : Athread → IProp GF) (s : Athread) (q1 q2 : Qp)
    (a : Int) (n : Nat) (e : Geid) (vs : List (BitVec 8)) :
    ⊢ hdlw GT nm (q1 + q2) a n e vs -∗
      (hdlw GT nm q1 a n e vs -∗ hdlw GT nm q2 a n e vs -∗
        @tierAWpd GF hlc _ _ (splPol GT) (gtAdGd GT) spinN Unit
          (spinOb6 ya (clRange xw nw) Cl cv) nm s .MaybeStuck i Φ) -∗
      @tierAWpd GF hlc _ _ (splPol GT) (gtAdGd GT) spinN Unit
        (spinOb6 ya (clRange xw nw) Cl cv) nm s .MaybeStuck i Φ := by
  iintro H HΨ
  iapply (wpdAnnotEntail (hlc := hlc) (pol := splPol GT) (gtAdGd GT) spinN Unit
    (spinOb6 ya (clRange xw nw) Cl cv) nm i Φ s e _ _
    (RbNSplit nm.1 (gtAdGd GT) q1 q2 (clRange a n) e vs)) $$ H
  iintro H
  iapply (wpdAnnotSplit (hlc := hlc) (pol := splPol GT) (gtAdGd GT) spinN Unit
    (spinOb6 ya (clRange xw nw) Cl cv) nm i Φ s e _ _) $$ H HΨ

theorem hdlwJoin (xw : Int) (nw : Nat) (Cl : List Int) (cv : Agent → List (BitVec 8))
    (GT : GdexecT) (nm : spinN) (i : Agent) (Φ : Athread → IProp GF) (s : Athread) (q1 q2 : Qp)
    (a : Int) (n : Nat) (e : Geid) (vs : List (BitVec 8)) :
    ⊢ hdlw GT nm q1 a n e vs -∗ hdlw GT nm q2 a n e vs -∗
      (hdlw GT nm (q1 + q2) a n e vs -∗
        @tierAWpd GF hlc _ _ (splPol GT) (gtAdGd GT) spinN Unit
          (spinOb6 ya (clRange xw nw) Cl cv) nm s .MaybeStuck i Φ) -∗
      @tierAWpd GF hlc _ _ (splPol GT) (gtAdGd GT) spinN Unit
        (spinOb6 ya (clRange xw nw) Cl cv) nm s .MaybeStuck i Φ := by
  have HPQ : iprop(RbN (GF := GF) nm.1 (gtAdGd GT) q1 (clRange a n) e vs ∗
      RbN nm.1 (gtAdGd GT) q2 (clRange a n) e vs) ⊢
      RbN nm.1 (gtAdGd GT) (q1 + q2) (clRange a n) e vs := by
    iintro H
    icases (RbNJoin nm.1 (gtAdGd GT) q1 q2 (clRange a n) e e vs vs) $$ H with ⟨H, -⟩
    iexact H
  iintro H1 H2 HΨ
  iapply (wpdAnnotMerge (hlc := hlc) (pol := splPol GT) (gtAdGd GT) spinN Unit
    (spinOb6 ya (clRange xw nw) Cl cv) nm i Φ s e _ _) $$ H1 H2
  iintro H
  iapply (wpdAnnotEntail (hlc := hlc) (pol := splPol GT) (gtAdGd GT) spinN Unit
    (spinOb6 ya (clRange xw nw) Cl cv) nm i Φ s e _ _ HPQ) $$ H HΨ

/-- THE FRACTIONAL OWNED LOAD (n bytes). -/
theorem wpdLdOwnN (xw : Int) (nw : Nat) (Cl : List Int) (cv : Agent → List (BitVec 8))
    (GT : GdexecT) (nm : spinN) (cpu : CPU) (Hcons : rvwmoCatConsistent (gtAdGd GT))
    (HlkX : ya ∉ X6 (clRange xw nw) Cl) (i : Agent) (k : Nat) (n : Nat) (Hn : n ≠ 0)
    (pa : PAddr) (Hdev : devAddr pa = false)
    (KK : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit) (ts : List Nat)
    (vs : List (BitVec 8)) (q : Qp) (e : Geid) (mv : List (BitVec 8)) (Φ : Athread → IProp GF) :
    k ≠ (AxOpsem.grow (gtAdGd GT) i).length →
    (AxOpsem.grow (gtAdGd GT) i)[k]? = some (Lbl.LLoad false (paZ pa) ts vs) →
    ts.length = n → vs.length = n →
    (∀ b, b ∈ clRange (paZ pa) n → b ∈ X6 (clRange xw nw) Cl) →
    e ∈ @Axpol.lobp (splPol GT) (gtAdGd GT) (i, k) →
    (∀ b w v', b ∈ clRange (paZ pa) n → gwritesByte (gtAdGd GT).gdG w b v' →
      WeakRvwmoGraph.gpo (gtAdGd GT).gdG w (i, k) → gmoLt (gtAdGd GT).gdG w (i, k)) →
    ⊢ hdlw GT nm q (paZ pa) n e mv -∗
      (hdlw GT nm q (paZ pa) n (i, k) vs -∗
        AxAnnot.annotOwn (i, k)
          iprop(⌜∀ (j : Nat) v0 v, mv[j]? = some v0 → vs[j]? = some v → v = v0⌝) -∗
        ∀ rs : RegFile, @tierAWpd GF hlc _ _ (splPol GT) (gtAdGd GT) spinN Unit
          (spinOb6 ya (clRange xw nw) Cl cv) nm
          ⟨hp cpu (KK (.Ok (wordOfBytes n vs, none))) rs, k + 1⟩ .MaybeStuck i Φ) -∗
      ∀ rs : RegFile, @tierAWpd GF hlc _ _ (splPol GT) (gtAdGd GT) spinN Unit
        (spinOb6 ya (clRange xw nw) Cl cv) nm
        ⟨hp cpu (.impure (.ok (.memRead n 64 (h4rreq n l3pAkP pa))) KK) rs, k⟩ .MaybeStuck i Φ := by
  intro Hne Hrow Hlts Hlvs HX Hin Hfw
  subst Hlvs
  have Hl : gxLbl (gtAdGd GT).gdG (i, k) = some (Lbl.LLoad false (paZ pa) ts vs) := by
    rw [gxLblGrow]; exact Hrow
  have Hadv : ∀ lb, (AxOpsem.grow (gtAdGd GT) i)[k]? = some lb → aidentAdvRd (aident lb) = 1 := by
    rw [Hrow]
    intro lb h
    cases h
    rfl
  have Hgv0 : graphValue (gtAdGd GT) (i, k) = some vs := by unfold graphValue; rw [Hl]; rfl
  have H := h4shRead (hlc := hlc) (pol := splPol GT) (gtAdGd GT) spinN Unit
    (spinOb6 ya (clRange xw nw) Cl cv) nm cpu i Φ vs.length Hn pa Hdev KK k Hne Hadv
    iprop(hdlw (GF := GF) GT nm q (paZ pa) vs.length e mv ∗
      (hdlw GT nm q (paZ pa) vs.length (i, k) vs -∗
        AxAnnot.annotOwn (i, k)
          iprop(⌜∀ (j : Nat) v0 v, mv[j]? = some v0 → vs[j]? = some v → v = v0⌝) -∗
        ∀ rs : RegFile, @tierAWpd GF hlc _ _ (splPol GT) (gtAdGd GT) spinN Unit
          (spinOb6 ya (clRange xw nw) Cl cv) nm
          ⟨hp cpu (KK (.Ok (wordOfBytes vs.length vs, none))) rs, k + 1⟩ .MaybeStuck i Φ))
    (fun v rs Hgv => by
      have Hvv : v = vs := Option.some.inj (Hgv.symm.trans Hgv0)
      subst v
      iintro ⟨Hh, HΨ⟩
      ihave Hfe := fe6RdN (hlc := hlc) ya (clRange xw nw) Cl cv GT nm Hcons HlkX (i, k) e q
        (paZ pa) ts vs mv Hl Hlts HX (splPolGmo GT e (i, k) Hin) Hfw
      iapply (evDraw (hlc := hlc) (pol := splPol GT) (gtAdGd GT) spinN Unit
        (spinOb6 ya (clRange xw nw) Cl cv) nm (splAxpolWf GT) i k e _
        (RbN nm.1 (gtAdGd GT) q (clRange (paZ pa) vs.length) (i, k) vs)
        iprop(⌜∀ (j : Nat) v0 v, mv[j]? = some v0 → vs[j]? = some v → v = v0⌝) _ _ Hgv Hin)
        $$ Hh Hfe
      iintro H1 H2
      iapply HΨ $$ H1 H2 %rs)
  iintro Hh HΨ
  iapply H $$ [$Hh $HΨ]

/-- THE OWNED STORE (n bytes), full handle. -/
theorem wpdSdOwnN (xw : Int) (nw : Nat) (Cl : List Int) (cv : Agent → List (BitVec 8))
    (GT : GdexecT) (nm : spinN) (cpu : CPU) (Hcons : rvwmoCatConsistent (gtAdGd GT))
    (HlkX : ya ∉ X6 (clRange xw nw) Cl) (i : Agent) (k : Nat) (n : Nat) (pa : PAddr)
    (Hdev : devAddr pa = false) (val : BitVec (8 * n)) (m' : SailM Unit) (cls : WmClass)
    (e : Geid) (mv : List (BitVec 8)) (Φ : Athread → IProp GF) :
    k ≠ (AxOpsem.grow (gtAdGd GT) i).length →
    (AxOpsem.grow (gtAdGd GT) i)[k]? =
      some (Lbl.LStore false (paZ pa) (WeakInterpProj.wbytes n val) cls) →
    (∀ b, b ∈ clRange (paZ pa) n → b ∈ X6 (clRange xw nw) Cl ∧ b ∉ Cl) →
    e ∈ @Axpol.lobp (splPol GT) (gtAdGd GT) (i, k) →
    ⊢ hdlw GT nm 1 (paZ pa) n e mv -∗
      (hdlw GT nm 1 (paZ pa) n (i, k) (WeakInterpProj.wbytes n val) -∗
        ∀ rs : RegFile, @tierAWpd GF hlc _ _ (splPol GT) (gtAdGd GT) spinN Unit
          (spinOb6 ya (clRange xw nw) Cl cv) nm ⟨hp cpu m' rs, k + 1⟩ .MaybeStuck i Φ) -∗
      ∀ rs : RegFile, @tierAWpd GF hlc _ _ (splPol GT) (gtAdGd GT) spinN Unit
        (spinOb6 ya (clRange xw nw) Cl cv) nm
        ⟨hp cpu (.impure (.ok (.memWrite n 64 (h4wreq n l3pAkP pa val))) (fun _ => m')) rs, k⟩
        .MaybeStuck i Φ := by
  intro Hne Hrow HX Hin
  have Hl : gxLbl (gtAdGd GT).gdG (i, k) =
      some (Lbl.LStore false (paZ pa) (WeakInterpProj.wbytes n val) cls) := by
    rw [gxLblGrow]; exact Hrow
  have Hlen : (WeakInterpProj.wbytes n val).length = n := wbytesLength n val
  have Hval : graphData (gtAdGd GT) (i, k) = some (WeakInterpProj.wbytes n val) := by
    unfold graphData; rw [Hl]; rfl
  have HX' : ∀ b, b ∈ clRange (paZ pa) (WeakInterpProj.wbytes n val).length →
      b ∈ X6 (clRange xw nw) Cl ∧ b ∉ Cl := by rw [Hlen]; exact HX
  have Hfe0 := fe6WrN (hlc := hlc) (GF := GF) ya (clRange xw nw) Cl cv GT nm Hcons HlkX (i, k) e
    (paZ pa) (WeakInterpProj.wbytes n val) mv cls iprop(True)
    ({[e := RbN nm.1 (gtAdGd GT) 1 (clRange (paZ pa) n) e mv]} : Mea GF) Hl HX'
    (splPolGmo GT e (i, k) Hin)
  rw [Hlen] at Hfe0
  have Hsing : ⊢ ([∗map] Rin ∈ ({[e := RbN (GF := GF) nm.1 (gtAdGd GT) 1 (clRange (paZ pa) n) e
      mv]} : Mea GF), Rin) -∗
      iprop(True ∗ RbN (GF := GF) nm.1 (gtAdGd GT) 1 (clRange (paZ pa) n) e mv) := by
    iintro H
    ihave H := (BigSepM.bigSepM_singleton (M := GMapF Geid)).1 $$ H
    isplitr
    · itrivial
    · iexact H
  have HB := h4shWrite (hlc := hlc) (pol := splPol GT) (gtAdGd GT) spinN Unit
    (spinOb6 ya (clRange xw nw) Cl cv) nm cpu i Φ n pa Hdev val m' k Hne
    iprop(hdlw (GF := GF) GT nm 1 (paZ pa) n e mv ∗
      (hdlw GT nm 1 (paZ pa) n (i, k) (WeakInterpProj.wbytes n val) -∗
        ∀ rs : RegFile, @tierAWpd GF hlc _ _ (splPol GT) (gtAdGd GT) spinN Unit
          (spinOb6 ya (clRange xw nw) Cl cv) nm ⟨hp cpu m' rs, k + 1⟩ .MaybeStuck i Φ))
    (fun rs => by
      iintro ⟨Hh, HΨ⟩
      ihave Hw := Hsing
      ihave Hfe := Hfe0 $$ Hw
      ihave Hfe := (@flowEqDynMono hlc GF _ (s6G ya (clRange xw nw) Cl cv GT nm) (splPol GT)
        (gtAdGd GT) (i, k) _ _
        iprop(True ∗ RbN nm.1 (gtAdGd GT) 1 (clRange (paZ pa) n) (i, k)
          (WeakInterpProj.wbytes n val))
        iprop(RbN nm.1 (gtAdGd GT) 1 (clRange (paZ pa) n) (i, k) (WeakInterpProj.wbytes n val) ∗
          True)) $$ [] Hfe
      · inext
        iintro ⟨_, H⟩
        isplitl [H]
        · iexact H
        · itrivial
      iapply (evDraw (hlc := hlc) (pol := splPol GT) (gtAdGd GT) spinN Unit
        (spinOb6 ya (clRange xw nw) Cl cv) nm (splAxpolWf GT) i k e _
        (RbN nm.1 (gtAdGd GT) 1 (clRange (paZ pa) n) (i, k) (WeakInterpProj.wbytes n val))
        iprop(True) _ _ Hval Hin) $$ Hh Hfe
      iintro H _
      iapply HΨ $$ H %rs)
  iintro Hh HΨ
  iapply HB $$ [$Hh $HΨ]

/-- THE RECOMBINING OWNED STORE: two fractions `q1 + q2 = 1` at two lob-predecessors; deposits
at `w` that their values agree. -/
theorem wpdSdOwnN2 (xw : Int) (nw : Nat) (Cl : List Int) (cv : Agent → List (BitVec 8))
    (GT : GdexecT) (nm : spinN) (cpu : CPU) (Hcons : rvwmoCatConsistent (gtAdGd GT))
    (HlkX : ya ∉ X6 (clRange xw nw) Cl) (i : Agent) (k : Nat) (n : Nat) (pa : PAddr)
    (Hdev : devAddr pa = false) (val : BitVec (8 * n)) (m' : SailM Unit) (cls : WmClass)
    (q1 q2 : Qp) (e1 e2 : Geid) (vs1 vs2 : List (BitVec 8)) (Φ : Athread → IProp GF) :
    q1 + q2 = 1 →
    k ≠ (AxOpsem.grow (gtAdGd GT) i).length →
    (AxOpsem.grow (gtAdGd GT) i)[k]? =
      some (Lbl.LStore false (paZ pa) (WeakInterpProj.wbytes n val) cls) →
    (∀ b, b ∈ clRange (paZ pa) n → b ∈ X6 (clRange xw nw) Cl ∧ b ∉ Cl) →
    e1 ≠ e2 → e1 ∈ @Axpol.lobp (splPol GT) (gtAdGd GT) (i, k) →
    e2 ∈ @Axpol.lobp (splPol GT) (gtAdGd GT) (i, k) →
    ⊢ hdlw GT nm q1 (paZ pa) n e1 vs1 -∗ hdlw GT nm q2 (paZ pa) n e2 vs2 -∗
      (hdlw GT nm 1 (paZ pa) n (i, k) (WeakInterpProj.wbytes n val) -∗
        AxAnnot.annotOwn (i, k)
          iprop(⌜∀ (j : Nat) v1 v2, j < n → vs1[j]? = some v1 → vs2[j]? = some v2 → v1 = v2⌝) -∗
        ∀ rs : RegFile, @tierAWpd GF hlc _ _ (splPol GT) (gtAdGd GT) spinN Unit
          (spinOb6 ya (clRange xw nw) Cl cv) nm ⟨hp cpu m' rs, k + 1⟩ .MaybeStuck i Φ) -∗
      ∀ rs : RegFile, @tierAWpd GF hlc _ _ (splPol GT) (gtAdGd GT) spinN Unit
        (spinOb6 ya (clRange xw nw) Cl cv) nm
        ⟨hp cpu (.impure (.ok (.memWrite n 64 (h4wreq n l3pAkP pa val))) (fun _ => m')) rs, k⟩
        .MaybeStuck i Φ := by
  intro Hq Hne Hrow HX He12 Hin1 Hin2
  have Hl : gxLbl (gtAdGd GT).gdG (i, k) =
      some (Lbl.LStore false (paZ pa) (WeakInterpProj.wbytes n val) cls) := by
    rw [gxLblGrow]; exact Hrow
  have Hlen : (WeakInterpProj.wbytes n val).length = n := wbytesLength n val
  have Hval : graphData (gtAdGd GT) (i, k) = some (WeakInterpProj.wbytes n val) := by
    unfold graphData; rw [Hl]; rfl
  have HX' : ∀ b, b ∈ clRange (paZ pa) (WeakInterpProj.wbytes n val).length →
      b ∈ X6 (clRange xw nw) Cl ∧ b ∉ Cl := by rw [Hlen]; exact HX
  have hnone : get? ({[e2 := RbN (GF := GF) nm.1 (gtAdGd GT) q2 (clRange (paZ pa) n) e2 vs2]} :
      Mea GF) e1 = none := lookupSingletonNe (Ne.symm He12)
  have Hsub : (FiniteMap.dom_set (insert
      ({[e2 := RbN (GF := GF) nm.1 (gtAdGd GT) q2 (clRange (paZ pa) n) e2 vs2]} : Mea GF) e1
      (RbN nm.1 (gtAdGd GT) q1 (clRange (paZ pa) n) e1 vs1)) : GSet Geid) ⊆
      @Axpol.lobp (splPol GT) (gtAdGd GT) (i, k) := by
    intro e He
    rw [domInsert, domSingleton] at He
    rcases elemOfUnion.1 He with h | h
    · rw [elemOfSingleton.1 h]; exact Hin1
    · rw [elemOfSingleton.1 h]; exact Hin2
  have Hjoin := RbNJoin (GF := GF) nm.1 (gtAdGd GT) q1 q2 (clRange (paZ pa) n) e1 e2 vs1 vs2
  rw [Hq] at Hjoin
  have Hwand : ⊢ ([∗map] Rin ∈ (insert
      ({[e2 := RbN (GF := GF) nm.1 (gtAdGd GT) q2 (clRange (paZ pa) n) e2 vs2]} : Mea GF) e1
      (RbN nm.1 (gtAdGd GT) q1 (clRange (paZ pa) n) e1 vs1)), Rin) -∗
      iprop(⌜∀ (j : Nat) v1 v2, j < n → vs1[j]? = some v1 → vs2[j]? = some v2 → v1 = v2⌝ ∗
        RbN (GF := GF) nm.1 (gtAdGd GT) 1 (clRange (paZ pa) n) e1 vs1) := by
    iintro H
    icases (BigSepM.bigSepM_insert hnone).1 $$ H with ⟨H1, H2⟩
    ihave H2 := (BigSepM.bigSepM_singleton (M := GMapF Geid)).1 $$ H2
    icases Hjoin $$ [$H1 $H2] with ⟨H, %Hag⟩
    isplitr
    · ipureintro
      intro j v1 v2 Hj E1 E2
      exact Hag j (paZ pa + (j : Int)) v1 v2
        ((AxSpinH4.clRangeLookup (paZ pa) n j _).2 ⟨Hj, rfl⟩) E1 E2
    · iexact H
  have Hfe0 := fe6WrN (hlc := hlc) (GF := GF) ya (clRange xw nw) Cl cv GT nm Hcons HlkX (i, k) e1
    (paZ pa) (WeakInterpProj.wbytes n val) vs1 cls
    iprop(⌜∀ (j : Nat) v1 v2, j < n → vs1[j]? = some v1 → vs2[j]? = some v2 → v1 = v2⌝)
    (insert ({[e2 := RbN (GF := GF) nm.1 (gtAdGd GT) q2 (clRange (paZ pa) n) e2 vs2]} : Mea GF) e1
      (RbN nm.1 (gtAdGd GT) q1 (clRange (paZ pa) n) e1 vs1)) Hl HX'
    (splPolGmo GT e1 (i, k) Hin1)
  rw [Hlen] at Hfe0
  have Hmk : ⊢ AxAnnot.annotOwn (GF := GF) e1
        (RbN nm.1 (gtAdGd GT) q1 (clRange (paZ pa) n) e1 vs1) -∗
      AxAnnot.annotOwn e2 (RbN nm.1 (gtAdGd GT) q2 (clRange (paZ pa) n) e2 vs2) -∗
      [∗map] e ↦ P ∈ (insert
        ({[e2 := RbN (GF := GF) nm.1 (gtAdGd GT) q2 (clRange (paZ pa) n) e2 vs2]} : Mea GF) e1
        (RbN nm.1 (gtAdGd GT) q1 (clRange (paZ pa) n) e1 vs1)), AxAnnot.annotOwn e P := by
    iintro Ha Hb
    iapply (BigSepM.bigSepM_insert hnone).2
    isplitl [Ha]
    · iexact Ha
    · iapply BigSepM.bigSepM_singleton.2
      iexact Hb
  have HB := h4shWrite (hlc := hlc) (pol := splPol GT) (gtAdGd GT) spinN Unit
    (spinOb6 ya (clRange xw nw) Cl cv) nm cpu i Φ n pa Hdev val m' k Hne
    iprop(hdlw (GF := GF) GT nm q1 (paZ pa) n e1 vs1 ∗ hdlw GT nm q2 (paZ pa) n e2 vs2 ∗
      (hdlw GT nm 1 (paZ pa) n (i, k) (WeakInterpProj.wbytes n val) -∗
        AxAnnot.annotOwn (i, k)
          iprop(⌜∀ (j : Nat) v1 v2, j < n → vs1[j]? = some v1 → vs2[j]? = some v2 → v1 = v2⌝) -∗
        ∀ rs : RegFile, @tierAWpd GF hlc _ _ (splPol GT) (gtAdGd GT) spinN Unit
          (spinOb6 ya (clRange xw nw) Cl cv) nm ⟨hp cpu m' rs, k + 1⟩ .MaybeStuck i Φ))
    (fun rs => by
      iintro ⟨H1, H2, HΨ⟩
      ihave Hm := Hmk $$ H1 H2
      ihave Hw := Hwand
      ihave Hfe := Hfe0 $$ Hw
      ihave Hfe := (@flowEqDynMono hlc GF _ (s6G ya (clRange xw nw) Cl cv GT nm) (splPol GT)
        (gtAdGd GT) (i, k) _ _
        iprop(⌜∀ (j : Nat) v1 v2, j < n → vs1[j]? = some v1 → vs2[j]? = some v2 → v1 = v2⌝ ∗
          RbN nm.1 (gtAdGd GT) 1 (clRange (paZ pa) n) (i, k) (WeakInterpProj.wbytes n val))
        iprop(RbN nm.1 (gtAdGd GT) 1 (clRange (paZ pa) n) (i, k) (WeakInterpProj.wbytes n val) ∗
          ⌜∀ (j : Nat) v1 v2, j < n → vs1[j]? = some v1 → vs2[j]? = some v2 → v1 = v2⌝))
        $$ [] Hfe
      · inext
        iintro ⟨HA, H⟩
        isplitl [H]
        · iexact H
        · iexact HA
      iapply (evDrawM (hlc := hlc) (pol := splPol GT) (gtAdGd GT) spinN Unit
        (spinOb6 ya (clRange xw nw) Cl cv) nm (splAxpolWf GT) i k _
        (RbN nm.1 (gtAdGd GT) 1 (clRange (paZ pa) n) (i, k) (WeakInterpProj.wbytes n val))
        iprop(⌜∀ (j : Nat) v1 v2, j < n → vs1[j]? = some v1 → vs2[j]? = some v2 → v1 = v2⌝)
        _ _ Hval Hsub) $$ Hm Hfe
      iintro H HA
      iapply HΨ $$ H HA %rs)
  iintro H1 H2 HΨ
  iapply HB $$ [$H1 $H2 $HΨ]

/-- THE FORWARDED-RELOAD LEAF (n bytes): store `w` of `bs`, then a load `r` of the same word, no
same-byte store po-between. -/
theorem wpdReloadOwnN (xw : Int) (nw : Nat) (Cl : List Int) (cv : Agent → List (BitVec 8))
    (GT : GdexecT) (nm : spinN) (cpu : CPU) (Hcons : rvwmoCatConsistent (gtAdGd GT))
    (HlkX : ya ∉ X6 (clRange xw nw) Cl) (i : Agent) (kw k : Nat) (n : Nat) (Hn : n ≠ 0)
    (pa : PAddr) (Hdev : devAddr pa = false)
    (KK : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit) (bs : List (BitVec 8))
    (cls : WmClass) (ts : List Nat) (vs : List (BitVec 8)) (Φ : Athread → IProp GF) :
    k ≠ (AxOpsem.grow (gtAdGd GT) i).length →
    (AxOpsem.grow (gtAdGd GT) i)[kw]? = some (Lbl.LStore false (paZ pa) bs cls) →
    (AxOpsem.grow (gtAdGd GT) i)[k]? = some (Lbl.LLoad false (paZ pa) ts vs) → kw < k →
    bs.length = n → ts.length = n → vs.length = n →
    (∀ b, b ∈ clRange (paZ pa) n → b ∈ X6 (clRange xw nw) Cl) →
    (∀ b w v', b ∈ clRange (paZ pa) n → gwritesByte (gtAdGd GT).gdG w b v' →
      WeakRvwmoGraph.gpo (gtAdGd GT).gdG (i, kw) w →
      WeakRvwmoGraph.gpo (gtAdGd GT).gdG w (i, k) → False) →
    ⊢ hdlw GT nm 1 (paZ pa) n (i, kw) bs -∗
      ((∃ (e' : Geid), ⌜e' = (i, kw) ∨ e' = (i, k)⌝ ∗ hdlw GT nm 1 (paZ pa) n e' bs) -∗
        AxAnnot.annotOwn (i, k) iprop(⌜vs = bs⌝) -∗
        ∀ rs : RegFile, @tierAWpd GF hlc _ _ (splPol GT) (gtAdGd GT) spinN Unit
          (spinOb6 ya (clRange xw nw) Cl cv) nm
          ⟨hp cpu (KK (.Ok (wordOfBytes n vs, none))) rs, k + 1⟩ .MaybeStuck i Φ) -∗
      ∀ rs : RegFile, @tierAWpd GF hlc _ _ (splPol GT) (gtAdGd GT) spinN Unit
        (spinOb6 ya (clRange xw nw) Cl cv) nm
        ⟨hp cpu (.impure (.ok (.memRead n 64 (h4rreq n l3pAkP pa))) KK) rs, k⟩ .MaybeStuck i Φ := by
  intro Hne Hroww Hrow Hlt Hlbs Hlts Hlvs HX Hnoint
  subst Hlvs
  have Hlw : gxLbl (gtAdGd GT).gdG (i, kw) = some (Lbl.LStore false (paZ pa) bs cls) := by
    rw [gxLblGrow]; exact Hroww
  have Hl : gxLbl (gtAdGd GT).gdG (i, k) = some (Lbl.LLoad false (paZ pa) ts vs) := by
    rw [gxLblGrow]; exact Hrow
  have Hadv : ∀ lb, (AxOpsem.grow (gtAdGd GT) i)[k]? = some lb → aidentAdvRd (aident lb) = 1 := by
    rw [Hrow]
    intro lb h
    cases h
    rfl
  have Hpo : WeakRvwmoGraph.gpo (gtAdGd GT).gdG (i, kw) (i, k) :=
    gpoRow (gtAdGd GT) i kw k _ _ Hlw Hl Hlt
  have Hgv0 : graphValue (gtAdGd GT) (i, k) = some vs := by unfold graphValue; rw [Hl]; rfl
  have H := h4shRead (hlc := hlc) (pol := splPol GT) (gtAdGd GT) spinN Unit
    (spinOb6 ya (clRange xw nw) Cl cv) nm cpu i Φ vs.length Hn pa Hdev KK k Hne Hadv
    iprop(hdlw (GF := GF) GT nm 1 (paZ pa) vs.length (i, kw) bs ∗
      ((∃ (e' : Geid), ⌜e' = (i, kw) ∨ e' = (i, k)⌝ ∗ hdlw GT nm 1 (paZ pa) vs.length e' bs) -∗
        AxAnnot.annotOwn (i, k) iprop(⌜vs = bs⌝) -∗
        ∀ rs : RegFile, @tierAWpd GF hlc _ _ (splPol GT) (gtAdGd GT) spinN Unit
          (spinOb6 ya (clRange xw nw) Cl cv) nm
          ⟨hp cpu (KK (.Ok (wordOfBytes vs.length vs, none))) rs, k + 1⟩ .MaybeStuck i Φ))
    (fun v rs Hgv => by
      have Hvv : v = vs := Option.some.inj (Hgv.symm.trans Hgv0)
      subst v
      iintro ⟨Hh, HΨ⟩
      by_cases Hb : gmoLt (gtAdGd GT).gdG (i, kw) (i, k)
      · have Hin : ((i, kw) : Geid) ∈ @Axpol.lobp (splPol GT) (gtAdGd GT) (i, k) :=
          splPolIntro GT (i, kw) (i, k) _ Hlw rfl Hpo Hb
        have Hfw : ∀ b w v', b ∈ clRange (paZ pa) vs.length → gwritesByte (gtAdGd GT).gdG w b v' →
            WeakRvwmoGraph.gpo (gtAdGd GT).gdG w (i, k) → gmoLt (gtAdGd GT).gdG w (i, k) := by
          intro b w v' Hbr
          have Hbr' : b ∈ clRange (paZ pa) bs.length := by rw [Hlbs]; exact Hbr
          exact poWritesGmoBeforeN (gtAdGd GT) Hcons i kw k (paZ pa) bs cls b Hlw Hbr'
            (fun w' v'' Hw' H1 H2 => Hnoint b w' v'' Hbr Hw' H1 H2) Hb w v'
        ihave Hfe := fe6RdN (hlc := hlc) ya (clRange xw nw) Cl cv GT nm Hcons HlkX (i, k) (i, kw) 1
          (paZ pa) ts vs bs Hl Hlts HX Hb Hfw
        ihave Hfe := (@flowEqDynMono hlc GF _ (s6G ya (clRange xw nw) Cl cv GT nm) (splPol GT)
          (gtAdGd GT) (i, k) _ _
          iprop(RbN nm.1 (gtAdGd GT) 1 (clRange (paZ pa) vs.length) (i, k) vs ∗
            ⌜∀ (j : Nat) v0 v, bs[j]? = some v0 → vs[j]? = some v → v = v0⌝)
          iprop(RbN nm.1 (gtAdGd GT) 1 (clRange (paZ pa) vs.length) (i, k) bs ∗ ⌜vs = bs⌝))
          $$ [] Hfe
        · inext
          iintro ⟨H, %Hf⟩
          have Heq : vs = bs := by
            apply List.ext_getElem?
            intro j
            cases Ev : vs[j]? with
            | none =>
              have Hge : vs.length ≤ j := List.getElem?_eq_none_iff.1 Ev
              exact (List.getElem?_eq_none (by omega)).symm
            | some v =>
              have Hj : j < vs.length := (List.getElem?_eq_some_iff.1 Ev).1
              have Hjb : j < bs.length := by omega
              have E0 : bs[j]? = some bs[j] := List.getElem?_eq_getElem Hjb
              rw [E0, Hf j bs[j] v E0 Ev]
          isplitl [H]
          · rw [← Heq]
            iexact H
          · ipureintro
            exact Heq
        iapply (evDraw (hlc := hlc) (pol := splPol GT) (gtAdGd GT) spinN Unit
          (spinOb6 ya (clRange xw nw) Cl cv) nm (splAxpolWf GT) i k (i, kw) _
          (RbN nm.1 (gtAdGd GT) 1 (clRange (paZ pa) vs.length) (i, k) bs) iprop(⌜vs = bs⌝)
          _ _ Hgv Hin) $$ Hh Hfe
        iintro H1 H2
        iapply HΨ $$ [H1] H2 %rs
        iexists (i, k)
        isplitr
        · ipureintro
          exact Or.inr rfl
        · iexact H1
      · have Heq : vs = bs := by
          apply List.ext_getElem?
          intro j
          cases Ev : vs[j]? with
          | none =>
            have Hge : vs.length ≤ j := List.getElem?_eq_none_iff.1 Ev
            exact (List.getElem?_eq_none (by omega)).symm
          | some v =>
            have Hj : j < vs.length := (List.getElem?_eq_some_iff.1 Ev).1
            have Hbr : (clRange (paZ pa) vs.length)[j]? = some (paZ pa + (j : Int)) :=
              (AxSpinH4.clRangeLookup _ _ _ _).2 ⟨Hj, rfl⟩
            obtain ⟨t, v', -, Ev', Hrd⟩ :=
              (loadNBytes _ (i, k) (paZ pa) ts vs Hl Hlts).1 j _ Hbr
            have Hvv' : v' = v := Option.some.inj (Ev'.symm.trans Ev)
            subst v'
            have Hbw : (clRange (paZ pa) bs.length)[j]? = some (paZ pa + (j : Int)) :=
              (AxSpinH4.clRangeLookup _ _ _ _).2 ⟨by omega, rfl⟩
            obtain ⟨vb, Eb, Hwb⟩ := (storeNBytes _ (i, kw) (paZ pa) bs cls Hlw).1 j _ Hbw
            obtain ⟨-, Hvalr⟩ := ownedReadRuleFwd (gtAdGd GT) (paZ pa + (j : Int)) (i, k) (i, kw)
              vb t v Hcons Hpo Hwb Hrd Hb
              (fun w' v'' Hw' H1 H2 => Hnoint _ w' v'' (List.mem_of_getElem? Hbr) Hw' H1 H2)
            rw [Eb, Hvalr t v Hrd]
        ihave Hfe := fe6PlainN (hlc := hlc) ya (clRange xw nw) Cl cv GT nm Hcons HlkX (i, k)
          (paZ pa) ts vs Hl Hlts HX
        ihave Hfe := (@flowEqDynMono hlc GF _ (s6G ya (clRange xw nw) Cl cv GT nm) (splPol GT)
          (gtAdGd GT) (i, k) _ (∅ : Mea GF) iprop(True) iprop(⌜vs = bs⌝ ∗ True)) $$ [] Hfe
        · inext
          iintro _
          isplitr
          · ipureintro
            exact Heq
          · itrivial
        iapply (evPlain (hlc := hlc) (pol := splPol GT) (gtAdGd GT) spinN Unit
          (spinOb6 ya (clRange xw nw) Cl cv) nm i k iprop(⌜vs = bs⌝) iprop(True) _ _ Hgv) $$ Hfe
        iintro H _
        iapply HΨ $$ [Hh] H %rs
        iexists (i, kw)
        isplitr
        · ipureintro
          exact Or.inl rfl
        · iexact Hh)
  iintro Hh HΨ
  iapply H $$ [$Hh $HΨ]

/-! ## The acquire / release contracts (hand lock instructions of `AxSpinProt7`: `acqRmw`,
`fenceM`, `relM`). -/

omit [AxannotGS GF] [SpinlockG GF] in
theorem RLRbN1 (GT : GdexecT) (nm : spinN) (xs : List Int) (e : Geid) :
    RL (GF := GF) nm.1 (gtAdGd GT) xs e ⊢ RbN nm.1 (gtAdGd GT) 1 xs e [] :=
  (RLRbN nm.1 (gtAdGd GT) xs e).1

/-- ACQUIRE (success), the claim's annotation allocated split along `Hsplit`. -/
theorem wpdAcquireGen6 (xw : Int) (nw : Nat) (Cl : List Int) (cv : Agent → List (BitVec 8))
    (GT : GdexecT) (nm : spinN) (cpu : CPU) (Hcons : rvwmoCatConsistent (gtAdGd GT))
    (HlkX : ya ∉ X6 (clRange xw nw) Cl) (i : Agent) (k t : Nat) (kok kf : SailM Unit)
    (R1 R2 : IProp GF) (Φ : Athread → IProp GF) :
    k ≠ (AxOpsem.grow (gtAdGd GT) i).length →
    (AxOpsem.grow (gtAdGd GT) i)[k]? = some (.LRmw true false ya [t] [b0] [b1] .WCplain) →
    (iprop(locked nm.2 ya i (i, k) ∗ spinR6 (clRange xw nw) Cl nm (gtAdGd GT) (i, k)) ⊢
      iprop(R1 ∗ R2)) →
    ⊢ isLock nm.2 ya (spinR6 (clRange xw nw) Cl nm (gtAdGd GT)) -∗ notheld nm.2 ya i -∗
      (⌜lkClaim ya (gtAdGd GT).gdG (i, k) (gwriteAt (gtAdGd GT).gdG t)⌝ -∗
        AxAnnot.annotOwn (i, k) R1 -∗ AxAnnot.annotOwn (i, k) R2 -∗
        ∀ rs : RegFile, @tierAWpd GF hlc _ _ (splPol GT) (gtAdGd GT) spinN Unit
          (spinOb6 ya (clRange xw nw) Cl cv) nm ⟨hp cpu kok rs, k + 1⟩ .MaybeStuck i Φ) -∗
      ∀ rs : RegFile, @tierAWpd GF hlc _ _ (splPol GT) (gtAdGd GT) spinN Unit
        (spinOb6 ya (clRange xw nw) Cl cv) nm ⟨hp cpu (acqRmw kok kf) rs, k⟩ .MaybeStuck i Φ := by
  intro Hne Hrow Hsplit
  have Hl : gxLbl (gtAdGd GT).gdG (i, k) = some (.LRmw true false ya [t] [b0] [b1] .WCplain) := by
    rw [gxLblGrow]; exact Hrow
  obtain ⟨Hrd, Hw, Hsg, -⟩ := gwbRmw _ _ _ _ _ _ _ Hl
  have Hcl : lkClaim ya (gtAdGd GT).gdG (i, k) (gwriteAt (gtAdGd GT).gdG t) := ⟨t, Hrd, rfl, Hw⟩
  have Hval : graphData (gtAdGd GT) (i, k) = some (WeakInterpProj.wbytes 1 b1) := by
    unfold graphData; rw [Hl]; simp [lblData, l3pWbytes1]
  have Hs : ⊢ iprop(locked (GF := GF) nm.2 ya i (i, k) ∗
      spinR6 (clRange xw nw) Cl nm (gtAdGd GT) (i, k)) -∗ iprop(R1 ∗ R2) :=
    BI.wand_intro (BI.emp_sep.1.trans Hsplit)
  have HW := shRmwWrite (hlc := hlc) (pol := splPol GT) (gtAdGd GT) spinN Unit
    (spinOb6 ya (clRange xw nw) Cl cv) nm cpu i Φ ypaM ypaMRam (if b0 = b0 then kok else kf) k Hne
    iprop(isLock (GF := GF) nm.2 ya (spinR6 (clRange xw nw) Cl nm (gtAdGd GT)) ∗
      notheld nm.2 ya i ∗
      (⌜lkClaim ya (gtAdGd GT).gdG (i, k) (gwriteAt (gtAdGd GT).gdG t)⌝ -∗
        AxAnnot.annotOwn (i, k) R1 -∗ AxAnnot.annotOwn (i, k) R2 -∗
        ∀ rs : RegFile, @tierAWpd GF hlc _ _ (splPol GT) (gtAdGd GT) spinN Unit
          (spinOb6 ya (clRange xw nw) Cl cv) nm ⟨hp cpu kok rs, k + 1⟩ .MaybeStuck i Φ))
    (fun rs => by
      iintro ⟨#Hil, Hnh, HΨ⟩
      ihave Hfe := (fe6Claim (hlc := hlc) ya (clRange xw nw) Cl cv GT nm Hcons HlkX (i, k)
        (gwriteAt (gtAdGd GT).gdG t) Hcl (fun a v H => (Hsg a v H).1)) $$ Hnh Hil
      ihave Hfe := (@flowEqDynMono hlc GF _ (s6G ya (clRange xw nw) Cl cv GT nm)
        (splPol GT) (gtAdGd GT) (i, k) _ (∅ : Mea GF)
        iprop(locked nm.2 ya i (i, k) ∗ spinR6 (clRange xw nw) Cl nm (gtAdGd GT) (i, k))
        iprop(R1 ∗ R2)) $$ [] Hfe
      · inext
        ihave H := Hs
        iexact H
      iapply (evPlain (hlc := hlc) (pol := splPol GT) (gtAdGd GT) spinN Unit
        (spinOb6 ya (clRange xw nw) Cl cv) nm i k R1 R2 _ _ Hval) $$ Hfe
      iintro H1 H2
      rw [if_pos rfl]
      iapply HΨ $$ %Hcl H1 H2 %rs)
  have HR := shRmwRead (hlc := hlc) (pol := splPol GT) (gtAdGd GT) spinN Unit
    (spinOb6 ya (clRange xw nw) Cl cv) nm cpu i Φ ypaM ypaMRam (acqK kok kf) k t b0 .WCplain Hne
    Hrow
    iprop(isLock (GF := GF) nm.2 ya (spinR6 (clRange xw nw) Cl nm (gtAdGd GT)) ∗
      notheld nm.2 ya i ∗
      (⌜lkClaim ya (gtAdGd GT).gdG (i, k) (gwriteAt (gtAdGd GT).gdG t)⌝ -∗
        AxAnnot.annotOwn (i, k) R1 -∗ AxAnnot.annotOwn (i, k) R2 -∗
        ∀ rs : RegFile, @tierAWpd GF hlc _ _ (splPol GT) (gtAdGd GT) spinN Unit
          (spinOb6 ya (clRange xw nw) Cl cv) nm ⟨hp cpu kok rs, k + 1⟩ .MaybeStuck i Φ))
    (fun rs => by
      iintro ⟨#Hil, Hnh, HΨ⟩
      rw [AxSpinProt7.acqKOk]
      iapply HW $$ [$Hil $Hnh $HΨ] %rs)
  iintro #Hil Hnh HΨ
  iapply HR $$ [$Hil $Hnh $HΨ]

/-- ACQUIRE, HANDLE FORM: `locked ∗ lk->cpu` at the claim, and the WORD as the full handle
`hdlw 1 xw nw c []` (value unknown). -/
theorem wpdAcquireH6 (xw : Int) (nw : Nat) (Cl : List Int) (cv : Agent → List (BitVec 8))
    (GT : GdexecT) (nm : spinN) (cpu : CPU) (Hcons : rvwmoCatConsistent (gtAdGd GT))
    (HlkX : ya ∉ X6 (clRange xw nw) Cl) (i : Agent) (k t : Nat) (kok kf : SailM Unit)
    (Φ : Athread → IProp GF) :
    k ≠ (AxOpsem.grow (gtAdGd GT) i).length →
    (AxOpsem.grow (gtAdGd GT) i)[k]? = some (.LRmw true false ya [t] [b0] [b1] .WCplain) →
    ⊢ isLock nm.2 ya (spinR6 (clRange xw nw) Cl nm (gtAdGd GT)) -∗ notheld nm.2 ya i -∗
      (⌜lkClaim ya (gtAdGd GT).gdG (i, k) (gwriteAt (gtAdGd GT).gdG t)⌝ -∗
        AxAnnot.annotOwn (i, k) iprop(locked nm.2 ya i (i, k) ∗ RL nm.1 (gtAdGd GT) Cl (i, k)) -∗
        hdlw GT nm 1 xw nw (i, k) [] -∗
        ∀ rs : RegFile, @tierAWpd GF hlc _ _ (splPol GT) (gtAdGd GT) spinN Unit
          (spinOb6 ya (clRange xw nw) Cl cv) nm ⟨hp cpu kok rs, k + 1⟩ .MaybeStuck i Φ) -∗
      ∀ rs : RegFile, @tierAWpd GF hlc _ _ (splPol GT) (gtAdGd GT) spinN Unit
        (spinOb6 ya (clRange xw nw) Cl cv) nm ⟨hp cpu (acqRmw kok kf) rs, k⟩ .MaybeStuck i Φ := by
  intro Hne Hrow
  have Hsplit : iprop(locked (GF := GF) nm.2 ya i (i, k) ∗
      spinR6 (clRange xw nw) Cl nm (gtAdGd GT) (i, k)) ⊢
      iprop((locked nm.2 ya i (i, k) ∗ RL nm.1 (gtAdGd GT) Cl (i, k)) ∗
        RbN nm.1 (gtAdGd GT) 1 (clRange xw nw) (i, k) []) := by
    unfold spinR6
    iintro ⟨Hlk, Hx, HC⟩
    isplitl [Hlk HC]
    · isplitl [Hlk]
      · iexact Hlk
      · iexact HC
    · iapply (RLRbN1 GT nm (clRange xw nw) (i, k)) $$ Hx
  iintro #Hil Hnh HΨ
  iapply (wpdAcquireGen6 (hlc := hlc) (GF := GF) xw nw Cl cv GT nm cpu Hcons HlkX i k t kok kf
    iprop(locked nm.2 ya i (i, k) ∗ RL nm.1 (gtAdGd GT) Cl (i, k))
    (RbN nm.1 (gtAdGd GT) 1 (clRange xw nw) (i, k) []) Φ Hne Hrow Hsplit) $$ Hil Hnh HΨ

/-- THE RELEASE CONTRACT, GENERIC FORM (copy of `wpdReleaseGen` at `spinOb6`): any family `m` of
po-earlier anchors produces `locked` and each component of `R`. -/
theorem wpdReleaseGen6 (xw : Int) (nw : Nat) (Cl : List Int) (cv : Agent → List (BitVec 8))
    (GT : GdexecT) (nm : spinN) (cpu : CPU) (Hcons : rvwmoCatConsistent (gtAdGd GT))
    (HlkX : ya ∉ X6 (clRange xw nw) Cl) (i : Agent) (kf : Nat) (m' : SailM Unit) (c : Geid)
    (m : Mea GF) (Φ : Athread → IProp GF) :
    kf ≠ (AxOpsem.grow (gtAdGd GT) i).length → kf + 1 ≠ (AxOpsem.grow (gtAdGd GT) i).length →
    (AxOpsem.grow (gtAdGd GT) i)[kf]? = some (.LFence true true false true) →
    (AxOpsem.grow (gtAdGd GT) i)[kf + 1]? = some (.LStore false ya [b0] .WCrel) →
    (∀ e, e ∈ (FiniteMap.dom_set m : GSet Geid) → e.1 = i ∧ e.2 < kf ∧
      ∃ l, (AxOpsem.grow (gtAdGd GT) i)[e.2]? = some l ∧ (lbIsR l || lbIsW l) = true) →
    ⊢ isLock nm.2 ya (spinR6 (clRange xw nw) Cl nm (gtAdGd GT)) -∗
      ([∗map] e ↦ P ∈ m, AxAnnot.annotOwn e P) -∗
      (([∗map] P ∈ m, P) -∗
        locked nm.2 ya i c ∗
        (∃ (a : Geid), ⌜a ∈ (FiniteMap.dom_set m : GSet Geid)⌝ ∗
          RL nm.1 (gtAdGd GT) (clRange xw nw) a) ∗
        (∃ (a : Geid), ⌜a ∈ (FiniteMap.dom_set m : GSet Geid)⌝ ∗ RL nm.1 (gtAdGd GT) Cl a)) -∗
      (AxAnnot.annotOwn (i, kf + 1) (notheld nm.2 ya i) -∗
        ∀ rs : RegFile, @tierAWpd GF hlc _ _ (splPol GT) (gtAdGd GT) spinN Unit
          (spinOb6 ya (clRange xw nw) Cl cv) nm ⟨hp cpu m' rs, kf + 1 + 1⟩ .MaybeStuck i Φ) -∗
      ∀ rs : RegFile, @tierAWpd GF hlc _ _ (splPol GT) (gtAdGd GT) spinN Unit
        (spinOb6 ya (clRange xw nw) Cl cv) nm ⟨hp cpu (fenceM (relM m')) rs, kf⟩ .MaybeStuck i Φ := by
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
    exact ⟨fenceGob (gtAdGd GT) i ek kf (kf + 1) l ya [b0] .WCrel Hl' Hmem Hlf Hls Hlt
        (by omega),
      fenceLobp (gtAdGd GT) Hcons i ek kf (kf + 1) l ya [b0] .WCrel Hl' Hmem Hlf Hls Hlt
        (by omega)⟩
  have HS := shPos (hlc := hlc) (pol := splPol GT) (gtAdGd GT) spinN Unit
    (spinOb6 ya (clRange xw nw) Cl cv) nm cpu i Φ
    iprop(isLock (GF := GF) nm.2 ya (spinR6 (clRange xw nw) Cl nm (gtAdGd GT)) ∗
      ([∗map] e ↦ P ∈ m, AxAnnot.annotOwn e P) ∗
      (([∗map] P ∈ m, P) -∗
        locked nm.2 ya i c ∗
        (∃ (a : Geid), ⌜a ∈ (FiniteMap.dom_set m : GSet Geid)⌝ ∗
          RL nm.1 (gtAdGd GT) (clRange xw nw) a) ∗
        (∃ (a : Geid), ⌜a ∈ (FiniteMap.dom_set m : GSet Geid)⌝ ∗ RL nm.1 (gtAdGd GT) Cl a)) ∗
      (AxAnnot.annotOwn (i, kf + 1) (notheld nm.2 ya i) -∗
        ∀ rs : RegFile, @tierAWpd GF hlc _ _ (splPol GT) (gtAdGd GT) spinN Unit
          (spinOb6 ya (clRange xw nw) Cl cv) nm ⟨hp cpu m' rs, kf + 1 + 1⟩ .MaybeStuck i Φ))
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
      have HF : ∀ Rj, Rj ∈ [RL (GF := GF) nm.1 (gtAdGd GT) (clRange xw nw),
          RL nm.1 (gtAdGd GT) Cl] → lkTransportable (gtAdGd GT) Rj := by
        intro Rj H
        simp only [List.mem_cons, List.not_mem_nil, or_false] at H
        rcases H with rfl | rfl <;> exact RLTransportable _ _ _ Hcons
      have HRs : ([∗list] Rj ∈ [RL (GF := GF) nm.1 (gtAdGd GT) (clRange xw nw),
          RL nm.1 (gtAdGd GT) Cl], Rj (i, kf + 1)) ⊢
          spinR6 (clRange xw nw) Cl nm (gtAdGd GT) (i, kf + 1) := by
        unfold spinR6
        iintro ⟨H1, H2⟩
        ihave H2 := BigSepL.bigSepL_singleton.1 $$ H2
        isplitl [H1]
        · iexact H1
        · iexact H2
      iintro ⟨#Hil, Hm, Hw, HΨ⟩
      ihave Hfe := (fe6Release' (hlc := hlc) ya (clRange xw nw) Cl cv GT nm Hcons HlkX (i, kf + 1)
        i c (spinR6 (clRange xw nw) Cl nm (gtAdGd GT))
        [RL (GF := GF) nm.1 (gtAdGd GT) (clRange xw nw), RL nm.1 (gtAdGd GT) Cl] m Hzw
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
        (spinOb6 ya (clRange xw nw) Cl cv) nm (splAxpolWf GT) i (kf + 1) m (notheld nm.2 ya i)
        iprop(True) _ _ Hval Hsub) $$ Hm [Hfe]
      · iapply (@flowEqDynMono hlc GF _ (s6G ya (clRange xw nw) Cl cv GT nm)
          (splPol GT) (gtAdGd GT) (i, kf + 1) _ _ (notheld nm.2 ya i)
          iprop(notheld nm.2 ya i ∗ True)) $$ [] Hfe
        inext
        iintro H
        isplitl [H]
        · iexact H
        · itrivial
      iintro H _
      iapply HΨ $$ H %rs)
  have H := shPos (hlc := hlc) (pol := splPol GT) (gtAdGd GT) spinN Unit
    (spinOb6 ya (clRange xw nw) Cl cv) nm cpu i Φ
    iprop(isLock (GF := GF) nm.2 ya (spinR6 (clRange xw nw) Cl nm (gtAdGd GT)) ∗
      ([∗map] e ↦ P ∈ m, AxAnnot.annotOwn e P) ∗
      (([∗map] P ∈ m, P) -∗
        locked nm.2 ya i c ∗
        (∃ (a : Geid), ⌜a ∈ (FiniteMap.dom_set m : GSet Geid)⌝ ∗
          RL nm.1 (gtAdGd GT) (clRange xw nw) a) ∗
        (∃ (a : Geid), ⌜a ∈ (FiniteMap.dom_set m : GSet Geid)⌝ ∗ RL nm.1 (gtAdGd GT) Cl a)) ∗
      (AxAnnot.annotOwn (i, kf + 1) (notheld nm.2 ya i) -∗
        ∀ rs : RegFile, @tierAWpd GF hlc _ _ (splPol GT) (gtAdGd GT) spinN Unit
          (spinOb6 ya (clRange xw nw) Cl cv) nm ⟨hp cpu m' rs, kf + 1 + 1⟩ .MaybeStuck i Φ))
    kf (fenceM (relM m')) Hne1
    (fun rs id K => noReadAtFence cpu _ (relM m') rs kf id K)
    (fun rs l s' Hst' => by
      obtain ⟨rfl, Hs', -⟩ := fenceInv2 cpu _ (relM m') rs kf l s' Hst'
      simp only [wlWdata]
      subst Hs'
      iintro ⟨#Hil, Hm, Hw, HΨ⟩
      iapply (shSkip2 (GF := GF) (gtAdGd GT) spinN Unit (spinOb6 ya (clRange xw nw) Cl cv) nm i
        _ _)
      inext
      iapply HS $$ [$Hil $Hm $Hw $HΨ] %rs)
  iintro #Hil Hm Hw HΨ
  iapply H $$ [$Hil $Hm $Hw $HΨ]

/-- RELEASE, TWO ANCHORS: `locked ∗ lk->cpu` at the claim `c`, the word handle at `ex ≠ c`. -/
theorem wpdReleaseH6 (xw : Int) (nw : Nat) (Cl : List Int) (cv : Agent → List (BitVec 8))
    (GT : GdexecT) (nm : spinN) (cpu : CPU) (Hcons : rvwmoCatConsistent (gtAdGd GT))
    (HlkX : ya ∉ X6 (clRange xw nw) Cl) (i : Agent) (kf : Nat) (m' : SailM Unit) (c ex : Geid)
    (vs : List (BitVec 8)) (Φ : Athread → IProp GF) :
    kf ≠ (AxOpsem.grow (gtAdGd GT) i).length → kf + 1 ≠ (AxOpsem.grow (gtAdGd GT) i).length →
    (AxOpsem.grow (gtAdGd GT) i)[kf]? = some (.LFence true true false true) →
    (AxOpsem.grow (gtAdGd GT) i)[kf + 1]? = some (.LStore false ya [b0] .WCrel) →
    c ≠ ex →
    (∀ e, e = c ∨ e = ex → e.1 = i ∧ e.2 < kf ∧
      ∃ l, (AxOpsem.grow (gtAdGd GT) i)[e.2]? = some l ∧ (lbIsR l || lbIsW l) = true) →
    ⊢ isLock nm.2 ya (spinR6 (clRange xw nw) Cl nm (gtAdGd GT)) -∗
      AxAnnot.annotOwn c iprop(locked nm.2 ya i c ∗ RL nm.1 (gtAdGd GT) Cl c) -∗
      hdlw GT nm 1 xw nw ex vs -∗
      (AxAnnot.annotOwn (i, kf + 1) (notheld nm.2 ya i) -∗
        ∀ rs : RegFile, @tierAWpd GF hlc _ _ (splPol GT) (gtAdGd GT) spinN Unit
          (spinOb6 ya (clRange xw nw) Cl cv) nm ⟨hp cpu m' rs, kf + 1 + 1⟩ .MaybeStuck i Φ) -∗
      ∀ rs : RegFile, @tierAWpd GF hlc _ _ (splPol GT) (gtAdGd GT) spinN Unit
        (spinOb6 ya (clRange xw nw) Cl cv) nm ⟨hp cpu (fenceM (relM m')) rs, kf⟩ .MaybeStuck i Φ := by
  intro Hne1 Hne2 Hf Hst Hce Hev
  have hnone : get? ({[ex := RbN (GF := GF) nm.1 (gtAdGd GT) 1 (clRange xw nw) ex vs]} : Mea GF)
      c = none := lookupSingletonNe (Ne.symm Hce)
  have Hdom : ∀ e, e ∈ (FiniteMap.dom_set (insert
      ({[ex := RbN (GF := GF) nm.1 (gtAdGd GT) 1 (clRange xw nw) ex vs]} : Mea GF) c
      iprop(locked nm.2 ya i c ∗ RL nm.1 (gtAdGd GT) Cl c)) : GSet Geid) →
      e.1 = i ∧ e.2 < kf ∧
        ∃ l, (AxOpsem.grow (gtAdGd GT) i)[e.2]? = some l ∧ (lbIsR l || lbIsW l) = true := by
    intro e He
    rw [domInsert, domSingleton] at He
    apply Hev
    rcases elemOfUnion.1 He with h | h
    · exact Or.inl (elemOfSingleton.1 h)
    · exact Or.inr (elemOfSingleton.1 h)
  have HexIn : ex ∈ (FiniteMap.dom_set (insert
      ({[ex := RbN (GF := GF) nm.1 (gtAdGd GT) 1 (clRange xw nw) ex vs]} : Mea GF) c
      iprop(locked nm.2 ya i c ∗ RL nm.1 (gtAdGd GT) Cl c)) : GSet Geid) := by
    rw [domInsert, domSingleton]
    exact elemOfUnionR (elemOfSingleton.2 rfl)
  have HcIn : c ∈ (FiniteMap.dom_set (insert
      ({[ex := RbN (GF := GF) nm.1 (gtAdGd GT) 1 (clRange xw nw) ex vs]} : Mea GF) c
      iprop(locked nm.2 ya i c ∗ RL nm.1 (gtAdGd GT) Cl c)) : GSet Geid) := by
    rw [domInsert, domSingleton]
    exact elemOfUnionL (elemOfSingleton.2 rfl)
  have Hmk : ⊢ AxAnnot.annotOwn (GF := GF) c
        iprop(locked nm.2 ya i c ∗ RL nm.1 (gtAdGd GT) Cl c) -∗
      AxAnnot.annotOwn ex (RbN nm.1 (gtAdGd GT) 1 (clRange xw nw) ex vs) -∗
      [∗map] e ↦ P ∈ (insert
        ({[ex := RbN (GF := GF) nm.1 (gtAdGd GT) 1 (clRange xw nw) ex vs]} : Mea GF) c
        iprop(locked nm.2 ya i c ∗ RL nm.1 (gtAdGd GT) Cl c)), AxAnnot.annotOwn e P := by
    iintro Ha Hb
    iapply (BigSepM.bigSepM_insert hnone).2
    isplitl [Ha]
    · iexact Ha
    · iapply BigSepM.bigSepM_singleton.2
      iexact Hb
  have Hsplit : ⊢ ([∗map] Rin ∈ (insert
      ({[ex := RbN (GF := GF) nm.1 (gtAdGd GT) 1 (clRange xw nw) ex vs]} : Mea GF) c
      iprop(locked nm.2 ya i c ∗ RL nm.1 (gtAdGd GT) Cl c)), Rin) -∗
      iprop(locked nm.2 ya i c ∗
        (∃ (a : Geid), ⌜a ∈ (FiniteMap.dom_set (insert
          ({[ex := RbN (GF := GF) nm.1 (gtAdGd GT) 1 (clRange xw nw) ex vs]} : Mea GF) c
          iprop(locked nm.2 ya i c ∗ RL nm.1 (gtAdGd GT) Cl c)) : GSet Geid)⌝ ∗
          RL nm.1 (gtAdGd GT) (clRange xw nw) a) ∗
        (∃ (a : Geid), ⌜a ∈ (FiniteMap.dom_set (insert
          ({[ex := RbN (GF := GF) nm.1 (gtAdGd GT) 1 (clRange xw nw) ex vs]} : Mea GF) c
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
      · iapply (RbNRL nm.1 (gtAdGd GT) (clRange xw nw) ex vs) $$ HX
    · iexists c
      isplitr
      · ipureintro
        exact HcIn
      · iexact HC
  iintro #Hil Hc Hx HΨ
  ihave Hm := Hmk $$ Hc Hx
  ihave Hw := Hsplit
  iapply (wpdReleaseGen6 (hlc := hlc) (GF := GF) xw nw Cl cv GT nm cpu Hcons HlkX i kf m' c _ Φ
    Hne1 Hne2 Hf Hst Hdom) $$ Hil Hm Hw HΨ

/-- RELEASE WHEN THE CS NEVER TOUCHED THE WORD: its handle is still AT THE CLAIM, a second
fragment at the same event -- MERGED (`wpdAnnotMerge`) and drawn as ONE anchor (closes
AxSpinH2's `ex ≠ c` finding). -/
theorem wpdReleaseH6Same (xw : Int) (nw : Nat) (Cl : List Int) (cv : Agent → List (BitVec 8))
    (GT : GdexecT) (nm : spinN) (cpu : CPU) (Hcons : rvwmoCatConsistent (gtAdGd GT))
    (HlkX : ya ∉ X6 (clRange xw nw) Cl) (i : Agent) (kf : Nat) (m' : SailM Unit) (c : Geid)
    (vs : List (BitVec 8)) (Φ : Athread → IProp GF) :
    kf ≠ (AxOpsem.grow (gtAdGd GT) i).length → kf + 1 ≠ (AxOpsem.grow (gtAdGd GT) i).length →
    (AxOpsem.grow (gtAdGd GT) i)[kf]? = some (.LFence true true false true) →
    (AxOpsem.grow (gtAdGd GT) i)[kf + 1]? = some (.LStore false ya [b0] .WCrel) →
    (c.1 = i ∧ c.2 < kf ∧
      ∃ l, (AxOpsem.grow (gtAdGd GT) i)[c.2]? = some l ∧ (lbIsR l || lbIsW l) = true) →
    ⊢ isLock nm.2 ya (spinR6 (clRange xw nw) Cl nm (gtAdGd GT)) -∗
      AxAnnot.annotOwn c iprop(locked nm.2 ya i c ∗ RL nm.1 (gtAdGd GT) Cl c) -∗
      hdlw GT nm 1 xw nw c vs -∗
      (AxAnnot.annotOwn (i, kf + 1) (notheld nm.2 ya i) -∗
        ∀ rs : RegFile, @tierAWpd GF hlc _ _ (splPol GT) (gtAdGd GT) spinN Unit
          (spinOb6 ya (clRange xw nw) Cl cv) nm ⟨hp cpu m' rs, kf + 1 + 1⟩ .MaybeStuck i Φ) -∗
      ∀ rs : RegFile, @tierAWpd GF hlc _ _ (splPol GT) (gtAdGd GT) spinN Unit
        (spinOb6 ya (clRange xw nw) Cl cv) nm ⟨hp cpu (fenceM (relM m')) rs, kf⟩ .MaybeStuck i Φ := by
  intro Hne1 Hne2 Hf Hst Hc
  have Hdom : ∀ e, e ∈ (FiniteMap.dom_set ({[c := iprop((locked (GF := GF) nm.2 ya i c ∗
      RL nm.1 (gtAdGd GT) Cl c) ∗ RbN nm.1 (gtAdGd GT) 1 (clRange xw nw) c vs)]} : Mea GF) :
      GSet Geid) →
      e.1 = i ∧ e.2 < kf ∧
        ∃ l, (AxOpsem.grow (gtAdGd GT) i)[e.2]? = some l ∧ (lbIsR l || lbIsW l) = true := by
    intro e He
    rw [domSingleton] at He
    rw [elemOfSingleton.1 He]
    exact Hc
  have HcIn : c ∈ (FiniteMap.dom_set ({[c := iprop((locked (GF := GF) nm.2 ya i c ∗
      RL nm.1 (gtAdGd GT) Cl c) ∗ RbN nm.1 (gtAdGd GT) 1 (clRange xw nw) c vs)]} : Mea GF) :
      GSet Geid) := by
    rw [domSingleton]
    exact elemOfSingleton.2 rfl
  have Hsplit : ⊢ ([∗map] Rin ∈ ({[c := iprop((locked (GF := GF) nm.2 ya i c ∗
      RL nm.1 (gtAdGd GT) Cl c) ∗ RbN nm.1 (gtAdGd GT) 1 (clRange xw nw) c vs)]} : Mea GF), Rin) -∗
      iprop(locked nm.2 ya i c ∗
        (∃ (a : Geid), ⌜a ∈ (FiniteMap.dom_set ({[c := iprop((locked (GF := GF) nm.2 ya i c ∗
          RL nm.1 (gtAdGd GT) Cl c) ∗ RbN nm.1 (gtAdGd GT) 1 (clRange xw nw) c vs)]} : Mea GF) :
          GSet Geid)⌝ ∗ RL nm.1 (gtAdGd GT) (clRange xw nw) a) ∗
        (∃ (a : Geid), ⌜a ∈ (FiniteMap.dom_set ({[c := iprop((locked (GF := GF) nm.2 ya i c ∗
          RL nm.1 (gtAdGd GT) Cl c) ∗ RbN nm.1 (gtAdGd GT) 1 (clRange xw nw) c vs)]} : Mea GF) :
          GSet Geid)⌝ ∗ RL nm.1 (gtAdGd GT) Cl a)) := by
    iintro H
    ihave H := (BigSepM.bigSepM_singleton (M := GMapF Geid)).1 $$ H
    icases H with ⟨⟨Hlk, HC⟩, HX⟩
    isplitl [Hlk]
    · iexact Hlk
    isplitl [HX]
    · iexists c
      isplitr
      · ipureintro
        exact HcIn
      · iapply (RbNRL nm.1 (gtAdGd GT) (clRange xw nw) c vs) $$ HX
    · iexists c
      isplitr
      · ipureintro
        exact HcIn
      · iexact HC
  iintro #Hil Hc Hx HΨ %rs
  iapply (wpdAnnotMerge (hlc := hlc) (pol := splPol GT) (gtAdGd GT) spinN Unit
    (spinOb6 ya (clRange xw nw) Cl cv) nm i Φ _ c _ _) $$ Hc Hx
  iintro Hcx
  ihave Hm := (BigSepM.bigSepM_singleton (M := GMapF Geid)
    (Φ := fun e P => AxAnnot.annotOwn (GF := GF) e P)).2 $$ Hcx
  ihave Hw := Hsplit
  iapply (wpdReleaseGen6 (hlc := hlc) (GF := GF) xw nw Cl cv GT nm cpu Hcons HlkX i kf m' c _ Φ
    Hne1 Hne2 Hf Hst Hdom) $$ Hil Hm Hw HΨ %rs

/-- The holder's `lw ya` (1 byte): `locked` (with any frame `Q`) drawn from the claim's
annotation (ppo rule 5), deposited back at the read together with `v ≠ 0`. -/
theorem wpdLkreadHeld6 (xw : Int) (nw : Nat) (Cl : List Int) (cv : Agent → List (BitVec 8))
    (GT : GdexecT) (nm : spinN) (cpu : CPU) (Hcons : rvwmoCatConsistent (gtAdGd GT))
    (HlkX : ya ∉ X6 (clRange xw nw) Cl) (i : Agent) (kc k : Nat)
    (KK : Result (BitVec (8 * 1) × Option Bool) Arch.abort → SailM Unit) (tc t : Nat)
    (v : BitVec 8) (Q : IProp GF) (Φ : Athread → IProp GF) :
    k ≠ (AxOpsem.grow (gtAdGd GT) i).length →
    (AxOpsem.grow (gtAdGd GT) i)[kc]? = some (.LRmw true false ya [tc] [b0] [b1] .WCplain) →
    kc < k →
    (AxOpsem.grow (gtAdGd GT) i)[k]? = some (.LLoad false ya [t] [v]) →
    nolk ya (gtAdGd GT).gdG (i, kc) (i, k) →
    ⊢ AxAnnot.annotOwn (i, kc) iprop(locked nm.2 ya i (i, kc) ∗ Q) -∗
      (AxAnnot.annotOwn (i, k) iprop(locked nm.2 ya i (i, kc) ∗ Q) -∗
        AxAnnot.annotOwn (i, k) iprop(⌜v ≠ b0⌝) -∗
        ∀ rs : RegFile, @tierAWpd GF hlc _ _ (splPol GT) (gtAdGd GT) spinN Unit
          (spinOb6 ya (clRange xw nw) Cl cv) nm ⟨hp cpu (KK (.Ok (v, none))) rs, k + 1⟩
          .MaybeStuck i Φ) -∗
      ∀ rs : RegFile, @tierAWpd GF hlc _ _ (splPol GT) (gtAdGd GT) spinN Unit
        (spinOb6 ya (clRange xw nw) Cl cv) nm
        ⟨hp cpu (.impure (.ok (.memRead 1 64 (l3pRreq l3pAkP ypaM))) KK) rs, k⟩ .MaybeStuck i Φ := by
  intro Hne Hrowc Hlt Hrow Hnl
  have Hlc : gxLbl (gtAdGd GT).gdG (i, kc) =
      some (.LRmw true false ya [tc] [b0] [b1] .WCplain) := by
    rw [gxLblGrow]; exact Hrowc
  have Hl : gxLbl (gtAdGd GT).gdG (i, k) = some (.LLoad false ya [t] [v]) := by
    rw [gxLblGrow]; exact Hrow
  have Hadv : ∀ lb, (AxOpsem.grow (gtAdGd GT) i)[k]? = some lb → aidentAdvRd (aident lb) = 1 := by
    rw [Hrow]
    intro lb h
    cases h
    rfl
  have H := shRead (hlc := hlc) (pol := splPol GT) (gtAdGd GT) spinN Unit
    (spinOb6 ya (clRange xw nw) Cl cv) nm cpu i Φ ypaM ypaMRam KK k Hne Hadv
    iprop(AxAnnot.annotOwn (GF := GF) (i, kc) iprop(locked nm.2 ya i (i, kc) ∗ Q) ∗
      (AxAnnot.annotOwn (i, k) iprop(locked nm.2 ya i (i, kc) ∗ Q) -∗
        AxAnnot.annotOwn (i, k) iprop(⌜v ≠ b0⌝) -∗
        ∀ rs : RegFile, @tierAWpd GF hlc _ _ (splPol GT) (gtAdGd GT) spinN Unit
          (spinOb6 ya (clRange xw nw) Cl cv) nm ⟨hp cpu (KK (.Ok (v, none))) rs, k + 1⟩
          .MaybeStuck i Φ))
    (fun vs b rs Hgv Hvs => by
      subst Hvs
      have Hgv' : (some [v] : Option (List (BitVec 8))) = some [b] := by
        rw [← Hgv]; unfold graphValue; rw [Hl]; rfl
      have Hb : b = v := by
        have h := Option.some.inj Hgv'
        simp only [List.cons.injEq, and_true] at h
        exact h.symm
      subst b
      have Hin : ((i, kc) : Geid) ∈ @Axpol.lobp (splPol GT) (gtAdGd GT) (i, k) :=
        acqLobp (gtAdGd GT) Hcons i kc k _ _ _ _ _ _ Hlc Hl rfl Hlt
      have Hpo : WeakRvwmoGraph.gpo (gtAdGd GT).gdG (i, kc) (i, k) :=
        gpoRow (gtAdGd GT) i kc k _ _ Hlc Hl Hlt
      have Hnw : gisW (gtAdGd GT).gdG (i, k) = false := by unfold gisW; rw [Hl]; rfl
      have Hsing : ⊢ ([∗map] Rin ∈ ({[((i, kc) : Geid) :=
          iprop(locked (GF := GF) nm.2 ya i (i, kc) ∗ Q)]} : Mea GF), Rin) -∗
          iprop(locked (GF := GF) nm.2 ya i (i, kc) ∗ Q) := by
        iintro H
        ihave H := (BigSepM.bigSepM_singleton (M := GMapF Geid)).1 $$ H
        iexact H
      iintro ⟨Hc, HΨ⟩
      ihave Hw := Hsing
      ihave Hfe := (fe6LkreadHeld (hlc := hlc) ya (clRange xw nw) Cl cv GT nm Hcons HlkX (i, k) i
        (i, kc) Q ({[((i, kc) : Geid) := iprop(locked (GF := GF) nm.2 ya i (i, kc) ∗ Q)]} : Mea GF)
        Hnw Hpo Hnl) $$ Hw
      ihave Hfe := (@flowEqDynMono hlc GF _ (s6G ya (clRange xw nw) Cl cv GT nm) (splPol GT)
        (gtAdGd GT) (i, k) _ _
        iprop((locked nm.2 ya i (i, kc) ∗ Q) ∗
          ⌜∀ t' v', greadsByte (gtAdGd GT).gdG (i, k) ya t' v' → v' ≠ b0⌝)
        iprop((locked nm.2 ya i (i, kc) ∗ Q) ∗ ⌜v ≠ b0⌝)) $$ [] Hfe
      · inext
        iintro ⟨H, %Hf⟩
        isplitl [H]
        · iexact H
        · ipureintro
          exact Hf t v (grbLoad _ _ _ _ _ Hl)
      iapply (evDraw (hlc := hlc) (pol := splPol GT) (gtAdGd GT) spinN Unit
        (spinOb6 ya (clRange xw nw) Cl cv) nm (splAxpolWf GT) i k (i, kc) _
        iprop(locked nm.2 ya i (i, kc) ∗ Q) iprop(⌜v ≠ b0⌝) _ _ Hgv Hin) $$ Hc Hfe
      iintro H1 H2
      iapply HΨ $$ H1 H2 %rs)
  iintro Hc HΨ
  iapply H $$ [$Hc $HΨ]

end leaves6

end Weak
