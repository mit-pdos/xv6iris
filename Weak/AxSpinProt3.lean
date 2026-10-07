/-
Weak: **Phase 1a, part 3 of the spinlock plan -- the hand programs of the certificates, their
rows and runs, and the per-hart WPds AT THE REAL PROTOCOL** (`AxSpinProt2.spinOb`, lock word at
`ya`, owned byte `xa`).

Rocq: `iris/AxSpinProt3.v` @ xxvzwolszwmp.

## The Rocq header, in substance

PROGRAMS (hand `Pexv6` nodes, `AxSpinWit`/`AxLock3Prog` style; amoswap = exclusive-aq read half
+ exclusive write half; HALT = `hlt`):
  hart B (1) `bM0`: `amoswap.aq lk ← 1; if old ≠ 0 then (amoswap.aq lk ← 1; if old ≠ 0 then HALT
             else CS) else CS`, CS = `ld x; fence rw,w; sw lk ← 0 (release); HALT` -- TWO
             attempts (the spin loop unrolled once); its row `bRow` is the ≥1-FAILED-SPIN path.
  hart A (0) `aM0`: `amoswap.aq lk ← 1; sd x ← 1; fence rw,w; sw lk ← 0; HALT` (row `aRow`).
  race A `rM0`: `amoswap.aq lk ← 1; fence rw,w; sw lk ← 0; sd x ← 2; HALT` -- writes `x` AFTER
             releasing the lock.
WPds: `wpdB` (post: `x`'s read value is `b1` or the image -- read back at the row end from the
x-read's annotation), `wpdA` (the positive A), `wpdRTriv` (race A at the TRIVIAL protocol).

## Deviations from Rocq

1. O2 STAGE C (as `AxSpinProt2` deviation 1): no text oracle -- Rocq's `Tf` arguments of
   `AxGA2`/`tierA_wpd` are gone.
2. CONTEXTS: Rocq section variables are explicit leading arguments; `invGS_gen HasNoLc Σ` ↦
   `[InvGS_gen hlc GF]` for any `hlc`; local instances `evG`/`spB_G`/`spA_G`/`spR_G` are the
   reducible `shG …` / `splG …` passed explicitly, policies `spl_pol GT` passed explicitly.
3. lean-sail shapes (as `AxSpinWit` deviation 3): read answers `.Ok (w, none)`; `bW` uses a
   decidable `if w = b0`; `init_regstate` ↦ `zeroRegs`; `S k` ↦ `k + 1`; `l !! k` ↦ `l[k]?`.
   The rows' lock address is `ya` (= `paZ ypaM` by `rfl`).

**Rocq → Lean name map.**  `b_rel` `AxSpinProt3.bRel`, `b_fence` `bFence`, `b_ld` `bLd`, `b_w`
`bW`, `b_k` `bK`, `b_rmw` `bRmw`, `b_m0` `AxSpinProt3.bM0`, `b_row` `AxSpinProt3.bRow`,
`a_fence` `aFence`, `a_st` `aSt`, `a_w` `aW`, `a_m0` `AxSpinProt3.aM0`, `a_row`
`AxSpinProt3.aRow`, `r_st` `rSt`, `r_rel` `rRel`, `r_fence` `rFence`, `r_w` `rW`, `r_m0`
`AxSpinProt3.rM0`, `r_row` `AxSpinProt3.rRow`, `b_k_B1` `bKB1`, `b_run` `AxSpinProt3.bRun`,
`a_run` `AxSpinProt3.aRun`, `r_run` `AxSpinProt3.rRun`, `gwb_rmw` `gwbRmw`, `grb_load_only`
`grbLoadOnly`, `store_no_read` `storeNoRead`, `gpo_row` `gpoRow`, `acq_gob` `acqGob`,
`fence_gob` `fenceGob`, `gob_gmo` `gobGmo`, `lobp_intro` `lobpIntro`, `ev_plain` `evPlain`,
`ev_draw` `evDraw`, `bL` `AxSpinProt3.bL`, `b_no_x` `bNoX`, `wB5/4/3/2` `AxSpinProt3.wB5/4/3/2`,
`wB1w`/`wB1r`/`wB0w` `AxSpinProt3.wB1w`/`wB1r`/`wB0w`, `wpdB` `AxSpinProt3.wpdB`, `aL`
`AxSpinProt3.aL`, `wA3/2/1` `AxSpinProt3.wA3/2/1`, `wA0w` `AxSpinProt3.wA0w`, `wpdA`
`AxSpinProt3.wpdA`, `fe_triv` `feTriv`, `rL` `rL`, `wR_st` `wRSt`, `wR_rel` `wRRel`, `wR_fence`
`wRFence`, `wpdR_triv` `AxSpinProt3.wpdRTriv`.  Duplicated Rocq names are file-qualified
(`AxSpinProt3.*`).  Lean-only (file-qualified): `AxSpinProt3.bKOk` (`bK` at any `Ok` answer),
`AxSpinProt3.annotEq` (a copy of `AxLock3Writer.annotEq`, to avoid that import).

4. PROOF ROUTE (not statements): `spinR` is a plain def (Rocq: a notation), so the x-read /
   x-write steps bridge `spinR xa nm GD e` and `Rx nm.1 xa GD e` by `.rfl` entailments.
   `ev_draw`'s `Hwf` (Rocq section hypothesis) is the explicit argument `Hwf : axpolWf`.
   The `wR*` sanity-twin lemmas take `GT`/`cpu`/`Hrow` explicitly (Rocq section context).

**Dropped:** none (55 Rocq decls; 57 Lean = 55 + 2 Lean-only).
-/
import Weak.AxSpinProt2

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D

/-! # 1. Programs and rows -/

abbrev AxSpinProt3.bRel : SailM Unit :=
  .impure (.ok (.memWrite 1 64 (l3pWreq l3pAkP ypaM b0))) (fun _ => hlt)
abbrev bFence : SailM Unit :=
  .impure (.ok (.barrier .Barrier_RISCV_rw_w)) (fun _ => AxSpinProt3.bRel)
abbrev bLd : SailM Unit :=
  .impure (.ok (.memRead 1 64 (l3pRreq l3pAkP xpaM))) (fun _ => bFence)
abbrev bW (w : BitVec 8) (kf : SailM Unit) : SailM Unit :=
  .impure (.ok (.memWrite 1 64 (l3pWreq l3pAkXpl ypaM b1)))
    (fun _ => if w = b0 then bLd else kf)
def bK (kf : SailM Unit) (res : Result (BitVec (8 * 1) × Option Bool) Arch.abort) : SailM Unit :=
  match res with
  | .Ok (w, _) => bW w kf
  | .Err _ => hlt
abbrev bRmw (kf : SailM Unit) : SailM Unit :=
  .impure (.ok (.memRead 1 64 (l3pRreq l3pAkXaq ypaM))) (bK kf)
abbrev AxSpinProt3.bM0 : SailM Unit := bRmw (bRmw hlt)

def AxSpinProt3.bRow (t1 t2 tx : Nat) (vx : BitVec 8) : List Lbl :=
  [.LRmw true false ya [t1] [b1] [b1] .WCplain,
   .LRmw true false ya [t2] [b0] [b1] .WCplain,
   .LLoad false xa [tx] [vx],
   .LFence true true false true,
   .LStore false ya [b0] .WCrel]

abbrev aFence : SailM Unit :=
  .impure (.ok (.barrier .Barrier_RISCV_rw_w)) (fun _ => AxSpinProt3.bRel)
abbrev aSt : SailM Unit :=
  .impure (.ok (.memWrite 1 64 (l3pWreq l3pAkP xpaM b1))) (fun _ => aFence)
abbrev aW : SailM Unit :=
  .impure (.ok (.memWrite 1 64 (l3pWreq l3pAkXpl ypaM b1))) (fun _ => aSt)
abbrev AxSpinProt3.aM0 : SailM Unit :=
  .impure (.ok (.memRead 1 64 (l3pRreq l3pAkXaq ypaM))) (fun _ => aW)

def AxSpinProt3.aRow (tA : Nat) : List Lbl :=
  [.LRmw true false ya [tA] [b0] [b1] .WCplain,
   .LStore false xa [b1] .WCplain,
   .LFence true true false true,
   .LStore false ya [b0] .WCrel]

abbrev rSt : SailM Unit :=
  .impure (.ok (.memWrite 1 64 (l3pWreq l3pAkP xpaM b2))) (fun _ => hlt)
abbrev rRel : SailM Unit :=
  .impure (.ok (.memWrite 1 64 (l3pWreq l3pAkP ypaM b0))) (fun _ => rSt)
abbrev rFence : SailM Unit :=
  .impure (.ok (.barrier .Barrier_RISCV_rw_w)) (fun _ => rRel)
abbrev rW : SailM Unit :=
  .impure (.ok (.memWrite 1 64 (l3pWreq l3pAkXpl ypaM b1))) (fun _ => rFence)
abbrev AxSpinProt3.rM0 : SailM Unit :=
  .impure (.ok (.memRead 1 64 (l3pRreq l3pAkXaq ypaM))) (fun _ => rW)

def AxSpinProt3.rRow : List Lbl :=
  [.LRmw true false ya [0] [b0] [b1] .WCplain,
   .LFence true true false true,
   .LStore false ya [b0] .WCrel,
   .LStore false xa [b2] .WCplain]

theorem bKB1 (kf : SailM Unit) : bK kf (.Ok (b1, none)) = bW b1 kf := rfl

/-- Lean-only: `bK` at any `Ok` answer. -/
theorem AxSpinProt3.bKOk (kf : SailM Unit) (w : BitVec (8 * 1)) (o : Option Bool) :
    bK kf (.Ok (w, o)) = bW w kf := rfl

/-! # 2. Runs over an ABSTRACT graph, row pinned -/

section runs3
variable (cpu : CPU)

theorem AxSpinProt3.bRun (GD : Gdexec) (t1 t2 tx : Nat) (vx : BitVec 8)
    (Hrow : AxOpsem.grow GD hB = AxSpinProt3.bRow t1 t2 tx vx) :
    nsteps (astepAnyNfGv GD hB) 7 ⟨hp cpu AxSpinProt3.bM0 zeroRegs, 0⟩
      ⟨hp cpu hlt zeroRegs, 5⟩ := by
  refine nsteps_l (runRmwRead cpu GD hB 0 ypaM ypaMRam t1 b1 .WCplain (bK (bRmw hlt)) zeroRegs
    (by rw [Hrow]; rfl)) ?_
  have H1 := runRmwWrite cpu GD hB 0 ypaM ypaMRam t1 b1 .WCplain
    (if b1 = b0 then bLd else bRmw hlt) zeroRegs (by rw [Hrow]; rfl)
  rw [if_neg (Ne.symm b0NeB1)] at H1
  refine nsteps_l H1 ?_
  refine nsteps_l (runRmwRead cpu GD hB 1 ypaM ypaMRam t2 b0 .WCplain (bK hlt) zeroRegs
    (by rw [Hrow]; rfl)) ?_
  have H3 := runRmwWrite cpu GD hB 1 ypaM ypaMRam t2 b0 .WCplain
    (if b0 = b0 then bLd else hlt) zeroRegs (by rw [Hrow]; rfl)
  rw [if_pos rfl] at H3
  refine nsteps_l H3 ?_
  refine nsteps_l (spRunRead cpu GD hB xpaM xpaMRam [tx] vx (fun _ => bFence) zeroRegs 2
    (by rw [Hrow]; rfl)) ?_
  refine nsteps_l (runFence cpu GD hB 3 AxSpinProt3.bRel zeroRegs (by rw [Hrow]; rfl)) ?_
  refine nsteps_l (spRunWrite cpu GD hB ypaM ypaMRam b0 hlt zeroRegs 4 .WCrel
    (by rw [Hrow]; rfl)) ?_
  exact nsteps_O _

theorem AxSpinProt3.aRun (GD : Gdexec) (tA : Nat)
    (Hrow : AxOpsem.grow GD hA = AxSpinProt3.aRow tA) :
    nsteps (astepAnyNfGv GD hA) 5 ⟨hp cpu AxSpinProt3.aM0 zeroRegs, 0⟩
      ⟨hp cpu hlt zeroRegs, 4⟩ := by
  refine nsteps_l (runRmwRead cpu GD hA 0 ypaM ypaMRam tA b0 .WCplain (fun _ => aW) zeroRegs
    (by rw [Hrow]; rfl)) ?_
  refine nsteps_l (runRmwWrite cpu GD hA 0 ypaM ypaMRam tA b0 .WCplain aSt zeroRegs
    (by rw [Hrow]; rfl)) ?_
  refine nsteps_l (spRunWrite cpu GD hA xpaM xpaMRam b1 aFence zeroRegs 1 .WCplain
    (by rw [Hrow]; rfl)) ?_
  refine nsteps_l (runFence cpu GD hA 2 AxSpinProt3.bRel zeroRegs (by rw [Hrow]; rfl)) ?_
  refine nsteps_l (spRunWrite cpu GD hA ypaM ypaMRam b0 hlt zeroRegs 3 .WCrel
    (by rw [Hrow]; rfl)) ?_
  exact nsteps_O _

theorem AxSpinProt3.rRun (GD : Gdexec) (Hrow : AxOpsem.grow GD hA = AxSpinProt3.rRow) :
    nsteps (astepAnyNfGv GD hA) 5 ⟨hp cpu AxSpinProt3.rM0 zeroRegs, 0⟩
      ⟨hp cpu hlt zeroRegs, 4⟩ := by
  refine nsteps_l (runRmwRead cpu GD hA 0 ypaM ypaMRam 0 b0 .WCplain (fun _ => rW) zeroRegs
    (by rw [Hrow]; rfl)) ?_
  refine nsteps_l (runRmwWrite cpu GD hA 0 ypaM ypaMRam 0 b0 .WCplain rFence zeroRegs
    (by rw [Hrow]; rfl)) ?_
  refine nsteps_l (runFence cpu GD hA 1 rRel zeroRegs (by rw [Hrow]; rfl)) ?_
  refine nsteps_l (spRunWrite cpu GD hA ypaM ypaMRam b0 rSt zeroRegs 2 .WCrel
    (by rw [Hrow]; rfl)) ?_
  refine nsteps_l (spRunWrite cpu GD hA xpaM xpaMRam b2 hlt zeroRegs 3 .WCplain
    (by rw [Hrow]; rfl)) ?_
  exact nsteps_O _

end runs3

/-! # 3. Event-step helpers: allocate the event's annotation, optionally DRAWING a
lob-predecessor's annotation, and SPLIT the new one. -/

/-- Lean-only (a copy of `AxLock3Writer.annotEq`, not imported here). -/
theorem AxSpinProt3.annotEq {GF : BundledGFunctors} (na : Mea GF) (e e' : Geid)
    (R P : IProp GF) :
    insert (insert na e R) e' P =
      PartialMap.union (PartialMap.union {[e' := P]} {[e := R]}) na := by
  rw [insertUnionSingletonL (M := GMapF Geid), insertUnionSingletonL (M := GMapF Geid)]
  exact mapUnionAssoc (M := GMapF Geid)

section ev
variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF] [AxannotGS GF]
  (GD : Gdexec) (N obSt0 : Type) (obi : N → Gdexec → obSt0 → GSet Geid → IProp GF) (nm : N)
  [pol : Axpol]

theorem evPlain (i : Agent) (k : Nat) (R1 R2 : IProp GF) (val : Prop) (Ψ : IProp GF) :
    val →
    ⊢ @flowEqDyn hlc GF _ (shG GD N obSt0 obi nm) GD (i, k) (Axpol.sPol GD (i, k)) (∅ : Mea GF)
        iprop(R1 ∗ R2) -∗
      (AxAnnot.annotOwn (i, k) R1 -∗ AxAnnot.annotOwn (i, k) R2 -∗ Ψ) -∗
      @wpEvStep hlc GF _ (shG GD N obSt0 obi nm) pol Unit GD i k (fun _ => True)
        (fun _ => val) (fun _ => k + 1) (fun _ => Ψ) := by
  intro Hval
  iintro Hfe HΨ
  unfold wpEvStep
  iintro %na ⟨Hpg, Hannot⟩
  ihave %Hnin := naAtProgressNotElemOf GD i k na $$ Hpg
  imod annotAlloc na (i, k) iprop(R1 ∗ R2) Hnin $$ Hannot with ⟨Hannot, Hfrag⟩
  imod (annotSplit (i, k) R1 R2) $$ Hfrag %_ Hannot with ⟨⟨Hf1, Hf2⟩, Hannot⟩
  imodintro
  inext
  imodintro
  iexists (), iprop(R1 ∗ R2), (∅ : Mea GF), (∅ : Mea GF), ()
  isplitr
  · ipureintro
    trivial
  isplitr
  · iapply AxSpinWit.naSplittingWfEmpty
  isplitl [Hfe]
  · iapply (@flowEqDynMono hlc GF _ (shG GD N obSt0 obi nm) pol GD (i, k) _ (∅ : Mea GF)
      iprop(R1 ∗ R2) iprop((R1 ∗ R2) ∗ ⌜val⌝)) $$ [] Hfe
    inext
    iintro H
    isplitl [H]
    · iexact H
    · ipureintro
      exact Hval
  isplitl [Hannot]
  · rw [AxLockWp.annotInsertEq na (i, k) iprop(R1 ∗ R2)]
    iexact Hannot
  isplitr
  · iapply AxSpinWit.localTrue
  · iapply HΨ $$ Hf1 Hf2

theorem evDraw (Hwf : @axpolWf pol) (i : Agent) (k : Nat) (e' : Geid) (P R1 R2 : IProp GF)
    (val : Prop) (Ψ : IProp GF) :
    val → e' ∈ Axpol.lobp GD (i, k) →
    ⊢ AxAnnot.annotOwn e' P -∗
      @flowEqDyn hlc GF _ (shG GD N obSt0 obi nm) GD (i, k) (Axpol.sPol GD (i, k))
        ({[e' := P]} : Mea GF) iprop(R1 ∗ R2) -∗
      (AxAnnot.annotOwn (i, k) R1 -∗ AxAnnot.annotOwn (i, k) R2 -∗ Ψ) -∗
      @wpEvStep hlc GF _ (shG GD N obSt0 obi nm) pol Unit GD i k (fun _ => True)
        (fun _ => val) (fun _ => k + 1) (fun _ => Ψ) := by
  intro Hval Hin
  iintro Hp Hfe HΨ
  unfold wpEvStep naAtProgress
  iintro %na ⟨%Hprog, Hannot⟩
  have Hb := Hwf GD i k e' Hin
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
  iexists (), iprop(R1 ∗ R2), ({[e' := P]} : Mea GF), ({[e' := Rr]} : Mea GF), ()
  isplitr
  · ipureintro
    trivial
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
  · iapply (@flowEqDynMono hlc GF _ (shG GD N obSt0 obi nm) pol GD (i, k) _
      ({[e' := P]} : Mea GF) iprop(R1 ∗ R2) iprop((R1 ∗ R2) ∗ ⌜val⌝)) $$ [] Hfe
    inext
    iintro H
    isplitl [H]
    · iexact H
    · ipureintro
      exact Hval
  isplitl [Hannot]
  · rw [← AxSpinProt3.annotEq]
    iexact Hannot
  isplitr
  · iapply AxSpinWit.localTrue
  · iapply HΨ $$ Hf1 Hf2

end ev

/-! # 4. Row graph facts -/

theorem gwbRmw (G : Gexec) (e : Geid) (base : Int) (t : Nat) (old new : BitVec 8)
    (cls : WmClass) :
    gxLbl G e = some (.LRmw true false base [t] [old] [new] cls) →
    greadsByte G e base t old ∧ gwritesByte G e base new ∧
    (∀ a v, gwritesByte G e a v → a = base ∧ v = new) ∧
    (∀ a t' v, greadsByte G e a t' v → a = base ∧ t' = t ∧ v = old) := by
  intro Hl
  refine ⟨⟨_, base, [t], [old], 0, Hl, rfl, rfl, rfl, by simp [accAddr]⟩,
    ⟨_, base, [new], 0, Hl, rfl, rfl, by simp [accAddr]⟩, ?_, ?_⟩
  · rintro a v ⟨l, base', vs, j, Hl', Hwr, Hv, Ha⟩
    rw [Hl] at Hl'
    cases Hl'
    simp only [lbWr, Option.some.injEq, Prod.mk.injEq] at Hwr
    obtain ⟨rfl, rfl⟩ := Hwr
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at Hv
      refine ⟨?_, Hv.symm⟩
      rw [← Ha]; simp [accAddr]
    | succ j => simp at Hv
  · rintro a t' v ⟨l, base', ts, vs, j, Hl', Hrd, Ht, Hv, Ha⟩
    rw [Hl] at Hl'
    cases Hl'
    simp only [lbRd, Option.some.injEq, Prod.mk.injEq] at Hrd
    obtain ⟨rfl, rfl, rfl⟩ := Hrd
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at Hv Ht
      refine ⟨?_, Ht.symm, Hv.symm⟩
      rw [← Ha]; simp [accAddr]
    | succ j => simp at Hv

theorem grbLoadOnly (G : Gexec) (e : Geid) (base : Int) (t : Nat) (b : BitVec 8) :
    gxLbl G e = some (.LLoad false base [t] [b]) →
    ∀ a t' v, greadsByte G e a t' v → a = base ∧ t' = t ∧ v = b := by
  rintro Hl a t' v ⟨l, base', ts, vs, j, Hl', Hrd, Ht, Hv, Ha⟩
  rw [Hl] at Hl'
  cases Hl'
  simp only [lbRd, Option.some.injEq, Prod.mk.injEq] at Hrd
  obtain ⟨rfl, rfl, rfl⟩ := Hrd
  cases j with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at Hv Ht
    refine ⟨?_, Ht.symm, Hv.symm⟩
    rw [← Ha]; simp [accAddr]
  | succ j => simp at Hv

theorem storeNoRead (G : Gexec) (e : Geid) (base : Int) (vs : List (BitVec 8)) (cls : WmClass)
    (a : Int) (t : Nat) (v : BitVec 8) :
    gxLbl G e = some (.LStore false base vs cls) → ¬ greadsByte G e a t v := by
  rintro Hl ⟨l, base', ts, vs', j, Hl', Hrd, -⟩
  rw [Hl] at Hl'
  cases Hl'
  simp [lbRd] at Hrd

section rowfacts
variable (GD : Gdexec)

theorem gpoRow (i : Agent) (k1 k2 : Nat) (l1 l2 : Lbl) :
    gxLbl GD.gdG (i, k1) = some l1 → gxLbl GD.gdG (i, k2) = some l2 → k1 < k2 →
    WeakRvwmoGraph.gpo GD.gdG (i, k1) (i, k2) := by
  intro H1 H2 Hlt
  exact ⟨rfl, Hlt, by rw [H1]; rfl, by rw [H2]; rfl⟩

theorem acqGob (i : Agent) (k1 k2 : Nat) (base : Int) (ts : List Nat) (rvs wvs : List (BitVec 8))
    (cls : WmClass) (l2 : Lbl) :
    gxLbl GD.gdG (i, k1) = some (.LRmw true false base ts rvs wvs cls) →
    gxLbl GD.gdG (i, k2) = some l2 → lbIsMem l2 = true → k1 < k2 →
    gobCat GD (i, k1) (i, k2) := by
  intro H1 H2 Hm Hlt
  apply gobCatStep
  refine .inl (.inl (.inr (.inr (.inr (.inr (.inl ?_))))))
  exact ⟨gpoRow GD i k1 k2 _ _ H1 H2 Hlt, ⟨_, H1, rfl⟩, ⟨_, H1, rfl⟩, ⟨l2, H2, Hm⟩⟩

theorem fenceGob (i : Agent) (k1 kf k2 : Nat) (l1 : Lbl) (base : Int) (vs : List (BitVec 8))
    (cls : WmClass) :
    gxLbl GD.gdG (i, k1) = some l1 → lbIsMem l1 = true →
    gxLbl GD.gdG (i, kf) = some (.LFence true true false true) →
    gxLbl GD.gdG (i, k2) = some (.LStore false base vs cls) →
    k1 < kf → kf < k2 → gobCat GD (i, k1) (i, k2) := by
  intro H1 Hm Hf H2 Hl1 Hl2
  apply gobCatStep
  refine .inl (.inl (.inr (.inr (.inr (.inl ?_)))))
  refine ⟨true, true, false, true, ⟨rfl, by simp only; omega, kf, Hl1, Hl2, Hf⟩, ?_, ?_⟩
  · unfold lbIsMem at Hm
    cases Hr : lbIsR l1 with
    | true => exact .inl ⟨⟨l1, H1, Hr⟩, rfl⟩
    | false =>
      rw [Hr, Bool.false_or] at Hm
      exact .inr ⟨⟨l1, H1, Hm⟩, rfl⟩
  · exact .inr ⟨⟨_, H2, rfl⟩, rfl⟩

theorem gobGmo (Hcons : rvwmoCatConsistent GD) (e1 e2 : Geid) :
    gobCat GD e1 e2 → gmoLt GD.gdG e1 e2 :=
  fun H => obCatSubGmo GD e1 e2 Hcons H

theorem lobpIntro (e' e : Geid) (l' : Lbl) :
    gxLbl GD.gdG e' = some l' → lbIsMem l' = true → WeakRvwmoGraph.gpo GD.gdG e' e →
    gmoLt GD.gdG e' e → e' ∈ splLobp GD e := by
  intro Hl Hm Hpo Hlt
  refine (elemOfSplLobp GD e e').2 ⟨Hlt.1, ?_, Hpo, Hlt⟩
  unfold gmemB
  rw [Hl]
  exact Hm

end rowfacts

/-! # 5. HART B's WPd at the real protocol (the ≥1-failed-spin handoff reader): the post
`x = 1 ∨ x = image` is READ BACK at the row end from the x-read's annotation. -/

section wpdB
variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF] [AxannotGS GF]
  [AxlogG GF Hent] [SpinlockG GF]

theorem AxSpinProt3.bL (GT : GdexecT) (t1 t2 tx : Nat) (vx : BitVec 8)
    (Hrow : AxOpsem.grow (gtAdGd GT) hB = AxSpinProt3.bRow t1 t2 tx vx) (k : Nat) (lb : Lbl) :
    (AxSpinProt3.bRow t1 t2 tx vx)[k]? = some lb → gxLbl (gtAdGd GT).gdG (hB, k) = some lb := by
  intro Hk
  rw [gxLblGrow, Hrow]
  exact Hk

theorem bNoX (GT : GdexecT) (t1 t2 tx : Nat) (vx : BitVec 8)
    (Hrow : AxOpsem.grow (gtAdGd GT) hB = AxSpinProt3.bRow t1 t2 tx vx) (w : Geid) (v : BitVec 8) :
    gwritesByte (gtAdGd GT).gdG w xa v → w.1 = hB → False := by
  rintro ⟨l, base, vs, j, Hl, Hwr, Hv, Ha⟩ Hh
  obtain ⟨wi, wk⟩ := w
  simp only at Hh
  subst Hh
  rw [gxLblGrow, Hrow] at Hl
  have hj : ∀ (b : Int) (vs : List (BitVec 8)), vs.length = 1 → vs[j]? = some v →
      accAddr b j = xa → b = xa := by
    intro b vs hl hv ha
    have : j < vs.length := by
      rcases Nat.lt_or_ge j vs.length with h | h
      · exact h
      · rw [List.getElem?_eq_none h] at hv; cases hv
    rw [← ha]; simp [accAddr]; omega
  match wk, Hl with
  | 0, Hl =>
    cases Hl; simp only [lbWr, Option.some.injEq, Prod.mk.injEq] at Hwr
    obtain ⟨rfl, rfl⟩ := Hwr
    exact xaNeYa (hj ya _ rfl Hv Ha).symm
  | 1, Hl =>
    cases Hl; simp only [lbWr, Option.some.injEq, Prod.mk.injEq] at Hwr
    obtain ⟨rfl, rfl⟩ := Hwr
    exact xaNeYa (hj ya _ rfl Hv Ha).symm
  | 2, Hl => cases Hl; simp [lbWr] at Hwr
  | 3, Hl => cases Hl; simp [lbWr] at Hwr
  | 4, Hl =>
    cases Hl; simp only [lbWr, Option.some.injEq, Prod.mk.injEq] at Hwr
    obtain ⟨rfl, rfl⟩ := Hwr
    exact xaNeYa (hj ya _ rfl Hv Ha).symm
  | _ + 5, Hl => simp [AxSpinProt3.bRow] at Hl

theorem AxSpinProt3.wB5 (GT : GdexecT) (nm : spinN) (cpu : CPU) (vx : BitVec 8) :
    ⊢ AxAnnot.annotOwn (GF := GF) (hB, 2) iprop(⌜vx = b1 ∨ (gtAdGd GT).gdG.gxImg xa = some vx⌝) -∗
      ∀ rs : RegFile, @tierAWpd GF hlc _ _ (splPol GT) (gtAdGd GT) spinN Unit (spinOb ya xa) nm
        ⟨hp cpu hlt rs, 5⟩ .MaybeStuck hB
        (fun _ => iprop(⌜vx = b1 ∨ (gtAdGd GT).gdG.gxImg xa = some vx⌝)) :=
  shHltReadback (hlc := hlc) (pol := splPol GT) (gtAdGd GT) spinN Unit (spinOb ya xa) nm cpu hB 5
    (hB, 2) rfl _ _ .rfl

theorem AxSpinProt3.wB4 (GT : GdexecT) (nm : spinN) (cpu : CPU)
    (Hcons : rvwmoCatConsistent (gtAdGd GT)) (t1 t2 tx : Nat) (vx : BitVec 8)
    (Hrow : AxOpsem.grow (gtAdGd GT) hB = AxSpinProt3.bRow t1 t2 tx vx) :
    ⊢ isLock (GF := GF) nm.2 ya (spinR xa nm (gtAdGd GT)) -∗
      AxAnnot.annotOwn (hB, 2) iprop(locked nm.2 ya hB (hB, 1) ∗ spinR xa nm (gtAdGd GT) (hB, 1)) -∗
      AxAnnot.annotOwn (hB, 2) iprop(⌜vx = b1 ∨ (gtAdGd GT).gdG.gxImg xa = some vx⌝) -∗
      ∀ rs : RegFile, @tierAWpd GF hlc _ _ (splPol GT) (gtAdGd GT) spinN Unit (spinOb ya xa) nm
        ⟨hp cpu AxSpinProt3.bRel rs, 4⟩ .MaybeStuck hB
        (fun _ => iprop(⌜vx = b1 ∨ (gtAdGd GT).gdG.gxImg xa = some vx⌝)) := by
  have Hne : 4 ≠ (AxOpsem.grow (gtAdGd GT) hB).length := by rw [Hrow]; simp [AxSpinProt3.bRow]
  have Hl1 := AxSpinProt3.bL GT t1 t2 tx vx Hrow 1 _ rfl
  have Hl2 := AxSpinProt3.bL GT t1 t2 tx vx Hrow 2 _ rfl
  have Hl3 := AxSpinProt3.bL GT t1 t2 tx vx Hrow 3 _ rfl
  have Hl4 := AxSpinProt3.bL GT t1 t2 tx vx Hrow 4 _ rfl
  have H := shPos (hlc := hlc) (pol := splPol GT) (gtAdGd GT) spinN Unit (spinOb ya xa) nm cpu hB
    (fun _ => iprop(⌜vx = b1 ∨ (gtAdGd GT).gdG.gxImg xa = some vx⌝))
    iprop(isLock (GF := GF) nm.2 ya (spinR xa nm (gtAdGd GT)) ∗
      AxAnnot.annotOwn (hB, 2) iprop(locked nm.2 ya hB (hB, 1) ∗ spinR xa nm (gtAdGd GT) (hB, 1)) ∗
      AxAnnot.annotOwn (hB, 2) iprop(⌜vx = b1 ∨ (gtAdGd GT).gdG.gxImg xa = some vx⌝))
    4 AxSpinProt3.bRel Hne
    (fun rs id K => noReadAtWrite cpu _ ypaM ypaMRam b0 hlt rs 4 id K)
    (fun rs l s' Hst => by
      obtain ⟨rfl, Hs', -⟩ := writeInv2 cpu _ ypaM ypaMRam b0 hlt rs 4 l s' Hst
      simp only [wlWdata]
      subst Hs'
      obtain ⟨Hzw, Hsg⟩ := gwbStore _ _ _ _ _ Hl4
      have Hval : graphData (gtAdGd GT) (hB, 4) = some (WeakInterpProj.wbytes 1 b0) := by
        unfold graphData; rw [Hl4]; simp [lblData, l3pWbytes1]
      have Hin : ((hB, 2) : Geid) ∈ @Axpol.lobp (splPol GT) (gtAdGd GT) (hB, 4) :=
        lobpIntro (gtAdGd GT) _ _ _ Hl2 rfl (gpoRow (gtAdGd GT) hB 2 4 _ _ Hl2 Hl4 (by decide))
          (gobGmo (gtAdGd GT) Hcons _ _ (fenceGob (gtAdGd GT) hB 2 3 4 _ _ _ _ Hl2 rfl Hl3 Hl4
            (by decide) (by decide)))
      have Hob : gobCat (gtAdGd GT) (hB, 1) (hB, 4) :=
        acqGob (gtAdGd GT) hB 1 4 _ _ _ _ _ _ Hl1 Hl4 rfl (by decide)
      iintro ⟨#Hil, Hp, Hf⟩
      ihave Hfe := (feRelease (hlc := hlc) ya xa GT nm Hcons (hB, 4) hB (hB, 1) (hB, 1)
        (spinR xa nm (gtAdGd GT))
        ({[((hB, 2) : Geid) := iprop(locked nm.2 ya hB (hB, 1) ∗
          spinR (GF := GF) xa nm (gtAdGd GT) (hB, 1))]} : Mea GF)
        Hzw (fun t v => storeNoRead _ _ _ _ _ _ _ _ Hl4)
        (fun v' H => xaNeYa (Hsg xa v' H).1) Hob (RxTransportable nm.1 xa (gtAdGd GT) Hcons))
        $$ Hil
      have Hsing : ⊢ ([∗map] Rin ∈ ({[((hB, 2) : Geid) := iprop(locked nm.2 ya hB (hB, 1) ∗
          spinR (GF := GF) xa nm (gtAdGd GT) (hB, 1))]} : Mea GF), Rin) -∗
          iprop(locked nm.2 ya hB (hB, 1) ∗ spinR (GF := GF) xa nm (gtAdGd GT) (hB, 1)) := by
        iintro H
        ihave H := (BigSepM.bigSepM_singleton (M := GMapF Geid)).1 $$ H
        iexact H
      ihave Hw := Hsing
      ihave Hfe := Hfe $$ Hw
      iapply (evDraw (hlc := hlc) (pol := splPol GT) (gtAdGd GT) spinN Unit (spinOb ya xa) nm
        (splAxpolWf GT) hB 4 (hB, 2) _ _ _ _ _ Hval Hin) $$ Hp Hfe
      iintro _ _
      iapply (AxSpinProt3.wB5 (hlc := hlc) GT nm cpu vx) $$ Hf %rs)
  iintro #Hil Hp Hf
  iapply H
  isplitl []
  · iexact Hil
  isplitl [Hp]
  · iexact Hp
  · iexact Hf

theorem AxSpinProt3.wB3 (GT : GdexecT) (nm : spinN) (cpu : CPU)
    (Hcons : rvwmoCatConsistent (gtAdGd GT)) (t1 t2 tx : Nat) (vx : BitVec 8)
    (Hrow : AxOpsem.grow (gtAdGd GT) hB = AxSpinProt3.bRow t1 t2 tx vx) :
    ⊢ isLock (GF := GF) nm.2 ya (spinR xa nm (gtAdGd GT)) -∗
      AxAnnot.annotOwn (hB, 2) iprop(locked nm.2 ya hB (hB, 1) ∗ spinR xa nm (gtAdGd GT) (hB, 1)) -∗
      AxAnnot.annotOwn (hB, 2) iprop(⌜vx = b1 ∨ (gtAdGd GT).gdG.gxImg xa = some vx⌝) -∗
      ∀ rs : RegFile, @tierAWpd GF hlc _ _ (splPol GT) (gtAdGd GT) spinN Unit (spinOb ya xa) nm
        ⟨hp cpu bFence rs, 3⟩ .MaybeStuck hB (fun _ => iprop(⌜vx = b1 ∨ (gtAdGd GT).gdG.gxImg xa = some vx⌝)) := by
  have Hne : 3 ≠ (AxOpsem.grow (gtAdGd GT) hB).length := by rw [Hrow]; simp [AxSpinProt3.bRow]
  have H := shPos (hlc := hlc) (pol := splPol GT) (gtAdGd GT) spinN Unit (spinOb ya xa) nm cpu hB
    (fun _ => iprop(⌜vx = b1 ∨ (gtAdGd GT).gdG.gxImg xa = some vx⌝))
    iprop(isLock (GF := GF) nm.2 ya (spinR xa nm (gtAdGd GT)) ∗
      AxAnnot.annotOwn (hB, 2) iprop(locked nm.2 ya hB (hB, 1) ∗ spinR xa nm (gtAdGd GT) (hB, 1)) ∗
      AxAnnot.annotOwn (hB, 2) iprop(⌜vx = b1 ∨ (gtAdGd GT).gdG.gxImg xa = some vx⌝))
    3 bFence Hne
    (fun rs id K => noReadAtFence cpu _ AxSpinProt3.bRel rs 3 id K)
    (fun rs l s' Hst => by
      obtain ⟨rfl, Hs', -⟩ := fenceInv2 cpu _ AxSpinProt3.bRel rs 3 l s' Hst
      simp only [wlWdata]
      subst Hs'
      iintro ⟨#Hil, Hp, Hf⟩
      iapply (shSkip2 (GF := GF) (gtAdGd GT) spinN Unit (spinOb ya xa) nm hB _ _)
      inext
      iapply (AxSpinProt3.wB4 (hlc := hlc) GT nm cpu Hcons t1 t2 tx vx Hrow) $$ Hil Hp Hf %rs)
  iintro #Hil Hp Hf
  iapply H
  isplitl []
  · iexact Hil
  isplitl [Hp]
  · iexact Hp
  · iexact Hf

theorem AxSpinProt3.wB2 (GT : GdexecT) (nm : spinN) (cpu : CPU)
    (Hcons : rvwmoCatConsistent (gtAdGd GT)) (t1 t2 tx : Nat) (vx : BitVec 8)
    (Hrow : AxOpsem.grow (gtAdGd GT) hB = AxSpinProt3.bRow t1 t2 tx vx) :
    ⊢ isLock (GF := GF) nm.2 ya (spinR xa nm (gtAdGd GT)) -∗
      AxAnnot.annotOwn (hB, 1) iprop(locked nm.2 ya hB (hB, 1) ∗ spinR xa nm (gtAdGd GT) (hB, 1)) -∗
      ∀ rs : RegFile, @tierAWpd GF hlc _ _ (splPol GT) (gtAdGd GT) spinN Unit (spinOb ya xa) nm
        ⟨hp cpu bLd rs, 2⟩ .MaybeStuck hB (fun _ => iprop(⌜vx = b1 ∨ (gtAdGd GT).gdG.gxImg xa = some vx⌝)) := by
  have Hne : 2 ≠ (AxOpsem.grow (gtAdGd GT) hB).length := by rw [Hrow]; simp [AxSpinProt3.bRow]
  have Hadv : ∀ lb, (AxOpsem.grow (gtAdGd GT) hB)[2]? = some lb → aidentAdvRd (aident lb) = 1 := by
    rw [Hrow]
    intro lb h
    cases h
    rfl
  have Hl1 := AxSpinProt3.bL GT t1 t2 tx vx Hrow 1 _ rfl
  have Hl2 := AxSpinProt3.bL GT t1 t2 tx vx Hrow 2 _ rfl
  have H := shRead (hlc := hlc) (pol := splPol GT) (gtAdGd GT) spinN Unit (spinOb ya xa) nm cpu hB
    (fun _ => iprop(⌜vx = b1 ∨ (gtAdGd GT).gdG.gxImg xa = some vx⌝)) xpaM xpaMRam (fun _ => bFence) 2 Hne Hadv
    iprop(isLock (GF := GF) nm.2 ya (spinR xa nm (gtAdGd GT)) ∗ AxAnnot.annotOwn (hB, 1) iprop(locked nm.2 ya hB (hB, 1) ∗ spinR xa nm (gtAdGd GT) (hB, 1)))
    (fun v b rs Hgv Hv => by
      subst Hv
      have Hb : b = vx := by
        have h : graphValue (gtAdGd GT) (hB, 2) = some [vx] := by
          unfold graphValue; rw [Hl2]; rfl
        rw [h] at Hgv
        exact ((List.cons.inj (Option.some.inj Hgv)).1).symm
      subst Hb
      have Hnw : gisW (gtAdGd GT).gdG (hB, 2) = false := by unfold gisW; rw [Hl2]; rfl
      have Hnr : ¬ lkread ya (gtAdGd GT).gdG (hB, 2) := by
        rintro ⟨⟨t, v, Hr⟩, -⟩
        exact xaNeYa (grbLoadOnly _ _ _ _ _ Hl2 _ _ _ Hr).1.symm
      have Hrd := grbLoad _ _ _ _ _ Hl2
      have Hlt : gmoLt (gtAdGd GT).gdG (hB, 1) (hB, 2) :=
        gobGmo (gtAdGd GT) Hcons _ _ (acqGob (gtAdGd GT) hB 1 2 _ _ _ _ _ _ Hl1 Hl2 rfl (by decide))
      have Hin : ((hB, 1) : Geid) ∈ @Axpol.lobp (splPol GT) (gtAdGd GT) (hB, 2) :=
        lobpIntro (gtAdGd GT) _ _ _ Hl1 rfl (gpoRow (gtAdGd GT) hB 1 2 _ _ Hl1 Hl2 (by decide)) Hlt
      have Hsing : ⊢ ([∗map] Rin ∈ ({[((hB, 1) : Geid) := iprop(locked nm.2 ya hB (hB, 1) ∗
          spinR (GF := GF) xa nm (gtAdGd GT) (hB, 1))]} : Mea GF), Rin) -∗
          iprop(locked nm.2 ya hB (hB, 1) ∗ Rx (GF := GF) nm.1 xa (gtAdGd GT) (hB, 1)) := by
        iintro H
        ihave H := (BigSepM.bigSepM_singleton (M := GMapF Geid)).1 $$ H
        iunfold spinR at H
        iexact H
      have Hbr : AxAnnot.annotOwn (GF := GF) (hB, 2)
          iprop(locked nm.2 ya hB (hB, 1) ∗ Rx (GF := GF) nm.1 xa (gtAdGd GT) (hB, 1)) ⊢
          AxAnnot.annotOwn (hB, 2) iprop(locked nm.2 ya hB (hB, 1) ∗ spinR xa nm (gtAdGd GT) (hB, 1)) := .rfl
      iintro ⟨#Hil, Hp⟩
      ihave Hw := Hsing
      ihave Hfe := (feXread (hlc := hlc) ya xa GT nm Hcons (hB, 2) (hB, 1) tx b
        iprop(locked nm.2 ya hB (hB, 1))
        ({[((hB, 1) : Geid) := iprop(locked nm.2 ya hB (hB, 1) ∗
          spinR (GF := GF) xa nm (gtAdGd GT) (hB, 1))]} : Mea GF)
        Hnw Hnr (bNoX GT t1 t2 tx b Hrow) Hrd Hlt) $$ Hw
      iapply (evDraw (hlc := hlc) (pol := splPol GT) (gtAdGd GT) spinN Unit (spinOb ya xa) nm (splAxpolWf GT) hB 2 (hB, 1) _ _ _ _ _ Hgv Hin) $$ Hp Hfe
      iintro Hp Hf
      ihave Hp := Hbr $$ Hp
      iapply (AxSpinProt3.wB3 (hlc := hlc) GT nm cpu Hcons t1 t2 tx b Hrow) $$ Hil Hp Hf %rs)
  iintro #Hil Hp
  iapply H
  isplitl []
  · iexact Hil
  · iexact Hp

theorem AxSpinProt3.wB1w (GT : GdexecT) (nm : spinN) (cpu : CPU)
    (Hcons : rvwmoCatConsistent (gtAdGd GT)) (t1 t2 tx : Nat) (vx : BitVec 8)
    (Hrow : AxOpsem.grow (gtAdGd GT) hB = AxSpinProt3.bRow t1 t2 tx vx) :
    ⊢ isLock (GF := GF) nm.2 ya (spinR xa nm (gtAdGd GT)) -∗ notheld nm.2 ya hB -∗
      ∀ rs : RegFile, @tierAWpd GF hlc _ _ (splPol GT) (gtAdGd GT) spinN Unit (spinOb ya xa) nm
        ⟨hp cpu (bW b0 hlt) rs, 1⟩ .MaybeStuck hB (fun _ => iprop(⌜vx = b1 ∨ (gtAdGd GT).gdG.gxImg xa = some vx⌝)) := by
  have Hne : 1 ≠ (AxOpsem.grow (gtAdGd GT) hB).length := by rw [Hrow]; simp [AxSpinProt3.bRow]
  have Hl1 := AxSpinProt3.bL GT t1 t2 tx vx Hrow 1 _ rfl
  obtain ⟨Hrd, Hw, Hsg, -⟩ := gwbRmw _ _ _ _ _ _ _ Hl1
  have Hval : graphData (gtAdGd GT) (hB, 1) = some (WeakInterpProj.wbytes 1 b1) := by
    unfold graphData; rw [Hl1]; simp [lblData, l3pWbytes1]
  have H := shRmwWrite (hlc := hlc) (pol := splPol GT) (gtAdGd GT) spinN Unit (spinOb ya xa) nm cpu hB
    (fun _ => iprop(⌜vx = b1 ∨ (gtAdGd GT).gdG.gxImg xa = some vx⌝)) ypaM ypaMRam (if b0 = b0 then bLd else hlt) 1 Hne
    iprop(isLock (GF := GF) nm.2 ya (spinR xa nm (gtAdGd GT)) ∗ notheld nm.2 ya hB)
    (fun rs => by
      iintro ⟨#Hil, Hnh⟩
      ihave Hfe := (feClaim (hlc := hlc) ya xa GT nm Hcons (hB, 1)
        (gwriteAt (gtAdGd GT).gdG t2) (spinR xa nm (gtAdGd GT)) ⟨t2, Hrd, rfl, Hw⟩
        (RxTransportable nm.1 xa (gtAdGd GT) Hcons) (fun v' H => xaNeYa (Hsg xa v' H).1))
        $$ Hnh Hil
      iapply (evPlain (hlc := hlc) (pol := splPol GT) (gtAdGd GT) spinN Unit (spinOb ya xa) nm hB 1 iprop(locked nm.2 ya hB (hB, 1) ∗ spinR xa nm (gtAdGd GT) (hB, 1)) iprop(True) _ _ Hval) $$ [Hfe]
      · iapply (@flowEqDynMono hlc GF _ (shG (gtAdGd GT) spinN Unit (spinOb ya xa) nm) (splPol GT)
          (gtAdGd GT) (hB, 1) _ (∅ : Mea GF) iprop(locked nm.2 ya hB (hB, 1) ∗ spinR xa nm (gtAdGd GT) (hB, 1))
          iprop((locked nm.2 ya hB (hB, 1) ∗ spinR xa nm (gtAdGd GT) (hB, 1)) ∗ True)) $$ [] Hfe
        inext
        iintro H
        isplitl [H]
        · iexact H
        · itrivial
      iintro Hp _
      rw [if_pos rfl]
      iapply (AxSpinProt3.wB2 (hlc := hlc) GT nm cpu Hcons t1 t2 tx vx Hrow) $$ Hil Hp %rs)
  iintro #Hil Hnh
  iapply H
  isplitl []
  · iexact Hil
  · iexact Hnh

theorem AxSpinProt3.wB1r (GT : GdexecT) (nm : spinN) (cpu : CPU)
    (Hcons : rvwmoCatConsistent (gtAdGd GT)) (t1 t2 tx : Nat) (vx : BitVec 8)
    (Hrow : AxOpsem.grow (gtAdGd GT) hB = AxSpinProt3.bRow t1 t2 tx vx) :
    ⊢ isLock (GF := GF) nm.2 ya (spinR xa nm (gtAdGd GT)) -∗ notheld nm.2 ya hB -∗
      ∀ rs : RegFile, @tierAWpd GF hlc _ _ (splPol GT) (gtAdGd GT) spinN Unit (spinOb ya xa) nm
        ⟨hp cpu (bRmw hlt) rs, 1⟩ .MaybeStuck hB (fun _ => iprop(⌜vx = b1 ∨ (gtAdGd GT).gdG.gxImg xa = some vx⌝)) := by
  have Hne : 1 ≠ (AxOpsem.grow (gtAdGd GT) hB).length := by rw [Hrow]; simp [AxSpinProt3.bRow]
  have Hl1 : (AxOpsem.grow (gtAdGd GT) hB)[1]? =
      some (.LRmw true false (paZ ypaM) [t2] [b0] [b1] .WCplain) := by rw [Hrow]; rfl
  have H := shRmwRead (hlc := hlc) (pol := splPol GT) (gtAdGd GT) spinN Unit (spinOb ya xa) nm cpu hB
    (fun _ => iprop(⌜vx = b1 ∨ (gtAdGd GT).gdG.gxImg xa = some vx⌝)) ypaM ypaMRam (bK hlt) 1 t2 b0 .WCplain Hne Hl1
    iprop(isLock (GF := GF) nm.2 ya (spinR xa nm (gtAdGd GT)) ∗ notheld nm.2 ya hB)
    (fun rs => by
      iintro ⟨#Hil, Hnh⟩
      rw [AxSpinProt3.bKOk]
      iapply (AxSpinProt3.wB1w (hlc := hlc) GT nm cpu Hcons t1 t2 tx vx Hrow) $$ Hil Hnh %rs)
  iintro #Hil Hnh
  iapply H
  isplitl []
  · iexact Hil
  · iexact Hnh

theorem AxSpinProt3.wB0w (GT : GdexecT) (nm : spinN) (cpu : CPU)
    (Hcons : rvwmoCatConsistent (gtAdGd GT)) (t1 t2 tx : Nat) (vx : BitVec 8)
    (Hrow : AxOpsem.grow (gtAdGd GT) hB = AxSpinProt3.bRow t1 t2 tx vx) :
    ⊢ isLock (GF := GF) nm.2 ya (spinR xa nm (gtAdGd GT)) -∗ notheld nm.2 ya hB -∗
      ∀ rs : RegFile, @tierAWpd GF hlc _ _ (splPol GT) (gtAdGd GT) spinN Unit (spinOb ya xa) nm
        ⟨hp cpu (bW b1 (bRmw hlt)) rs, 0⟩ .MaybeStuck hB (fun _ => iprop(⌜vx = b1 ∨ (gtAdGd GT).gdG.gxImg xa = some vx⌝)) := by
  have Hne : 0 ≠ (AxOpsem.grow (gtAdGd GT) hB).length := by rw [Hrow]; simp [AxSpinProt3.bRow]
  have Hl0 := AxSpinProt3.bL GT t1 t2 tx vx Hrow 0 _ rfl
  obtain ⟨Hrd, Hw, Hsg, -⟩ := gwbRmw _ _ _ _ _ _ _ Hl0
  have Hval : graphData (gtAdGd GT) (hB, 0) = some (WeakInterpProj.wbytes 1 b1) := by
    unfold graphData; rw [Hl0]; simp [lblData, l3pWbytes1]
  have H := shRmwWrite (hlc := hlc) (pol := splPol GT) (gtAdGd GT) spinN Unit (spinOb ya xa) nm cpu hB
    (fun _ => iprop(⌜vx = b1 ∨ (gtAdGd GT).gdG.gxImg xa = some vx⌝)) ypaM ypaMRam (if b1 = b0 then bLd else bRmw hlt) 0 Hne
    iprop(isLock (GF := GF) nm.2 ya (spinR xa nm (gtAdGd GT)) ∗ notheld nm.2 ya hB)
    (fun rs => by
      iintro ⟨#Hil, Hnh⟩
      ihave Hfe := AxSpinProt2.feNeutral (hlc := hlc) (GF := GF) ya xa GT nm (hB, 0) t1 b1 Hrd
        (Ne.symm b0NeB1) Hw (fun v' H => xaNeYa (Hsg xa v' H).1)
      iapply (evPlain (hlc := hlc) (pol := splPol GT) (gtAdGd GT) spinN Unit (spinOb ya xa) nm hB 0 iprop(True) iprop(True) _ _ Hval) $$ [Hfe]
      · iapply (@flowEqDynMono hlc GF _ (shG (gtAdGd GT) spinN Unit (spinOb ya xa) nm) (splPol GT)
          (gtAdGd GT) (hB, 0) _ (∅ : Mea GF) iprop(True) iprop(True ∗ True)) $$ [] Hfe
        inext
        iintro _
        isplitl []
        · itrivial
        · itrivial
      iintro _ _
      rw [if_neg (Ne.symm b0NeB1)]
      iapply (AxSpinProt3.wB1r (hlc := hlc) GT nm cpu Hcons t1 t2 tx vx Hrow) $$ Hil Hnh %rs)
  iintro #Hil Hnh
  iapply H
  isplitl []
  · iexact Hil
  · iexact Hnh

theorem AxSpinProt3.wpdB (GT : GdexecT) (nm : spinN) (cpu : CPU)
    (Hcons : rvwmoCatConsistent (gtAdGd GT)) (t1 t2 tx : Nat) (vx : BitVec 8)
    (Hrow : AxOpsem.grow (gtAdGd GT) hB = AxSpinProt3.bRow t1 t2 tx vx) :
    ⊢ isLock (GF := GF) nm.2 ya (spinR xa nm (gtAdGd GT)) -∗ notheld nm.2 ya hB -∗
      @tierAWpd GF hlc _ _ (splPol GT) (gtAdGd GT) spinN Unit (spinOb ya xa) nm
        ⟨hp cpu AxSpinProt3.bM0 zeroRegs, 0⟩ .MaybeStuck hB (fun _ => iprop(⌜vx = b1 ∨ (gtAdGd GT).gdG.gxImg xa = some vx⌝)) := by
  have Hne : 0 ≠ (AxOpsem.grow (gtAdGd GT) hB).length := by rw [Hrow]; simp [AxSpinProt3.bRow]
  have Hl0 : (AxOpsem.grow (gtAdGd GT) hB)[0]? =
      some (.LRmw true false (paZ ypaM) [t1] [b1] [b1] .WCplain) := by rw [Hrow]; rfl
  have H := shRmwRead (hlc := hlc) (pol := splPol GT) (gtAdGd GT) spinN Unit (spinOb ya xa) nm cpu hB
    (fun _ => iprop(⌜vx = b1 ∨ (gtAdGd GT).gdG.gxImg xa = some vx⌝)) ypaM ypaMRam (bK (bRmw hlt)) 0 t1 b1 .WCplain Hne Hl0
    iprop(isLock (GF := GF) nm.2 ya (spinR xa nm (gtAdGd GT)) ∗ notheld nm.2 ya hB)
    (fun rs => by
      iintro ⟨#Hil, Hnh⟩
      rw [AxSpinProt3.bKOk]
      iapply (AxSpinProt3.wB0w (hlc := hlc) GT nm cpu Hcons t1 t2 tx vx Hrow) $$ Hil Hnh %rs)
  iintro #Hil Hnh
  iapply H $$ [$Hil $Hnh] %zeroRegs

end wpdB

/-! # 6. HART A's WPd at the real protocol (the positive writer): claims genesis (or any
release), writes `x := 1` under the lock, releases. -/

section wpdA
variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF] [AxannotGS GF]
  [AxlogG GF Hent] [SpinlockG GF]

theorem AxSpinProt3.aL (GT : GdexecT) (tA : Nat)
    (Hrow : AxOpsem.grow (gtAdGd GT) hA = AxSpinProt3.aRow tA) (k : Nat) (lb : Lbl) :
    (AxSpinProt3.aRow tA)[k]? = some lb → gxLbl (gtAdGd GT).gdG (hA, k) = some lb := by
  intro Hk
  rw [gxLblGrow, Hrow]
  exact Hk

theorem AxSpinProt3.wA3 (GT : GdexecT) (nm : spinN) (cpu : CPU)
    (Hcons : rvwmoCatConsistent (gtAdGd GT)) (tA : Nat)
    (Hrow : AxOpsem.grow (gtAdGd GT) hA = AxSpinProt3.aRow tA) :
    ⊢ isLock (GF := GF) nm.2 ya (spinR xa nm (gtAdGd GT)) -∗
      AxAnnot.annotOwn (hA, 1) iprop(locked nm.2 ya hA (hA, 0) ∗ spinR xa nm (gtAdGd GT) (hA, 1)) -∗
      ∀ rs : RegFile, @tierAWpd GF hlc _ _ (splPol GT) (gtAdGd GT) spinN Unit (spinOb ya xa) nm
        ⟨hp cpu AxSpinProt3.bRel rs, 3⟩ .MaybeStuck hA (fun _ => iprop(True)) := by
  have Hne : 3 ≠ (AxOpsem.grow (gtAdGd GT) hA).length := by rw [Hrow]; simp [AxSpinProt3.aRow]
  have Hl1 := AxSpinProt3.aL GT tA Hrow 1 _ rfl
  have Hl2 := AxSpinProt3.aL GT tA Hrow 2 _ rfl
  have Hl3 := AxSpinProt3.aL GT tA Hrow 3 _ rfl
  have H := shPos (hlc := hlc) (pol := splPol GT) (gtAdGd GT) spinN Unit (spinOb ya xa) nm cpu hA (fun _ => iprop(True))
    iprop(isLock (GF := GF) nm.2 ya (spinR xa nm (gtAdGd GT)) ∗ AxAnnot.annotOwn (hA, 1) iprop(locked nm.2 ya hA (hA, 0) ∗ spinR xa nm (gtAdGd GT) (hA, 1)))
    3 AxSpinProt3.bRel Hne
    (fun rs id K => noReadAtWrite cpu _ ypaM ypaMRam b0 hlt rs 3 id K)
    (fun rs l s' Hst => by
      obtain ⟨rfl, Hs', -⟩ := writeInv2 cpu _ ypaM ypaMRam b0 hlt rs 3 l s' Hst
      simp only [wlWdata]
      subst Hs'
      obtain ⟨Hzw, Hsg⟩ := gwbStore _ _ _ _ _ Hl3
      have Hval : graphData (gtAdGd GT) (hA, 3) = some (WeakInterpProj.wbytes 1 b0) := by
        unfold graphData; rw [Hl3]; simp [lblData, l3pWbytes1]
      have Hob : gobCat (gtAdGd GT) (hA, 1) (hA, 3) :=
        fenceGob (gtAdGd GT) hA 1 2 3 _ _ _ _ Hl1 rfl Hl2 Hl3 (by decide) (by decide)
      have Hin : ((hA, 1) : Geid) ∈ @Axpol.lobp (splPol GT) (gtAdGd GT) (hA, 3) :=
        lobpIntro (gtAdGd GT) _ _ _ Hl1 rfl (gpoRow (gtAdGd GT) hA 1 3 _ _ Hl1 Hl3 (by decide))
          (gobGmo (gtAdGd GT) Hcons _ _ Hob)
      iintro ⟨#Hil, Hp⟩
      ihave Hfe := (feRelease (hlc := hlc) ya xa GT nm Hcons (hA, 3) hA (hA, 0) (hA, 1)
        (spinR xa nm (gtAdGd GT))
        ({[((hA, 1) : Geid) := iprop(locked nm.2 ya hA (hA, 0) ∗
          spinR (GF := GF) xa nm (gtAdGd GT) (hA, 1))]} : Mea GF)
        Hzw (fun t v => storeNoRead _ _ _ _ _ _ _ _ Hl3)
        (fun v' H => xaNeYa (Hsg xa v' H).1) Hob (RxTransportable nm.1 xa (gtAdGd GT) Hcons))
        $$ Hil
      have Hsing : ⊢ ([∗map] Rin ∈ ({[((hA, 1) : Geid) := iprop(locked nm.2 ya hA (hA, 0) ∗
          spinR (GF := GF) xa nm (gtAdGd GT) (hA, 1))]} : Mea GF), Rin) -∗
          iprop(locked nm.2 ya hA (hA, 0) ∗ spinR (GF := GF) xa nm (gtAdGd GT) (hA, 1)) := by
        iintro H
        ihave H := (BigSepM.bigSepM_singleton (M := GMapF Geid)).1 $$ H
        iexact H
      ihave Hw := Hsing
      ihave Hfe := Hfe $$ Hw
      iapply (evDraw (hlc := hlc) (pol := splPol GT) (gtAdGd GT) spinN Unit (spinOb ya xa) nm (splAxpolWf GT) hA 3 (hA, 1) _ _ _ _ _ Hval Hin) $$ Hp Hfe
      iintro _ _
      iapply (shHltTrue (hlc := hlc) (pol := splPol GT) (gtAdGd GT) spinN Unit (spinOb ya xa) nm cpu hA (3 + 1)) $$ %rs)
  iintro #Hil Hp
  iapply H
  isplitl []
  · iexact Hil
  · iexact Hp

theorem AxSpinProt3.wA2 (GT : GdexecT) (nm : spinN) (cpu : CPU)
    (Hcons : rvwmoCatConsistent (gtAdGd GT)) (tA : Nat)
    (Hrow : AxOpsem.grow (gtAdGd GT) hA = AxSpinProt3.aRow tA) :
    ⊢ isLock (GF := GF) nm.2 ya (spinR xa nm (gtAdGd GT)) -∗
      AxAnnot.annotOwn (hA, 1) iprop(locked nm.2 ya hA (hA, 0) ∗ spinR xa nm (gtAdGd GT) (hA, 1)) -∗
      ∀ rs : RegFile, @tierAWpd GF hlc _ _ (splPol GT) (gtAdGd GT) spinN Unit (spinOb ya xa) nm
        ⟨hp cpu aFence rs, 2⟩ .MaybeStuck hA (fun _ => iprop(True)) := by
  have Hne : 2 ≠ (AxOpsem.grow (gtAdGd GT) hA).length := by rw [Hrow]; simp [AxSpinProt3.aRow]
  have H := shPos (hlc := hlc) (pol := splPol GT) (gtAdGd GT) spinN Unit (spinOb ya xa) nm cpu hA (fun _ => iprop(True))
    iprop(isLock (GF := GF) nm.2 ya (spinR xa nm (gtAdGd GT)) ∗ AxAnnot.annotOwn (hA, 1) iprop(locked nm.2 ya hA (hA, 0) ∗ spinR xa nm (gtAdGd GT) (hA, 1)))
    2 aFence Hne
    (fun rs id K => noReadAtFence cpu _ AxSpinProt3.bRel rs 2 id K)
    (fun rs l s' Hst => by
      obtain ⟨rfl, Hs', -⟩ := fenceInv2 cpu _ AxSpinProt3.bRel rs 2 l s' Hst
      simp only [wlWdata]
      subst Hs'
      iintro ⟨#Hil, Hp⟩
      iapply (shSkip2 (GF := GF) (gtAdGd GT) spinN Unit (spinOb ya xa) nm hA _ _)
      inext
      iapply (AxSpinProt3.wA3 (hlc := hlc) GT nm cpu Hcons tA Hrow) $$ Hil Hp %rs)
  iintro #Hil Hp
  iapply H
  isplitl []
  · iexact Hil
  · iexact Hp

theorem AxSpinProt3.wA1 (GT : GdexecT) (nm : spinN) (cpu : CPU)
    (Hcons : rvwmoCatConsistent (gtAdGd GT)) (tA : Nat)
    (Hrow : AxOpsem.grow (gtAdGd GT) hA = AxSpinProt3.aRow tA) :
    ⊢ isLock (GF := GF) nm.2 ya (spinR xa nm (gtAdGd GT)) -∗
      AxAnnot.annotOwn (hA, 0) iprop(locked nm.2 ya hA (hA, 0) ∗ spinR xa nm (gtAdGd GT) (hA, 0)) -∗
      ∀ rs : RegFile, @tierAWpd GF hlc _ _ (splPol GT) (gtAdGd GT) spinN Unit (spinOb ya xa) nm
        ⟨hp cpu aSt rs, 1⟩ .MaybeStuck hA (fun _ => iprop(True)) := by
  have Hne : 1 ≠ (AxOpsem.grow (gtAdGd GT) hA).length := by rw [Hrow]; simp [AxSpinProt3.aRow]
  have Hl0 := AxSpinProt3.aL GT tA Hrow 0 _ rfl
  have Hl1 := AxSpinProt3.aL GT tA Hrow 1 _ rfl
  have H := shPos (hlc := hlc) (pol := splPol GT) (gtAdGd GT) spinN Unit (spinOb ya xa) nm cpu hA (fun _ => iprop(True))
    iprop(isLock (GF := GF) nm.2 ya (spinR xa nm (gtAdGd GT)) ∗ AxAnnot.annotOwn (hA, 0) iprop(locked nm.2 ya hA (hA, 0) ∗ spinR xa nm (gtAdGd GT) (hA, 0)))
    1 aSt Hne
    (fun rs id K => noReadAtWrite cpu _ xpaM xpaMRam b1 aFence rs 1 id K)
    (fun rs l s' Hst => by
      obtain ⟨rfl, Hs', -⟩ := writeInv2 cpu _ xpaM xpaMRam b1 aFence rs 1 l s' Hst
      simp only [wlWdata]
      subst Hs'
      obtain ⟨Hwx, Hsg⟩ := gwbStore _ _ _ _ _ Hl1
      have Hval : graphData (gtAdGd GT) (hA, 1) = some (WeakInterpProj.wbytes 1 b1) := by
        unfold graphData; rw [Hl1]; simp [lblData, l3pWbytes1]
      have Hlt : gmoLt (gtAdGd GT).gdG (hA, 0) (hA, 1) :=
        gobGmo (gtAdGd GT) Hcons _ _ (acqGob (gtAdGd GT) hA 0 1 _ _ _ _ _ _ Hl0 Hl1 rfl (by decide))
      have Hin : ((hA, 0) : Geid) ∈ @Axpol.lobp (splPol GT) (gtAdGd GT) (hA, 1) :=
        lobpIntro (gtAdGd GT) _ _ _ Hl0 rfl (gpoRow (gtAdGd GT) hA 0 1 _ _ Hl0 Hl1 (by decide)) Hlt
      have Hsing : ⊢ ([∗map] Rin ∈ ({[((hA, 0) : Geid) := iprop(locked nm.2 ya hA (hA, 0) ∗
          spinR (GF := GF) xa nm (gtAdGd GT) (hA, 0))]} : Mea GF), Rin) -∗
          iprop(locked nm.2 ya hA (hA, 0) ∗ Rx (GF := GF) nm.1 xa (gtAdGd GT) (hA, 0)) := by
        iintro H
        ihave H := (BigSepM.bigSepM_singleton (M := GMapF Geid)).1 $$ H
        iunfold spinR at H
        iexact H
      have Hbr : AxAnnot.annotOwn (GF := GF) (hA, 1)
          iprop(locked nm.2 ya hA (hA, 0) ∗ Rx (GF := GF) nm.1 xa (gtAdGd GT) (hA, 1)) ⊢
          AxAnnot.annotOwn (hA, 1) iprop(locked nm.2 ya hA (hA, 0) ∗ spinR xa nm (gtAdGd GT) (hA, 1)) := .rfl
      iintro ⟨#Hil, Hp⟩
      ihave Hw := Hsing
      ihave Hfe := (feXwrite (hlc := hlc) ya xa xaNeYa GT nm (hA, 1) (hA, 0) iprop(locked nm.2 ya hA (hA, 0))
        ({[((hA, 0) : Geid) := iprop(locked nm.2 ya hA (hA, 0) ∗
          spinR (GF := GF) xa nm (gtAdGd GT) (hA, 0))]} : Mea GF)
        Hlt Hwx (fun a' v' H => (Hsg a' v' H).1)) $$ Hw
      iapply (evDraw (hlc := hlc) (pol := splPol GT) (gtAdGd GT) spinN Unit (spinOb ya xa) nm (splAxpolWf GT) hA 1 (hA, 0) _
        iprop(locked nm.2 ya hA (hA, 0) ∗ Rx (GF := GF) nm.1 xa (gtAdGd GT) (hA, 1)) iprop(True) _ _ Hval Hin)
        $$ Hp [Hfe]
      · iapply (@flowEqDynMono hlc GF _ (shG (gtAdGd GT) spinN Unit (spinOb ya xa) nm) (splPol GT)
          (gtAdGd GT) (hA, 1) _ _ iprop(locked nm.2 ya hA (hA, 0) ∗ Rx (GF := GF) nm.1 xa (gtAdGd GT) (hA, 1))
          iprop((locked nm.2 ya hA (hA, 0) ∗ Rx (GF := GF) nm.1 xa (gtAdGd GT) (hA, 1)) ∗ True)) $$ [] Hfe
        inext
        iintro H
        isplitl [H]
        · iexact H
        · itrivial
      iintro Hp _
      ihave Hp := Hbr $$ Hp
      iapply (AxSpinProt3.wA2 (hlc := hlc) GT nm cpu Hcons tA Hrow) $$ Hil Hp %rs)
  iintro #Hil Hp
  iapply H
  isplitl []
  · iexact Hil
  · iexact Hp

theorem AxSpinProt3.wA0w (GT : GdexecT) (nm : spinN) (cpu : CPU)
    (Hcons : rvwmoCatConsistent (gtAdGd GT)) (tA : Nat)
    (Hrow : AxOpsem.grow (gtAdGd GT) hA = AxSpinProt3.aRow tA) :
    ⊢ isLock (GF := GF) nm.2 ya (spinR xa nm (gtAdGd GT)) -∗ notheld nm.2 ya hA -∗
      ∀ rs : RegFile, @tierAWpd GF hlc _ _ (splPol GT) (gtAdGd GT) spinN Unit (spinOb ya xa) nm
        ⟨hp cpu aW rs, 0⟩ .MaybeStuck hA (fun _ => iprop(True)) := by
  have Hne : 0 ≠ (AxOpsem.grow (gtAdGd GT) hA).length := by rw [Hrow]; simp [AxSpinProt3.aRow]
  have Hl0 := AxSpinProt3.aL GT tA Hrow 0 _ rfl
  obtain ⟨Hrd, Hw, Hsg, -⟩ := gwbRmw _ _ _ _ _ _ _ Hl0
  have Hval : graphData (gtAdGd GT) (hA, 0) = some (WeakInterpProj.wbytes 1 b1) := by
    unfold graphData; rw [Hl0]; simp [lblData, l3pWbytes1]
  have H := shRmwWrite (hlc := hlc) (pol := splPol GT) (gtAdGd GT) spinN Unit (spinOb ya xa) nm cpu hA (fun _ => iprop(True)) ypaM ypaMRam aSt 0 Hne
    iprop(isLock (GF := GF) nm.2 ya (spinR xa nm (gtAdGd GT)) ∗ notheld nm.2 ya hA)
    (fun rs => by
      iintro ⟨#Hil, Hnh⟩
      ihave Hfe := (feClaim (hlc := hlc) ya xa GT nm Hcons (hA, 0)
        (gwriteAt (gtAdGd GT).gdG tA) (spinR xa nm (gtAdGd GT)) ⟨tA, Hrd, rfl, Hw⟩
        (RxTransportable nm.1 xa (gtAdGd GT) Hcons) (fun v' H => xaNeYa (Hsg xa v' H).1))
        $$ Hnh Hil
      iapply (evPlain (hlc := hlc) (pol := splPol GT) (gtAdGd GT) spinN Unit (spinOb ya xa) nm hA 0 iprop(locked nm.2 ya hA (hA, 0) ∗ spinR xa nm (gtAdGd GT) (hA, 0)) iprop(True) _ _ Hval) $$ [Hfe]
      · iapply (@flowEqDynMono hlc GF _ (shG (gtAdGd GT) spinN Unit (spinOb ya xa) nm) (splPol GT)
          (gtAdGd GT) (hA, 0) _ (∅ : Mea GF) iprop(locked nm.2 ya hA (hA, 0) ∗ spinR xa nm (gtAdGd GT) (hA, 0))
          iprop((locked nm.2 ya hA (hA, 0) ∗ spinR xa nm (gtAdGd GT) (hA, 0)) ∗ True)) $$ [] Hfe
        inext
        iintro H
        isplitl [H]
        · iexact H
        · itrivial
      iintro Hp _
      iapply (AxSpinProt3.wA1 (hlc := hlc) GT nm cpu Hcons tA Hrow) $$ Hil Hp %rs)
  iintro #Hil Hnh
  iapply H
  isplitl []
  · iexact Hil
  · iexact Hnh

theorem AxSpinProt3.wpdA (GT : GdexecT) (nm : spinN) (cpu : CPU)
    (Hcons : rvwmoCatConsistent (gtAdGd GT)) (tA : Nat)
    (Hrow : AxOpsem.grow (gtAdGd GT) hA = AxSpinProt3.aRow tA) :
    ⊢ isLock (GF := GF) nm.2 ya (spinR xa nm (gtAdGd GT)) -∗ notheld nm.2 ya hA -∗
      @tierAWpd GF hlc _ _ (splPol GT) (gtAdGd GT) spinN Unit (spinOb ya xa) nm
        ⟨hp cpu AxSpinProt3.aM0 zeroRegs, 0⟩ .MaybeStuck hA (fun _ => iprop(True)) := by
  have Hne : 0 ≠ (AxOpsem.grow (gtAdGd GT) hA).length := by rw [Hrow]; simp [AxSpinProt3.aRow]
  have Hl0 : (AxOpsem.grow (gtAdGd GT) hA)[0]? =
      some (.LRmw true false (paZ ypaM) [tA] [b0] [b1] .WCplain) := by rw [Hrow]; rfl
  have H := shRmwRead (hlc := hlc) (pol := splPol GT) (gtAdGd GT) spinN Unit (spinOb ya xa) nm cpu hA (fun _ => iprop(True)) ypaM ypaMRam (fun _ => aW) 0 tA b0
    .WCplain Hne Hl0 iprop(isLock (GF := GF) nm.2 ya (spinR xa nm (gtAdGd GT)) ∗ notheld nm.2 ya hA)
    (fun rs => by
      iintro ⟨#Hil, Hnh⟩
      iapply (AxSpinProt3.wA0w (hlc := hlc) GT nm cpu Hcons tA Hrow) $$ Hil Hnh %rs)
  iintro #Hil Hnh
  iapply H $$ [$Hil $Hnh] %zeroRegs

end wpdA

/-! # 7. The race program at the TRIVIAL protocol (sanity twin) -/

section wpdR
variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF] [AxannotGS GF]

theorem feTriv (GD : Gdexec) [pol : Axpol] (e : Geid) (s0 : GSet Geid) (fi : Mea GF) :
    ⊢ @flowEqDyn hlc GF _ (shG GD Unit Unit trivOb ()) GD e s0 fi iprop(True ∗ True) := by
  unfold flowEqDyn
  iintro %σ %s %Hsub %Hnin _ _
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  inext
  imod Hclose
  imodintro
  iexists σ
  have Ht : ⊢ @AxirisG.obStInterp GF (shG GD Unit Unit trivOb ()) GD σ (({e} : GSet Geid) ∪ s) := by
    show ⊢ iprop(True)
    itrivial
  isplitr
  · iapply Ht
  · isplitr
    · itrivial
    · itrivial

theorem rL (GT : GdexecT) (Hrow : AxOpsem.grow (gtAdGd GT) hA = AxSpinProt3.rRow) (k : Nat)
    (lb : Lbl) : AxSpinProt3.rRow[k]? = some lb → gxLbl (gtAdGd GT).gdG (hA, k) = some lb := by
  intro Hk
  rw [gxLblGrow, Hrow]
  exact Hk

theorem wRSt (GT : GdexecT) (cpu : CPU) (Hrow : AxOpsem.grow (gtAdGd GT) hA = AxSpinProt3.rRow) :
    ⊢ ∀ rs : RegFile, @tierAWpd GF hlc _ _ (splPol GT) (gtAdGd GT) Unit Unit trivOb ()
      ⟨hp cpu rSt rs, 3⟩ .MaybeStuck hA (fun _ => iprop(True)) := by
  have Hne : 3 ≠ (AxOpsem.grow (gtAdGd GT) hA).length := by rw [Hrow]; simp [AxSpinProt3.rRow]
  have Hl3 := rL GT Hrow 3 _ rfl
  have H := shPos (hlc := hlc) (GF := GF) (pol := splPol GT) (gtAdGd GT) Unit Unit trivOb () cpu hA
    (fun _ => iprop(True)) iprop(True) 3 rSt Hne
    (fun rs id K => noReadAtWrite cpu _ xpaM xpaMRam b2 hlt rs 3 id K)
    (fun rs l s' Hst => by
      obtain ⟨rfl, Hs', -⟩ := writeInv2 cpu _ xpaM xpaMRam b2 hlt rs 3 l s' Hst
      simp only [wlWdata]
      subst Hs'
      have Hval : graphData (gtAdGd GT) (hA, 3) = some (WeakInterpProj.wbytes 1 b2) := by
        unfold graphData; rw [Hl3]; simp [lblData, l3pWbytes1]
      iintro _
      iapply (evPlain (hlc := hlc) (pol := splPol GT) (gtAdGd GT) Unit Unit trivOb () hA 3
        iprop(True) iprop(True) _ _ Hval) $$ []
      · iapply feTriv
      iintro _ _
      iapply (shHltTrue (hlc := hlc) (pol := splPol GT) (gtAdGd GT) Unit Unit trivOb () cpu hA
        (3 + 1)) $$ %rs)
  iintro %rs
  iapply H $$ [] %rs
  itrivial

theorem wRRel (GT : GdexecT) (cpu : CPU) (Hrow : AxOpsem.grow (gtAdGd GT) hA = AxSpinProt3.rRow) :
    ⊢ ∀ rs : RegFile, @tierAWpd GF hlc _ _ (splPol GT) (gtAdGd GT) Unit Unit trivOb ()
      ⟨hp cpu rRel rs, 2⟩ .MaybeStuck hA (fun _ => iprop(True)) := by
  have Hne : 2 ≠ (AxOpsem.grow (gtAdGd GT) hA).length := by rw [Hrow]; simp [AxSpinProt3.rRow]
  have Hl2 := rL GT Hrow 2 _ rfl
  have H := shPos (hlc := hlc) (GF := GF) (pol := splPol GT) (gtAdGd GT) Unit Unit trivOb () cpu hA
    (fun _ => iprop(True)) iprop(True) 2 rRel Hne
    (fun rs id K => noReadAtWrite cpu _ ypaM ypaMRam b0 rSt rs 2 id K)
    (fun rs l s' Hst => by
      obtain ⟨rfl, Hs', -⟩ := writeInv2 cpu _ ypaM ypaMRam b0 rSt rs 2 l s' Hst
      simp only [wlWdata]
      subst Hs'
      have Hval : graphData (gtAdGd GT) (hA, 2) = some (WeakInterpProj.wbytes 1 b0) := by
        unfold graphData; rw [Hl2]; simp [lblData, l3pWbytes1]
      iintro _
      iapply (evPlain (hlc := hlc) (pol := splPol GT) (gtAdGd GT) Unit Unit trivOb () hA 2
        iprop(True) iprop(True) _ _ Hval) $$ []
      · iapply feTriv
      iintro _ _
      iapply (wRSt (hlc := hlc) GT cpu Hrow) $$ %rs)
  iintro %rs
  iapply H $$ [] %rs
  itrivial

theorem wRFence (GT : GdexecT) (cpu : CPU)
    (Hrow : AxOpsem.grow (gtAdGd GT) hA = AxSpinProt3.rRow) :
    ⊢ ∀ rs : RegFile, @tierAWpd GF hlc _ _ (splPol GT) (gtAdGd GT) Unit Unit trivOb ()
      ⟨hp cpu rFence rs, 1⟩ .MaybeStuck hA (fun _ => iprop(True)) := by
  have Hne : 1 ≠ (AxOpsem.grow (gtAdGd GT) hA).length := by rw [Hrow]; simp [AxSpinProt3.rRow]
  have H := shPos (hlc := hlc) (GF := GF) (pol := splPol GT) (gtAdGd GT) Unit Unit trivOb () cpu hA
    (fun _ => iprop(True)) iprop(True) 1 rFence Hne
    (fun rs id K => noReadAtFence cpu _ rRel rs 1 id K)
    (fun rs l s' Hst => by
      obtain ⟨rfl, Hs', -⟩ := fenceInv2 cpu _ rRel rs 1 l s' Hst
      simp only [wlWdata]
      subst Hs'
      iintro _
      iapply (shSkip2 (GF := GF) (gtAdGd GT) Unit Unit trivOb () hA _ _)
      inext
      iapply (wRRel (hlc := hlc) GT cpu Hrow) $$ %rs)
  iintro %rs
  iapply H $$ [] %rs
  itrivial

theorem AxSpinProt3.wpdRTriv (GT : GdexecT) (cpu : CPU)
    (Hrow : AxOpsem.grow (gtAdGd GT) hA = AxSpinProt3.rRow) :
    ⊢ @tierAWpd GF hlc _ _ (splPol GT) (gtAdGd GT) Unit Unit trivOb ()
      ⟨hp cpu AxSpinProt3.rM0 zeroRegs, 0⟩ .MaybeStuck hA (fun _ => iprop(True)) := by
  have Hne : 0 ≠ (AxOpsem.grow (gtAdGd GT) hA).length := by rw [Hrow]; simp [AxSpinProt3.rRow]
  have Hl0' := rL GT Hrow 0 _ rfl
  have Hl0 : (AxOpsem.grow (gtAdGd GT) hA)[0]? =
      some (.LRmw true false (paZ ypaM) [0] [b0] [b1] .WCplain) := by rw [Hrow]; rfl
  have Hval : graphData (gtAdGd GT) (hA, 0) = some (WeakInterpProj.wbytes 1 b1) := by
    unfold graphData; rw [Hl0']; simp [lblData, l3pWbytes1]
  have HW := shRmwWrite (hlc := hlc) (GF := GF) (pol := splPol GT) (gtAdGd GT) Unit Unit trivOb () cpu hA
    (fun _ => iprop(True)) ypaM ypaMRam rFence 0 Hne iprop(True)
    (fun rs => by
      iintro _
      iapply (evPlain (hlc := hlc) (pol := splPol GT) (gtAdGd GT) Unit Unit trivOb () hA 0
        iprop(True) iprop(True) _ _ Hval) $$ []
      · iapply feTriv
      iintro _ _
      iapply (wRFence (hlc := hlc) GT cpu Hrow) $$ %rs)
  have H := shRmwRead (hlc := hlc) (GF := GF) (pol := splPol GT) (gtAdGd GT) Unit Unit trivOb () cpu hA
    (fun _ => iprop(True)) ypaM ypaMRam (fun _ => rW) 0 0 b0 .WCplain Hne Hl0 iprop(True)
    (fun rs => by
      iintro _
      iapply HW $$ [] %rs
      itrivial)
  iapply H $$ [] %zeroRegs
  itrivial

end wpdR

end Weak
