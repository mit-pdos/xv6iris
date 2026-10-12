/-
Weak: **the RELEASING STORE of xv6's real `release`** (`sw zero,0(s1)` at release + 0x1a) at the
joint instance Ixv6 — Theorem 2 design (`notes/weak-lb-thm2-design.md` §C.2, §D row `AxSpinRl3`).
NEW Lean file (no Rocq source: Rocq's `AxSpinRs`/`AxSpinRl*` were never written).

## What this file provides

§1 KERNEL CROSS-CHECK.  `AxSpinRl3.relWord` (`decide +kernel` on `Xv6.Kernel.textTree`): this
   tree's release + 0x1a = 0x80000cfa holds `0x0004a023` (4 bytes) = `sw zero,0(s1)` =
   `.STORE (0#12, x0, x9, 4)`.  So xv6's `__sync_lock_release` compiles here to
   `fence rw,w` (release + 0x16, AxSpinRl2's `XxFence`) followed by a PLAIN 4-byte `sw` — not an
   `amoswap.w.rl` — and the store's `WCrel` class comes from the release-pending flag armed by
   the fence (AxSpinRl1 §4, `rowReleaseRelHonest`).  The leaf takes `textOkB …` of the generic
   `.STORE (imm, rs2, rs1, 4)` AST (callers discharge it with the `*TextOf` certificates).
   `AxSpinRl3.stBytesZero`: the bus bytes of a 4-byte store of 0 are `AxSpinX4.z4`.
§2 TWO dflowO PLUMBING LEMMAS (Lean-only).  `AxSpinRl3.dflowODrawM` — a data-event flow DRAWING
   A FAMILY `m` of lob-predecessor annotations (`AxSpinProt7.evDrawM`'s plumbing in
   `dflowO` form, as `AxSpinHdB.dflowODraw` is `evDraw`'s); `AxSpinRl3.dflowOPastM` — a flow at a
   position `k ≤ e0.2` for an owned annotation `e0 ∈ dom m` of hart `i` is vacuous
   (`AxSpinRl2.dflowOPast` through `bigSepM_lookup`).
§3 `FstRel` — THE POSITIONAL RELEASE FLOW (the positional twin of `AxSpinU.wpdReleaseX`):
   `FstM (dokAtP L.xlLk 4) i (ORel L nm i kw)`.  At the releasing store position `kw` (row label
   `LStore false L.xlLk z4 cls`, the fence `LFence true true false true` at some `kf < kw`) the
   flow is `AxSpinX2.fxReleasePid` with flowIn = a family `m` of po-earlier anchors of hart `i`
   (all before the fence), drawn through `dflowODrawM`; `gobCat a w` / `a ∈ lobp w` for every
   anchor by `fenceGob` / `fenceLobp` (`Weak/AxSpinProt3.lean:389`, `AxSpinProt5.lean:112`);
   the wand `[∗map] m -∗ locked i c ∗ RCpu a1 ∗ RNp a2` supplies the lock-invariant payload.
   It deposits `(i, kw) ↦ₐ notheld i` (`ORel`).  Other positions: `k ≤ e0.2` (a designated
   anchor) is refuted by `dflowOPastM`; `k > e0.2` is `kw` by the row premise `Hone` ("no other
   lock-word write of hart `i` after the anchor").
§4 `XxSwRel` — THE 4-BYTE WCrel STORE LEAF: `AxSpinAp8.XxStF` over `FstRel`; store at `k`,
   continuation at `k + 1` with `graphData (i, k) = some z4` and `(i, k) ↦ₐ notheld i`.
§5 `XxSwRelRel` — the wrapper AT THE `RowRelease` POSITION (for AxSpinRl4): store at
   `relKw kr`, continuation at `relKp kr`, the fence at `relKf kr` (`rowReleaseFence`), with the
   three anchors of the design given as annotations —
     * `locked` from holding's lock-word read `(i, relKh kr)` (`OHeld`'s deposit
       `locked i (i, kc) ∗ Ql`, `AxSpinHdC.holdingFromRelease'`),
     * `RCPU` from release's own `sd zero,16(s1)` at `(i, relKc kr)` (`XxSdCpuRel`'s deposit
       `Qc ∗ RVL (clb L) (i, relKc kr) vs`),
     * `RNP` from allocpid's nextpid write `(i, ks)`, `ks < kr` (AxSpinAp9: `ks = k + 65`,
       `FstMNp`'s deposit `RNp (i, ks)`).
   The flowIn map is `insert (insert {[(i, ks) := …]} (i, relKc kr) …) (i, relKh kr) …`; the
   designated anchor `e0` is `(i, relKc kr)`.

## Deviations from the design / honesty notes

1. THE STORE IS `fence rw,w; sw` (checked, §1), not `amoswap.w.rl`; the leaf is a plain store
   leaf (`XxStF`, `CertBStoreS`).  The certificate (like every positional store leaf) does not
   relate the row label's CLASS to the program — the positional bridge only checks the bytes; the
   `WCrel` class is the row's (`RowRelease`, `rowReleaseRel`), and its honesty is AxSpinRl1's
   `rowReleaseRelHonest` (the fence arms the flag).  `fxReleasePid` itself is class-agnostic.
2. TWO ROW PREMISES on hart `i`'s OWN events (`FstM` quantifies over EVERY row position, as for
   `AxSpinRl2.FstMCpu`, deviation 2 there):
   * `Hst` — the releasing store's DATA is `z4` (the store writes `x0`).  The flow must exist for
     every graph data, and a non-zero lock-word write by the holder has no arm (only the zero
     WCrel release does); on every row of the real code the data is `z4` (the positional bridge
     itself demands `graphData = stBytes 4 (x0) = z4`).  To be listed among AxSpinT2a's
     `allocFull` value conditions.  OPEN QUESTION for the orchestrator (with AxSpinRl2's): confirm
     that T2a's row family carries "release's lock-word store writes `z4`".
   * `Hone` — no lock-word write of hart `i` lies po-after the designated anchor other than the
     releasing store (true on `allocSeg`: release is the row's last lock-word access).
   Neither says anything about other harts.
3. Frames: the anchors' frames (`Ql`, `Qc`) are DROPPED (`fxReleasePid`'s flowIn wand yields
   exactly `locked ∗ RCpu ∗ RNp`); the deposited annotation is `notheld i` alone (design:
   "deposits `(i, kw) ↦ₐ NH i`, unused by the theorem").
4. `XxSwRel`/`XxSwRelRel` keep the operands generic (`imm rs2 rs1`, `gprVal rs rs2 = 0#64`), as
   `XxSdCpu`; the caller instantiates `0#12, 0, 9` and `AxSpinE8.gprValZero`.

**Reused:** `fxReleasePid`, `RCpu`/`RNp`/`RPid`/`isLock`/`locked`/`notheld`, `lwb`/`clb`
(AxSpinX/X2/Prot), `fenceGob`, `fenceLobp`, `gobGmo` (AxSpinProt3/5), `annotDetachBig`,
`annotAlloc`, `annotSplit`, `naAtProgress` (AxWp; `evDrawM`'s script, AxSpinProt7), `dflowO`,
`FstM` (AxSymMem), `AxSpinRl2.dflowOPast`, `XxStF` (AxSpinAp8), `gwbStoren`, `storenNoRead`,
`inClr`, `zero32Byte0`, `AxSpinX5.addZero`, `lblOfRow`, `xv6AxpolWf`, `HGX`,
`AxSpinWit.localTrue`, `flowEqDynMono`, `RowRelease`/`relK*`/`rowReleaseFence`/`rowReleaseItem`/
`rowReleaseCpu`/`rowReleaseLen` (AxSpinRl1).  New names grepped absent from the tree.

**W13 (I) (plan `notes/weak-allocproc-plan.md` §C W13 (I); [OWN.27]).** the release lemmas' anchor-domain premise is `(lbIsR l || lbIsW l) = true` (was `lbIsMem l = true`: `gwf` admits I/O events, which `fence rw,w` does not order, D48); `AxSpinRl3.memOfRead` concludes the RAM form.
-/
import Weak.AxSpinRl2

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-! # 1. Kernel cross-check -/

/-- (Lean-only) this tree's image holds release+0x1a `sw zero,0(s1)` (0x0004a023, 4 bytes). -/
theorem AxSpinRl3.relWord :
    ([(0x80000cfa, 4, 0x0004a023)] : List (Nat × Nat × Nat)).all
      (fun p => match Xv6.Kernel.textTree.find? p.1 with
        | some k => Nat.beq k.width p.2.1 && Nat.beq k.enc p.2.2
        | none => false) = true := by
  decide +kernel

/-- (Lean-only) the offset: release = 0x80000ce0. -/
theorem AxSpinRl3.relOffset : (KernelSyms.«release» : Nat) + 0x1a = 0x80000cfa := by
  decide +kernel

/-- (Lean-only) a 4-byte store of 0 puts `z4` on the bus. -/
theorem AxSpinRl3.stBytesZero : stBytes 4 (0#64) = AxSpinX4.z4 := by
  decide +kernel

/-- (Lean-only) a read row label is a memory event. -/
theorem AxSpinRl3.memOfRead (lb : Lbl) (aq : Bool) (b : Int) (n : Nat) :
    aident lb = .IRead aq b n → (lbIsR lb || lbIsW lb) = true := by
  intro h
  cases lb <;> first | rfl | simp [aident] at h

/-! # 2. dflowO plumbing -/

section plumb
variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF] [AxannotGS GF]
  [AxSpinX.Xv6G GF]
variable (L : Xlay) (GT : GdexecT) (nm : Xv6N)

/-- (Lean-only) a data-event flow DRAWING a family `m` of lob-predecessor annotations
(`evDrawM`'s plumbing in `dflowO` form); the new annotation is split in two. -/
theorem AxSpinRl3.dflowODrawM (i : Agent) (k : Nat) (m : Mea GF) (R1 R2 O : IProp GF) :
    (FiniteMap.dom_set m : GSet Geid) ⊆ @Axpol.lobp (xv6Pol GT) (gtAdGd GT) (i, k) →
    ⊢ ([∗map] e ↦ P ∈ m, AxAnnot.annotOwn e P) -∗
      @flowEqDyn hlc GF _ (AxSpinX2.xG L GT nm) (gtAdGd GT) (i, k)
        (@Axpol.sPol (xv6Pol GT) (gtAdGd GT) (i, k)) m iprop(R1 ∗ R2) -∗
      (AxAnnot.annotOwn (i, k) R1 -∗ AxAnnot.annotOwn (i, k) R2 -∗ O) -∗
      @dflowO hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) i (gtAdGd GT) k O := by
  intro Hsub
  iintro Hm Hfe HO
  unfold dflowO naAtProgress
  iintro %na ⟨%Hprog, Hannot⟩
  have Hdom : (FiniteMap.dom_set m : GSet Geid) ⊆ FiniteMap.dom_set na := by
    intro e' He'
    have Hb := xv6AxpolWf GT (gtAdGd GT) i k e' (Hsub e' He')
    rw [← Hprog] at Hb
    exact (elemOfFilter.1 Hb).2
  have Hnin : (i, k) ∉ (FiniteMap.dom_set na : GSet Geid) := by
    intro Hd
    have Hf : (i, k) ∈ FiniteSet.filter (fun e : Geid => decide (e.1 = i))
        (FiniteMap.dom_set na : GSet Geid) := elemOfFilter.2 ⟨by simp, Hd⟩
    rw [Hprog, elemOfEidsBefore] at Hf
    exact Nat.lt_irrefl _ Hf.2.1
  imod annotDetachBig na m $$ Hannot Hm with ⟨%m'', %Hdm, Hannot, Hw⟩
  have Hnin' : (i, k) ∉ (FiniteMap.dom_set (PartialMap.union m'' na) : GSet Geid) := by
    intro Hd
    have hn : get? m'' (i, k) = none := by
      apply notElemOfDom1 (S := GSet Geid)
      rw [Hdm]
      exact fun h => Hnin (Hdom _ h)
    apply Hnin
    have h := elemOfDom.1 Hd
    have hl : get? (PartialMap.union m'' na) (i, k) = get? na (i, k) := lookupUnionR hn
    rw [hl] at h
    exact elemOfDom.2 h
  have Hmono : ([∗map] e ↦ R;R' ∈ m;m'',
        AxWp.fromOption (fun P' => iprop(▷ □ (P' -∗ R ∗ R'))) iprop(emp) (get? na e)) ⊢
      [∗map] e ↦ Pu;Puu ∈ m;m'',
        iprop(▷ □ (AxWp.fromOption (fun P => P) iprop(emp) (get? na e) -∗ Pu ∗ Puu)) :=
    BigSepM2.bigSepM2_mono fun {e _ _} h1 _ => by
      obtain ⟨P0, HP0⟩ := Option.isSome_iff_exists.1 (elemOfDom.1 (Hdom _ (elemOfDom2 h1)))
      rw [HP0]
      exact .rfl
  imod annotAlloc (PartialMap.union m'' na) (i, k) iprop(R1 ∗ R2) Hnin' $$ Hannot
    with ⟨Hannot, Hfrag⟩
  imod (annotSplit (i, k) R1 R2) $$ Hfrag %_ Hannot with ⟨⟨Hf1, Hf2⟩, Hannot⟩
  imodintro
  inext
  imodintro
  iexists iprop(R1 ∗ R2), m, m'', (() : Unit)
  isplitl [Hw]
  · unfold naSplittingWf
    isplitr
    · ipureintro
      exact Hsub
    · iapply Hmono
      iexact Hw
  isplitl [Hfe]
  · iexact Hfe
  isplitl [Hannot]
  · have Heq : insert (PartialMap.union m'' na) (i, k) iprop(R1 ∗ R2) =
        PartialMap.union (PartialMap.union {[(i, k) := iprop(R1 ∗ R2)]} m'') na := by
      rw [insertUnionSingletonL (M := GMapF Geid)]
      exact mapUnionAssoc (M := GMapF Geid)
    rw [← Heq]
    iexact Hannot
  isplitr
  · iapply (AxSpinWit.localTrue (gtAdGd GT) Xv6N Unit (protXv6 L) nm (gtAdGd GT) i (k + 1) ())
  · iapply HO $$ Hf1 Hf2

/-- (Lean-only) a flow at `k ≤ e0.2`, `e0` an owned annotation of hart `i` in the family `m`, is
vacuous. -/
theorem AxSpinRl3.dflowOPastM (i : Agent) (k : Nat) (m : Mea GF) (e0 : Geid) (O : IProp GF) :
    e0 ∈ (FiniteMap.dom_set m : GSet Geid) → e0.1 = i → k ≤ e0.2 →
    ⊢ ([∗map] e ↦ P ∈ m, AxAnnot.annotOwn e P) -∗
      @dflowO hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) i (gtAdGd GT) k O := by
  intro He0 Hi Hk
  obtain ⟨P0, HP0⟩ := Option.isSome_iff_exists.1 (elemOfDom.1 He0)
  iintro Hm
  ihave H0 := (BigSepM.bigSepM_lookup (Φ := fun e P => AxAnnot.annotOwn (GF := GF) e P) HP0) $$ Hm
  iapply (AxSpinRl2.dflowOPast L GT nm i k e0 P0 O Hi Hk) $$ H0

end plumb

/-! # 3. The positional release flow -/

section flow
variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF] [AxannotGS GF]
  [AxSpinX.Xv6G GF]
variable (L : Xlay) (GT : GdexecT) (nm : Xv6N)
variable (HL : xlayOk L) (Hcons : rvwmoCatConsistent (gtAdGd GT))

/-- The releasing store's output: at `kw` the deposited `notheld`. -/
def ORel (i : Agent) (kw k : Nat) (_data : List (BitVec 8)) : IProp GF :=
  if k = kw then AxAnnot.annotOwn (i, kw) (notheld nm.xnReg L.xlLk i) else iprop(True)

theorem AxSpinRl3.oRelAt (i : Agent) (kw : Nat) (data : List (BitVec 8)) :
    ORel (GF := GF) L nm i kw kw data = AxAnnot.annotOwn (i, kw) (notheld nm.xnReg L.xlLk i) :=
  if_pos rfl

include HL Hcons in
/-- THE POSITIONAL RELEASE FLOW (`fxReleasePid` at the row position `kw`): the anchors `m` (all
of hart `i`, po-before the fence at `kf`) are drawn; lk->cpu from `a1`, nextpid from `a2`,
gob-before the store through the fence; deposits `notheld`. -/
theorem FstRel (i : Agent) (kf kw : Nat) (c a1 a2 e0 : Geid) (m : Mea GF) (cls : WmClass) :
    kf < kw →
    (AxOpsem.grow (gtAdGd GT) i)[kf]? = some (.LFence true true false true) →
    (AxOpsem.grow (gtAdGd GT) i)[kw]? = some (.LStore false L.xlLk AxSpinX4.z4 cls) →
    (∀ e, e ∈ (FiniteMap.dom_set m : GSet Geid) → e.1 = i ∧ e.2 < kf ∧
      ∃ l, (AxOpsem.grow (gtAdGd GT) i)[e.2]? = some l ∧ (lbIsR l || lbIsW l) = true) →
    a1 ∈ (FiniteMap.dom_set m : GSet Geid) → a2 ∈ (FiniteMap.dom_set m : GSet Geid) →
    e0 ∈ (FiniteMap.dom_set m : GSet Geid) →
    (∀ (k' : Nat) (lb : Lbl) (rl : Bool) (n : Nat), e0.2 < k' →
      (AxOpsem.grow (gtAdGd GT) i)[k']? = some lb →
      aidentWr (aident lb) = some (rl, L.xlLk, n) → k' = kw) →
    ⊢ isLock nm.xnReg L.xlLk (RPid L nm.xnH nm.xnM nm.xnI (gtAdGd GT)) -∗
      ([∗map] e ↦ P ∈ m, AxAnnot.annotOwn e P) -∗
      (([∗map] P ∈ m, P) -∗
        locked nm.xnReg L.xlLk i c ∗ RCpu L nm.xnH (gtAdGd GT) a1 ∗
          RNp L nm.xnH nm.xnM nm.xnI (gtAdGd GT) a2) -∗
      @FstM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent
        (dokAtP L.xlLk 4) i (ORel L nm i kw) := by
  intro Hlt Hf Hst Hdom Ha1 Ha2 He0 Hone
  iintro #Hil Hm Hw
  unfold FstM
  iintro %GD %ls %k %data %base %n %Hcs #Hg _ %Hgd %Hd
  ihave %Heq := (HGX L GT nm GD Hcs) $$ Hg
  subst Heq
  obtain ⟨⟨rfl, -⟩, lb, rl, Hlb, Hid⟩ := Hd
  rcases Nat.lt_or_ge e0.2 k with hk | hk
  · obtain rfl : k = kw := Hone k lb rl _ hk Hlb Hid
    rw [AxSpinRl3.oRelAt]
    have Hlf := lblOfRow _ _ _ _ Hf
    have Hls := lblOfRow _ _ _ _ Hst
    obtain ⟨Hws, Hsgs⟩ := gwbStoren _ _ _ _ _ Hls
    have Hzw : zw L.xlLk (gtAdGd GT).gdG (i, k) := by
      have H := Hws 0 b0 zero32Byte0
      rw [AxSpinX5.addZero] at H
      exact H
    have Hlw : ∀ a v', gwritesByte (gtAdGd GT).gdG (i, k) a v' → a ∈ lwb L := by
      intro a v' Hw'
      obtain ⟨j, Hj, rfl⟩ := Hsgs a v' Hw'
      have hj := (List.getElem?_eq_some_iff.1 Hj).1
      simp only [AxSpinX4.z4, wbytesLength] at hj
      unfold lwb
      rw [inClr]
      omega
    have Hgob : ∀ e, e ∈ (FiniteMap.dom_set m : GSet Geid) →
        gobCat (gtAdGd GT) e (i, k) ∧ e ∈ @Axpol.lobp (xv6Pol GT) (gtAdGd GT) (i, k) := by
      rintro ⟨ei, ek⟩ He
      obtain ⟨Hi, Hlt', l, Hl, Hmem⟩ := Hdom _ He
      dsimp only at Hi Hlt' Hl
      rw [show ((ei, ek) : Geid) = (i, ek) from by rw [Hi]]
      have Hl' := lblOfRow _ _ _ _ Hl
      exact ⟨fenceGob (gtAdGd GT) i ek kf k l _ _ _ Hl' Hmem Hlf Hls Hlt' Hlt,
        fenceLobp (gtAdGd GT) Hcons i ek kf k l _ _ _ Hl' Hmem Hlf Hls Hlt' Hlt⟩
    have Hsub : (FiniteMap.dom_set m : GSet Geid) ⊆
        @Axpol.lobp (xv6Pol GT) (gtAdGd GT) (i, k) := fun e He => (Hgob e He).2
    have Hfe0 := fxReleasePid (hlc := hlc) L GT nm HL Hcons (i, k) i c a1 a2 m Hzw
      (fun t v => storenNoRead _ _ _ _ _ _ _ _ Hls) Hlw (Hgob a1 Ha1).1 (Hgob a2 Ha2).1
    have Hmono : ⊢ ▷ (notheld (GF := GF) nm.xnReg L.xlLk i -∗
        iprop(notheld nm.xnReg L.xlLk i ∗ True)) := by
      inext
      iintro H
      isplitl [H]
      · iexact H
      · itrivial
    ihave Hfe1 := Hfe0
    ihave Hfe2 := Hfe1 $$ Hil Hw
    ihave Hmo := Hmono
    ihave Hmn := (@flowEqDynMono hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) (gtAdGd GT) (i, k)
      (@Axpol.sPol (xv6Pol GT) (gtAdGd GT) (i, k)) m
      (notheld nm.xnReg L.xlLk i) iprop(notheld nm.xnReg L.xlLk i ∗ True))
    ihave Hfe := Hmn $$ Hmo Hfe2
    iapply (AxSpinRl3.dflowODrawM L GT nm i k m (notheld nm.xnReg L.xlLk i) iprop(True) _ Hsub)
      $$ Hm Hfe
    iintro H -
    iexact H
  · iapply (AxSpinRl3.dflowOPastM L GT nm i k m e0 _ He0 (Hdom e0 He0).1 hk) $$ Hm

end flow

/-! # 4. The WCrel store leaf -/

section swrel
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

include HL Hcons hmode hasid hppn Hfix HΨmid in
/-- THE RELEASING STORE (`sw zero,0(s1)` after `fence rw,w`): store at `k`, continuation at
`k + 1` with the graph data `z4` and the deposited `notheld`. -/
theorem XxSwRel (s : Athread) (rs : RegFile) (k : Nat) (pc : BitVec 64) (is_rvc : Bool)
    (imm : BitVec 12) (rs2 rs1 : BitVec 5) (va pa : BitVec 64) (kf : Nat) (c a1 a2 e0 : Geid)
    (m : Mea GF) (cls : WmClass) :
    RetX cpu rs k s → ctrlOkSW T satp0 rs → rs .PC = pc → hitW rs pc →
    textOkB σi T satp0 pc is_rvc (.STORE (imm, .Regidx rs2, .Regidx rs1, 4)) →
    va = gprVal rs rs1 + sign_extend (m := 64) imm →
    dataAtS σi T (.Store .Data) va 4 pa → hitW rs va → paZ pa = L.xlLk →
    gprVal rs rs2 = 0#64 →
    kf < k →
    (AxOpsem.grow (gtAdGd GT) i)[kf]? = some (.LFence true true false true) →
    (AxOpsem.grow (gtAdGd GT) i)[k]? = some (.LStore false L.xlLk AxSpinX4.z4 cls) →
    (∀ e, e ∈ (FiniteMap.dom_set m : GSet Geid) → e.1 = i ∧ e.2 < kf ∧
      ∃ l, (AxOpsem.grow (gtAdGd GT) i)[e.2]? = some l ∧ (lbIsR l || lbIsW l) = true) →
    a1 ∈ (FiniteMap.dom_set m : GSet Geid) → a2 ∈ (FiniteMap.dom_set m : GSet Geid) →
    e0 ∈ (FiniteMap.dom_set m : GSet Geid) →
    (∀ (k' : Nat) (lb : Lbl) (rl : Bool) (n : Nat), e0.2 < k' →
      (AxOpsem.grow (gtAdGd GT) i)[k']? = some lb →
      aidentWr (aident lb) = some (rl, L.xlLk, n) → k' = k) →
    k + 1 ≤ (AxOpsem.grow (gtAdGd GT) i).length →
    ⊢ isLock nm.xnReg L.xlLk (RPid L nm.xnH nm.xnM nm.xnI (gtAdGd GT)) -∗
      ([∗map] e ↦ P ∈ m, AxAnnot.annotOwn e P) -∗
      (([∗map] P ∈ m, P) -∗
        locked nm.xnReg L.xlLk i c ∗ RCpu L nm.xnH (gtAdGd GT) a1 ∗
          RNp L nm.xnH nm.xnM nm.xnI (gtAdGd GT) a2) -∗
      (∀ (rs' : RegFile) (ib' : Ibch), ⌜GoodB T satp0 rs pc is_rvc none none rs'⌝ -∗
        ⌜graphData (gtAdGd GT) (i, k) = some AxSpinX4.z4⌝ -∗
        AxAnnot.annotOwn (i, k) (notheld nm.xnReg L.xlLk i) -∗
        @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
          ⟨.PHart cpu (.pure ()) rs' none ib', k + 1⟩ Ψ) -∗
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i s Ψ := by
  intro HRet Hc HPC Hhit Htx Hva Hda Hhv Hpa Hval Hlt Hf Hst Hdom Ha1 Ha2 He0 Hone Hle
  have HF := FstRel L GT nm HL Hcons i kf k c a1 a2 e0 m cls Hlt Hf Hst Hdom Ha1 Ha2 He0 Hone
  have HF' : ⊢ isLock nm.xnReg L.xlLk (RPid L nm.xnH nm.xnM nm.xnI (gtAdGd GT)) -∗
      ([∗map] e ↦ P ∈ m, AxAnnot.annotOwn e P) -∗
      (([∗map] P ∈ m, P) -∗
        locked nm.xnReg L.xlLk i c ∗ RCpu L nm.xnH (gtAdGd GT) a1 ∗
          RNp L nm.xnH nm.xnM nm.xnI (gtAdGd GT) a2) -∗
      @FstM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent
        (dokAtP (paZ pa) 4) i (ORel L nm i k) := by
    rw [Hpa]
    exact HF
  have H := XxStF L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Ψ HΨmid s rs k pc
    is_rvc imm rs2 rs1 4 va pa (ORel L nm i k) HRet Hc HPC Hhit Htx (Or.inr (Or.inr (Or.inl rfl)))
    (by omega) (by omega) Hva Hda Hhv Hle
  have E : stBytes 4 (gprVal rs rs2) = AxSpinX4.z4 := by
    rw [Hval]
    exact AxSpinRl3.stBytesZero
  rw [E, AxSpinRl3.oRelAt] at H
  iintro #Hil Hm Hw C
  ihave F0 := HF'
  ihave F := F0 $$ Hil Hm Hw
  iapply H $$ F
  iintro %rs' %ib' %HGB %Hgd HO
  iapply C $$ %rs' %ib' %HGB %Hgd HO

/-! # 5. The wrapper at the `RowRelease` position -/

include HL Hcons hmode hasid hppn Hfix HΨmid in
/-- release's `sw zero,0(s1)` at `relKw kr` (continuation `relKp kr`), over AxSpinRl1's shape,
the three anchors of the design: holding's lock-word read `(i, relKh kr)` (`locked`), release's
lk->cpu store `(i, relKc kr)` (`RCpu`), allocpid's nextpid write `(i, ks)` (`RNp`). -/
theorem XxSwRelRel (kr : Nat) (c : Bool)
    (pra ps0 ps1 plk pcl hra hs0 hs1 hram hs0m qra qs0 qmra qms0 pn pint : Int)
    (s : Athread) (rs : RegFile) (pc : BitVec 64) (is_rvc : Bool) (imm : BitVec 12)
    (rs2 rs1 : BitVec 5) (va pa : BitVec 64) (kc ks : Nat) (vs : List (BitVec 8))
    (Ql Qc : IProp GF) :
    RowRelease kr c (AxOpsem.grow (gtAdGd GT) i)
      pra ps0 ps1 plk pcl hra hs0 hs1 hram hs0m qra qs0 qmra qms0 pn pint →
    (AxOpsem.grow (gtAdGd GT) i)[relKw kr]? =
      some (.LStore false L.xlLk AxSpinX4.z4 .WCrel) →
    ks < kr → (∃ l, (AxOpsem.grow (gtAdGd GT) i)[ks]? = some l ∧ (lbIsR l || lbIsW l) = true) →
    (∀ (k' : Nat) (lb : Lbl) (rl : Bool) (n : Nat), relKc kr < k' →
      (AxOpsem.grow (gtAdGd GT) i)[k']? = some lb →
      aidentWr (aident lb) = some (rl, L.xlLk, n) → k' = relKw kr) →
    RetX cpu rs (relKw kr) s → ctrlOkSW T satp0 rs → rs .PC = pc → hitW rs pc →
    textOkB σi T satp0 pc is_rvc (.STORE (imm, .Regidx rs2, .Regidx rs1, 4)) →
    va = gprVal rs rs1 + sign_extend (m := 64) imm →
    dataAtS σi T (.Store .Data) va 4 pa → hitW rs va → paZ pa = L.xlLk →
    gprVal rs rs2 = 0#64 →
    ⊢ isLock nm.xnReg L.xlLk (RPid L nm.xnH nm.xnM nm.xnI (gtAdGd GT)) -∗
      AxAnnot.annotOwn (i, relKh kr) iprop(locked nm.xnReg L.xlLk i (i, kc) ∗ Ql) -∗
      AxAnnot.annotOwn (i, relKc kr) iprop(Qc ∗ RVL nm.xnH (gtAdGd GT) (clb L) (i, relKc kr) vs) -∗
      AxAnnot.annotOwn (i, ks) (RNp L nm.xnH nm.xnM nm.xnI (gtAdGd GT) (i, ks)) -∗
      (∀ (rs' : RegFile) (ib' : Ibch), ⌜GoodB T satp0 rs pc is_rvc none none rs'⌝ -∗
        ⌜graphData (gtAdGd GT) (i, relKw kr) = some AxSpinX4.z4⌝ -∗
        AxAnnot.annotOwn (i, relKw kr) (notheld nm.xnReg L.xlLk i) -∗
        @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
          ⟨.PHart cpu (.pure ()) rs' none ib', relKp kr⟩ Ψ) -∗
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i s Ψ := by
  intro HR Hst Hks Hksm Hone HRet Hc HPC Hhit Htx Hva Hda Hhv Hpa Hval
  let P1 : IProp GF := iprop(locked nm.xnReg L.xlLk i (i, kc) ∗ Ql)
  let P2 : IProp GF := iprop(Qc ∗ RVL nm.xnH (gtAdGd GT) (clb L) (i, relKc kr) vs)
  let P3 : IProp GF := RNp L nm.xnH nm.xnM nm.xnI (gtAdGd GT) (i, ks)
  let m : Mea GF := insert (insert ({[((i, ks) : Geid) := P3]} : Mea GF) (i, relKc kr) P2)
    (i, relKh kr) P1
  have Hn2 : get? ({[((i, ks) : Geid) := P3]} : Mea GF) (i, relKc kr) = none :=
    lookupSingletonNe (by simp only [relKc, ne_eq, Prod.mk.injEq, true_and]; omega)
  have Hn1 : get? (insert ({[((i, ks) : Geid) := P3]} : Mea GF) (i, relKc kr) P2)
      (i, relKh kr) = none := by
    rw [lookupInsertNe (by simp only [relKc, relKh, ne_eq, Prod.mk.injEq, true_and]; omega),
      lookupSingletonNe (by simp only [relKh, ne_eq, Prod.mk.injEq, true_and]; omega)]
  have Hdm : ∀ e, e ∈ (FiniteMap.dom_set m : GSet Geid) →
      e = (i, relKh kr) ∨ e = (i, relKc kr) ∨ e = (i, ks) := by
    intro e He
    simp only [m] at He
    rw [domInsert, domInsert, domSingleton] at He
    rcases elemOfUnion.1 He with H | H
    · exact Or.inl (elemOfSingleton.1 H)
    rcases elemOfUnion.1 H with H | H
    · exact Or.inr (Or.inl (elemOfSingleton.1 H))
    · exact Or.inr (Or.inr (elemOfSingleton.1 H))
  have Hin1 : ((i, relKh kr) : Geid) ∈ (FiniteMap.dom_set m : GSet Geid) := by
    simp only [m]
    rw [domInsert]
    exact elemOfUnion.2 (Or.inl (elemOfSingleton.2 rfl))
  have Hin2 : ((i, relKc kr) : Geid) ∈ (FiniteMap.dom_set m : GSet Geid) := by
    simp only [m]
    rw [domInsert, domInsert]
    exact elemOfUnion.2 (Or.inr (elemOfUnion.2 (Or.inl (elemOfSingleton.2 rfl))))
  have Hin3 : ((i, ks) : Geid) ∈ (FiniteMap.dom_set m : GSet Geid) := by
    simp only [m]
    rw [domInsert, domInsert, domSingleton]
    exact elemOfUnion.2 (Or.inr (elemOfUnion.2 (Or.inr (elemOfSingleton.2 rfl))))
  have Hmh : ∃ l, (AxOpsem.grow (gtAdGd GT) i)[relKh kr]? = some l ∧ (lbIsR l || lbIsW l) = true := by
    obtain ⟨lb, Hlb, aq, Hs⟩ := rowReleaseItem 3 (.it (.RL plk 4)) HR (by cases c <;> rfl)
    exact ⟨lb, Hlb, AxSpinRl3.memOfRead lb aq plk 4 Hs⟩
  have Hmc : ∃ l, (AxOpsem.grow (gtAdGd GT) i)[relKc kr]? = some l ∧ (lbIsR l || lbIsW l) = true := by
    obtain ⟨vw, cls, Hlb, -⟩ := rowReleaseCpu HR
    exact ⟨_, Hlb, rfl⟩
  have Hdom : ∀ e, e ∈ (FiniteMap.dom_set m : GSet Geid) → e.1 = i ∧ e.2 < relKf kr ∧
      ∃ l, (AxOpsem.grow (gtAdGd GT) i)[e.2]? = some l ∧ (lbIsR l || lbIsW l) = true := by
    intro e He
    rcases Hdm e He with rfl | rfl | rfl
    · exact ⟨rfl, by simp only [relKh, relKf]; omega, Hmh⟩
    · exact ⟨rfl, by simp only [relKc, relKf]; omega, Hmc⟩
    · exact ⟨rfl, by simp only [relKf]; omega, Hksm⟩
  have Hlen := (rowReleaseLen HR).1
  have H := XxSwRel L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Ψ HΨmid s rs
    (relKw kr) pc is_rvc imm rs2 rs1 va pa (relKf kr) (i, kc) (i, relKc kr) (i, ks)
    (i, relKc kr) m .WCrel HRet Hc HPC Hhit Htx Hva Hda Hhv Hpa Hval
    (by simp only [relKf, relKw]; omega) (rowReleaseFence HR) Hst Hdom Hin2 Hin3 Hin2 Hone
    (by simp only [relKe, relKr, relKp, relKw] at Hlen ⊢; omega)
  rw [show relKw kr + 1 = relKp kr from rfl] at H
  iintro #Hil A1 A2 A3 C
  iapply H $$ Hil [A1 A2 A3] [] [C]
  · iapply (BigSepM.bigSepM_insert Hn1).2
    isplitl [A1]
    · iexact A1
    iapply (BigSepM.bigSepM_insert Hn2).2
    isplitl [A2]
    · iexact A2
    iapply BigSepM.bigSepM_singleton.2
    iexact A3
  · iintro Hb
    icases (BigSepM.bigSepM_insert Hn1).1 $$ Hb with ⟨⟨Hl, -⟩, Hb⟩
    icases (BigSepM.bigSepM_insert Hn2).1 $$ Hb with ⟨⟨-, Hv⟩, Hb⟩
    ihave Hn := (BigSepM.bigSepM_singleton (M := GMapF Geid)).1 $$ Hb
    isplitl [Hl]
    · iexact Hl
    isplitl [Hv]
    · unfold RCpu
      iexists vs
      iexact Hv
    · iexact Hn
  · iintro %rs' %ib' %HGB %Hgd HO
    iapply C $$ %rs' %ib' %HGB %Hgd HO

end swrel

end Weak
