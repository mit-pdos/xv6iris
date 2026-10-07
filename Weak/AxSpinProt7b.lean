/-
Weak: **Phase 1b, part 3 of the spinlock plan (second half) -- HART B's WPd at `spinOb5` and
the race program at the TRIVIAL protocol.**  Lean-only split of `AxSpinProt7` (which holds
§1–§6: programs, rows, runs, the shells `evDrawM`/`shHltReadbackM`, the two-component `R` and
hart A's `wpdA5`); importers of Rocq `AxSpinProt7` import this file.

Rocq: `iris/AxSpinProt7.v` @ xxvzwolszwmp, §7–§8.

## The Rocq header, in substance (§7–§8)

§7 HART B's WPd at `spin_ob5`: non-holder lk->cpu read, failed spin, claim (`notheld` in hand),
owned placement read of `x`, the HOLDER's `lw lk` (REQUIRED (3)), release (`fe5Release'`, two
components from one annotation, `locked` from another), RE-ACQUIRE with `notheld` drawn from its
own release's annotation (REQUIRED (2)), release.  The post `QB5` -- three facts deposited at
three different reads (the x-read's placement, the `lw`'s `≠ 0`, the cpu-read's `rdFact`) -- is
READ BACK at the row end (`shHltReadbackM`).
§8 the race program A' at the TRIVIAL protocol (sanity twin).

## Deviations from Rocq

As `AxSpinProt7` deviations 1–3 (no `Tf`; section variables explicit in Rocq's order, only where
Rocq's section mechanism includes them; local instances `b5_G`/`r5_G` ↦ `shG …`, policies
`b5_pol`/`r5_pol` ↦ `splPol GT` passed explicitly; lean-sail shapes).  The Rocq notations
`TWB`/`LKB`/`R5`/`RX`/`RC`/`SH`/`RDf`/`PLf`/`LWf`/`FB`/`TWR` are unfolded; `PLf`'s and `LWf`'s
propositions are the Lean-only reducible abbrevs `AxSpinProt7b.plF`/`lwF` (`QB5` is stated
literally, definitionally their conjunction with `rdFact`).  `fe_triv5` drops Rocq's unused
policy instance.

**Rocq → Lean name map.**  `QB5` `QB5`, `wB10/9/8` `AxSpinProt7.wB10/9/8`, `wB7w` `wB7w`, `wB7r`
`wB7r`, `wB6/5/4/3` `AxSpinProt7.wB6/5/4/3`, `wB2w` `wB2w`, `wB2r` `wB2r`, `wB1w`/`wB1r`
`AxSpinProt7.wB1w`/`wB1r`, `wpdB5` `wpdB5`, `fe_triv5` `feTriv5`, `r5L` `r5L`, `wR5_st`
`wR5St`, `wR5_rel` `wR5Rel`, `wR5_fence` `wR5Fence`, `wpdR5_triv` `wpdR5Triv`.  Duplicated Rocq
names are file-qualified with the Rocq file name (`AxSpinProt7.*`).  Lean-only
(file-qualified): `AxSpinProt7b.plF`, `AxSpinProt7b.lwF`.

**Dropped:** none (§7–§8: 25 Rocq decls incl. the 4 local instances `b5_G`/`b5_pol`/`r5_G`/
`r5_pol` (inlined); 23 Lean = 21 + 2 Lean-only).
-/
import Weak.AxSpinProt7

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D

/-! # 7. HART B's WPd at `spinOb5` -/

/-- Lean-only: the x-read's placement fact (Rocq notation `PLf`). -/
abbrev AxSpinProt7b.plF (G : Gexec) (tx : Nat) (vx : BitVec 8) : Prop :=
  tx = 0 ∨ ∃ w, gwriteAt G tx = some w ∧ gwritesByte G w xa vx ∧
    (w = (hB, 2) ∨ gmoLt G w (hB, 2))

/-- Lean-only: the holder's `lw lk` fact (Rocq notation `LWf`). -/
abbrev AxSpinProt7b.lwF (G : Gexec) : Prop :=
  ∀ t v, greadsByte G (hB, 4) ya t v → v ≠ b0

def QB5 (G : Gexec) (tx : Nat) (vx : BitVec 8) : Prop :=
  (tx = 0 ∨ ∃ w, gwriteAt G tx = some w ∧ gwritesByte G w xa vx ∧
                 (w = (hB, 2) ∨ gmoLt G w (hB, 2))) ∧
  (∀ t v, greadsByte G (hB, 4) ya t v → v ≠ b0) ∧
  rdFact [ca] cv5 G (hB, 0)

section wpdB5
variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF] [AxannotGS GF]
  [AxlogG GF Hent] [SpinlockG GF]

theorem AxSpinProt7.wB10 (GT : GdexecT) (nm : spinN) (cpu : CPU) (tx : Nat) (vx : BitVec 8) :
    ⊢ iprop(AxAnnot.annotOwn (GF := GF) (hB, 0) iprop(⌜rdFact [ca] cv5 (gtAdGd GT).gdG (hB, 0)⌝) ∗
        AxAnnot.annotOwn (hB, 3) iprop(⌜AxSpinProt7b.plF (gtAdGd GT).gdG tx vx⌝) ∗
        AxAnnot.annotOwn (hB, 4) iprop(⌜AxSpinProt7b.lwF (gtAdGd GT).gdG⌝)) -∗
      ∀ rs : RegFile, @tierAWpd GF hlc _ _ (splPol GT) (gtAdGd GT) spinN Unit
        (spinOb5 ya xa [ca] cv5) nm ⟨hp cpu hlt rs, 10⟩ .MaybeStuck hB
        (fun _ => iprop(⌜QB5 (gtAdGd GT).gdG tx vx⌝)) := by
  have h4 : get? ({[((hB, 4) : Geid) := iprop(⌜AxSpinProt7b.lwF (gtAdGd GT).gdG⌝)]} : Mea GF)
      (hB, 3) = none := lookupSingletonNe (by decide)
  have h0 : get? (insert ({[((hB, 4) : Geid) := iprop(⌜AxSpinProt7b.lwF (gtAdGd GT).gdG⌝)]} :
      Mea GF) (hB, 3) iprop(⌜AxSpinProt7b.plF (gtAdGd GT).gdG tx vx⌝)) (hB, 0) = none := by
    rw [lookupInsertNe (by decide)]
    exact lookupSingletonNe (by decide)
  have Hm : ∀ e, e ∈ (FiniteMap.dom_set (insert (insert
      ({[((hB, 4) : Geid) := iprop(⌜AxSpinProt7b.lwF (gtAdGd GT).gdG⌝)]} : Mea GF) (hB, 3)
        iprop(⌜AxSpinProt7b.plF (gtAdGd GT).gdG tx vx⌝)) (hB, 0)
        iprop(⌜rdFact [ca] cv5 (gtAdGd GT).gdG (hB, 0)⌝)) : GSet Geid) → e.1 = hB := by
    intro e He
    rw [domInsert, domInsert, domSingleton] at He
    rcases elemOfUnion.1 He with H | H
    · rw [elemOfSingleton.1 H]
    rcases elemOfUnion.1 H with H | H <;> rw [elemOfSingleton.1 H]
  have HRQ : ([∗map] R ∈ (insert (insert
      ({[((hB, 4) : Geid) := iprop(⌜AxSpinProt7b.lwF (gtAdGd GT).gdG⌝)]} : Mea GF) (hB, 3)
        iprop(⌜AxSpinProt7b.plF (gtAdGd GT).gdG tx vx⌝)) (hB, 0)
        iprop(⌜rdFact [ca] cv5 (gtAdGd GT).gdG (hB, 0)⌝)), R) ⊢
      ⌜QB5 (gtAdGd GT).gdG tx vx⌝ := by
    iintro H
    icases (BigSepM.bigSepM_insert h0).1 $$ H with ⟨%H0, H⟩
    icases (BigSepM.bigSepM_insert h4).1 $$ H with ⟨%H3, H⟩
    ihave %H4 := (BigSepM.bigSepM_singleton (M := GMapF Geid)).1 $$ H
    ipureintro
    exact ⟨H3, H4, H0⟩
  have Hmk : iprop(AxAnnot.annotOwn (GF := GF) (hB, 0)
        iprop(⌜rdFact [ca] cv5 (gtAdGd GT).gdG (hB, 0)⌝) ∗
      AxAnnot.annotOwn (hB, 3) iprop(⌜AxSpinProt7b.plF (gtAdGd GT).gdG tx vx⌝) ∗
      AxAnnot.annotOwn (hB, 4) iprop(⌜AxSpinProt7b.lwF (gtAdGd GT).gdG⌝)) ⊢
      [∗map] e ↦ P ∈ (insert (insert
        ({[((hB, 4) : Geid) := iprop(⌜AxSpinProt7b.lwF (gtAdGd GT).gdG⌝)]} : Mea GF) (hB, 3)
          iprop(⌜AxSpinProt7b.plF (gtAdGd GT).gdG tx vx⌝)) (hB, 0)
          iprop(⌜rdFact [ca] cv5 (gtAdGd GT).gdG (hB, 0)⌝)), AxAnnot.annotOwn e P := by
    iintro ⟨H0, H3, H4⟩
    iapply (BigSepM.bigSepM_insert h0).2
    isplitl [H0]
    · iexact H0
    iapply (BigSepM.bigSepM_insert h4).2
    isplitl [H3]
    · iexact H3
    iapply BigSepM.bigSepM_singleton.2
    iexact H4
  iintro HF
  ihave Hm' := Hmk $$ HF
  iapply (shHltReadbackM (hlc := hlc) (pol := splPol GT) (gtAdGd GT) spinN Unit
    (spinOb5 ya xa [ca] cv5) nm cpu hB 10 _ Hm _ HRQ) $$ Hm'

theorem AxSpinProt7.wB9 (GT : GdexecT) (nm : spinN) (cpu : CPU)
    (Hcons : rvwmoCatConsistent (gtAdGd GT)) (tc : Nat) (vc : BitVec 8) (t1 t2 tx : Nat)
    (vx : BitVec 8) (tl : Nat) (vl : BitVec 8) (t3 : Nat)
    (Hrow : AxOpsem.grow (gtAdGd GT) hB = b5Row tc vc t1 t2 tx vx tl vl t3) :
    ⊢ isLock (GF := GF) nm.2 ya (spinR5 xa [ca] nm (gtAdGd GT)) -∗
      AxAnnot.annotOwn (hB, 7)
        iprop(locked nm.2 ya hB (hB, 7) ∗ spinR5 xa [ca] nm (gtAdGd GT) (hB, 7)) -∗
      iprop(AxAnnot.annotOwn (hB, 0) iprop(⌜rdFact [ca] cv5 (gtAdGd GT).gdG (hB, 0)⌝) ∗
        AxAnnot.annotOwn (hB, 3) iprop(⌜AxSpinProt7b.plF (gtAdGd GT).gdG tx vx⌝) ∗
        AxAnnot.annotOwn (hB, 4) iprop(⌜AxSpinProt7b.lwF (gtAdGd GT).gdG⌝)) -∗
      ∀ rs : RegFile, @tierAWpd GF hlc _ _ (splPol GT) (gtAdGd GT) spinN Unit
        (spinOb5 ya xa [ca] cv5) nm ⟨hp cpu (relM hlt) rs, 9⟩ .MaybeStuck hB
        (fun _ => iprop(⌜QB5 (gtAdGd GT).gdG tx vx⌝)) := by
  have Hne : 9 ≠ (AxOpsem.grow (gtAdGd GT) hB).length := by rw [Hrow]; simp [b5Row]
  have Hl7 := b5L (gtAdGd GT) tc vc t1 t2 tx vx tl vl t3 Hrow 7 _ rfl
  have Hl9 := b5L (gtAdGd GT) tc vc t1 t2 tx vx tl vl t3 Hrow 9 _ rfl
  have H := shPos (hlc := hlc) (pol := splPol GT) (gtAdGd GT) spinN Unit (spinOb5 ya xa [ca] cv5)
    nm cpu hB (fun _ => iprop(⌜QB5 (gtAdGd GT).gdG tx vx⌝))
    iprop(isLock (GF := GF) nm.2 ya (spinR5 xa [ca] nm (gtAdGd GT)) ∗
      AxAnnot.annotOwn (hB, 7)
        iprop(locked nm.2 ya hB (hB, 7) ∗ spinR5 xa [ca] nm (gtAdGd GT) (hB, 7)) ∗
      AxAnnot.annotOwn (hB, 0) iprop(⌜rdFact [ca] cv5 (gtAdGd GT).gdG (hB, 0)⌝) ∗
      AxAnnot.annotOwn (hB, 3) iprop(⌜AxSpinProt7b.plF (gtAdGd GT).gdG tx vx⌝) ∗
      AxAnnot.annotOwn (hB, 4) iprop(⌜AxSpinProt7b.lwF (gtAdGd GT).gdG⌝))
    9 (relM hlt) Hne
    (fun rs id K => noReadAtWrite cpu _ ypaM ypaMRam b0 hlt rs 9 id K)
    (fun rs l s' Hst => by
      obtain ⟨rfl, Hs', -⟩ := writeInv2 cpu _ ypaM ypaMRam b0 hlt rs 9 l s' Hst
      simp only [wlWdata]
      subst Hs'
      obtain ⟨Hzw, Hsg⟩ := gwbStore _ _ _ _ _ Hl9
      have Hval : graphData (gtAdGd GT) (hB, 9) = some (WeakInterpProj.wbytes 1 b0) := by
        unfold graphData; rw [Hl9]; simp [lblData, l3pWbytes1]
      have Hin : ((hB, 7) : Geid) ∈ @Axpol.lobp (splPol GT) (gtAdGd GT) (hB, 9) :=
        acqLobp (gtAdGd GT) Hcons hB 7 9 _ _ _ _ _ _ Hl7 Hl9 rfl (by decide)
      have Hob : gobCat (gtAdGd GT) (hB, 7) (hB, 9) :=
        acqGob (gtAdGd GT) hB 7 9 _ _ _ _ _ _ Hl7 Hl9 rfl (by decide)
      have Hsplit : ⊢ ([∗map] Rin ∈ ({[((hB, 7) : Geid) := iprop(locked (GF := GF) nm.2 ya hB (hB, 7)
          ∗ spinR5 xa [ca] nm (gtAdGd GT) (hB, 7))]} : Mea GF), Rin) -∗
          iprop(locked nm.2 ya hB (hB, 7) ∗ [∗list] Rj ∈ [RL (GF := GF) nm.1 (gtAdGd GT) [xa],
            RL nm.1 (gtAdGd GT) [ca]], ∃ a, ⌜gobCat (gtAdGd GT) a (hB, 9)⌝ ∗ Rj a) := by
        iintro H
        ihave H := (BigSepM.bigSepM_singleton (M := GMapF Geid)).1 $$ H
        icases H with ⟨Hlk, HR⟩
        iunfold spinR5 at HR
        icases HR with ⟨HX, HC⟩
        isplitl [Hlk]
        · iexact Hlk
        isplitl [HX]
        · iexists (hB, 7)
          isplitr
          · ipureintro; exact Hob
          · iexact HX
        · iapply BigSepL.bigSepL_singleton.2
          iexists (hB, 7)
          isplitr
          · ipureintro; exact Hob
          · iexact HC
      iintro ⟨#Hil, Hp, HF⟩
      ihave Hw := Hsplit
      ihave Hfe := (fe5Release' (hlc := hlc) ya xa [ca] cv5 GT nm Hcons yaNX5 (hB, 9) hB (hB, 7)
        (spinR5 xa [ca] nm (gtAdGd GT))
        [RL (GF := GF) nm.1 (gtAdGd GT) [xa], RL nm.1 (gtAdGd GT) [ca]]
        ({[((hB, 7) : Geid) := iprop(locked (GF := GF) nm.2 ya hB (hB, 7)
          ∗ spinR5 xa [ca] nm (gtAdGd GT) (hB, 7))]} : Mea GF) Hzw
        (fun t v => storeNoRead _ _ _ _ _ _ _ _ Hl9) (fun a v H => (Hsg a v H).1)
        (HF5 nm (gtAdGd GT) Hcons) (HRs5 nm (gtAdGd GT) (hB, 9))) $$ Hil Hw
      iapply (evDraw (hlc := hlc) (pol := splPol GT) (gtAdGd GT) spinN Unit
        (spinOb5 ya xa [ca] cv5) nm (splAxpolWf GT) hB 9 (hB, 7) _ (notheld nm.2 ya hB)
        iprop(True) _ _ Hval Hin) $$ Hp [Hfe]
      · iapply (@flowEqDynMono hlc GF _ (shG (gtAdGd GT) spinN Unit (spinOb5 ya xa [ca] cv5) nm)
          (splPol GT) (gtAdGd GT) (hB, 9) _ _ (notheld nm.2 ya hB)
          iprop(notheld nm.2 ya hB ∗ True)) $$ [] Hfe
        inext
        iintro H
        isplitl [H]
        · iexact H
        · itrivial
      iintro _ _
      iapply (AxSpinProt7.wB10 (hlc := hlc) GT nm cpu tx vx) $$ HF %rs)
  iintro #Hil Hp HF
  iapply H $$ [$Hil $Hp $HF]

theorem AxSpinProt7.wB8 (GT : GdexecT) (nm : spinN) (cpu : CPU)
    (Hcons : rvwmoCatConsistent (gtAdGd GT)) (tc : Nat) (vc : BitVec 8) (t1 t2 tx : Nat)
    (vx : BitVec 8) (tl : Nat) (vl : BitVec 8) (t3 : Nat)
    (Hrow : AxOpsem.grow (gtAdGd GT) hB = b5Row tc vc t1 t2 tx vx tl vl t3) :
    ⊢ isLock (GF := GF) nm.2 ya (spinR5 xa [ca] nm (gtAdGd GT)) -∗
      AxAnnot.annotOwn (hB, 7)
        iprop(locked nm.2 ya hB (hB, 7) ∗ spinR5 xa [ca] nm (gtAdGd GT) (hB, 7)) -∗
      iprop(AxAnnot.annotOwn (hB, 0) iprop(⌜rdFact [ca] cv5 (gtAdGd GT).gdG (hB, 0)⌝) ∗
        AxAnnot.annotOwn (hB, 3) iprop(⌜AxSpinProt7b.plF (gtAdGd GT).gdG tx vx⌝) ∗
        AxAnnot.annotOwn (hB, 4) iprop(⌜AxSpinProt7b.lwF (gtAdGd GT).gdG⌝)) -∗
      ∀ rs : RegFile, @tierAWpd GF hlc _ _ (splPol GT) (gtAdGd GT) spinN Unit
        (spinOb5 ya xa [ca] cv5) nm ⟨hp cpu (fenceM (relM hlt)) rs, 8⟩ .MaybeStuck hB
        (fun _ => iprop(⌜QB5 (gtAdGd GT).gdG tx vx⌝)) := by
  have Hne : 8 ≠ (AxOpsem.grow (gtAdGd GT) hB).length := by rw [Hrow]; simp [b5Row]
  have H := shPos (hlc := hlc) (pol := splPol GT) (gtAdGd GT) spinN Unit (spinOb5 ya xa [ca] cv5)
    nm cpu hB (fun _ => iprop(⌜QB5 (gtAdGd GT).gdG tx vx⌝))
    iprop(isLock (GF := GF) nm.2 ya (spinR5 xa [ca] nm (gtAdGd GT)) ∗
      AxAnnot.annotOwn (hB, 7)
        iprop(locked nm.2 ya hB (hB, 7) ∗ spinR5 xa [ca] nm (gtAdGd GT) (hB, 7)) ∗
      AxAnnot.annotOwn (hB, 0) iprop(⌜rdFact [ca] cv5 (gtAdGd GT).gdG (hB, 0)⌝) ∗
      AxAnnot.annotOwn (hB, 3) iprop(⌜AxSpinProt7b.plF (gtAdGd GT).gdG tx vx⌝) ∗
      AxAnnot.annotOwn (hB, 4) iprop(⌜AxSpinProt7b.lwF (gtAdGd GT).gdG⌝))
    8 (fenceM (relM hlt)) Hne
    (fun rs id K => noReadAtFence cpu _ (relM hlt) rs 8 id K)
    (fun rs l s' Hst => by
      obtain ⟨rfl, Hs', -⟩ := fenceInv2 cpu _ (relM hlt) rs 8 l s' Hst
      simp only [wlWdata]
      subst Hs'
      iintro ⟨#Hil, Hp, HF⟩
      iapply (shSkip2 (GF := GF) (gtAdGd GT) spinN Unit (spinOb5 ya xa [ca] cv5) nm hB _ _)
      inext
      iapply (AxSpinProt7.wB9 (hlc := hlc) GT nm cpu Hcons tc vc t1 t2 tx vx tl vl t3 Hrow)
        $$ Hil Hp HF %rs)
  iintro #Hil Hp HF
  iapply H $$ [$Hil $Hp $HF]

/-- RE-ACQUIRE: `notheld` comes from the annotation of B's OWN release `(B,6)` (REQUIRED (2);
`relClaimLobp`). -/
theorem wB7w (GT : GdexecT) (nm : spinN) (cpu : CPU)
    (Hcons : rvwmoCatConsistent (gtAdGd GT)) (tc : Nat) (vc : BitVec 8) (t1 t2 tx : Nat)
    (vx : BitVec 8) (tl : Nat) (vl : BitVec 8) (t3 : Nat)
    (Hrow : AxOpsem.grow (gtAdGd GT) hB = b5Row tc vc t1 t2 tx vx tl vl t3) :
    ⊢ isLock (GF := GF) nm.2 ya (spinR5 xa [ca] nm (gtAdGd GT)) -∗
      AxAnnot.annotOwn (hB, 6) (notheld nm.2 ya hB) -∗
      iprop(AxAnnot.annotOwn (hB, 0) iprop(⌜rdFact [ca] cv5 (gtAdGd GT).gdG (hB, 0)⌝) ∗
        AxAnnot.annotOwn (hB, 3) iprop(⌜AxSpinProt7b.plF (gtAdGd GT).gdG tx vx⌝) ∗
        AxAnnot.annotOwn (hB, 4) iprop(⌜AxSpinProt7b.lwF (gtAdGd GT).gdG⌝)) -∗
      ∀ rs : RegFile, @tierAWpd GF hlc _ _ (splPol GT) (gtAdGd GT) spinN Unit
        (spinOb5 ya xa [ca] cv5) nm ⟨hp cpu (acqW (fenceM (relM hlt)) hlt b0) rs, 7⟩
        .MaybeStuck hB (fun _ => iprop(⌜QB5 (gtAdGd GT).gdG tx vx⌝)) := by
  have Hne : 7 ≠ (AxOpsem.grow (gtAdGd GT) hB).length := by rw [Hrow]; simp [b5Row]
  have Hl6 := b5L (gtAdGd GT) tc vc t1 t2 tx vx tl vl t3 Hrow 6 _ rfl
  have Hl7 := b5L (gtAdGd GT) tc vc t1 t2 tx vx tl vl t3 Hrow 7 _ rfl
  obtain ⟨Hrd, Hw, Hsg, -⟩ := gwbRmw _ _ _ _ _ _ _ Hl7
  have Hval : graphData (gtAdGd GT) (hB, 7) = some (WeakInterpProj.wbytes 1 b1) := by
    unfold graphData; rw [Hl7]; simp [lblData, l3pWbytes1]
  have Hcl : lkClaim ya (gtAdGd GT).gdG (hB, 7) (gwriteAt (gtAdGd GT).gdG t3) :=
    ⟨t3, Hrd, rfl, Hw⟩
  have Hin : ((hB, 6) : Geid) ∈ @Axpol.lobp (splPol GT) (gtAdGd GT) (hB, 7) := by
    obtain ⟨Hz6, -⟩ := gwbStore _ _ _ _ _ Hl6
    exact relClaimLobp (gtAdGd GT) Hcons ya (hB, 6) (hB, 7) _ _ Hl6 rfl Hz6
      (gpoRow (gtAdGd GT) hB 6 7 _ _ Hl6 Hl7 (by decide)) Hcl
  have H := shRmwWrite (hlc := hlc) (pol := splPol GT) (gtAdGd GT) spinN Unit
    (spinOb5 ya xa [ca] cv5) nm cpu hB (fun _ => iprop(⌜QB5 (gtAdGd GT).gdG tx vx⌝)) ypaM ypaMRam
    (if b0 = b0 then fenceM (relM hlt) else hlt) 7 Hne
    iprop(isLock (GF := GF) nm.2 ya (spinR5 xa [ca] nm (gtAdGd GT)) ∗
      AxAnnot.annotOwn (hB, 6) (notheld nm.2 ya hB) ∗
      AxAnnot.annotOwn (hB, 0) iprop(⌜rdFact [ca] cv5 (gtAdGd GT).gdG (hB, 0)⌝) ∗
      AxAnnot.annotOwn (hB, 3) iprop(⌜AxSpinProt7b.plF (gtAdGd GT).gdG tx vx⌝) ∗
      AxAnnot.annotOwn (hB, 4) iprop(⌜AxSpinProt7b.lwF (gtAdGd GT).gdG⌝))
    (fun rs => by
      have Hsing : ⊢ ([∗map] Rin ∈ ({[((hB, 6) : Geid) := notheld (GF := GF) nm.2 ya hB]} :
          Mea GF), Rin) -∗ iprop(notheld (GF := GF) nm.2 ya hB ∗ True) := by
        iintro H
        ihave H := (BigSepM.bigSepM_singleton (M := GMapF Geid)).1 $$ H
        isplitl [H]
        · iexact H
        · itrivial
      iintro ⟨#Hil, Hp, HF⟩
      ihave Hw := Hsing
      ihave Hfe := (fe5Claim' (hlc := hlc) ya xa [ca] cv5 GT nm Hcons yaNX5 (hB, 7)
        (gwriteAt (gtAdGd GT).gdG t3) iprop(True)
        ({[((hB, 6) : Geid) := notheld (GF := GF) nm.2 ya hB]} : Mea GF) Hcl
        (fun a v H => (Hsg a v H).1)) $$ Hil Hw
      iapply (evDraw (hlc := hlc) (pol := splPol GT) (gtAdGd GT) spinN Unit
        (spinOb5 ya xa [ca] cv5) nm (splAxpolWf GT) hB 7 (hB, 6) _
        iprop(locked nm.2 ya hB (hB, 7) ∗ spinR5 xa [ca] nm (gtAdGd GT) (hB, 7)) iprop(True) _ _
        Hval Hin) $$ Hp Hfe
      iintro Hp _
      rw [if_pos rfl]
      iapply (AxSpinProt7.wB8 (hlc := hlc) GT nm cpu Hcons tc vc t1 t2 tx vx tl vl t3 Hrow)
        $$ Hil Hp HF %rs)
  iintro #Hil Hp HF
  iapply H $$ [$Hil $Hp $HF]

theorem wB7r (GT : GdexecT) (nm : spinN) (cpu : CPU)
    (Hcons : rvwmoCatConsistent (gtAdGd GT)) (tc : Nat) (vc : BitVec 8) (t1 t2 tx : Nat)
    (vx : BitVec 8) (tl : Nat) (vl : BitVec 8) (t3 : Nat)
    (Hrow : AxOpsem.grow (gtAdGd GT) hB = b5Row tc vc t1 t2 tx vx tl vl t3) :
    ⊢ isLock (GF := GF) nm.2 ya (spinR5 xa [ca] nm (gtAdGd GT)) -∗
      AxAnnot.annotOwn (hB, 6) (notheld nm.2 ya hB) -∗
      iprop(AxAnnot.annotOwn (hB, 0) iprop(⌜rdFact [ca] cv5 (gtAdGd GT).gdG (hB, 0)⌝) ∗
        AxAnnot.annotOwn (hB, 3) iprop(⌜AxSpinProt7b.plF (gtAdGd GT).gdG tx vx⌝) ∗
        AxAnnot.annotOwn (hB, 4) iprop(⌜AxSpinProt7b.lwF (gtAdGd GT).gdG⌝)) -∗
      ∀ rs : RegFile, @tierAWpd GF hlc _ _ (splPol GT) (gtAdGd GT) spinN Unit
        (spinOb5 ya xa [ca] cv5) nm ⟨hp cpu b5Acq2 rs, 7⟩ .MaybeStuck hB
        (fun _ => iprop(⌜QB5 (gtAdGd GT).gdG tx vx⌝)) := by
  have Hne : 7 ≠ (AxOpsem.grow (gtAdGd GT) hB).length := by rw [Hrow]; simp [b5Row]
  have Hl7 : (AxOpsem.grow (gtAdGd GT) hB)[7]? =
      some (.LRmw true false (paZ ypaM) [t3] [b0] [b1] .WCplain) := by rw [Hrow]; rfl
  have H := shRmwRead (hlc := hlc) (pol := splPol GT) (gtAdGd GT) spinN Unit
    (spinOb5 ya xa [ca] cv5) nm cpu hB (fun _ => iprop(⌜QB5 (gtAdGd GT).gdG tx vx⌝)) ypaM ypaMRam
    (acqK (fenceM (relM hlt)) hlt) 7 t3 b0 .WCplain Hne Hl7
    iprop(isLock (GF := GF) nm.2 ya (spinR5 xa [ca] nm (gtAdGd GT)) ∗
      AxAnnot.annotOwn (hB, 6) (notheld nm.2 ya hB) ∗
      AxAnnot.annotOwn (hB, 0) iprop(⌜rdFact [ca] cv5 (gtAdGd GT).gdG (hB, 0)⌝) ∗
      AxAnnot.annotOwn (hB, 3) iprop(⌜AxSpinProt7b.plF (gtAdGd GT).gdG tx vx⌝) ∗
      AxAnnot.annotOwn (hB, 4) iprop(⌜AxSpinProt7b.lwF (gtAdGd GT).gdG⌝))
    (fun rs => by
      iintro ⟨#Hil, Hp, HF⟩
      rw [AxSpinProt7.acqKOk]
      iapply (wB7w (hlc := hlc) GT nm cpu Hcons tc vc t1 t2 tx vx tl vl t3 Hrow) $$ Hil Hp HF %rs)
  iintro #Hil Hp HF
  iapply H $$ [$Hil $Hp $HF]

/-- FIRST RELEASE: the two components drawn from `(B,3)` (both anchored at the claim `(B,2)`),
`locked` from `(B,4)`. -/
theorem AxSpinProt7.wB6 (GT : GdexecT) (nm : spinN) (cpu : CPU)
    (Hcons : rvwmoCatConsistent (gtAdGd GT)) (tc : Nat) (vc : BitVec 8) (t1 t2 tx : Nat)
    (vx : BitVec 8) (tl : Nat) (vl : BitVec 8) (t3 : Nat)
    (Hrow : AxOpsem.grow (gtAdGd GT) hB = b5Row tc vc t1 t2 tx vx tl vl t3) :
    ⊢ isLock (GF := GF) nm.2 ya (spinR5 xa [ca] nm (gtAdGd GT)) -∗
      AxAnnot.annotOwn (hB, 3)
        iprop(RL nm.1 (gtAdGd GT) [ca] (hB, 2) ∗ RL nm.1 (gtAdGd GT) [xa] (hB, 2)) -∗
      AxAnnot.annotOwn (hB, 4) iprop(locked nm.2 ya hB (hB, 2) ∗ True) -∗
      iprop(AxAnnot.annotOwn (hB, 0) iprop(⌜rdFact [ca] cv5 (gtAdGd GT).gdG (hB, 0)⌝) ∗
        AxAnnot.annotOwn (hB, 3) iprop(⌜AxSpinProt7b.plF (gtAdGd GT).gdG tx vx⌝) ∗
        AxAnnot.annotOwn (hB, 4) iprop(⌜AxSpinProt7b.lwF (gtAdGd GT).gdG⌝)) -∗
      ∀ rs : RegFile, @tierAWpd GF hlc _ _ (splPol GT) (gtAdGd GT) spinN Unit
        (spinOb5 ya xa [ca] cv5) nm ⟨hp cpu (relM b5Acq2) rs, 6⟩ .MaybeStuck hB
        (fun _ => iprop(⌜QB5 (gtAdGd GT).gdG tx vx⌝)) := by
  have Hne : 6 ≠ (AxOpsem.grow (gtAdGd GT) hB).length := by rw [Hrow]; simp [b5Row]
  have Hl2 := b5L (gtAdGd GT) tc vc t1 t2 tx vx tl vl t3 Hrow 2 _ rfl
  have Hl3 := b5L (gtAdGd GT) tc vc t1 t2 tx vx tl vl t3 Hrow 3 _ rfl
  have Hl4 := b5L (gtAdGd GT) tc vc t1 t2 tx vx tl vl t3 Hrow 4 _ rfl
  have Hl5 := b5L (gtAdGd GT) tc vc t1 t2 tx vx tl vl t3 Hrow 5 _ rfl
  have Hl6 := b5L (gtAdGd GT) tc vc t1 t2 tx vx tl vl t3 Hrow 6 _ rfl
  have hnone : get? ({[((hB, 4) : Geid) := iprop(locked (GF := GF) nm.2 ya hB (hB, 2) ∗ True)]} :
      Mea GF) (hB, 3) = none := lookupSingletonNe (by decide)
  have Hmk : ⊢ AxAnnot.annotOwn (GF := GF) (hB, 3)
        iprop(RL nm.1 (gtAdGd GT) [ca] (hB, 2) ∗ RL nm.1 (gtAdGd GT) [xa] (hB, 2)) -∗
      AxAnnot.annotOwn (hB, 4) iprop(locked nm.2 ya hB (hB, 2) ∗ True) -∗
      [∗map] e ↦ P ∈ (insert
        {[((hB, 4) : Geid) := iprop(locked (GF := GF) nm.2 ya hB (hB, 2) ∗ True)]} (hB, 3)
        iprop(RL nm.1 (gtAdGd GT) [ca] (hB, 2) ∗ RL nm.1 (gtAdGd GT) [xa] (hB, 2)) : Mea GF),
        AxAnnot.annotOwn e P := by
    iintro Ha Hb
    iapply (BigSepM.bigSepM_insert hnone).2
    isplitl [Ha]
    · iexact Ha
    · iapply BigSepM.bigSepM_singleton.2
      iexact Hb
  have H := shPos (hlc := hlc) (pol := splPol GT) (gtAdGd GT) spinN Unit (spinOb5 ya xa [ca] cv5)
    nm cpu hB (fun _ => iprop(⌜QB5 (gtAdGd GT).gdG tx vx⌝))
    iprop(isLock (GF := GF) nm.2 ya (spinR5 xa [ca] nm (gtAdGd GT)) ∗
      AxAnnot.annotOwn (hB, 3)
        iprop(RL nm.1 (gtAdGd GT) [ca] (hB, 2) ∗ RL nm.1 (gtAdGd GT) [xa] (hB, 2)) ∗
      AxAnnot.annotOwn (hB, 4) iprop(locked nm.2 ya hB (hB, 2) ∗ True) ∗
      AxAnnot.annotOwn (hB, 0) iprop(⌜rdFact [ca] cv5 (gtAdGd GT).gdG (hB, 0)⌝) ∗
      AxAnnot.annotOwn (hB, 3) iprop(⌜AxSpinProt7b.plF (gtAdGd GT).gdG tx vx⌝) ∗
      AxAnnot.annotOwn (hB, 4) iprop(⌜AxSpinProt7b.lwF (gtAdGd GT).gdG⌝))
    6 (relM b5Acq2) Hne
    (fun rs id K => noReadAtWrite cpu _ ypaM ypaMRam b0 b5Acq2 rs 6 id K)
    (fun rs l s' Hst => by
      obtain ⟨rfl, Hs', -⟩ := writeInv2 cpu _ ypaM ypaMRam b0 b5Acq2 rs 6 l s' Hst
      simp only [wlWdata]
      subst Hs'
      obtain ⟨Hzw, Hsg⟩ := gwbStore _ _ _ _ _ Hl6
      have Hval : graphData (gtAdGd GT) (hB, 6) = some (WeakInterpProj.wbytes 1 b0) := by
        unfold graphData; rw [Hl6]; simp [lblData, l3pWbytes1]
      have Hob : gobCat (gtAdGd GT) (hB, 2) (hB, 6) :=
        acqGob (gtAdGd GT) hB 2 6 _ _ _ _ _ _ Hl2 Hl6 rfl (by decide)
      have H3 : ((hB, 3) : Geid) ∈ @Axpol.lobp (splPol GT) (gtAdGd GT) (hB, 6) :=
        fenceLobp (gtAdGd GT) Hcons hB 3 5 6 _ _ _ _ Hl3 rfl Hl5 Hl6 (by decide) (by decide)
      have H4 : ((hB, 4) : Geid) ∈ @Axpol.lobp (splPol GT) (gtAdGd GT) (hB, 6) :=
        fenceLobp (gtAdGd GT) Hcons hB 4 5 6 _ _ _ _ Hl4 rfl Hl5 Hl6 (by decide) (by decide)
      have Hsub : (FiniteMap.dom_set (insert
          {[((hB, 4) : Geid) := iprop(locked (GF := GF) nm.2 ya hB (hB, 2) ∗ True)]} (hB, 3)
          iprop(RL nm.1 (gtAdGd GT) [ca] (hB, 2) ∗ RL nm.1 (gtAdGd GT) [xa] (hB, 2)) : Mea GF) :
            GSet Geid) ⊆ @Axpol.lobp (splPol GT) (gtAdGd GT) (hB, 6) := by
        rw [domInsert, domSingleton]
        intro x hx
        rcases elemOfUnion.1 hx with h | h
        · rw [elemOfSingleton.1 h]; exact H3
        · rw [elemOfSingleton.1 h]; exact H4
      have Hsplit : ⊢ ([∗map] Rin ∈ (insert
          {[((hB, 4) : Geid) := iprop(locked (GF := GF) nm.2 ya hB (hB, 2) ∗ True)]} (hB, 3)
          iprop(RL nm.1 (gtAdGd GT) [ca] (hB, 2) ∗ RL nm.1 (gtAdGd GT) [xa] (hB, 2)) : Mea GF),
            Rin) -∗
          iprop(locked nm.2 ya hB (hB, 2) ∗ [∗list] Rj ∈ [RL (GF := GF) nm.1 (gtAdGd GT) [xa],
            RL nm.1 (gtAdGd GT) [ca]], ∃ a, ⌜gobCat (gtAdGd GT) a (hB, 6)⌝ ∗ Rj a) := by
        iintro H
        icases (BigSepM.bigSepM_insert hnone).1 $$ H with ⟨⟨HC, HX⟩, H4⟩
        ihave H4 := (BigSepM.bigSepM_singleton (M := GMapF Geid)).1 $$ H4
        icases H4 with ⟨Hlk, -⟩
        isplitl [Hlk]
        · iexact Hlk
        isplitl [HX]
        · iexists (hB, 2)
          isplitr
          · ipureintro; exact Hob
          · iexact HX
        · iapply BigSepL.bigSepL_singleton.2
          iexists (hB, 2)
          isplitr
          · ipureintro; exact Hob
          · iexact HC
      iintro ⟨#Hil, H3, H4, HF⟩
      ihave Hm := Hmk $$ H3 H4
      ihave Hw := Hsplit
      ihave Hfe := (fe5Release' (hlc := hlc) ya xa [ca] cv5 GT nm Hcons yaNX5 (hB, 6) hB (hB, 2)
        (spinR5 xa [ca] nm (gtAdGd GT))
        [RL (GF := GF) nm.1 (gtAdGd GT) [xa], RL nm.1 (gtAdGd GT) [ca]]
        (insert
          {[((hB, 4) : Geid) := iprop(locked (GF := GF) nm.2 ya hB (hB, 2) ∗ True)]} (hB, 3)
          iprop(RL nm.1 (gtAdGd GT) [ca] (hB, 2) ∗ RL nm.1 (gtAdGd GT) [xa] (hB, 2)) : Mea GF)
        Hzw (fun t v => storeNoRead _ _ _ _ _ _ _ _ Hl6) (fun a v H => (Hsg a v H).1)
        (HF5 nm (gtAdGd GT) Hcons) (HRs5 nm (gtAdGd GT) (hB, 6))) $$ Hil Hw
      iapply (evDrawM (hlc := hlc) (pol := splPol GT) (gtAdGd GT) spinN Unit
        (spinOb5 ya xa [ca] cv5) nm (splAxpolWf GT) hB 6 _ (notheld nm.2 ya hB) iprop(True) _ _
        Hval Hsub) $$ Hm [Hfe]
      · iapply (@flowEqDynMono hlc GF _ (shG (gtAdGd GT) spinN Unit (spinOb5 ya xa [ca] cv5) nm)
          (splPol GT) (gtAdGd GT) (hB, 6) _ _ (notheld nm.2 ya hB)
          iprop(notheld nm.2 ya hB ∗ True)) $$ [] Hfe
        inext
        iintro H
        isplitl [H]
        · iexact H
        · itrivial
      iintro Hp _
      iapply (wB7r (hlc := hlc) GT nm cpu Hcons tc vc t1 t2 tx vx tl vl t3 Hrow) $$ Hil Hp HF %rs)
  iintro #Hil H3 H4 HF
  iapply H $$ [$Hil $H3 $H4 $HF]

theorem AxSpinProt7.wB5 (GT : GdexecT) (nm : spinN) (cpu : CPU)
    (Hcons : rvwmoCatConsistent (gtAdGd GT)) (tc : Nat) (vc : BitVec 8) (t1 t2 tx : Nat)
    (vx : BitVec 8) (tl : Nat) (vl : BitVec 8) (t3 : Nat)
    (Hrow : AxOpsem.grow (gtAdGd GT) hB = b5Row tc vc t1 t2 tx vx tl vl t3) :
    ⊢ isLock (GF := GF) nm.2 ya (spinR5 xa [ca] nm (gtAdGd GT)) -∗
      AxAnnot.annotOwn (hB, 3)
        iprop(RL nm.1 (gtAdGd GT) [ca] (hB, 2) ∗ RL nm.1 (gtAdGd GT) [xa] (hB, 2)) -∗
      AxAnnot.annotOwn (hB, 4) iprop(locked nm.2 ya hB (hB, 2) ∗ True) -∗
      iprop(AxAnnot.annotOwn (hB, 0) iprop(⌜rdFact [ca] cv5 (gtAdGd GT).gdG (hB, 0)⌝) ∗
        AxAnnot.annotOwn (hB, 3) iprop(⌜AxSpinProt7b.plF (gtAdGd GT).gdG tx vx⌝) ∗
        AxAnnot.annotOwn (hB, 4) iprop(⌜AxSpinProt7b.lwF (gtAdGd GT).gdG⌝)) -∗
      ∀ rs : RegFile, @tierAWpd GF hlc _ _ (splPol GT) (gtAdGd GT) spinN Unit
        (spinOb5 ya xa [ca] cv5) nm ⟨hp cpu (fenceM (relM b5Acq2)) rs, 5⟩ .MaybeStuck hB
        (fun _ => iprop(⌜QB5 (gtAdGd GT).gdG tx vx⌝)) := by
  have Hne : 5 ≠ (AxOpsem.grow (gtAdGd GT) hB).length := by rw [Hrow]; simp [b5Row]
  have H := shPos (hlc := hlc) (pol := splPol GT) (gtAdGd GT) spinN Unit (spinOb5 ya xa [ca] cv5)
    nm cpu hB (fun _ => iprop(⌜QB5 (gtAdGd GT).gdG tx vx⌝))
    iprop(isLock (GF := GF) nm.2 ya (spinR5 xa [ca] nm (gtAdGd GT)) ∗
      AxAnnot.annotOwn (hB, 3)
        iprop(RL nm.1 (gtAdGd GT) [ca] (hB, 2) ∗ RL nm.1 (gtAdGd GT) [xa] (hB, 2)) ∗
      AxAnnot.annotOwn (hB, 4) iprop(locked nm.2 ya hB (hB, 2) ∗ True) ∗
      AxAnnot.annotOwn (hB, 0) iprop(⌜rdFact [ca] cv5 (gtAdGd GT).gdG (hB, 0)⌝) ∗
      AxAnnot.annotOwn (hB, 3) iprop(⌜AxSpinProt7b.plF (gtAdGd GT).gdG tx vx⌝) ∗
      AxAnnot.annotOwn (hB, 4) iprop(⌜AxSpinProt7b.lwF (gtAdGd GT).gdG⌝))
    5 (fenceM (relM b5Acq2)) Hne
    (fun rs id K => noReadAtFence cpu _ (relM b5Acq2) rs 5 id K)
    (fun rs l s' Hst => by
      obtain ⟨rfl, Hs', -⟩ := fenceInv2 cpu _ (relM b5Acq2) rs 5 l s' Hst
      simp only [wlWdata]
      subst Hs'
      iintro ⟨#Hil, H3, H4, HF⟩
      iapply (shSkip2 (GF := GF) (gtAdGd GT) spinN Unit (spinOb5 ya xa [ca] cv5) nm hB _ _)
      inext
      iapply (AxSpinProt7.wB6 (hlc := hlc) GT nm cpu Hcons tc vc t1 t2 tx vx tl vl t3 Hrow)
        $$ Hil H3 H4 HF %rs)
  iintro #Hil H3 H4 HF
  iapply H $$ [$Hil $H3 $H4 $HF]

/-- THE HOLDER's `lw lk` (REQUIRED (3)): `locked` drawn from the claim (rule 5); the `≠ 0`
fact deposited AT THE READ. -/
theorem AxSpinProt7.wB4 (GT : GdexecT) (nm : spinN) (cpu : CPU)
    (Hcons : rvwmoCatConsistent (gtAdGd GT)) (tc : Nat) (vc : BitVec 8) (t1 t2 tx : Nat)
    (vx : BitVec 8) (tl : Nat) (vl : BitVec 8) (t3 : Nat)
    (Hrow : AxOpsem.grow (gtAdGd GT) hB = b5Row tc vc t1 t2 tx vx tl vl t3) :
    ⊢ isLock (GF := GF) nm.2 ya (spinR5 xa [ca] nm (gtAdGd GT)) -∗
      AxAnnot.annotOwn (hB, 2) (locked nm.2 ya hB (hB, 2)) -∗
      AxAnnot.annotOwn (hB, 3)
        iprop(RL nm.1 (gtAdGd GT) [ca] (hB, 2) ∗ RL nm.1 (gtAdGd GT) [xa] (hB, 2)) -∗
      AxAnnot.annotOwn (hB, 0) iprop(⌜rdFact [ca] cv5 (gtAdGd GT).gdG (hB, 0)⌝) -∗
      AxAnnot.annotOwn (hB, 3) iprop(⌜AxSpinProt7b.plF (gtAdGd GT).gdG tx vx⌝) -∗
      ∀ rs : RegFile, @tierAWpd GF hlc _ _ (splPol GT) (gtAdGd GT) spinN Unit
        (spinOb5 ya xa [ca] cv5) nm ⟨hp cpu (AxSpinProt7.ldM ypaM (fenceM (relM b5Acq2))) rs, 4⟩
        .MaybeStuck hB (fun _ => iprop(⌜QB5 (gtAdGd GT).gdG tx vx⌝)) := by
  have Hne : 4 ≠ (AxOpsem.grow (gtAdGd GT) hB).length := by rw [Hrow]; simp [b5Row]
  have Hadv : ∀ lb, (AxOpsem.grow (gtAdGd GT) hB)[4]? = some lb → aidentAdvRd (aident lb) = 1 := by
    rw [Hrow]
    intro lb h
    cases h
    rfl
  have Hl2 := b5L (gtAdGd GT) tc vc t1 t2 tx vx tl vl t3 Hrow 2 _ rfl
  have Hl4 := b5L (gtAdGd GT) tc vc t1 t2 tx vx tl vl t3 Hrow 4 _ rfl
  have H := shRead (hlc := hlc) (pol := splPol GT) (gtAdGd GT) spinN Unit (spinOb5 ya xa [ca] cv5)
    nm cpu hB (fun _ => iprop(⌜QB5 (gtAdGd GT).gdG tx vx⌝)) ypaM ypaMRam
    (fun _ => fenceM (relM b5Acq2)) 4 Hne Hadv
    iprop(isLock (GF := GF) nm.2 ya (spinR5 xa [ca] nm (gtAdGd GT)) ∗
      AxAnnot.annotOwn (hB, 2) (locked nm.2 ya hB (hB, 2)) ∗
      AxAnnot.annotOwn (hB, 3)
        iprop(RL nm.1 (gtAdGd GT) [ca] (hB, 2) ∗ RL nm.1 (gtAdGd GT) [xa] (hB, 2)) ∗
      AxAnnot.annotOwn (hB, 0) iprop(⌜rdFact [ca] cv5 (gtAdGd GT).gdG (hB, 0)⌝) ∗
      AxAnnot.annotOwn (hB, 3) iprop(⌜AxSpinProt7b.plF (gtAdGd GT).gdG tx vx⌝))
    (fun v b rs Hgv Hv => by
      subst Hv
      have Hnw : gisW (gtAdGd GT).gdG (hB, 4) = false := by unfold gisW; rw [Hl4]; rfl
      have Hpo : WeakRvwmoGraph.gpo (gtAdGd GT).gdG (hB, 2) (hB, 4) :=
        gpoRow (gtAdGd GT) hB 2 4 _ _ Hl2 Hl4 (by decide)
      have Hin : ((hB, 2) : Geid) ∈ @Axpol.lobp (splPol GT) (gtAdGd GT) (hB, 4) :=
        acqLobp (gtAdGd GT) Hcons hB 2 4 _ _ _ _ _ _ Hl2 Hl4 rfl (by decide)
      have Hsing : ⊢ ([∗map] Rin ∈ ({[((hB, 2) : Geid) := locked (GF := GF) nm.2 ya hB (hB, 2)]} :
          Mea GF), Rin) -∗ iprop(locked (GF := GF) nm.2 ya hB (hB, 2) ∗ True) := by
        iintro H
        ihave H := (BigSepM.bigSepM_singleton (M := GMapF Geid)).1 $$ H
        isplitl [H]
        · iexact H
        · itrivial
      iintro ⟨#Hil, H2, H3, H0, Hp3⟩
      ihave Hw := Hsing
      ihave Hfe := (fe5LkreadHeld (hlc := hlc) ya xa [ca] cv5 GT nm Hcons yaNX5 (hB, 4) hB (hB, 2)
        iprop(True) ({[((hB, 2) : Geid) := locked (GF := GF) nm.2 ya hB (hB, 2)]} : Mea GF)
        Hnw Hpo (b5Nolk (gtAdGd GT) tc vc t1 t2 tx vx tl vl t3 Hrow)) $$ Hw
      iapply (evDraw (hlc := hlc) (pol := splPol GT) (gtAdGd GT) spinN Unit
        (spinOb5 ya xa [ca] cv5) nm (splAxpolWf GT) hB 4 (hB, 2) _
        iprop(locked nm.2 ya hB (hB, 2) ∗ True)
        iprop(⌜AxSpinProt7b.lwF (gtAdGd GT).gdG⌝) _ _ Hgv Hin) $$ H2 Hfe
      iintro H4 Hf4
      iapply (AxSpinProt7.wB5 (hlc := hlc) GT nm cpu Hcons tc vc t1 t2 tx vx tl vl t3 Hrow)
        $$ Hil H3 H4 [$H0 $Hp3 $Hf4] %rs)
  iintro #Hil H2 H3 H0 Hp3
  iapply H $$ [$Hil $H2 $H3 $H0 $Hp3]

theorem AxSpinProt7.wB3 (GT : GdexecT) (nm : spinN) (cpu : CPU)
    (Hcons : rvwmoCatConsistent (gtAdGd GT)) (tc : Nat) (vc : BitVec 8) (t1 t2 tx : Nat)
    (vx : BitVec 8) (tl : Nat) (vl : BitVec 8) (t3 : Nat)
    (Hrow : AxOpsem.grow (gtAdGd GT) hB = b5Row tc vc t1 t2 tx vx tl vl t3) :
    ⊢ isLock (GF := GF) nm.2 ya (spinR5 xa [ca] nm (gtAdGd GT)) -∗
      AxAnnot.annotOwn (hB, 2) (locked nm.2 ya hB (hB, 2)) -∗
      AxAnnot.annotOwn (hB, 2) (spinR5 xa [ca] nm (gtAdGd GT) (hB, 2)) -∗
      AxAnnot.annotOwn (hB, 0) iprop(⌜rdFact [ca] cv5 (gtAdGd GT).gdG (hB, 0)⌝) -∗
      ∀ rs : RegFile, @tierAWpd GF hlc _ _ (splPol GT) (gtAdGd GT) spinN Unit
        (spinOb5 ya xa [ca] cv5) nm ⟨hp cpu b5Cs rs, 3⟩ .MaybeStuck hB
        (fun _ => iprop(⌜QB5 (gtAdGd GT).gdG tx vx⌝)) := by
  have Hne : 3 ≠ (AxOpsem.grow (gtAdGd GT) hB).length := by rw [Hrow]; simp [b5Row]
  have Hadv : ∀ lb, (AxOpsem.grow (gtAdGd GT) hB)[3]? = some lb → aidentAdvRd (aident lb) = 1 := by
    rw [Hrow]
    intro lb h
    cases h
    rfl
  have Hl2 := b5L (gtAdGd GT) tc vc t1 t2 tx vx tl vl t3 Hrow 2 _ rfl
  have Hl3 := b5L (gtAdGd GT) tc vc t1 t2 tx vx tl vl t3 Hrow 3 _ rfl
  have H := shRead (hlc := hlc) (pol := splPol GT) (gtAdGd GT) spinN Unit (spinOb5 ya xa [ca] cv5)
    nm cpu hB (fun _ => iprop(⌜QB5 (gtAdGd GT).gdG tx vx⌝)) xpaM xpaMRam
    (fun _ => AxSpinProt7.ldM ypaM (fenceM (relM b5Acq2))) 3 Hne Hadv
    iprop(isLock (GF := GF) nm.2 ya (spinR5 xa [ca] nm (gtAdGd GT)) ∗
      AxAnnot.annotOwn (hB, 2) (locked nm.2 ya hB (hB, 2)) ∗
      AxAnnot.annotOwn (hB, 2) (spinR5 xa [ca] nm (gtAdGd GT) (hB, 2)) ∗
      AxAnnot.annotOwn (hB, 0) iprop(⌜rdFact [ca] cv5 (gtAdGd GT).gdG (hB, 0)⌝))
    (fun v b rs Hgv Hv => by
      subst Hv
      have Hnw : gisW (gtAdGd GT).gdG (hB, 3) = false := by unfold gisW; rw [Hl3]; rfl
      have Hnr : ¬ lkread ya (gtAdGd GT).gdG (hB, 3) := by
        rintro ⟨⟨t, v, Hr⟩, -⟩
        exact xaNeYa (grbLoadOnly _ _ _ _ _ Hl3 _ _ _ Hr).1.symm
      have Hrd := grbLoad _ _ _ _ _ Hl3
      have Hlt : gmoLt (gtAdGd GT).gdG (hB, 2) (hB, 3) :=
        gobGmo (gtAdGd GT) Hcons _ _ (acqGob (gtAdGd GT) hB 2 3 _ _ _ _ _ _ Hl2 Hl3 rfl (by decide))
      have Hin : ((hB, 2) : Geid) ∈ @Axpol.lobp (splPol GT) (gtAdGd GT) (hB, 3) :=
        acqLobp (gtAdGd GT) Hcons hB 2 3 _ _ _ _ _ _ Hl2 Hl3 rfl (by decide)
      have Hsing : ⊢ ([∗map] Rin ∈ ({[((hB, 2) : Geid) :=
          spinR5 (GF := GF) xa [ca] nm (gtAdGd GT) (hB, 2)]} : Mea GF), Rin) -∗
          iprop(RL (GF := GF) nm.1 (gtAdGd GT) [ca] (hB, 2) ∗
            RL nm.1 (gtAdGd GT) [xa] (hB, 2)) := by
        iintro H
        ihave H := (BigSepM.bigSepM_singleton (M := GMapF Geid)).1 $$ H
        iunfold spinR5 at H
        icases H with ⟨HX, HC⟩
        isplitl [HC]
        · iexact HC
        · iexact HX
      iintro ⟨#Hil, H2, HR, H0⟩
      ihave Hw := Hsing
      ihave Hfe := (fe5Rbread (hlc := hlc) ya xa [ca] cv5 GT nm Hcons yaNX5 (hB, 3) (hB, 2) xa tx vx
        (RL (GF := GF) nm.1 (gtAdGd GT) [ca] (hB, 2))
        ({[((hB, 2) : Geid) := spinR5 (GF := GF) xa [ca] nm (gtAdGd GT) (hB, 2)]} : Mea GF)
        xaX5 Hnw Hnr (fun w v' Hw Hh => b5NoX (gtAdGd GT) tc vc t1 t2 tx vx tl vl t3 Hrow w v' Hw Hh)
        Hrd Hlt) $$ Hw
      iapply (evDraw (hlc := hlc) (pol := splPol GT) (gtAdGd GT) spinN Unit
        (spinOb5 ya xa [ca] cv5) nm (splAxpolWf GT) hB 3 (hB, 2) _
        iprop(RL nm.1 (gtAdGd GT) [ca] (hB, 2) ∗ RL nm.1 (gtAdGd GT) [xa] (hB, 2))
        iprop(⌜AxSpinProt7b.plF (gtAdGd GT).gdG tx vx⌝) _ _ Hgv Hin) $$ HR Hfe
      iintro H3 Hp3
      iapply (AxSpinProt7.wB4 (hlc := hlc) GT nm cpu Hcons tc vc t1 t2 tx vx tl vl t3 Hrow)
        $$ Hil H2 H3 H0 Hp3 %rs)
  iintro #Hil H2 HR H0
  iapply H $$ [$Hil $H2 $HR $H0]

theorem wB2w (GT : GdexecT) (nm : spinN) (cpu : CPU)
    (Hcons : rvwmoCatConsistent (gtAdGd GT)) (tc : Nat) (vc : BitVec 8) (t1 t2 tx : Nat)
    (vx : BitVec 8) (tl : Nat) (vl : BitVec 8) (t3 : Nat)
    (Hrow : AxOpsem.grow (gtAdGd GT) hB = b5Row tc vc t1 t2 tx vx tl vl t3) :
    ⊢ isLock (GF := GF) nm.2 ya (spinR5 xa [ca] nm (gtAdGd GT)) -∗ notheld nm.2 ya hB -∗
      AxAnnot.annotOwn (hB, 0) iprop(⌜rdFact [ca] cv5 (gtAdGd GT).gdG (hB, 0)⌝) -∗
      ∀ rs : RegFile, @tierAWpd GF hlc _ _ (splPol GT) (gtAdGd GT) spinN Unit
        (spinOb5 ya xa [ca] cv5) nm ⟨hp cpu (acqW b5Cs hlt b0) rs, 2⟩ .MaybeStuck hB
        (fun _ => iprop(⌜QB5 (gtAdGd GT).gdG tx vx⌝)) := by
  have Hne : 2 ≠ (AxOpsem.grow (gtAdGd GT) hB).length := by rw [Hrow]; simp [b5Row]
  have Hl2 := b5L (gtAdGd GT) tc vc t1 t2 tx vx tl vl t3 Hrow 2 _ rfl
  obtain ⟨Hrd, Hw, Hsg, -⟩ := gwbRmw _ _ _ _ _ _ _ Hl2
  have Hval : graphData (gtAdGd GT) (hB, 2) = some (WeakInterpProj.wbytes 1 b1) := by
    unfold graphData; rw [Hl2]; simp [lblData, l3pWbytes1]
  have H := shRmwWrite (hlc := hlc) (pol := splPol GT) (gtAdGd GT) spinN Unit
    (spinOb5 ya xa [ca] cv5) nm cpu hB (fun _ => iprop(⌜QB5 (gtAdGd GT).gdG tx vx⌝)) ypaM ypaMRam
    (if b0 = b0 then b5Cs else hlt) 2 Hne
    iprop(isLock (GF := GF) nm.2 ya (spinR5 xa [ca] nm (gtAdGd GT)) ∗ notheld nm.2 ya hB ∗
      AxAnnot.annotOwn (hB, 0) iprop(⌜rdFact [ca] cv5 (gtAdGd GT).gdG (hB, 0)⌝))
    (fun rs => by
      iintro ⟨#Hil, Hnh, H0⟩
      ihave Hfe := (fe5Claim (hlc := hlc) ya xa [ca] cv5 GT nm Hcons yaNX5 (hB, 2)
        (gwriteAt (gtAdGd GT).gdG t2) ⟨t2, Hrd, rfl, Hw⟩ (fun a v H => (Hsg a v H).1))
        $$ Hnh Hil
      iapply (evPlain (hlc := hlc) (pol := splPol GT) (gtAdGd GT) spinN Unit
        (spinOb5 ya xa [ca] cv5) nm hB 2 (locked nm.2 ya hB (hB, 2))
        (spinR5 xa [ca] nm (gtAdGd GT) (hB, 2)) _ _ Hval) $$ Hfe
      iintro H2 HR
      rw [if_pos rfl]
      iapply (AxSpinProt7.wB3 (hlc := hlc) GT nm cpu Hcons tc vc t1 t2 tx vx tl vl t3 Hrow)
        $$ Hil H2 HR H0 %rs)
  iintro #Hil Hnh H0
  iapply H $$ [$Hil $Hnh $H0]

theorem wB2r (GT : GdexecT) (nm : spinN) (cpu : CPU)
    (Hcons : rvwmoCatConsistent (gtAdGd GT)) (tc : Nat) (vc : BitVec 8) (t1 t2 tx : Nat)
    (vx : BitVec 8) (tl : Nat) (vl : BitVec 8) (t3 : Nat)
    (Hrow : AxOpsem.grow (gtAdGd GT) hB = b5Row tc vc t1 t2 tx vx tl vl t3) :
    ⊢ isLock (GF := GF) nm.2 ya (spinR5 xa [ca] nm (gtAdGd GT)) -∗ notheld nm.2 ya hB -∗
      AxAnnot.annotOwn (hB, 0) iprop(⌜rdFact [ca] cv5 (gtAdGd GT).gdG (hB, 0)⌝) -∗
      ∀ rs : RegFile, @tierAWpd GF hlc _ _ (splPol GT) (gtAdGd GT) spinN Unit
        (spinOb5 ya xa [ca] cv5) nm ⟨hp cpu (acqRmw b5Cs hlt) rs, 2⟩ .MaybeStuck hB
        (fun _ => iprop(⌜QB5 (gtAdGd GT).gdG tx vx⌝)) := by
  have Hne : 2 ≠ (AxOpsem.grow (gtAdGd GT) hB).length := by rw [Hrow]; simp [b5Row]
  have Hl2 : (AxOpsem.grow (gtAdGd GT) hB)[2]? =
      some (.LRmw true false (paZ ypaM) [t2] [b0] [b1] .WCplain) := by rw [Hrow]; rfl
  have H := shRmwRead (hlc := hlc) (pol := splPol GT) (gtAdGd GT) spinN Unit
    (spinOb5 ya xa [ca] cv5) nm cpu hB (fun _ => iprop(⌜QB5 (gtAdGd GT).gdG tx vx⌝)) ypaM ypaMRam
    (acqK b5Cs hlt) 2 t2 b0 .WCplain Hne Hl2
    iprop(isLock (GF := GF) nm.2 ya (spinR5 xa [ca] nm (gtAdGd GT)) ∗ notheld nm.2 ya hB ∗
      AxAnnot.annotOwn (hB, 0) iprop(⌜rdFact [ca] cv5 (gtAdGd GT).gdG (hB, 0)⌝))
    (fun rs => by
      iintro ⟨#Hil, Hnh, H0⟩
      rw [AxSpinProt7.acqKOk]
      iapply (wB2w (hlc := hlc) GT nm cpu Hcons tc vc t1 t2 tx vx tl vl t3 Hrow)
        $$ Hil Hnh H0 %rs)
  iintro #Hil Hnh H0
  iapply H $$ [$Hil $Hnh $H0]

/-- ACQUIRE-FAIL (the spin): neutral. -/
theorem AxSpinProt7.wB1w (GT : GdexecT) (nm : spinN) (cpu : CPU)
    (Hcons : rvwmoCatConsistent (gtAdGd GT)) (tc : Nat) (vc : BitVec 8) (t1 t2 tx : Nat)
    (vx : BitVec 8) (tl : Nat) (vl : BitVec 8) (t3 : Nat)
    (Hrow : AxOpsem.grow (gtAdGd GT) hB = b5Row tc vc t1 t2 tx vx tl vl t3) :
    ⊢ isLock (GF := GF) nm.2 ya (spinR5 xa [ca] nm (gtAdGd GT)) -∗ notheld nm.2 ya hB -∗
      AxAnnot.annotOwn (hB, 0) iprop(⌜rdFact [ca] cv5 (gtAdGd GT).gdG (hB, 0)⌝) -∗
      ∀ rs : RegFile, @tierAWpd GF hlc _ _ (splPol GT) (gtAdGd GT) spinN Unit
        (spinOb5 ya xa [ca] cv5) nm ⟨hp cpu (acqW b5Cs (acqRmw b5Cs hlt) b1) rs, 1⟩ .MaybeStuck hB
        (fun _ => iprop(⌜QB5 (gtAdGd GT).gdG tx vx⌝)) := by
  have Hne : 1 ≠ (AxOpsem.grow (gtAdGd GT) hB).length := by rw [Hrow]; simp [b5Row]
  have Hl1 := b5L (gtAdGd GT) tc vc t1 t2 tx vx tl vl t3 Hrow 1 _ rfl
  obtain ⟨Hrd, Hw, Hsg, -⟩ := gwbRmw _ _ _ _ _ _ _ Hl1
  have Hval : graphData (gtAdGd GT) (hB, 1) = some (WeakInterpProj.wbytes 1 b1) := by
    unfold graphData; rw [Hl1]; simp [lblData, l3pWbytes1]
  have H := shRmwWrite (hlc := hlc) (pol := splPol GT) (gtAdGd GT) spinN Unit
    (spinOb5 ya xa [ca] cv5) nm cpu hB (fun _ => iprop(⌜QB5 (gtAdGd GT).gdG tx vx⌝)) ypaM ypaMRam
    (if b1 = b0 then b5Cs else acqRmw b5Cs hlt) 1 Hne
    iprop(isLock (GF := GF) nm.2 ya (spinR5 xa [ca] nm (gtAdGd GT)) ∗ notheld nm.2 ya hB ∗
      AxAnnot.annotOwn (hB, 0) iprop(⌜rdFact [ca] cv5 (gtAdGd GT).gdG (hB, 0)⌝))
    (fun rs => by
      iintro ⟨#Hil, Hnh, H0⟩
      ihave Hfe := fe5Neutral (hlc := hlc) (GF := GF) ya xa [ca] cv5 GT nm Hcons yaNX5 (hB, 1) t1
        b1 Hrd (Ne.symm b0NeB1) Hw (fun a v H => (Hsg a v H).1)
      iapply (evPlain (hlc := hlc) (pol := splPol GT) (gtAdGd GT) spinN Unit
        (spinOb5 ya xa [ca] cv5) nm hB 1 iprop(True) iprop(True) _ _ Hval) $$ [Hfe]
      · iapply (@flowEqDynMono hlc GF _ (shG (gtAdGd GT) spinN Unit (spinOb5 ya xa [ca] cv5) nm)
          (splPol GT) (gtAdGd GT) (hB, 1) _ (∅ : Mea GF) iprop(True) iprop(True ∗ True)) $$ [] Hfe
        inext
        iintro _
        isplitl []
        · itrivial
        · itrivial
      iintro _ _
      rw [if_neg (Ne.symm b0NeB1)]
      iapply (wB2r (hlc := hlc) GT nm cpu Hcons tc vc t1 t2 tx vx tl vl t3 Hrow) $$ Hil Hnh H0 %rs)
  iintro #Hil Hnh H0
  iapply H $$ [$Hil $Hnh $H0]

theorem AxSpinProt7.wB1r (GT : GdexecT) (nm : spinN) (cpu : CPU)
    (Hcons : rvwmoCatConsistent (gtAdGd GT)) (tc : Nat) (vc : BitVec 8) (t1 t2 tx : Nat)
    (vx : BitVec 8) (tl : Nat) (vl : BitVec 8) (t3 : Nat)
    (Hrow : AxOpsem.grow (gtAdGd GT) hB = b5Row tc vc t1 t2 tx vx tl vl t3) :
    ⊢ isLock (GF := GF) nm.2 ya (spinR5 xa [ca] nm (gtAdGd GT)) -∗ notheld nm.2 ya hB -∗
      AxAnnot.annotOwn (hB, 0) iprop(⌜rdFact [ca] cv5 (gtAdGd GT).gdG (hB, 0)⌝) -∗
      ∀ rs : RegFile, @tierAWpd GF hlc _ _ (splPol GT) (gtAdGd GT) spinN Unit
        (spinOb5 ya xa [ca] cv5) nm ⟨hp cpu b5Acq1 rs, 1⟩ .MaybeStuck hB
        (fun _ => iprop(⌜QB5 (gtAdGd GT).gdG tx vx⌝)) := by
  have Hne : 1 ≠ (AxOpsem.grow (gtAdGd GT) hB).length := by rw [Hrow]; simp [b5Row]
  have Hl1 : (AxOpsem.grow (gtAdGd GT) hB)[1]? =
      some (.LRmw true false (paZ ypaM) [t1] [b1] [b1] .WCplain) := by rw [Hrow]; rfl
  have H := shRmwRead (hlc := hlc) (pol := splPol GT) (gtAdGd GT) spinN Unit
    (spinOb5 ya xa [ca] cv5) nm cpu hB (fun _ => iprop(⌜QB5 (gtAdGd GT).gdG tx vx⌝)) ypaM ypaMRam
    (acqK b5Cs (acqRmw b5Cs hlt)) 1 t1 b1 .WCplain Hne Hl1
    iprop(isLock (GF := GF) nm.2 ya (spinR5 xa [ca] nm (gtAdGd GT)) ∗ notheld nm.2 ya hB ∗
      AxAnnot.annotOwn (hB, 0) iprop(⌜rdFact [ca] cv5 (gtAdGd GT).gdG (hB, 0)⌝))
    (fun rs => by
      iintro ⟨#Hil, Hnh, H0⟩
      rw [AxSpinProt7.acqKOk]
      iapply (AxSpinProt7.wB1w (hlc := hlc) GT nm cpu Hcons tc vc t1 t2 tx vx tl vl t3 Hrow)
        $$ Hil Hnh H0 %rs)
  iintro #Hil Hnh H0
  iapply H $$ [$Hil $Hnh $H0]

/-- THE NON-HOLDER's lk->cpu read: the racy-read fact deposited AT THE READ. -/
theorem wpdB5 (GT : GdexecT) (nm : spinN) (cpu : CPU)
    (Hcons : rvwmoCatConsistent (gtAdGd GT)) (tc : Nat) (vc : BitVec 8) (t1 t2 tx : Nat)
    (vx : BitVec 8) (tl : Nat) (vl : BitVec 8) (t3 : Nat)
    (Hrow : AxOpsem.grow (gtAdGd GT) hB = b5Row tc vc t1 t2 tx vx tl vl t3) :
    ⊢ isLock (GF := GF) nm.2 ya (spinR5 xa [ca] nm (gtAdGd GT)) -∗ notheld nm.2 ya hB -∗
      @tierAWpd GF hlc _ _ (splPol GT) (gtAdGd GT) spinN Unit (spinOb5 ya xa [ca] cv5) nm
        ⟨hp cpu b5M0 zeroRegs, 0⟩ .MaybeStuck hB
        (fun _ => iprop(⌜QB5 (gtAdGd GT).gdG tx vx⌝)) := by
  have Hne : 0 ≠ (AxOpsem.grow (gtAdGd GT) hB).length := by rw [Hrow]; simp [b5Row]
  have Hadv : ∀ lb, (AxOpsem.grow (gtAdGd GT) hB)[0]? = some lb → aidentAdvRd (aident lb) = 1 := by
    rw [Hrow]
    intro lb h
    cases h
    rfl
  have Hl0 := b5L (gtAdGd GT) tc vc t1 t2 tx vx tl vl t3 Hrow 0 _ rfl
  have H := shRead (hlc := hlc) (pol := splPol GT) (gtAdGd GT) spinN Unit (spinOb5 ya xa [ca] cv5)
    nm cpu hB (fun _ => iprop(⌜QB5 (gtAdGd GT).gdG tx vx⌝)) cpaM cpaMRam (fun _ => b5Acq1) 0 Hne
    Hadv iprop(isLock (GF := GF) nm.2 ya (spinR5 xa [ca] nm (gtAdGd GT)) ∗ notheld nm.2 ya hB)
    (fun v b rs Hgv Hv => by
      subst Hv
      have Hnw : gisW (gtAdGd GT).gdG (hB, 0) = false := by unfold gisW; rw [Hl0]; rfl
      have Hnr : ¬ lkread ya (gtAdGd GT).gdG (hB, 0) := by
        rintro ⟨⟨t, v, Hr⟩, -⟩
        exact caNeYa (grbLoadOnly _ _ _ _ _ Hl0 _ _ _ Hr).1.symm
      iintro ⟨#Hil, Hnh⟩
      ihave Hfe := fe5Cpuread (hlc := hlc) (GF := GF) ya xa [ca] cv5 GT nm Hcons yaNX5 (hB, 0) Hnw
        Hnr
      iapply (evPlain (hlc := hlc) (pol := splPol GT) (gtAdGd GT) spinN Unit
        (spinOb5 ya xa [ca] cv5) nm hB 0 iprop(⌜rdFact [ca] cv5 (gtAdGd GT).gdG (hB, 0)⌝)
        iprop(True) _ _ Hgv) $$ [Hfe]
      · iapply (@flowEqDynMono hlc GF _ (shG (gtAdGd GT) spinN Unit (spinOb5 ya xa [ca] cv5) nm)
          (splPol GT) (gtAdGd GT) (hB, 0) _ (∅ : Mea GF)
          iprop(⌜rdFact [ca] cv5 (gtAdGd GT).gdG (hB, 0)⌝)
          iprop(⌜rdFact [ca] cv5 (gtAdGd GT).gdG (hB, 0)⌝ ∗ True)) $$ [] Hfe
        inext
        iintro H
        isplitl [H]
        · iexact H
        · itrivial
      iintro H0 _
      iapply (AxSpinProt7.wB1r (hlc := hlc) GT nm cpu Hcons tc vc t1 t2 tx vx tl vl t3 Hrow)
        $$ Hil Hnh H0 %rs)
  iintro #Hil Hnh
  iapply H $$ [$Hil $Hnh] %zeroRegs

end wpdB5

/-! # 8. The race program at the TRIVIAL protocol (sanity twin) -/

section wpdR5
variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF] [AxannotGS GF]

theorem feTriv5 (GT : GdexecT) (e : Geid) (s0 : GSet Geid) (fi : Mea GF) :
    ⊢ @flowEqDyn hlc GF _ (shG (gtAdGd GT) Unit Unit trivOb ()) (gtAdGd GT) e s0 fi
      iprop(True ∗ True) := by
  unfold flowEqDyn
  iintro %σ %s %Hsub %Hnin _ _
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  inext
  imod Hclose
  imodintro
  iexists σ
  have Ht : ⊢ @AxirisG.obStInterp GF (shG (gtAdGd GT) Unit Unit trivOb ()) (gtAdGd GT) σ
      (({e} : GSet Geid) ∪ s) := by
    show ⊢ iprop(True)
    itrivial
  isplitr
  · iapply Ht
  · isplitr
    · itrivial
    · itrivial

theorem r5L (GT : GdexecT) (Hrow : AxOpsem.grow (gtAdGd GT) hA = r5Row) (k : Nat) (lb : Lbl) :
    r5Row[k]? = some lb → gxLbl (gtAdGd GT).gdG (hA, k) = some lb := by
  intro Hk
  rw [gxLblGrow, Hrow]
  exact Hk

theorem wR5St (GT : GdexecT) (cpu : CPU) (Hrow : AxOpsem.grow (gtAdGd GT) hA = r5Row) :
    ⊢ ∀ rs : RegFile, @tierAWpd GF hlc _ _ (splPol GT) (gtAdGd GT) Unit Unit trivOb ()
      ⟨hp cpu (AxSpinProt7.sdM xpaM b1 hlt) rs, 3⟩ .MaybeStuck hA (fun _ => iprop(True)) := by
  have Hne : 3 ≠ (AxOpsem.grow (gtAdGd GT) hA).length := by rw [Hrow]; simp [r5Row]
  have Hl3 := r5L GT Hrow 3 _ rfl
  have H := shPos (hlc := hlc) (GF := GF) (pol := splPol GT) (gtAdGd GT) Unit Unit trivOb () cpu hA
    (fun _ => iprop(True)) iprop(True) 3 (AxSpinProt7.sdM xpaM b1 hlt) Hne
    (fun rs id K => noReadAtWrite cpu _ xpaM xpaMRam b1 hlt rs 3 id K)
    (fun rs l s' Hst => by
      obtain ⟨rfl, Hs', -⟩ := writeInv2 cpu _ xpaM xpaMRam b1 hlt rs 3 l s' Hst
      simp only [wlWdata]
      subst Hs'
      have Hval : graphData (gtAdGd GT) (hA, 3) = some (WeakInterpProj.wbytes 1 b1) := by
        unfold graphData; rw [Hl3]; simp [lblData, l3pWbytes1]
      iintro _
      iapply (evPlain (hlc := hlc) (pol := splPol GT) (gtAdGd GT) Unit Unit trivOb () hA 3
        iprop(True) iprop(True) _ _ Hval) $$ []
      · iapply feTriv5
      iintro _ _
      iapply (shHltTrue (hlc := hlc) (pol := splPol GT) (gtAdGd GT) Unit Unit trivOb () cpu hA
        (3 + 1)) $$ %rs)
  iintro %rs
  iapply H $$ [] %rs
  itrivial

theorem wR5Rel (GT : GdexecT) (cpu : CPU) (Hrow : AxOpsem.grow (gtAdGd GT) hA = r5Row) :
    ⊢ ∀ rs : RegFile, @tierAWpd GF hlc _ _ (splPol GT) (gtAdGd GT) Unit Unit trivOb ()
      ⟨hp cpu (relM (AxSpinProt7.sdM xpaM b1 hlt)) rs, 2⟩ .MaybeStuck hA
      (fun _ => iprop(True)) := by
  have Hne : 2 ≠ (AxOpsem.grow (gtAdGd GT) hA).length := by rw [Hrow]; simp [r5Row]
  have Hl2 := r5L GT Hrow 2 _ rfl
  have H := shPos (hlc := hlc) (GF := GF) (pol := splPol GT) (gtAdGd GT) Unit Unit trivOb () cpu hA
    (fun _ => iprop(True)) iprop(True) 2 (relM (AxSpinProt7.sdM xpaM b1 hlt)) Hne
    (fun rs id K => noReadAtWrite cpu _ ypaM ypaMRam b0 (AxSpinProt7.sdM xpaM b1 hlt) rs 2 id K)
    (fun rs l s' Hst => by
      obtain ⟨rfl, Hs', -⟩ := writeInv2 cpu _ ypaM ypaMRam b0 (AxSpinProt7.sdM xpaM b1 hlt) rs 2
        l s' Hst
      simp only [wlWdata]
      subst Hs'
      have Hval : graphData (gtAdGd GT) (hA, 2) = some (WeakInterpProj.wbytes 1 b0) := by
        unfold graphData; rw [Hl2]; simp [lblData, l3pWbytes1]
      iintro _
      iapply (evPlain (hlc := hlc) (pol := splPol GT) (gtAdGd GT) Unit Unit trivOb () hA 2
        iprop(True) iprop(True) _ _ Hval) $$ []
      · iapply feTriv5
      iintro _ _
      iapply (wR5St (hlc := hlc) GT cpu Hrow) $$ %rs)
  iintro %rs
  iapply H $$ [] %rs
  itrivial

theorem wR5Fence (GT : GdexecT) (cpu : CPU) (Hrow : AxOpsem.grow (gtAdGd GT) hA = r5Row) :
    ⊢ ∀ rs : RegFile, @tierAWpd GF hlc _ _ (splPol GT) (gtAdGd GT) Unit Unit trivOb ()
      ⟨hp cpu (fenceM (relM (AxSpinProt7.sdM xpaM b1 hlt))) rs, 1⟩ .MaybeStuck hA
      (fun _ => iprop(True)) := by
  have Hne : 1 ≠ (AxOpsem.grow (gtAdGd GT) hA).length := by rw [Hrow]; simp [r5Row]
  have H := shPos (hlc := hlc) (GF := GF) (pol := splPol GT) (gtAdGd GT) Unit Unit trivOb () cpu hA
    (fun _ => iprop(True)) iprop(True) 1 (fenceM (relM (AxSpinProt7.sdM xpaM b1 hlt))) Hne
    (fun rs id K => noReadAtFence cpu _ (relM (AxSpinProt7.sdM xpaM b1 hlt)) rs 1 id K)
    (fun rs l s' Hst => by
      obtain ⟨rfl, Hs', -⟩ := fenceInv2 cpu _ (relM (AxSpinProt7.sdM xpaM b1 hlt)) rs 1 l s' Hst
      simp only [wlWdata]
      subst Hs'
      iintro _
      iapply (shSkip2 (GF := GF) (gtAdGd GT) Unit Unit trivOb () hA _ _)
      inext
      iapply (wR5Rel (hlc := hlc) GT cpu Hrow) $$ %rs)
  iintro %rs
  iapply H $$ [] %rs
  itrivial

theorem wpdR5Triv (GT : GdexecT) (cpu : CPU) (Hrow : AxOpsem.grow (gtAdGd GT) hA = r5Row) :
    ⊢ @tierAWpd GF hlc _ _ (splPol GT) (gtAdGd GT) Unit Unit trivOb ()
      ⟨hp cpu r5M0 zeroRegs, 0⟩ .MaybeStuck hA (fun _ => iprop(True)) := by
  have Hne : 0 ≠ (AxOpsem.grow (gtAdGd GT) hA).length := by rw [Hrow]; simp [r5Row]
  have Hl0' := r5L GT Hrow 0 _ rfl
  have Hl0 : (AxOpsem.grow (gtAdGd GT) hA)[0]? =
      some (.LRmw true false (paZ ypaM) [0] [b0] [b1] .WCplain) := by rw [Hrow]; rfl
  have Hval : graphData (gtAdGd GT) (hA, 0) = some (WeakInterpProj.wbytes 1 b1) := by
    unfold graphData; rw [Hl0']; simp [lblData, l3pWbytes1]
  have HW := shRmwWrite (hlc := hlc) (GF := GF) (pol := splPol GT) (gtAdGd GT) Unit Unit trivOb ()
    cpu hA (fun _ => iprop(True)) ypaM ypaMRam
    (if b0 = b0 then fenceM (relM (AxSpinProt7.sdM xpaM b1 hlt)) else hlt) 0 Hne iprop(True)
    (fun rs => by
      iintro _
      iapply (evPlain (hlc := hlc) (pol := splPol GT) (gtAdGd GT) Unit Unit trivOb () hA 0
        iprop(True) iprop(True) _ _ Hval) $$ []
      · iapply feTriv5
      iintro _ _
      rw [if_pos rfl]
      iapply (wR5Fence (hlc := hlc) GT cpu Hrow) $$ %rs)
  have H := shRmwRead (hlc := hlc) (GF := GF) (pol := splPol GT) (gtAdGd GT) Unit Unit trivOb ()
    cpu hA (fun _ => iprop(True)) ypaM ypaMRam
    (acqK (fenceM (relM (AxSpinProt7.sdM xpaM b1 hlt))) hlt) 0 0 b0 .WCplain Hne Hl0 iprop(True)
    (fun rs => by
      iintro _
      rw [AxSpinProt7.acqKOk]
      iapply HW $$ [] %rs
      itrivial)
  iapply H $$ [] %zeroRegs
  itrivial

end wpdR5

end Weak
