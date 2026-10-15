/-
Weak: **W10-4 [OWN.94] (N2′), decision (A), step 4a — the walk order with SKIPS: the invariant, the
relativized per-step datum, the policy** (`PROGRESS-W10N2p.md`).  Lean-only, no Rocq twin.

  §1  `CertZ29.keepEv` (an event whose `GF` label is no failed acquire), **`CertZ29.lockInvR4`** (the
      walk invariant with each hart's trace re-indexing its row prefix FILTERED by `keepB`),
      **`CertZ29.prefInv4`** (the order's prefix: the trace's agents are the KEPT events of `L.take k`);
  §2  **`CertZ29.hartStepRI4`** — the per-step datum RELATIVIZED to walk-invariant states (the trace is
      the kept prefix of `L`, the next event is `L[k]`, each hart's trace re-indexes its filtered row
      prefix): at a failed-acquire slot the relation advances with the certified state unchanged (the
      xv6 failed iteration), elsewhere a certified step re-indexing the row label;
  §3  **`CertZ29.walkPolOfOrdR4`** — the policy with skips from a walk order and the datum.

Spec: the datum is a fact of the program's Sail semantics at each site (W10-4 per pc; its skip clause
is the per-pc failed-iteration fact: a failed `amoswap.w.aq; bnez` writes 1 over 1 and changes only rd,
overwritten by the next iteration); FAITHFUL.  Lean-only helpers file-qualified (`CertZ29.*`).
-/
import Weak.CertZ28

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open TsoShadow

/-! # 1. The invariant -/

/-- An event the walk realizes (its `GF` label is no failed acquire; off the rows: kept). -/
noncomputable def CertZ29.keepEv (rows : List (List Lbl)) (Lb : Int → Prop) (e : Geid) : Bool :=
  match (rows.getD e.1 [])[e.2]? with
  | some l => CertZ26.keepB Lb l
  | none => true

/-- **THE WALK INVARIANT WITH SKIPS.** -/
def CertZ29.lockInvR4 (rows : List (List Lbl)) (Lb : Int → Prop) (F : Nat → Nat → Pexv6)
    (Rel : CertZ9.HRel) (X : CertZ2.WInv) : CertZ2.WInv :=
  fun St itvOf fiOf cnt =>
    (∀ x, x < rows.length →
      cnt x ≤ (rows.getD x []).length ∧
      (∃ pC, (St.cstPst (cdEnd St.cstC))[x]? = some pC ∧ Rel x (cnt x) (F x (cnt x)) pC) ∧
      List.Forall₂ lblReidxW (((rows.getD x []).take (cnt x)).filter (CertZ26.keepB Lb))
        (CertZ2.hartTr St.cstC.cdTr x)) ∧
    (∀ s, s ∈ St.cstC.cdTr → s.esAg < rows.length) ∧
    X St itvOf fiOf cnt

/-- **THE ORDER'S PREFIX, WITH SKIPS.** -/
def CertZ29.prefInv4 (rows : List (List Lbl)) (Lb : Int → Prop) (L dev : List Geid)
    (fab : Nat → Efab) : CertZ2.WInv :=
  fun St _ _ cnt => ∃ k, k ≤ L.length ∧
    (∀ x, cnt x = ((L.take k).filter (fun e => decide (e.1 = x))).length) ∧
    St.cstDv (cdEnd St.cstC) = fab (((L.take k).filter (fun e => decide (e ∈ dev))).length) ∧
    St.cstC.cdTr.map Estep.esAg = ((L.take k).filter (CertZ29.keepEv rows Lb)).map Prod.fst

/-! # 2. The relativized per-step datum -/

/-- **THE PER-STEP DATUM AT WALK-INVARIANT STATES, WITH SKIPS** (W10-4's per-pc obligation, named). -/
def CertZ29.hartStepRI4 (d0 : Efab) (rows : List (List Lbl)) (Lb : Int → Prop) (L : List Geid)
    (Rel : CertZ9.HRel) : Prop :=
  ∀ (St : CycState) (itvOf : Nat → Nat → Nat) (fiOf : Nat → Nat → Bool) (x n : Nat) (lb : Lbl)
    (ws : Wstate) (ls : List Wlabel) (l : Wlabel) (pE pE' pC : Pexv6) (d' : Efab) (k : Nat),
    CertZ.cstOkZW d0 St itvOf fiOf →
    (St.cstPst (cdEnd St.cstC))[x]? = some pC → Rel x n pE pC → CertZ4.lblShape lb →
    ((lbFused l ∧ GraphFetchBlocks.blkOne (St.cstDv (cdEnd St.cstC)) d' ws lb ls l pE pE') ∨
      GraphFetchBlocks.blkPair (St.cstDv (cdEnd St.cstC)) d' ws lb ls l pE pE') →
    St.cstC.cdTr.map Estep.esAg = ((L.take k).filter (CertZ29.keepEv rows Lb)).map Prod.fst →
    L[k]? = some (x, n) →
    (∀ y, y < rows.length →
      List.Forall₂ lblReidxW
        (((rows.getD y []).take (((L.take k).filter (fun e => decide (e.1 = y))).length)).filter
          (CertZ26.keepB Lb))
        (CertZ2.hartTr St.cstC.cdTr y)) →
    (rows.getD x [])[n]? = some lb →
    (CertZ24.lblFail Lb lb → Rel x (n + 1) pE' pC) ∧
    (¬ CertZ24.lblFail Lb lb →
      ∃ (lb' : Lbl) (pa : Pexv6) (da : Efab) (ls' : List Wlabel) (pC' : Pexv6),
        lblReidxW lb lb' ∧ CertZ2.stepOkZ St itvOf x lb' pC pa da ls' pC' d' ∧
        Rel x (n + 1) pE' pC')

/-! # 3. The policy -/

theorem CertZ29.keepEvAt (rows : List (List Lbl)) (Lb : Int → Prop) (x a : Nat) (lb : Lbl) :
    (rows.getD x [])[a]? = some lb → CertZ29.keepEv rows Lb (x, a) = CertZ26.keepB Lb lb := by
  intro h
  unfold CertZ29.keepEv
  dsimp only
  rw [h]

theorem CertZ29.filterSnocB (L : List Geid) (e : Geid) (p : Geid → Bool) :
    (L ++ [e]).filter p = L.filter p ++ (if p e then [e] else []) := by
  rw [List.filter_append]
  by_cases h : p e <;> simp [h]

theorem CertZ29.lblFilterSnoc (Lb : Int → Prop) (row : List Lbl) (lb : Lbl) :
    (row ++ [lb]).filter (CertZ26.keepB Lb) =
      row.filter (CertZ26.keepB Lb) ++ (if CertZ26.keepB Lb lb then [lb] else []) := by
  rw [List.filter_append]
  by_cases h : CertZ26.keepB Lb lb <;> simp [h]

/-- **`CertZ29.walkPolOfOrdR4` — THE POLICY WITH SKIPS FROM THE ORDER AND THE DATUM.** -/
theorem CertZ29.walkPolOfOrdR4 (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (GF : Gfexec)
    (D : Nat → CertZ7.EmData) (L : List Geid) (Lb : Int → Prop) (Rel : CertZ9.HRel) :
    CertZ7.emDataOk boot fab GF D → GF.gfDev.Nodup →
    CertZ8.walkOrd GF.gfGd.gdG.gxProg GF.gfDev L →
    (∀ e, e ∈ GF.gfDev → e ∈ L) →
    (∀ (x n : Nat) (lb : Lbl), (GF.gfGd.gdG.gxProg.getD x [])[n]? = some lb → CertZ4.lblShape lb) →
    (∀ e, e ∈ GF.gfDev → CertZ29.keepEv GF.gfGd.gdG.gxProg Lb e = true) →
    CertZ29.hartStepRI4 d0 GF.gfGd.gdG.gxProg Lb L Rel →
    CertZ26.walkPolZ4 d0 GF.gfGd.gdG.gxProg Lb
      (CertZ29.lockInvR4 GF.gfGd.gdG.gxProg Lb (fun x => (D x).f) Rel
        (CertZ29.prefInv4 GF.gfGd.gdG.gxProg Lb L GF.gfDev fab)) := by
  intro hD hdnd hord hsub hshape hdevK hstep St itvOf fiOf cnt hok hinv hnd
  obtain ⟨hper, hagt, ⟨k, hkL, hcnt, hfab, hags⟩⟩ := hinv
  obtain ⟨y0, hy0, hy0c⟩ := hnd
  have hkl : k < L.length := by
    refine Nat.lt_of_le_of_ne hkL (fun he => ?_)
    rw [hcnt y0, he, List.take_length, CertZ8.countAll _ _ L y0 hord hy0] at hy0c
    omega
  obtain ⟨⟨x, a⟩, hk⟩ : ∃ e, L[k]? = some e := ⟨L[k], List.getElem?_eq_getElem hkl⟩
  have hev := (hord.2.1 _).1 (List.mem_of_getElem? hk)
  have hx : x < GF.gfGd.gdG.gxProg.length := hev.1
  have hca : cnt x = a := by rw [hcnt x]; exact CertZ8.ordCount _ _ L k x a hord hk
  obtain ⟨lb, hlb⟩ : ∃ lb, (GF.gfGd.gdG.gxProg.getD x [])[a]? = some lb :=
    ⟨_, List.getElem?_eq_getElem hev.2⟩
  rw [← hca] at hlb hk
  obtain ⟨-, ⟨pC, hp, hrel⟩, hf2⟩ := hper x hx
  obtain ⟨em, -, hiff, hpin, -, -, hblk⟩ := hD x _ (CertZ7.getDSome _ x hx)
  have hdevIdx : (x, cnt x) ∈ GF.gfDev → ∃ m, GF.gfDev[m]? = some (x, cnt x) ∧
      ((L.take k).filter (fun e => decide (e ∈ GF.gfDev))).length = m := by
    intro hin
    obtain ⟨m, hm⟩ := List.mem_iff_getElem?.1 hin
    exact ⟨m, hm, CertZ8.devCount _ _ L k m _ hord hdnd hsub hm hk⟩
  have hB : ∃ d', (((lbFused ((D x).r (cnt x)) ∧
      GraphFetchBlocks.blkOne (St.cstDv (cdEnd St.cstC)) d'
        (rowWsAux 0 wsInit ((GF.gfGd.gdG.gxProg.getD x []).take (cnt x))) lb ((D x).g (cnt x))
        ((D x).r (cnt x)) ((D x).f (cnt x)) ((D x).f (cnt x + 1))) ∨
      GraphFetchBlocks.blkPair (St.cstDv (cdEnd St.cstC)) d'
        (rowWsAux 0 wsInit ((GF.gfGd.gdG.gxProg.getD x []).take (cnt x))) lb ((D x).g (cnt x))
        ((D x).r (cnt x)) ((D x).f (cnt x)) ((D x).f (cnt x + 1))) ∧
      d' = fab (((L.take (k + 1)).filter (fun e => decide (e ∈ GF.gfDev))).length)) := by
    rw [take_S_r hk, CertZ8.filterSnoc]
    by_cases htq : (D x).tq (cnt x) = true
    · obtain ⟨m, hm, hmc⟩ := hdevIdx ((hiff _ (lookup_lt_Some hlb)).2 (.inr (.inr htq)))
      have hD0 : (D x).dvi (cnt x) = St.cstDv (cdEnd St.cstC) := by
        rw [hfab, hmc]; exact (hpin _ m hm).1
      refine ⟨(D x).dvo (cnt x), ?_, ?_⟩
      · rw [← hD0]
        rcases hblk (cnt x) lb hlb with ⟨hfu, h1, -⟩ | ⟨h1, -⟩
        · exact .inl ⟨hfu, h1⟩
        · exact .inr h1
      · rw [hmc, if_pos (decide_eq_true (List.mem_of_getElem? hm))]
        exact (hpin _ m hm).2
    · have htq' : (D x).tq (cnt x) = false := by simpa using htq
      have hnin := CertZ8.quietNotDev boot fab GF D x (cnt x) lb hD hlb hx htq'
      refine ⟨St.cstDv (cdEnd St.cstC), ?_, ?_⟩
      · rcases hblk (cnt x) lb hlb with ⟨hfu, -, hq⟩ | ⟨-, hq⟩
        · exact .inl ⟨hfu, hq htq' _⟩
        · exact .inr (hq htq' _)
      · rw [hfab, if_neg (by simpa using hnin), Nat.add_zero]
  obtain ⟨d', hblkD, hd'⟩ := hB
  have hperF : ∀ y, y < GF.gfGd.gdG.gxProg.length →
      List.Forall₂ lblReidxW
        (((GF.gfGd.gdG.gxProg.getD y []).take
          (((L.take k).filter (fun e => decide (e.1 = y))).length)).filter (CertZ26.keepB Lb))
        (CertZ2.hartTr St.cstC.cdTr y) := by
    intro y hy
    rw [← hcnt y]
    exact (hper y hy).2.2
  obtain ⟨hskip, hreal⟩ := hstep St itvOf fiOf x (cnt x) lb _ _ _ _ _ pC d' k hok hp hrel
    (hshape x _ lb hlb) hblkD hags hk hperF hlb
  have hcntS : ∀ y, CertZ2.bump cnt x y =
      ((L.take (k + 1)).filter (fun e => decide (e.1 = y))).length := by
    intro y
    rw [take_S_r hk, CertZ8.filterSnoc]
    by_cases hy : y = x
    · subst hy; rw [CertZ2.bumpSelf, hcnt y]; simp
    · rw [CertZ2.bumpNe cnt x y hy, hcnt y]
      simp [Ne.symm hy]
  have hkeepA : CertZ29.keepEv GF.gfGd.gdG.gxProg Lb (x, cnt x) = CertZ26.keepB Lb lb :=
    CertZ29.keepEvAt _ Lb x (cnt x) lb hlb
  refine ⟨x, lb, hx, hlb, ?_⟩
  by_cases hf : CertZ24.lblFail Lb lb
  · -- SKIP
    have hkf : CertZ26.keepB Lb lb = false := by
      cases h : CertZ26.keepB Lb lb with
      | false => rfl
      | true => exact absurd hf ((CertZ26.keepBTrue Lb lb).1 h)
    have hndev : (x, cnt x) ∉ GF.gfDev := fun hin => by
      have := hdevK _ hin; rw [hkeepA, hkf] at this; cases this
    refine .inl ⟨hf, ⟨fun y hy => ?_, hagt, k + 1, hkl, hcntS, ?_, ?_⟩⟩
    · obtain ⟨hle, ⟨pCy, hpy, hrely⟩, hfy⟩ := hper y hy
      by_cases hy' : y = x
      · subst hy'
        rw [CertZ2.bumpSelf]
        refine ⟨lookup_lt_Some hlb, ⟨pC, hp, hskip hf⟩, ?_⟩
        rw [take_S_r hlb, CertZ29.lblFilterSnoc, hkf]
        simpa using hfy
      · rw [CertZ2.bumpNe cnt x y hy']
        exact ⟨hle, ⟨pCy, hpy, hrely⟩, hfy⟩
    · rw [hfab, take_S_r hk, CertZ8.filterSnoc, if_neg (by simpa using hndev), Nat.add_zero]
    · rw [hags, take_S_r hk, CertZ29.filterSnocB, hkeepA, hkf]
      simp
  · -- REALIZED
    have hkt : CertZ26.keepB Lb lb = true := (CertZ26.keepBTrue Lb lb).2 hf
    obtain ⟨lb', pa, da, ls', pC', hre, hok', hrel'⟩ := hreal hf
    refine .inr ⟨hf, lb', pC, pa, da, ls', pC', d', hp, hre, hok',
      ⟨fun y hy => ?_, fun s hs => ?_, k + 1, hkl, hcntS, ?_, ?_⟩⟩
    · obtain ⟨hle, ⟨pCy, hpy, hrely⟩, hfy⟩ := hper y hy
      have hpst : (CertZ2.stSnoc St x lb' pC' d').cstPst
          (cdEnd (CertZ2.stSnoc St x lb' pC' d').cstC) =
          (St.cstPst (cdEnd St.cstC)).set x pC' := by
        show pstSnoc St.cstC St.cstPst x _ (cdEnd (candSnoc St.cstC _)) = _
        rw [cdEndSnoc, pstSnocGt _ _ _ _ _ (by omega)]
      rw [hpst]
      show _ ∧ _ ∧ List.Forall₂ lblReidxW _ (CertZ2.hartTr (St.cstC.cdTr ++ [⟨x, lb'⟩]) y)
      rw [CertZ6.hartTrSnoc]
      by_cases hy' : y = x
      · subst hy'
        rw [CertZ2.bumpSelf, if_pos rfl]
        refine ⟨lookup_lt_Some hlb, ⟨pC', List.getElem?_set_self (lookup_lt_Some hp), hrel'⟩, ?_⟩
        rw [take_S_r hlb, CertZ29.lblFilterSnoc, hkt, if_pos rfl]
        exact CertZ6.forall₂Snoc _ _ _ _ _ hfy hre
      · rw [CertZ2.bumpNe cnt x y hy', if_neg (Ne.symm hy'),
          List.getElem?_set_ne (Ne.symm hy')]
        exact ⟨hle, ⟨pCy, hpy, hrely⟩, hfy⟩
    · change s ∈ St.cstC.cdTr ++ [⟨x, lb'⟩] at hs
      rcases List.mem_append.1 hs with hs | hs
      · exact hagt s hs
      · simp only [List.mem_singleton] at hs
        rw [hs]
        exact hx
    · show dvSnoc St.cstC St.cstDv _ (cdEnd (candSnoc St.cstC _)) = _
      rw [cdEndSnoc, dvSnocGt _ _ _ _ (by omega)]
      exact hd'
    · show (St.cstC.cdTr ++ [(⟨x, lb'⟩ : Estep)]).map Estep.esAg = _
      rw [List.map_append, hags, take_S_r hk, CertZ29.filterSnocB, hkeepA, hkt, if_pos rfl,
        List.map_append]
      rfl

end Weak
