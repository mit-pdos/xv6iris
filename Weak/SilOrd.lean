/-
Weak: **(c) [OWN.100], increment 5d-i — the twin walk FROM AN ORDER, its step datum, the realized
member's lock co, and the zero-cut kill** (`PROGRESS-W10N2p.md`).  Lean-only, no Rocq twin.

The twin of CertZ29–31 with NO skips: the walk follows a walk order `L` of the graph's events, every slot
an appended twin step (a failed acquire SILENTLY), so the certified hart stays LOCKSTEP with its emission
(no lag, no skip clause, no timer drift).

  §1  `SilOrd.pairs`, `SilOrd.inv` (per hart: counter, program-state relation, `relW` row prefix),
      `SilOrd.pref` (the trace's agents are `L.take k`'s), **`SilOrd.hartStepRIS`** (the per-step datum at
      walk-invariant states — W10-4's per-pc obligation, named), **`SilOrd.walkPolOfOrdS`**;
  §2  `SilOrd.projAgs`, **`SilOrd.lockCoOfOrdS`** (the realized member's successful-protocol lock co from
      the order's);
  §3  `CatLin.SilOrd.stepSupplyS`, `CatLin.SilOrd.spNfS`, **`CatLin.SilOrd.walkSupplyOfOrdStepS`** (the
      walk order is an INPUT: the registered `orderSupplyCZ3`);
  §4  **`CatLin.SilOrd.cycleKillOfOrdStepS`**.

Spec: FAITHFUL (proof organisation; the named premises' truth in `PROGRESS-W10N2p.md`).
-/
import Weak.SilWalk2

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open TsoShadow

/-! # 1. The invariant, the datum, the policy -/

/-- The appended steps with their silent marks. -/
def SilOrd.pairs (S : SilWalk.St) : List (Estep × Option Nat) := S.c.tr.zip S.c.sil

theorem SilOrd.pairsSnoc (S : SilWalk.St) (x : Nat) (lb : Lbl) (o : Option Nat) (pC' : Pexv6)
    (d' : Efab) (w' : Wstate) :
    S.c.sil.length = S.c.tr.length →
    SilOrd.pairs (SilWalk.snoc S x lb o pC' d' w') = SilOrd.pairs S ++ [(⟨x, lb⟩, o)] := by
  intro h
  show (S.c.tr ++ [(⟨x, lb⟩ : Estep)]).zip (S.c.sil ++ [o]) = _
  rw [List.zip_append h.symm]
  rfl

theorem SilOrd.hartPrSnoc (pr : List (Estep × Option Nat)) (p : Estep × Option Nat) (y : Nat) :
    SilWalk.hartPr (pr ++ [p]) y =
      SilWalk.hartPr pr y ++ (if p.1.esAg = y then [(p.1.esLb, p.2)] else []) := by
  by_cases h : p.1.esAg = y <;> simp [SilWalk.hartPr, h]

theorem SilOrd.snocPstEnd (S : SilWalk.St) (x : Nat) (lb : Lbl) (o : Option Nat) (pC' : Pexv6)
    (d' : Efab) (w' : Wstate) :
    (SilWalk.snoc S x lb o pC' d' w').pst (SilWalk.snoc S x lb o pC' d' w').c.tr.length
      = (S.pst S.c.tr.length).set x pC' := by
  simp only [SilWalk.snoc, List.length_append, List.length_singleton]
  rw [if_neg (by omega)]

theorem SilOrd.snocDvEnd (S : SilWalk.St) (x : Nat) (lb : Lbl) (o : Option Nat) (pC' : Pexv6)
    (d' : Efab) (w' : Wstate) :
    (SilWalk.snoc S x lb o pC' d' w').dv (SilWalk.snoc S x lb o pC' d' w').c.tr.length = d' := by
  simp only [SilWalk.snoc, List.length_append, List.length_singleton]
  rw [if_neg (by omega)]

/-- **THE TWIN WALK INVARIANT.** -/
def SilOrd.inv (rows : List (List Lbl)) (Lb : Int → Prop) (F : Nat → Nat → Pexv6) (Rel : CertZ9.HRel)
    (X : SilWalk.St → (Nat → Nat) → Prop) : SilWalk.St → (Nat → Nat) → Prop :=
  fun S cnt =>
    (∀ x, x < rows.length →
      cnt x ≤ (rows.getD x []).length ∧
      (∃ pC, (S.pst S.c.tr.length)[x]? = some pC ∧ Rel x (cnt x) (F x (cnt x)) pC) ∧
      List.Forall₂ (SilWalk.relW Lb) ((rows.getD x []).take (cnt x))
        (SilWalk.hartPr (SilOrd.pairs S) x)) ∧
    (∀ s, s ∈ S.c.tr → s.esAg < rows.length) ∧
    X S cnt

/-- **THE ORDER'S PREFIX** (no keep filter: every event of `L.take k` is a step). -/
def SilOrd.pref (L dev : List Geid) (fab : Nat → Efab) : SilWalk.St → (Nat → Nat) → Prop :=
  fun S cnt => ∃ k, k ≤ L.length ∧
    (∀ x, cnt x = ((L.take k).filter (fun e => decide (e.1 = x))).length) ∧
    S.dv S.c.tr.length = fab (((L.take k).filter (fun e => decide (e ∈ dev))).length) ∧
    S.c.tr.map Estep.esAg = (L.take k).map Prod.fst

/-- **THE PER-STEP DATUM AT TWIN WALK-INVARIANT STATES** (W10-4's per-pc obligation, named): from the
emission's block at the next event `L[k] = (x, n)`, an appended `(lb', o)` related to the graph's label
(`relW`: silent exactly at a failed acquire), its step obligation, and the relation advanced. -/
def SilOrd.hartStepRIS (d0 : Efab) (rows : List (List Lbl)) (Lb : Int → Prop) (L : List Geid)
    (Rel : CertZ9.HRel) : Prop :=
  ∀ (S : SilWalk.St) (x n : Nat) (lb : Lbl) (ws : Wstate) (ls : List Wlabel) (l : Wlabel)
    (pE pE' pC : Pexv6) (d' : Efab) (k : Nat),
    SilWalk.ok d0 S →
    (S.pst S.c.tr.length)[x]? = some pC → Rel x n pE pC → CertZ4.lblShape lb →
    ((lbFused l ∧ GraphFetchBlocks.blkOne (S.dv S.c.tr.length) d' ws lb ls l pE pE') ∨
      GraphFetchBlocks.blkPair (S.dv S.c.tr.length) d' ws lb ls l pE pE') →
    S.c.tr.map Estep.esAg = (L.take k).map Prod.fst →
    L[k]? = some (x, n) →
    (∀ y, y < rows.length →
      List.Forall₂ (SilWalk.relW Lb)
        ((rows.getD y []).take (((L.take k).filter (fun e => decide (e.1 = y))).length))
        (SilWalk.hartPr (SilOrd.pairs S) y)) →
    (rows.getD x [])[n]? = some lb →
    ∃ (lb' : Lbl) (o : Option Nat) (pa : Pexv6) (da : Efab) (ls' : List Wlabel) (pC' : Pexv6)
      (w' : Wstate),
      SilWalk.relW Lb lb (lb', o) ∧ SilWalk.stepOk S x lb' o pC pa da ls' pC' d' w' ∧
      Rel x (n + 1) pE' pC'

/-- **THE TWIN POLICY FROM THE ORDER AND THE DATUM.** -/
theorem SilOrd.walkPolOfOrdS (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (GF : Gfexec)
    (D : Nat → CertZ7.EmData) (L : List Geid) (Lb : Int → Prop) (Rel : CertZ9.HRel) :
    CertZ7.emDataOk boot fab GF D → GF.gfDev.Nodup →
    CertZ8.walkOrd GF.gfGd.gdG.gxProg GF.gfDev L →
    (∀ e, e ∈ GF.gfDev → e ∈ L) →
    (∀ (x n : Nat) (lb : Lbl), (GF.gfGd.gdG.gxProg.getD x [])[n]? = some lb → CertZ4.lblShape lb) →
    SilOrd.hartStepRIS d0 GF.gfGd.gdG.gxProg Lb L Rel →
    SilWalk.walkPol d0 GF.gfGd.gdG.gxProg Lb
      (SilOrd.inv GF.gfGd.gdG.gxProg Lb (fun x => (D x).f) Rel (SilOrd.pref L GF.gfDev fab)) := by
  intro hD hdnd hord hsub hshape hstep S cnt hok hinv hnd
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
  obtain ⟨-, ⟨pC, hp, hrel⟩, -⟩ := hper x hx
  obtain ⟨em, -, hiff, hpin, -, -, hblk⟩ := hD x _ (CertZ7.getDSome _ x hx)
  have hdevIdx : (x, cnt x) ∈ GF.gfDev → ∃ m, GF.gfDev[m]? = some (x, cnt x) ∧
      ((L.take k).filter (fun e => decide (e ∈ GF.gfDev))).length = m := by
    intro hin
    obtain ⟨m, hm⟩ := List.mem_iff_getElem?.1 hin
    exact ⟨m, hm, CertZ8.devCount _ _ L k m _ hord hdnd hsub hm hk⟩
  have hB : ∃ d', (((lbFused ((D x).r (cnt x)) ∧
      GraphFetchBlocks.blkOne (S.dv S.c.tr.length) d'
        (rowWsAux 0 wsInit ((GF.gfGd.gdG.gxProg.getD x []).take (cnt x))) lb ((D x).g (cnt x))
        ((D x).r (cnt x)) ((D x).f (cnt x)) ((D x).f (cnt x + 1))) ∨
      GraphFetchBlocks.blkPair (S.dv S.c.tr.length) d'
        (rowWsAux 0 wsInit ((GF.gfGd.gdG.gxProg.getD x []).take (cnt x))) lb ((D x).g (cnt x))
        ((D x).r (cnt x)) ((D x).f (cnt x)) ((D x).f (cnt x + 1))) ∧
      d' = fab (((L.take (k + 1)).filter (fun e => decide (e ∈ GF.gfDev))).length)) := by
    rw [take_S_r hk, CertZ8.filterSnoc]
    by_cases htq : (D x).tq (cnt x) = true
    · obtain ⟨m, hm, hmc⟩ := hdevIdx ((hiff _ (lookup_lt_Some hlb)).2 (.inr (.inr htq)))
      have hD0 : (D x).dvi (cnt x) = S.dv S.c.tr.length := by
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
      refine ⟨S.dv S.c.tr.length, ?_, ?_⟩
      · rcases hblk (cnt x) lb hlb with ⟨hfu, -, hq⟩ | ⟨-, hq⟩
        · exact .inl ⟨hfu, hq htq' _⟩
        · exact .inr (hq htq' _)
      · rw [hfab, if_neg (by simpa using hnin), Nat.add_zero]
  obtain ⟨d', hblkD, hd'⟩ := hB
  have hperF : ∀ y, y < GF.gfGd.gdG.gxProg.length →
      List.Forall₂ (SilWalk.relW Lb)
        ((GF.gfGd.gdG.gxProg.getD y []).take
          (((L.take k).filter (fun e => decide (e.1 = y))).length))
        (SilWalk.hartPr (SilOrd.pairs S) y) := by
    intro y hy
    rw [← hcnt y]
    exact (hper y hy).2.2
  obtain ⟨lb', o, pa, da, ls', pC', w', hre, hok', hrel'⟩ := hstep S x (cnt x) lb _ _ _ _ _ pC d' k hok
    hp hrel (hshape x _ lb hlb) hblkD hags hk hperF hlb
  have hcntS : ∀ y, CertZ2.bump cnt x y =
      ((L.take (k + 1)).filter (fun e => decide (e.1 = y))).length := by
    intro y
    rw [take_S_r hk, CertZ8.filterSnoc]
    by_cases hy : y = x
    · subst hy; rw [CertZ2.bumpSelf, hcnt y]; simp
    · rw [CertZ2.bumpNe cnt x y hy, hcnt y]
      simp [Ne.symm hy]
  refine ⟨x, lb, hx, hlb, lb', o, pC, pa, da, ls', pC', d', w', hp, hre, hok',
    ⟨fun y hy => ?_, fun s hs => ?_, k + 1, hkl, hcntS, ?_, ?_⟩⟩
  · obtain ⟨hle, ⟨pCy, hpy, hrely⟩, hfy⟩ := hper y hy
    rw [SilOrd.snocPstEnd, SilOrd.pairsSnoc _ _ _ _ _ _ _ hok.1, SilOrd.hartPrSnoc]
    by_cases hy' : y = x
    · subst hy'
      rw [CertZ2.bumpSelf, if_pos rfl]
      refine ⟨lookup_lt_Some hlb, ⟨pC', List.getElem?_set_self (lookup_lt_Some hp), hrel'⟩, ?_⟩
      rw [take_S_r hlb]
      exact CertZ6.forall₂Snoc _ _ _ _ _ hfy hre
    · rw [CertZ2.bumpNe cnt x y hy', if_neg (Ne.symm hy'), List.getElem?_set_ne (Ne.symm hy'),
        List.append_nil]
      exact ⟨hle, ⟨pCy, hpy, hrely⟩, hfy⟩
  · change s ∈ S.c.tr ++ [⟨x, lb'⟩] at hs
    rcases List.mem_append.1 hs with hs | hs
    · exact hagt s hs
    · simp only [List.mem_singleton] at hs
      rw [hs]
      exact hx
  · rw [SilOrd.snocDvEnd]
    exact hd'
  · show (S.c.tr ++ [(⟨x, lb'⟩ : Estep)]).map Estep.esAg = _
    rw [List.map_append, hags, take_S_r hk, List.map_append]
    rfl

/-! # 2. The realized member's lock co from the order -/

theorem SilOrd.projAgs (c : SilCand.CandS) :
    (SilCand.proj c).cdTr.map Estep.esAg = c.tr.map Estep.esAg := by
  apply List.ext_getElem?
  intro k
  rw [List.getElem?_map, List.getElem?_map, SilCand.projTr]
  cases c.tr[k]? <;> simp [SilWalk.projStepAg]

/-- A non-failed `GF` write is a write of the realized member at its trace position in `L`. -/
theorem SilOrd.wrAt (G : Gexec) (dev L : List Geid) (N : Nat) (c : SilCand.CandS) (Lb : Int → Prop)
    (e : Geid) (a : Int) (v : BitVec 8) :
    CertZ8.walkOrd G.gxProg dev L →
    (SilCand.proj c).cdTr.map Estep.esAg = L.map Prod.fst →
    (∀ s, s ∈ (SilCand.proj c).cdTr → s.esAg < N) →
    SilAgree.lblAgreeS G (SilAgree.memberS N c) (fun t => t) Lb →
    gwritesByte G e a v → CertZ24.nf G Lb e →
    ∃ (i : Nat) (s : Estep), L[i]? = some e ∧ (SilCand.proj c).cdTr[i]? = some s ∧
      lbIsW s.esLb = true ∧ ceid (candExec (SilCand.proj c)) i = e := by
  intro hord hags hag hagr hw hnf
  obtain ⟨i, hi⟩ := CertZ30.evOfWr G dev L e a v hord hw
  obtain ⟨s, hs, -, hce⟩ := CertZ8.ceidOrd G.gxProg dev L (SilCand.proj c) i e hord hags hi
  obtain ⟨l, base, vs, j, hl, hwr, -, -⟩ := hw
  have hWl : lbIsW l = true := lbWrIsW _ _ hwr
  rcases hagr e with ⟨h1, -⟩ | ⟨l0, l', h1, h2, hrel⟩
  · rw [hl] at h1; cases h1
  · rw [hl, Option.some.injEq] at h1
    subst h1
    rcases hrel with ⟨-, hre⟩ | ⟨hf, -⟩
    · rw [lblRenId] at hre
      have hW' : lbIsW l' = true := by rw [lblReidxWIsw _ _ hre]; exact hWl
      have hcg := (cgLbl (candExec (SilCand.proj c)) i s hs).1
      rw [SilAgree.memberS, CertZ3.memberLbl N _ e hag, ← hce, hcg, Option.some.injEq] at h2
      exact ⟨i, s, hi, hs, by rw [h2]; exact hW', hce⟩
    · exact absurd ((CertZ24.failIff G Lb e _ hl).1 hf) hnf

/-- **THE REALIZED MEMBER'S SUCCESSFUL-PROTOCOL LOCK CO** from the order. -/
theorem SilOrd.lockCoOfOrdS (G : Gexec) (dev L : List Geid) (N : Nat) (c : SilCand.CandS)
    (Lb : Int → Prop) :
    gwf G → CertZ8.walkOrd G.gxProg dev L → CertZ23.ordCoSP G L Lb →
    c.tr.map Estep.esAg = L.map Prod.fst →
    (∀ s, s ∈ c.tr → s.esAg < N) →
    SilAgree.lblAgreeS G (SilAgree.memberS N c) (fun t => t) Lb →
    (∀ b e v, Lb b → gwritesByte G e b v → CertZ18.sp G b e → CertZ24.nf G Lb e) →
    CertZ18.lockCoSP G (SilAgree.memberS N c) Lb := by
  intro hwf hord hco hags hag hagr hnf b x y vx vy hb hx hy hsx hsy
  have hagsP : (SilCand.proj c).cdTr.map Estep.esAg = L.map Prod.fst := by
    rw [SilOrd.projAgs, hags]
  have hagP := SilCand.projAg c N hag
  obtain ⟨i, si, hi, hsi, hWi, hcei⟩ :=
    SilOrd.wrAt G dev L N c Lb x b vx hord hagsP hagP hagr hx (hnf b x vx hb hx hsx)
  obtain ⟨j, sj, hj, hsj, hWj, hcej⟩ :=
    SilOrd.wrAt G dev L N c Lb y b vy hord hagsP hagP hagr hy (hnf b y vy hb hy hsy)
  have key := CertZ8.memberWixIff N (SilCand.proj c) i j si sj hagP hsi hsj hWi hWj
  rw [hcei, hcej] at key
  show gwix G x < gwix G y ↔
    gwix (CertZ3.member N (SilCand.proj c)) x < gwix (CertZ3.member N (SilCand.proj c)) y
  rw [key]
  constructor
  · intro hlt
    exact hco b x y vx vy i j hb hx hy hsx hsy hlt hi hj
  · intro hij
    have hxw := gwritesByteGwrites G x b vx hwf hx
    have hyw := gwritesByteGwrites G y b vy hwf hy
    rcases Nat.lt_trichotomy (gwix G x) (gwix G y) with h | h | h
    · exact h
    · have := gwixInj G x y hwf.1 hxw hyw h
      subst this
      have := NoDup_lookup hord.1 hi hj
      omega
    · have := hco b y x vy vx j i hb hy hx hsy hsx h hj hi
      omega

theorem SilOrd.hartPrNil (pr : List (Estep × Option Nat)) (x : Nat) :
    (∀ p, p ∈ pr → p.1.esAg ≠ x) → SilWalk.hartPr pr x = [] := by
  intro h
  unfold SilWalk.hartPr
  rw [List.filter_eq_nil_iff.2 (fun p hp => by simpa using h p hp)]
  rfl

/-! # 3. The walk supply from the order -/

namespace CatLin

/-- **THE TWIN STEP SUPPLY AT WALK-INVARIANT STATES (named, W10-4 per pc).** -/
def SilOrd.stepSupplyS (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image)
    (P : Int → Int → Prop) : Prop :=
  ∀ (GF : Gfexec) (ad : List (Geid × Geid)) (z : Geid) (ss : List Seg),
    GF.gfGd.gdG.gxImg = im → rvwmoCatAD GF.gfGd ad → GraphFabConf.gfexecConfZF boot d0 fab GF →
    ioResidueGmo GF → gdiskRead14 GF.gfGd.gdG →
    ss ≠ [] → rawChainC GF.gfGd (ioCross GF) z z ss →
    ∀ D : Nat → CertZ7.EmData, CertZ7.emDataOk boot fab GF D →
    ∀ L : List Geid, CertZ8.walkOrd GF.gfGd.gdG.gxProg GF.gfDev L →
      CertZ23.ordCoSP GF.gfGd.gdG L (GraphFetchN2.lockBytes P) →
    ∃ Rel : CertZ9.HRel,
      (∀ x, x < GF.gfGd.gdG.gxProg.length → Rel x 0 (boot x) (boot x)) ∧
      SilOrd.hartStepRIS d0 GF.gfGd.gdG.gxProg (GraphFetchN2.lockBytes P) L Rel

/-- A successful-protocol lock write is no failed acquire (of any lock byte). -/
def SilOrd.spNfS (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image)
    (P : Int → Int → Prop) : Prop :=
  ∀ (GF : Gfexec) (ad : List (Geid × Geid)),
    GF.gfGd.gdG.gxImg = im → rvwmoCatAD GF.gfGd ad → GraphFabConf.gfexecConfZF boot d0 fab GF →
    ∀ b e v, GraphFetchN2.lockBytes P b → gwritesByte GF.gfGd.gdG e b v →
      CertZ18.sp GF.gfGd.gdG b e → CertZ24.nf GF.gfGd.gdG (GraphFetchN2.lockBytes P) e

/-- **THE TWIN WALK SUPPLY FROM THE ORDER AND THE STEP SUPPLY.** -/
theorem SilOrd.walkSupplyOfOrdStepS (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab)
    (im : Image) (N : Nat) (P : Int → Int → Prop) :
    (∀ (GF : Gfexec) (ad : List (Geid × Geid)), GF.gfGd.gdG.gxImg = im → rvwmoCatAD GF.gfGd ad →
      GraphFabConf.gfexecConfZF boot d0 fab GF →
      GF.gfGd.gdG.gxProg.length ≤ N ∧ GraphFetchBlocks.emPremOk boot GF.gfGd.gdG) →
    orderSupplyCZ3 boot d0 fab im P → SilOrd.spNfS boot d0 fab im P →
    SilOrd.stepSupplyS boot d0 fab im P →
    SilWalk.walkSupplyS boot d0 fab im N P := by
  intro hpre hordS hspnf hstep GF ad z ss him hc hconf hres hdr hne hch
  obtain ⟨hN, hp2⟩ := hpre GF ad him hc hconf
  obtain ⟨D, hD⟩ := CertZ7.emDataOfConf boot d0 fab GF hconf hp2
  obtain ⟨L, hL, hco⟩ := hordS GF ad him hc hconf hres
  obtain ⟨Rel, hR0, hsR⟩ := hstep GF ad z ss him hc hconf hres hdr hne hch D hD L hL hco
  have hsub : ∀ e, e ∈ GF.gfDev → e ∈ L := by
    intro e he
    obtain ⟨n, hn⟩ := List.mem_iff_getElem?.1 he
    obtain ⟨i, k⟩ := e
    obtain ⟨row, hrow, hk⟩ := hconf.2.2.1 n i k hn
    have hi : i < GF.gfGd.gdG.gxProg.length := lookup_lt_Some hrow
    refine (hL.2.1 _).2 ⟨hi, ?_⟩
    rw [List.getD_eq_getElem?_getD, hrow, Option.getD_some]
    exact hk
  have hshape : ∀ (x n : Nat) (lb : Lbl), (GF.gfGd.gdG.gxProg.getD x [])[n]? = some lb →
      CertZ4.lblShape lb := by
    intro x n lb hlb
    have hx : x < GF.gfGd.gdG.gxProg.length := by
      refine Nat.lt_of_not_le (fun hge => ?_)
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge, Option.getD_none] at hlb
      cases hlb
    have hl : gxLbl GF.gfGd.gdG (x, n) = some lb := by
      unfold gxLbl
      rw [CertZ7.getDSome _ x hx]
      exact hlb
    have := gwfLblShape GF.gfGd.gdG (x, n) lb hc.1 hl
    cases lb <;> exact this
  refine ⟨SilOrd.inv GF.gfGd.gdG.gxProg _ (fun x => (D x).f) Rel (SilOrd.pref L GF.gfDev fab),
    ?_, SilOrd.walkPolOfOrdS boot d0 fab GF D L _ Rel hD hconf.2.1 hL hsub hshape hsR, ?_⟩
  · refine ⟨fun x hx => ⟨Nat.zero_le _, ⟨boot x, ?_, ?_⟩, ?_⟩, fun s hs => by
      simp [SilWalk.start] at hs, ⟨0, Nat.zero_le _, fun x => by simp, ?_, by simp [SilWalk.start]⟩⟩
    · show ((List.range' 0 N).map boot)[x]? = some (boot x)
      rw [List.getElem?_map, lookup_seq_lt (by omega), Nat.zero_add]
      rfl
    · obtain ⟨_, _, _, _, _, hf0, _⟩ := hD x _ (CertZ7.getDSome _ x hx)
      show Rel x 0 ((D x).f 0) (boot x)
      rw [hf0]
      exact hR0 x hx
    · simp [SilOrd.pairs, SilWalk.start, SilWalk.hartPr]
    · show d0 = fab _
      simp only [List.take_zero, List.filter_nil, List.length_nil]
      exact hconf.1.symm
  · intro Sf cntF hinv hok hdone
    obtain ⟨hper, hagt, ⟨k, hkL, hcnt, -, hags⟩⟩ := hinv
    have hk : k = L.length := by
      refine Nat.le_antisymm hkL (Nat.le_of_not_lt (fun hlt => ?_))
      obtain ⟨⟨x, a⟩, hx⟩ : ∃ e, L[k]? = some e := ⟨L[k], List.getElem?_eq_getElem hlt⟩
      have hev := (hL.2.1 _).1 (List.mem_of_getElem? hx)
      have hca := CertZ8.ordCount _ _ L k x a hL hx
      rw [← hcnt x] at hca
      have := hdone x hev.1
      have := hev.2
      dsimp only at this
      omega
    rw [hk, List.take_length] at hags
    have hagN : ∀ s, s ∈ Sf.c.tr → s.esAg < N := fun s hs => by have := hagt s hs; omega
    have hlenS : Sf.c.sil.length = Sf.c.tr.length := hok.1
    have hprojTr : (SilCand.proj Sf.c).cdTr
        = (SilOrd.pairs Sf).map (fun p => SilCand.projStep p.1 p.2) := by
      have h1 : (SilOrd.pairs Sf).map Prod.fst = Sf.c.tr := List.map_fst_zip (by omega)
      have h2 : (SilOrd.pairs Sf).map Prod.snd = Sf.c.sil := List.map_snd_zip (by omega)
      show Sf.c.tr.mapIdx (fun k s => SilCand.projStep s (Sf.c.sil.getD k none)) = _
      conv => lhs; rw [← h1, ← h2]
      exact SilWalk.projMapIdx _
    have hagr : SilAgree.lblAgreeS GF.gfGd.gdG (SilAgree.memberS N Sf.c) (fun t => t)
        (GraphFetchN2.lockBytes P) := by
      refine SilWalk.lblAgreeOfRows _ N _ Sf.c (SilCand.projAg Sf.c N hagN) (fun x => ?_)
      rw [hprojTr, SilWalk.hartTrProj]
      refine SilWalk.forall₂Map _ _ _ _ _ ?_ (fun a b h => SilWalk.relSOfW _ a b h)
      by_cases hx : x < GF.gfGd.gdG.gxProg.length
      · obtain ⟨hle, -, hf⟩ := hper x hx
        rw [List.take_of_length_le (Nat.le_antisymm hle (hdone x hx) ▸ Nat.le_refl _)] at hf
        exact hf
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega), Option.getD_none,
          SilOrd.hartPrNil]
        · exact .nil
        · intro p hp
          have hmem : p.1 ∈ Sf.c.tr := (List.of_mem_zip hp).1
          have := hagt p.1 hmem
          omega
    exact SilOrd.lockCoOfOrdS _ GF.gfDev L N Sf.c _ hc.1 hL hco hags hagN hagr
      (hspnf GF ad him hc hconf)

/-! # 4. The zero-cut kill -/

section glue

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode
open Language.Notation PrimStep
open LeanRV64D

/-- **`cycleKillOfOrdStepS`** — THE ZERO-CUT KILL AT THE SILENT TWIN: the twin weak-WP tier, (harts ≤ N ∧
P2), the walk ORDER (input), sp writes are no failed acquires, the twin STEP supply, and the lock facts /
L2′ claim at REALIZED members. -/
theorem SilOrd.cycleKillOfOrdStepS (hlc : HasLC) (GF0 : BundledGFunctors) [MachGpreS hlc GF0]
    [WeakGpreS GF0] (gen : Nat) (σ0 : WGState) (D : CPU → List Register) (hD : ∀ c, (D c).Nodup)
    (P : Int → Int → Prop)
    (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (N : Nat) :
    freshEra gen σ0 →
    (List.range' 0 N).map boot = epsInit σ0 →
    d0 = efInit σ0.wgdev →
    SilKill.wpPackageS hlc GF0 gen σ0 D →
    SilKill.regZeroRunS gen σ0 P →
    (∀ ρ, rtc SilEpf.epfRunS (epInit gen, σ0) ρ → efetchItvOk ρ.1 ρ.2) →
    (∀ (GF : Gfexec) (ad : List (Geid × Geid)), GF.gfGd.gdG.gxImg = imgZ σ0.wgimg →
      rvwmoCatAD GF.gfGd ad → GraphFabConf.gfexecConfZF boot d0 fab GF →
      GF.gfGd.gdG.gxProg.length ≤ N ∧ GraphFetchBlocks.emPremOk boot GF.gfGd.gdG) →
    orderSupplyCZ3 boot d0 fab (imgZ σ0.wgimg) P →
    SilOrd.spNfS boot d0 fab (imgZ σ0.wgimg) P →
    SilOrd.stepSupplyS boot d0 fab (imgZ σ0.wgimg) P →
    SilKill.acqAqS boot d0 fab (imgZ σ0.wgimg) N P →
    SilKill.relCoversS boot d0 fab (imgZ σ0.wgimg) N P →
    SilKill.l2ClaimS boot d0 fab (imgZ σ0.wgimg) N P (SilKill.badRunS gen σ0) →
    cycleKillCZC boot d0 fab (imgZ σ0.wgimg) :=
  fun hfr hb1 hb2 hwp hrz hcov hpre hordS hspnf hstep hAQ hRC hl2 =>
    SilKill.cycleKillOfL2S hlc GF0 gen σ0 D hD P boot d0 fab N hfr hb1 hb2 hwp hrz hcov
      (cutSupplyOfCycleCZC boot d0 fab _)
      (SilWalk.certSupplyOfWalkS boot d0 fab _ N P
        (SilOrd.walkSupplyOfOrdStepS boot d0 fab _ N P hpre hordS hspnf hstep))
      hAQ hRC hl2

end glue

end CatLin

end Weak
