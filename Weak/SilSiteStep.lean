/-
Weak: **row 6m (W11-F B5), increment D1 — the twin port of `CertZ13.hartStepOfSite`: the twin walk's
per-step datum FROM the per-site read datum** (`PROGRESS-W11F-6i6m.md` Task D).  Lean-only, no Rocq twin.

  §1  **the datum at the EMISSION's block** (F10): `SilOrd.hartStepRIS` / `SilSite.atSteps` quantify the
      emission block (`ws`, `ls`, `l`, `pE`, `pE'`) freely, but their only consumer
      (`SilOrd.walkPolOfOrdS`) applies them at the emission datum's block; a free block is FALSE-suspect
      (fetch answers that are not the memory's bytes, a `wRelp` other than the row prefix's, a fabric
      the walk's bookkeeping does not know).  `SilSiteStep.stepCtxD` / **`hartStepRISD`** / `atStepsD`
      restate them at `D`'s block (`hartStepRISOfFree`, `atStepsDOf`: the old forms imply the new), and
      `walkPolOfOrdSD` / **`CatLin.SilSiteStep.walkSupplyOfOrdStepSD`** are `SilOrd`'s walk policy /
      supply with the restricted datum (proofs copied, the datum's application unchanged) → the
      `SilWalk.walkSupplyS` that `SilKillT.certSupplyOfWalkS` consumes;
  §2  **`relpAgreeS`** — the twin's release-pending bit IS the row prefix's (from the walk's `relW`
      invariant; `CertZ6.relpAgree`'s twin) — so no `wRelp` premise;
  §3  re-timing: `starRetS` (a star's fetch answers re-timed, `fetchQ` = TEXT CUSTODY at the twin),
      `oneRetS` / `pairRetS` (the realizing read re-timed, `setTs`);
  §4  **`twinBlk`** (the twin's block for a twin label) and **`stepOfTwinBlk`** (→ `SilWalk.stepOk`:
      ordinary, or SILENT with the shadow's dependency bound `depAll`); `twinBlkLock` (lockstep: the
      emission's block re-timed);
  §5  the premises beyond the read datum: **`silentQD`** (the failed acquire: `silentQ` + `rl = false` +
      the silent write's dependency bound), `poisLbl`, `relS TR` (lockstep or `TR`-tainted), **`sailQ`**
      (F11: the Sail meaning of `SilSiteTaint.siteOk` — the value/bit-aware `csync`, NOT proved here);
      `memAgree` (the twin label of an agreeing step); F12 `poisonOkL` / **`valQL`** (`SilSite.valQ` at
      the same read width), `readDatumPtL`;
  §6  **`hartStepOfSiteSD`** (the datum from the five read families with `valQL`, `rmwQ`, `silentQD`,
      `fetchQ`, `sailQ`) and **`hartStepOfAgreeSD`** (every census read AGREES — NO Sail premise);
      `CatLin.SilSiteStep.siteSupplySD` → **`stepSupplyOfSiteSD`**;
  §7  the trimmed kills at the restricted datum (`CatLin.SilSiteStep.cycleKillSD` / `cycleKillZSD`).

Spec: FAITHFUL (proof organisation; the restricted datum is strictly weaker than the old one; every
premise is a per-step fact at the emission's block — none is a memory-model choice).  Lean-only helpers
`SilSiteStep.*`.
-/
import Weak.SilSite
import Weak.SilKillT

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open TsoShadow

namespace SilSiteStep

/-! # 1. The datum at the emission's block -/

/-- The emission datum's block of hart `x` at slot `n` (row label `lb`), at fabric `d → d'`. -/
def emBlk (D : Nat → CertZ7.EmData) (rows : List (List Lbl)) (x n : Nat) (lb : Lbl) (d d' : Efab) :
    Prop :=
  (lbFused ((D x).r n) ∧
    GraphFetchBlocks.blkOne d d' (rowWsAux 0 wsInit ((rows.getD x []).take n)) lb ((D x).g n)
      ((D x).r n) ((D x).f n) ((D x).f (n + 1))) ∨
  GraphFetchBlocks.blkPair d d' (rowWsAux 0 wsInit ((rows.getD x []).take n)) lb ((D x).g n)
    ((D x).r n) ((D x).f n) ((D x).f (n + 1))

/-- **THE STEP CONTEXT AT THE EMISSION'S BLOCK**: a twin walk state, hart `x`'s twin program state `pC`
related to its emission state `(D x).f n`, the emission's block at the walk's fabric, the next order event
`L[k] = (x, n)` with hart `x`'s count `n`, and every hart's appended labels `relW` of its row prefix. -/
def stepCtxD (d0 : Efab) (rows : List (List Lbl)) (Lb : Int → Prop) (L : List Geid)
    (Rel : CertZ9.HRel) (D : Nat → CertZ7.EmData) (S : SilWalk.St) (x n : Nat) (lb : Lbl)
    (pC : Pexv6) (d' : Efab) (k : Nat) : Prop :=
  SilWalk.ok d0 S ∧
  (S.pst S.c.tr.length)[x]? = some pC ∧ Rel x n ((D x).f n) pC ∧ CertZ4.lblShape lb ∧
  emBlk D rows x n lb (S.dv S.c.tr.length) d' ∧
  S.c.tr.map Estep.esAg = (L.take k).map Prod.fst ∧
  L[k]? = some (x, n) ∧
  ((L.take k).filter (fun e => decide (e.1 = x))).length = n ∧
  (∀ y, y < rows.length →
    List.Forall₂ (SilWalk.relW Lb)
      ((rows.getD y []).take (((L.take k).filter (fun e => decide (e.1 = y))).length))
      (SilWalk.hartPr (SilOrd.pairs S) y)) ∧
  (rows.getD x [])[n]? = some lb

/-- **THE PER-STEP DATUM AT THE EMISSION'S BLOCK** (`SilOrd.hartStepRIS` restricted to where
`SilOrd.walkPolOfOrdS` uses it). -/
def hartStepRISD (d0 : Efab) (rows : List (List Lbl)) (Lb : Int → Prop) (L : List Geid)
    (Rel : CertZ9.HRel) (D : Nat → CertZ7.EmData) : Prop :=
  ∀ (S : SilWalk.St) (x n : Nat) (lb : Lbl) (pC : Pexv6) (d' : Efab) (k : Nat),
    stepCtxD d0 rows Lb L Rel D S x n lb pC d' k →
    ∃ (lb' : Lbl) (o : Option Nat) (pa : Pexv6) (da : Efab) (ls' : List Wlabel) (pC' : Pexv6)
      (w' : Wstate),
      SilWalk.relW Lb lb (lb', o) ∧ SilWalk.stepOk S x lb' o pC pa da ls' pC' d' w' ∧
      Rel x (n + 1) ((D x).f (n + 1)) pC'

/-- The restricted context is an instance of `SilSite.stepCtx`. -/
theorem stepCtxOfD (d0 : Efab) (rows : List (List Lbl)) (Lb : Int → Prop) (L : List Geid)
    (Rel : CertZ9.HRel) (D : Nat → CertZ7.EmData) (S : SilWalk.St) (x n : Nat) (lb : Lbl)
    (pC : Pexv6) (d' : Efab) (k : Nat) :
    stepCtxD d0 rows Lb L Rel D S x n lb pC d' k →
    SilSite.stepCtx d0 rows Lb L Rel S x n lb (rowWsAux 0 wsInit ((rows.getD x []).take n))
      ((D x).g n) ((D x).r n) ((D x).f n) ((D x).f (n + 1)) pC d' k :=
  fun ⟨h1, h2, h3, h4, h5, h6, h7, _, h9, h10⟩ => ⟨h1, h2, h3, h4, h5, h6, h7, h9, h10⟩

/-- The free datum implies the restricted one. -/
theorem hartStepRISOfFree (d0 : Efab) (rows : List (List Lbl)) (Lb : Int → Prop) (L : List Geid)
    (Rel : CertZ9.HRel) (D : Nat → CertZ7.EmData) :
    SilOrd.hartStepRIS d0 rows Lb L Rel → hartStepRISD d0 rows Lb L Rel D := by
  intro h S x n lb pC d' k hctx
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, _, h9, h10⟩ := hctx
  exact h S x n lb _ _ _ _ _ pC d' k h1 h2 h3 h4 h5 h6 h7 h9 h10

/-- `Q` at every step of the restricted quantifier (`Q` sees hart `x`'s twin state `pC`, the slot `n`
and the next fabric `d'`). -/
def atCtxD (d0 : Efab) (rows : List (List Lbl)) (Lb : Int → Prop) (L : List Geid)
    (Rel : CertZ9.HRel) (D : Nat → CertZ7.EmData)
    (Q : SilWalk.St → Nat → Nat → Lbl → Pexv6 → Efab → Prop) : Prop :=
  ∀ (S : SilWalk.St) (x n : Nat) (lb : Lbl) (pC : Pexv6) (d' : Efab) (k : Nat),
    stepCtxD d0 rows Lb L Rel D S x n lb pC d' k → Q S x n lb pC d'

/-- A `SilSite` premise family at the restricted quantifier (the block is `D`'s). -/
def atStepsD (d0 : Efab) (rows : List (List Lbl)) (Lb : Int → Prop) (L : List Geid)
    (Rel : CertZ9.HRel) (D : Nat → CertZ7.EmData)
    (Q : SilWalk.St → Nat → Lbl → List Wlabel → Prop) : Prop :=
  atCtxD d0 rows Lb L Rel D (fun S x n lb _ _ => Q S x lb ((D x).g n))

/-- Every `SilSite.atSteps` premise gives its restricted form. -/
theorem atStepsDOf (d0 : Efab) (rows : List (List Lbl)) (Lb : Int → Prop) (L : List Geid)
    (Rel : CertZ9.HRel) (D : Nat → CertZ7.EmData) (Q : SilWalk.St → Nat → Lbl → List Wlabel → Prop) :
    SilSite.atSteps d0 rows Lb L Rel Q → atStepsD d0 rows Lb L Rel D Q :=
  fun h S x n lb pC d' k hctx =>
    h S x n lb _ _ _ _ _ pC d' k (stepCtxOfD d0 rows Lb L Rel D S x n lb pC d' k hctx)

/-- **THE TWIN POLICY FROM THE ORDER AND THE RESTRICTED DATUM** (`SilOrd.walkPolOfOrdS`'s proof; the
datum is applied at the emission's block exactly as there). -/
theorem walkPolOfOrdSD (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (GF : Gfexec)
    (D : Nat → CertZ7.EmData) (L : List Geid) (Lb : Int → Prop) (Rel : CertZ9.HRel) :
    CertZ7.emDataOk boot fab GF D → GF.gfDev.Nodup →
    CertZ8.walkOrd GF.gfGd.gdG.gxProg GF.gfDev L →
    (∀ e, e ∈ GF.gfDev → e ∈ L) →
    (∀ (x n : Nat) (lb : Lbl), (GF.gfGd.gdG.gxProg.getD x [])[n]? = some lb → CertZ4.lblShape lb) →
    hartStepRISD d0 GF.gfGd.gdG.gxProg Lb L Rel D →
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
  have hB : ∃ d', emBlk D GF.gfGd.gdG.gxProg x (cnt x) lb (S.dv S.c.tr.length) d' ∧
      d' = fab (((L.take (k + 1)).filter (fun e => decide (e ∈ GF.gfDev))).length) := by
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
  obtain ⟨lb', o, pa, da, ls', pC', w', hre, hok', hrel'⟩ := hstep S x (cnt x) lb pC d' k
    ⟨hok, hp, hrel, hshape x _ lb hlb, hblkD, hags, hk, (hcnt x).symm, hperF, hlb⟩
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

end SilSiteStep

namespace CatLin

/-- **THE TWIN STEP SUPPLY AT THE EMISSION'S BLOCK** (`SilOrd.stepSupplyS` with the restricted datum). -/
def SilSiteStep.stepSupplySD (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image)
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
      SilSiteStep.hartStepRISD d0 GF.gfGd.gdG.gxProg (GraphFetchN2.lockBytes P) L Rel D

/-- The free supply implies the restricted one. -/
theorem SilSiteStep.stepSupplySDOfS (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image)
    (P : Int → Int → Prop) :
    SilOrd.stepSupplyS boot d0 fab im P → SilSiteStep.stepSupplySD boot d0 fab im P := by
  intro h GF ad z ss him hc hconf hres hdr hne hch D hD L hL hco
  obtain ⟨Rel, h0, hs⟩ := h GF ad z ss him hc hconf hres hdr hne hch D hD L hL hco
  exact ⟨Rel, h0, SilSiteStep.hartStepRISOfFree _ _ _ _ _ D hs⟩

/-- **THE TWIN WALK SUPPLY FROM THE ORDER AND THE RESTRICTED STEP SUPPLY**
(`SilOrd.walkSupplyOfOrdStepS`'s proof with `walkPolOfOrdSD`). -/
theorem SilSiteStep.walkSupplyOfOrdStepSD (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab)
    (im : Image) (N : Nat) (P : Int → Int → Prop) :
    (∀ (GF : Gfexec) (ad : List (Geid × Geid)), GF.gfGd.gdG.gxImg = im → rvwmoCatAD GF.gfGd ad →
      GraphFabConf.gfexecConfZF boot d0 fab GF →
      GF.gfGd.gdG.gxProg.length ≤ N ∧ GraphFetchBlocks.emPremOk boot GF.gfGd.gdG) →
    orderSupplyCZ3 boot d0 fab im P → SilOrd.spNfS boot d0 fab im P →
    SilSiteStep.stepSupplySD boot d0 fab im P →
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
    ?_, SilSiteStep.walkPolOfOrdSD boot d0 fab GF D L _ Rel hD hconf.2.1 hL hsub hshape hsR, ?_⟩
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

end CatLin

namespace SilSiteStep

/-! # 2. The twin's release-pending bit is the row prefix's -/

/-- `mnext`'s agent states: the acting agent moves by `lblPost` at the log length, the others stay. -/
theorem mnextWs (σ : Mstate) (i : Nat) (lb : Lbl) (j : Nat) :
    (mnext σ i lb).msWs j = if j = i then lblPost σ.msLog.length (σ.msWs i) lb else σ.msWs j := by
  cases lb with
  | LIo kd base vs =>
    show σ.msWs j = _
    by_cases h : j = i
    · subst h; rw [if_pos rfl]; rfl
    · rw [if_neg h]
  | _ => rfl

/-- **One twin step moves the release-pending bit by `lpostRelp`** (a silent AMO as its RMW label). -/
theorem nextSRelp (σ : Mstate) (s : Estep) (o : Option Nat) (j : Nat) :
    ((SilCand.nextS σ s o).msWs j).wRelp =
      if s.esAg = j then lpostRelp (σ.msWs j).wRelp s.esLb else (σ.msWs j).wRelp := by
  obtain ⟨i, lb⟩ := s
  have hold : ((mnext σ i lb).msWs j).wRelp =
      if i = j then lpostRelp (σ.msWs j).wRelp lb else (σ.msWs j).wRelp := by
    rw [mnextWs]
    by_cases h : i = j
    · subst h; rw [if_pos rfl, if_pos rfl, lblPostRelp]
    · rw [if_neg (Ne.symm h), if_neg h]
  cases o with
  | none => exact hold
  | some q =>
    cases lb with
    | LRmw aq rl base ts rvs wvs kc =>
      show ((updWs σ.msWs i (SilCand.silentPost (σ.msWs i) aq base ts wvs.length q)) j).wRelp = _
      unfold updWs
      by_cases h : i = j
      · subst h
        rw [if_pos rfl, if_pos rfl]
        show (storePostRun (SilCand.aqRaise (loadPostRun (σ.msWs i) aq base ts) q) false base
          wvs.length q).wRelp = _
        rw [storePostRunRelp]
        cases wvs with
        | nil =>
          show (SilCand.aqRaise (loadPostRun (σ.msWs i) aq base ts) q).wRelp = (σ.msWs i).wRelp
          exact WeakRvwmoConf.loadPostRunRelp _ _ _ _
        | cons _ _ => rfl
      · rw [if_neg (Ne.symm h), if_neg h]
    | LLoad => exact hold
    | LStore => exact hold
    | LFence => exact hold
    | LIo => exact hold

/-- The twin's release-pending bit of agent `x` at index `k` is the fold of `x`'s labels so far. -/
theorem stAtRelp (c : SilCand.CandS) (x : Nat) :
    ∀ k, k ≤ c.tr.length →
      ((SilCand.stAt c k).msWs x).wRelp =
        (((c.tr.take k).filter (fun s => decide (s.esAg = x))).map Estep.esLb).foldl lpostRelp false := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hk
    obtain ⟨s, hs⟩ : ∃ s, c.tr[k]? = some s := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    rw [SilReplay.stAtSucc c k s hs, nextSRelp, ih (by omega), take_S_r hs, List.filter_append,
      List.map_append, List.foldl_append]
    by_cases h : s.esAg = x
    · rw [if_pos h]
      simp [h]
    · rw [if_neg h]
      simp [h]

/-- The appended labels of agent `x`, read off the pairs. -/
theorem hartPrFst (tr : List Estep) (sil : List (Option Nat)) (x : Nat) :
    sil.length = tr.length →
    (SilWalk.hartPr (tr.zip sil) x).map Prod.fst =
      (tr.filter (fun s => decide (s.esAg = x))).map Estep.esLb := by
  induction tr generalizing sil with
  | nil => intro _; rfl
  | cons s tr ih =>
    intro h
    cases sil with
    | nil => cases h
    | cons o sil =>
      rw [List.zip_cons_cons, SilWalk.hartPrCons]
      by_cases hx : s.esAg = x
      · rw [if_pos hx]
        simp only [List.map_cons, List.filter_cons, hx, decide_true, if_true]
        rw [ih sil (by simpa using h)]
      · rw [if_neg hx]
        simp only [List.filter_cons, hx, decide_false]
        exact ih sil (by simpa using h)

theorem forall₂MapR {α β γ : Type _} (R : α → β → Prop) (Q : α → γ → Prop) (f : β → γ) (l1 : List α)
    (l2 : List β) : List.Forall₂ R l1 l2 → (∀ a b, R a b → Q a (f b)) → List.Forall₂ Q l1 (l2.map f) := by
  intro h hf
  induction h with
  | nil => exact .nil
  | cons hab _ ih => exact .cons (hf _ _ hab) ih

/-- The twin's current state. -/
abbrev cur (S : SilWalk.St) : Mstate := SilSite.cur S

/-- **`relpAgreeS` — THE TWIN'S RELEASE-PENDING BIT IS THE ROW PREFIX'S** (the walk's `relW` invariant). -/
theorem relpAgreeS (S : SilWalk.St) (Lb : Int → Prop) (x : Nat) (row : List Lbl) (n : Nat) :
    S.c.sil.length = S.c.tr.length →
    List.Forall₂ (SilWalk.relW Lb) (row.take n) (SilWalk.hartPr (SilOrd.pairs S) x) →
    ((cur S).msWs x).wRelp = (rowWsAux 0 wsInit (row.take n)).wRelp := by
  intro hlen h
  have h1 : List.Forall₂ lblReidxW (row.take n) ((SilWalk.hartPr (SilOrd.pairs S) x).map Prod.fst) :=
    forall₂MapR _ _ _ _ _ h (fun _ _ hr => hr.1)
  have h2 := CertZ6.foldRelpReidx false _ _ h1
  have h3 : (SilWalk.hartPr (SilOrd.pairs S) x).map Prod.fst =
      (S.c.tr.filter (fun s => decide (s.esAg = x))).map Estep.esLb := hartPrFst S.c.tr S.c.sil x hlen
  rw [h3] at h2
  show ((SilCand.stAt S.c S.c.tr.length).msWs x).wRelp = _
  rw [stAtRelp S.c x _ (Nat.le_refl _), List.take_length, rowWsAuxRelp, h2]
  rfl


/-! # 3. Re-timing: the star's fetches, the realizing read -/

/-- Two stars equal but for the timestamps of fetch answers. -/
def fetchEqv (ls lsC : List Wlabel) : Prop :=
  List.Forall₂ (fun a b => a = b ∨
    ∃ (base : Int) (tvs tvs' : List (Nat × BitVec 8)),
      a = Wlabel.LIFetch base tvs ∧ b = Wlabel.LIFetch base tvs') ls lsC

/-- A fetch moves no agent state: fetch-equivalent stars fold to the same shadow state. -/
theorem starWsEqv (w : Wstate) (n : Nat) (ls lsC : List Wlabel) :
    fetchEqv ls lsC → SilDep.starWs w ls n = SilDep.starWs w lsC n := by
  intro h
  induction h generalizing w with
  | nil => rfl
  | @cons a b la lb hab _ ih =>
    show SilDep.starWs (SilDep.wsStep w a n) la n = SilDep.starWs (SilDep.wsStep w b n) lb n
    rcases hab with rfl | ⟨base, tvs, tvs', rfl, rfl⟩
    · exact ih _
    · exact ih w

/-- **THE STAR, RE-TIMED**: every fetch answer of a star replaced by an equal-valued one satisfying `F`
(when one exists) — a star again, fetch-equivalent. -/
theorem starRetS (F : Int → List (Nat × BitVec 8) → Prop) (instr : Bool) (p : Pexv6) (d : Efab)
    (ls : List Wlabel) (p' : Pexv6) (d' : Efab) :
    admRunG pstepEv instr p d ls p' d' →
    (∀ base tvs, Wlabel.LIFetch base tvs ∈ ls →
      ∃ tvs' : List (Nat × BitVec 8), tvs'.map Prod.snd = tvs.map Prod.snd ∧ F base tvs') →
    ∃ lsC, admRunG pstepEv instr p d lsC p' d' ∧
      (∀ base tvs, Wlabel.LIFetch base tvs ∈ lsC → F base tvs) ∧ fetchEqv ls lsC := by
  intro h
  induction h with
  | nil p d => exact fun _ => ⟨[], .nil p d, fun _ _ hm => (by cases hm), .nil⟩
  | cons p d l p1 d1 ls p' d' ha hs _ ih =>
    intro hF
    obtain ⟨lsC, hrun, hfet, heqv⟩ :=
      ih (fun base tvs hm => hF base tvs (List.mem_cons.2 (.inr hm)))
    cases l with
    | LIFetch base tvs =>
      obtain ⟨tvs', hv, hf⟩ := hF base tvs (List.mem_cons.2 (.inl rfl))
      refine ⟨.LIFetch base tvs' :: lsC,
        .cons p d _ p1 d1 _ p' d' ha (pstepEvTsIfetch _ _ _ _ _ _ _ hs hv) hrun, ?_,
        .cons (.inr ⟨base, tvs, tvs', rfl, rfl⟩) heqv⟩
      intro b t hm
      rcases List.mem_cons.1 hm with he | hm
      · cases he; exact hf
      · exact hfet b t hm
    | _ =>
      refine ⟨_ :: lsC, .cons p d _ p1 d1 _ p' d' ha hs hrun, ?_, .cons (.inl rfl) heqv⟩
      intro b t hm
      rcases List.mem_cons.1 hm with he | hm
      · cases he
      · exact hfet b t hm

/-- **TEXT CUSTODY at the twin (named; the old `CertZ5.fetchAgree`'s twin)**: every fetch of the star
reads bytes the twin can fetch at view 0 (equal values, its own timestamps). -/
def fetchQ (S : SilWalk.St) (ls : List Wlabel) : Prop :=
  ∀ (base : Int) (tvs : List (Nat × BitVec 8)), Wlabel.LIFetch base tvs ∈ ls →
    ∃ tvs' : List (Nat × BitVec 8), tvs'.map Prod.snd = tvs.map Prod.snd ∧
      ifetchOk (cur S).msImg (cur S).msLog 0 base tvs'

/-- The row label at the twin's read timestamps `ts'` (values kept). -/
def setTs (lb : Lbl) (ts' : List Nat) : Lbl :=
  match lb with
  | .LLoad aq base _ vs => .LLoad aq base ts' vs
  | .LRmw aq rl base _ rvs wvs kc => .LRmw aq rl base ts' rvs wvs kc
  | l => l

/-- A fused realizing step, its read RE-TIMED to `ts'` (values kept), at a state with the same
release-pending bit. -/
theorem oneRetS (pa : Pexv6) (da : Efab) (ws wt : Wstate) (lb : Lbl) (l : Wlabel) (p' : Pexv6)
    (d' : Efab) (ts' : List Nat) :
    wt.wRelp = ws.wRelp → lbFused l → hlblRealizes pa ws lb l → pstepEv pa da l p' d' →
    (∀ aq base ts vs, lb = .LLoad aq base ts vs → ts'.length = ts.length) →
    ∃ l', hlblRealizes pa wt (setTs lb ts') l' ∧ pstepEv pa da l' p' d' := by
  intro hr hf hre hst hlen
  obtain ⟨hnb, hlat, hrf, hpr⟩ := hlblRealizesRelp pa ws wt lb l hr hre
  cases l with
  | LLoad aq lat base tvs asrc =>
    simp only [latFree] at hlat
    simp only [lbRfoldfree] at hrf
    subst hlat hrf
    simp only [projLbl, Option.some.injEq] at hpr
    subst hpr
    have hl := hlen aq base _ _ rfl
    rw [List.length_map] at hl
    have h1 : ts'.length ≤ (tvs.map Prod.snd).length := by rw [List.length_map]; omega
    have h2 : (tvs.map Prod.snd).length ≤ ts'.length := by rw [List.length_map]; omega
    refine ⟨.LLoad aq false base (ts'.zip (tvs.map Prod.snd)) [], ⟨trivial, rfl, rfl, ?_⟩, ?_⟩
    · simp only [projLbl, setTs]
      rw [List.map_fst_zip h1, List.map_snd_zip h2]
    · exact pstepEvTsLoad _ _ _ _ _ _ _ _ hst (List.map_snd_zip h2)
  | LRmw => exact absurd hst (pstepEvNoRmw _ _ _ _ _ _ _ _ _ _ _)
  | LExLoad => exact absurd hf (by simp [lbFused])
  | LExStore => exact absurd hf (by simp [lbFused])
  | LStore rl base data asrc vsrc =>
    simp only [projLbl, Option.some.injEq] at hpr
    subst hpr
    exact ⟨_, ⟨hnb, trivial, hrf, rfl⟩, hst⟩
  | LFence pr pw sr sw =>
    simp only [projLbl, Option.some.injEq] at hpr
    subst hpr
    exact ⟨_, ⟨hnb, trivial, hrf, rfl⟩, hst⟩
  | LDev kd base vs sa sv =>
    simp only [projLbl, Option.some.injEq] at hpr
    subst hpr
    exact ⟨_, ⟨hnb, trivial, hrf, rfl⟩, hst⟩
  | LSilent => simp [projLbl] at hpr
  | LRegW => simp [projLbl] at hpr
  | LCtrl => simp [projLbl] at hpr
  | LInstr => simp [projLbl] at hpr
  | LIFetch => simp [projLbl] at hpr

/-- The exclusive pair, its read RE-TIMED to `ts'` (values kept), at a state with the same
release-pending bit. -/
theorem pairRetS (pa pm2 : Pexv6) (ws wt : Wstate) (lb : Lbl) (l1 l2 : Wlabel) (ts' : List Nat) :
    wt.wRelp = ws.wRelp → hlblRealizesPair pa pm2 ws lb l1 l2 →
    (∀ aq rl base ts rvs wvs kc, lb = .LRmw aq rl base ts rvs wvs kc → ts'.length = ts.length) →
    ∃ l1', hlblRealizesPair pa pm2 wt (setTs lb ts') l1' l2 ∧
      ∀ (da : Efab) (pm : Pexv6) (dm : Efab), pstepEv pa da l1 pm dm → pstepEv pa da l1' pm dm := by
  rintro hr ⟨aq, rl, base, tvs, data, asrc1, asrc2, vsrc2, rfl, rfl, hne, hlen, rfl⟩ hts
  have hl := hts aq rl base _ _ _ _ rfl
  rw [List.length_map] at hl
  have h1 : ts'.length ≤ (tvs.map Prod.snd).length := by rw [List.length_map]; omega
  have h2 : (tvs.map Prod.snd).length ≤ ts'.length := by rw [List.length_map]; omega
  refine ⟨.LExLoad aq base (ts'.zip (tvs.map Prod.snd)) asrc1,
    ⟨aq, rl, base, ts'.zip (tvs.map Prod.snd), data, asrc1, asrc2, vsrc2, rfl, rfl, hne,
      by rw [List.length_zip, List.length_map]; omega, ?_⟩,
    fun da pm dm h => pstepEvTsExload _ _ _ _ _ _ _ _ _ h (List.map_snd_zip h2)⟩
  simp only [setTs]
  rw [List.map_fst_zip h1, List.map_snd_zip h2,
    WeakRvwmoConf.pclsEvRelp pm2 _ (loadPostRun wt aq base ts')
      (loadPostRun ws aq base (tvs.map Prod.fst))
      (by rw [WeakRvwmoConf.loadPostRunRelp, WeakRvwmoConf.loadPostRunRelp, hr])]

/-- A fused step never realizes an RMW. -/
theorem fusedNoRmw (pa : Pexv6) (da : Efab) (ws : Wstate) (aq rl : Bool) (base : Int)
    (ts : List Nat) (rvs wvs : List (BitVec 8)) (kc : WmClass) (l : Wlabel) (p' : Pexv6) (d' : Efab) :
    hlblRealizes pa ws (.LRmw aq rl base ts rvs wvs kc) l → ¬ pstepEv pa da l p' d' := by
  rintro ⟨-, -, -, hpr⟩ hst
  cases l with
  | LRmw => exact pstepEvNoRmw _ _ _ _ _ _ _ _ _ _ _ hst
  | _ => simp [projLbl] at hpr

/-- Only an RMW label is a failed acquire. -/
theorem failRmw (L : Int → Prop) (lb : Lbl) :
    CertZ24.lblFail L lb → ∃ aq rl base ts rvs wvs kc, lb = .LRmw aq rl base ts rvs wvs kc := by
  rintro ⟨b, -, ⟨base, vs, j, v, hw, -⟩, ⟨base', ts, vs', j', t, v', hr, -⟩⟩
  cases lb with
  | LRmw aq rl base ts rvs wvs kc => exact ⟨_, _, _, _, _, _, _, rfl⟩
  | _ => simp [lbWr, lbRd] at hw hr

/-! # 4. The twin's block and the step obligation -/

/-- **THE TWIN'S BLOCK** for the twin label `lb'` from `pC`: a star whose fetches are among the
emission's `ls` (or empty), the realization at the twin's views (fused, or the exclusive pair), ending at
`pC'` at fabric `d'`. -/
def twinBlk (S : SilWalk.St) (x : Nat) (ls : List Wlabel) (lb' : Lbl) (pC : Pexv6) (d' : Efab)
    (pC' : Pexv6) : Prop :=
  ∃ (lsC : List Wlabel) (pa : Pexv6) (da : Efab),
    admRunG pstepEv true pC (S.dv S.c.tr.length) lsC pa da ∧
    (∀ base tvs, Wlabel.LIFetch base tvs ∈ lsC → tvs = [] ∨ Wlabel.LIFetch base tvs ∈ ls) ∧
    ((∃ l', hlblRealizes pa ((cur S).msWs x) lb' l' ∧ pstepEv pa da l' pC' d') ∨
     (∃ (pm : Pexv6) (dm : Efab) (ls2 : List Wlabel) (pm2 : Pexv6) (dm2 : Efab) (l1 l2 : Wlabel),
        hlblRealizesPair pa pm2 ((cur S).msWs x) lb' l1 l2 ∧ pstepEv pa da l1 pm dm ∧
        admRunG pstepEv false pm dm ls2 pm2 dm2 ∧ pstepEv pm2 dm2 l2 pC' d'))

/-- The SILENT write's dependency bound at every twin pair block for `lb'` from `pC` (the 6c bound at
the shadow, `SilDep.depOkL` at the write node's state `SilDep.preW`). -/
def depAll (S : SilWalk.St) (x : Nat) (lb' : Lbl) (pC : Pexv6) (q : Nat) : Prop :=
  ∀ (lsC : List Wlabel) (pa : Pexv6) (da : Efab) (pm : Pexv6) (dm : Efab) (ls2 : List Wlabel)
    (pm2 : Pexv6) (dm2 : Efab) (l1 l2 : Wlabel) (pC'' : Pexv6) (d'' : Efab),
    admRunG pstepEv true pC (S.dv S.c.tr.length) lsC pa da →
    hlblRealizesPair pa pm2 ((cur S).msWs x) lb' l1 l2 → pstepEv pa da l1 pm dm →
    admRunG pstepEv false pm dm ls2 pm2 dm2 → pstepEv pm2 dm2 l2 pC'' d'' →
    SilDep.depOkL (SilDep.preW (S.sh S.c.tr.length x) lsC l1 ls2 (cur S).msLog.length) l2 q

/-- **THE STEP OBLIGATION FROM A TWIN BLOCK**: the twin's block, text custody of the emission's star,
the label's admissibility (ordinary) or its silent conditions and dependency bound give
`SilWalk.stepOk` (the star's fetches re-timed by `fetchQ`; the shadow state `w'` is the block's). -/
theorem stepOfTwinBlk (S : SilWalk.St) (x : Nat) (ls : List Wlabel) (lb' : Lbl) (o : Option Nat)
    (pC : Pexv6) (d' : Efab) (pC' : Pexv6) :
    twinBlk S x ls lb' pC d' pC' → fetchQ S ls →
    (o = none → mstepOk (cur S) x lb') →
    (∀ q, o = some q → ∃ aq base ts rvs wvs kc, lb' = .LRmw aq false base ts rvs wvs kc ∧
      SilCand.silentOk (cur S) x aq base ts rvs wvs q) →
    (∀ q, o = some q → depAll S x lb' pC q) →
    ∃ (pa : Pexv6) (da : Efab) (ls' : List Wlabel) (w' : Wstate),
      SilWalk.stepOk S x lb' o pC pa da ls' pC' d' w' := by
  rintro ⟨lsC, pa, da, hrun, hinc, harm⟩ hfq hm hsil hdep
  obtain ⟨lsR, hrunR, hfetR, -⟩ := starRetS (fun base tvs => ifetchOk (cur S).msImg
    (cur S).msLog 0 base tvs) true _ _ _ _ _ hrun (fun base tvs hmem => by
      rcases hinc base tvs hmem with rfl | h
      · exact ⟨[], rfl, fun j t v hj => by simp at hj⟩
      · exact hfq base tvs h)
  rcases harm with ⟨l', hre, hst⟩ | ⟨pm, dm, ls2, pm2, dm2, l1, l2, hpair, hst1, hrun2, hst2⟩
  · cases o with
    | none =>
      exact ⟨pa, da, lsR, _, hm, fun q h => (by cases h), hrunR, hfetR,
        .inl ⟨rfl, l', hre, hst, rfl⟩⟩
    | some q =>
      obtain ⟨aq, base, ts, rvs, wvs, kc, rfl, -⟩ := hsil q rfl
      exact absurd hst (fusedNoRmw pa da _ aq false base ts rvs wvs kc l' pC' d' hre)
  · cases o with
    | none =>
      exact ⟨pa, da, lsR, _, hm, fun q h => (by cases h), hrunR, hfetR,
        .inr ⟨pm, dm, ls2, pm2, dm2, l1, l2, hpair, hst1, hrun2, hst2, rfl⟩⟩
    | some q =>
      exact ⟨pa, da, lsR, _, fun h => (by cases h), hsil, hrunR, hfetR,
        .inr ⟨pm, dm, ls2, pm2, dm2, l1, l2, hpair, hst1, hrun2, hst2,
          hdep q rfl lsR pa da pm dm ls2 pm2 dm2 l1 l2 pC' d' hrunR hpair hst1 hrun2 hst2, rfl⟩⟩

/-- **THE LOCKSTEP BLOCK**: in lockstep, the emission's block with its read re-timed is the twin's
block (the release-pending bit agreeing, `relpAgreeS`). -/
theorem twinBlkLock (S : SilWalk.St) (x : Nat) (D : Nat → CertZ7.EmData) (rows : List (List Lbl))
    (n : Nat) (lb : Lbl) (d' : Efab) (ts' : List Nat) :
    ((cur S).msWs x).wRelp = (rowWsAux 0 wsInit ((rows.getD x []).take n)).wRelp →
    emBlk D rows x n lb (S.dv S.c.tr.length) d' →
    (∀ aq base ts vs, lb = .LLoad aq base ts vs → ts'.length = ts.length) →
    (∀ aq rl base ts rvs wvs kc, lb = .LRmw aq rl base ts rvs wvs kc → ts'.length = ts.length) →
    twinBlk S x ((D x).g n) (setTs lb ts') ((D x).f n) d' ((D x).f (n + 1)) := by
  intro hr hblk hl hrm
  rcases hblk with ⟨hfu, pa, da, hrun, hre, hst⟩ |
      ⟨pa, da, pm, dm, ls2, pm2, dm2, l2, hrun, hpair, hst1, hrun2, hst2⟩
  · obtain ⟨l', hre', hst'⟩ := oneRetS pa da _ _ lb _ _ d' ts' hr hfu hre hst hl
    exact ⟨_, pa, da, hrun, fun _ _ h => .inr h, .inl ⟨l', hre', hst'⟩⟩
  · obtain ⟨l1', hpair', hst1'⟩ := pairRetS pa pm2 _ _ lb _ l2 ts' hr hpair hrm
    exact ⟨_, pa, da, hrun, fun _ _ h => .inr h,
      .inr ⟨pm, dm, ls2, pm2, dm2, l1', l2, hpair', hst1' da pm dm hst1, hrun2, hst2⟩⟩

/-! # 5. The named premises beyond the read datum, and the twin's labels -/

/-- **THE FAILED ACQUIRE (named; `SilSite.silentQ` + `rl = false` + the shadow's dependency bound)**: a
failed acquire is an `LRmw … false …` whose read the twin re-times to `ts'` with a silent position `q`
(its window, `SilCand.silentOk`), and every twin pair block for it meets the silent write's dependency
bound at `q`. -/
def silentQD (Lb : Int → Prop) (S : SilWalk.St) (x : Nat) (lb : Lbl) (pC : Pexv6) : Prop :=
  CertZ24.lblFail Lb lb →
    ∃ (aq : Bool) (base : Int) (ts : List Nat) (rvs wvs : List (BitVec 8)) (kc : WmClass),
      lb = .LRmw aq false base ts rvs wvs kc ∧
      ∃ (ts' : List Nat) (q : Nat), SilCand.silentOk (cur S) x aq base ts' rvs wvs q ∧
        depAll S x (.LRmw aq false base ts' rvs wvs kc) pC q

/-- A value-ruled POISONED twin load at a `tTabAll` row (`SilSite.poisonOk`'s label). -/
def poisLbl (me : Nat) (lb : Lbl) (ls : List Wlabel) (lb' : Lbl) : Prop :=
  ∃ (pc base : Int) (ts : List Nat) (vs : List (BitVec 8)) (ts' : List Nat) (vs' : List (BitVec 8)),
    SilSite.blockPc ls = some pc ∧ pc ∈ SilSite.tPcsAll ∧ lb = .LLoad false base ts vs ∧
    lb' = .LLoad false base ts' vs' ∧ ts'.length = ts.length ∧ vs'.length = ts'.length ∧
    SilSite.vRule pc me vs vs'

/-- Lockstep, or TAINTED by `TR` (the abstract Sail-level relation of the static walk). -/
def relS (TR : CertZ9.HRel) : CertZ9.HRel := fun x n pE pC => pC = pE ∨ TR x n pE pC

/-- **THE SAIL MEANING OF THE STATIC WALK (named; F11)**: from a `TR`-TAINTED state, for any twin label
that re-indexes the row's or is a value-ruled poisoned load, and from LOCKSTEP at a value-ruled poisoned
load, the twin has a block for it ending in lockstep or `TR` — the value/bit-aware `csync` of
`SilSiteTaint.siteOk` (exit writes verbatim; no fault, CSR or differing branch on poison). -/
def sailQ (TR : CertZ9.HRel) (cpuOf : Nat → Nat) (D : Nat → CertZ7.EmData) :
    SilWalk.St → Nat → Nat → Lbl → Pexv6 → Efab → Prop :=
  fun S x n lb pC d' => ∀ lb' : Lbl,
    ((TR x n ((D x).f n) pC ∧ (lblReidx lb lb' ∨ poisLbl (cpuOf x) lb ((D x).g n) lb')) ∨
     (pC = (D x).f n ∧ poisLbl (cpuOf x) lb ((D x).g n) lb')) →
    ∃ pC' : Pexv6, twinBlk S x ((D x).g n) lb' pC d' pC' ∧
      relS TR x (n + 1) ((D x).f (n + 1)) pC'

/-- **THE TWIN'S LABEL WHEN THE READ AGREES**: at the restricted context, an agreeing load
(`valAgree`), a successful RMW (`rmwQ`), a failed acquire (`silentQD`), anything else verbatim — the
row label re-timed (`setTs`), related by `relW`, admissible or silent with its bound. -/
theorem memAgree (d0 : Efab) (rows : List (List Lbl)) (Lb : Int → Prop) (L : List Geid)
    (Rel : CertZ9.HRel) (D : Nat → CertZ7.EmData) (S : SilWalk.St) (x n : Nat) (lb : Lbl)
    (pC : Pexv6) (d' : Efab) (k : Nat) :
    stepCtxD d0 rows Lb L Rel D S x n lb pC d' k →
    (∀ aq base ts vs, lb = .LLoad aq base ts vs → SilSite.valAgree S x lb) →
    SilSite.rmwQ Lb S x lb ((D x).g n) → silentQD Lb S x lb pC →
    ∃ (ts' : List Nat) (o : Option Nat),
      SilWalk.relW Lb lb (setTs lb ts', o) ∧ lblReidx lb (setTs lb ts') ∧
      (o = none → mstepOk (cur S) x (setTs lb ts')) ∧
      (∀ q, o = some q → ∃ aq base ts rvs wvs kc, setTs lb ts' = .LRmw aq false base ts rvs wvs kc ∧
        SilCand.silentOk (cur S) x aq base ts rvs wvs q) ∧
      (∀ q, o = some q → depAll S x (setTs lb ts') pC q) ∧
      (∀ aq base ts vs, lb = .LLoad aq base ts vs → ts'.length = ts.length) ∧
      (∀ aq rl base ts rvs wvs kc, lb = .LRmw aq rl base ts rvs wvs kc → ts'.length = ts.length) := by
  intro hctx hag hrmw hsil
  obtain ⟨-, -, -, hsh, -⟩ := hctx
  cases lb with
  | LLoad aq base ts vs =>
    obtain ⟨ts', hrd⟩ := hag aq base ts vs rfl aq base ts vs rfl
    have hl : ts'.length = ts.length := by have := hrd.1; have : vs.length = ts.length := hsh; omega
    refine ⟨ts', none, ⟨.inl ⟨rfl, rfl, rfl, hl⟩, .inl ⟨fun hf => ?_, rfl⟩⟩, ⟨rfl, rfl, rfl, hl⟩,
      fun _ => hrd, fun q h => (by cases h), fun q h => (by cases h),
      fun _ _ _ _ he => (by cases he; exact hl), fun _ _ _ _ _ _ _ he => (by cases he)⟩
    obtain ⟨_, _, _, _, _, _, _, he⟩ := failRmw Lb _ hf
    cases he
  | LStore rl base vs kc =>
    refine ⟨[], none, ⟨lblReidxWRefl _, .inl ⟨fun hf => ?_, rfl⟩⟩, lblReidxRefl _, fun _ => hsh,
      fun q h => (by cases h), fun q h => (by cases h), fun _ _ _ _ he => (by cases he),
      fun _ _ _ _ _ _ _ he => (by cases he)⟩
    obtain ⟨_, _, _, _, _, _, _, he⟩ := failRmw Lb _ hf
    cases he
  | LFence pr pw sr sw =>
    refine ⟨[], none, ⟨lblReidxWRefl _, .inl ⟨fun hf => ?_, rfl⟩⟩, lblReidxRefl _,
      fun _ => trivial, fun q h => (by cases h), fun q h => (by cases h), fun _ _ _ _ he => (by cases he),
      fun _ _ _ _ _ _ _ he => (by cases he)⟩
    obtain ⟨_, _, _, _, _, _, _, he⟩ := failRmw Lb _ hf
    cases he
  | LIo kd base vs =>
    refine ⟨[], none, ⟨lblReidxWRefl _, .inl ⟨fun hf => ?_, rfl⟩⟩, lblReidxRefl _,
      fun _ => trivial, fun q h => (by cases h), fun q h => (by cases h), fun _ _ _ _ he => (by cases he),
      fun _ _ _ _ _ _ _ he => (by cases he)⟩
    obtain ⟨_, _, _, _, _, _, _, he⟩ := failRmw Lb _ hf
    cases he
  | LRmw aq rl base ts rvs wvs kc =>
    obtain ⟨hne, hwl, hrl⟩ := hsh
    by_cases hf : CertZ24.lblFail Lb (.LRmw aq rl base ts rvs wvs kc)
    · obtain ⟨aq0, base0, ts0, rvs0, wvs0, kc0, he, ts', q, hso, hdep⟩ := hsil hf
      simp only [Lbl.LRmw.injEq] at he
      obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := he
      have hl : ts'.length = ts.length := by have := hso.2.2.1; omega
      refine ⟨ts', some q, ⟨.inl ⟨rfl, rfl, rfl, rfl, rfl, rfl, hl⟩, .inr ⟨hf, by simp⟩⟩,
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, hl⟩, fun h => (by cases h), ?_, ?_,
        fun _ _ _ _ he => (by cases he), fun _ _ _ _ _ _ _ he => (by cases he; exact hl)⟩
      · intro q' h
        cases h
        exact ⟨aq, base, ts', rvs, wvs, kc, rfl, hso⟩
      · intro q' h
        cases h
        exact hdep
    · obtain ⟨ts', hrd, hlat⟩ := hrmw hf aq rl base ts rvs wvs kc rfl
      have hrl' := hrd.1
      have hl : ts'.length = ts.length := by omega
      refine ⟨ts', none, ⟨.inl ⟨rfl, rfl, rfl, rfl, rfl, rfl, hl⟩, .inl ⟨hf, rfl⟩⟩,
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, hl⟩, fun _ => ⟨hne, by omega, hrd, hlat⟩,
        fun q h => (by cases h), fun q h => (by cases h), fun _ _ _ _ he => (by cases he),
        fun _ _ _ _ _ _ _ he => (by cases he; exact hl)⟩

/-- The read datum, pointwise (`SilSite.readDatumOf`'s case split). -/
theorem readDatumPt (cpuOf : Nat → Nat) (isDev : Nat → Prop) (S : SilWalk.St) (x : Nat) (lb : Lbl)
    (ls : List Wlabel) :
    SilSite.ordQ (fun pc => pc ∈ SilSite.pinRdK) isDev S x lb ls → SilSite.devQ isDev S x lb ls →
    SilSite.valQ cpuOf isDev S x lb ls → SilSite.custQ isDev S x lb ls →
    SilSite.drfQ isDev S x lb ls → SilSite.readDatum S x (cpuOf x) lb ls := by
  intro hord hdev hval hcust hdrf _
  by_cases hd : isDev x
  · exact .inl (hdev hd)
  · cases hb : SilSite.blockPc ls with
    | none =>
      refine .inl (hdrf hd (fun pc hpc => ?_))
      rw [hb] at hpc
      cases hpc
    | some pc =>
      by_cases h1 : pc ∈ SilSite.pinRdK
      · exact .inl (hord hd ⟨pc, hb, h1⟩)
      · by_cases h2 : pc ∈ SilSite.tPcsAll
        · exact hval hd pc hb h2
        · by_cases h3 : pc ∈ SilSite.nPcs
          · exact .inl (hcust hd pc hb h3)
          · refine .inl (hdrf hd (fun pc' hpc' => ?_))
            rw [hb, Option.some.injEq] at hpc'
            subst hpc'
            exact ⟨h1, h2, h3⟩

/-- **`SilSite.poisonOk` AT THE SAME FOOTPRINT** (F12): the twin's poisoned read has the graph read's
width (`vs'.length = vs.length`) — without it a `readsAt` of another width (e.g. the empty read) would be a
"poisoned" label no Sail load realizes. -/
def poisonOkL (S : SilWalk.St) (x me : Nat) (lb : Lbl) (ls : List Wlabel) : Prop :=
  ∃ (pc base : Int) (ts : List Nat) (vs : List (BitVec 8)),
    SilSite.blockPc ls = some pc ∧ pc ∈ SilSite.tPcsAll ∧ lb = .LLoad false base ts vs ∧
    ∃ vs' : List (BitVec 8), vs'.length = vs.length ∧ SilSite.readsAt S x false base vs' ∧
      SilSite.vRule pc me vs vs'

/-- **VALUE (T/O) at the same footprint**: `SilSite.valQ` with `poisonOkL`. -/
def valQL (cpuOf : Nat → Nat) (isDev : Nat → Prop) :
    SilWalk.St → Nat → Lbl → List Wlabel → Prop :=
  fun S x lb ls => ¬ isDev x → ∀ pc, SilSite.blockPc ls = some pc → pc ∈ SilSite.tPcsAll →
    SilSite.valAgree S x lb ∨ poisonOkL S x (cpuOf x) lb ls

/-- `valQL` is `SilSite.valQ` with the width clause. -/
theorem valQOfL (cpuOf : Nat → Nat) (isDev : Nat → Prop) (S : SilWalk.St) (x : Nat) (lb : Lbl)
    (ls : List Wlabel) : valQL cpuOf isDev S x lb ls → SilSite.valQ cpuOf isDev S x lb ls := by
  intro h hd pc hb hm
  rcases h hd pc hb hm with h | ⟨pc', base, ts, vs, h1, h2, h3, vs', -, h4, h5⟩
  · exact .inl h
  · exact .inr ⟨pc', base, ts, vs, h1, h2, h3, vs', h4, h5⟩

/-- The two-sided value form at the same footprint (`SilSite.valQOfRule`'s, pointwise). -/
theorem valQLOfRule (cpuOf : Nat → Nat) (isDev : Nat → Prop) (S : SilWalk.St) (x : Nat) (lb : Lbl)
    (ls : List Wlabel) :
    (¬ isDev x → ∀ pc, SilSite.blockPc ls = some pc → pc ∈ SilSite.tPcsAll →
      ∀ aq base ts vs, lb = .LLoad aq base ts vs →
        aq = false ∧ ∃ vs' : List (BitVec 8), vs'.length = vs.length ∧
          SilSite.readsAt S x false base vs' ∧ SilSite.vRule pc (cpuOf x) vs vs') →
    valQL cpuOf isDev S x lb ls := by
  intro h hd pc hb hm
  by_cases hl : ∃ aq base ts vs, lb = .LLoad aq base ts vs
  · obtain ⟨aq, base, ts, vs, rfl⟩ := hl
    obtain ⟨rfl, vs', hlen, hr, hv⟩ := h hd pc hb hm aq base ts vs rfl
    exact .inr ⟨pc, base, ts, vs, hb, hm, rfl, vs', hlen, hr, hv⟩
  · exact .inl (fun aq base ts vs he => absurd ⟨aq, base, ts, vs, he⟩ hl)

/-- The read datum at the same footprint. -/
def readDatumL (S : SilWalk.St) (x me : Nat) (lb : Lbl) (ls : List Wlabel) : Prop :=
  (∃ aq base ts vs, lb = .LLoad aq base ts vs) → SilSite.valAgree S x lb ∨ poisonOkL S x me lb ls

/-- The read datum at the same footprint, pointwise. -/
theorem readDatumPtL (cpuOf : Nat → Nat) (isDev : Nat → Prop) (S : SilWalk.St) (x : Nat) (lb : Lbl)
    (ls : List Wlabel) :
    SilSite.ordQ (fun pc => pc ∈ SilSite.pinRdK) isDev S x lb ls → SilSite.devQ isDev S x lb ls →
    valQL cpuOf isDev S x lb ls → SilSite.custQ isDev S x lb ls →
    SilSite.drfQ isDev S x lb ls → readDatumL S x (cpuOf x) lb ls := by
  intro hord hdev hval hcust hdrf _
  by_cases hd : isDev x
  · exact .inl (hdev hd)
  · cases hb : SilSite.blockPc ls with
    | none =>
      refine .inl (hdrf hd (fun pc hpc => ?_))
      rw [hb] at hpc
      cases hpc
    | some pc =>
      by_cases h1 : pc ∈ SilSite.pinRdK
      · exact .inl (hord hd ⟨pc, hb, h1⟩)
      · by_cases h2 : pc ∈ SilSite.tPcsAll
        · exact hval hd pc hb h2
        · by_cases h3 : pc ∈ SilSite.nPcs
          · exact .inl (hcust hd pc hb h3)
          · refine .inl (hdrf hd (fun pc' hpc' => ?_))
            rw [hb, Option.some.injEq] at hpc'
            subst hpc'
            exact ⟨h1, h2, h3⟩

/-! # 6. The per-step datum from the site datum -/

/-- The context's release-pending agreement (from its `relW` clause). -/
theorem ctxRelp (d0 : Efab) (rows : List (List Lbl)) (Lb : Int → Prop) (L : List Geid)
    (Rel : CertZ9.HRel) (D : Nat → CertZ7.EmData) (S : SilWalk.St) (x n : Nat) (lb : Lbl)
    (pC : Pexv6) (d' : Efab) (k : Nat) :
    stepCtxD d0 rows Lb L Rel D S x n lb pC d' k →
    ((cur S).msWs x).wRelp = (rowWsAux 0 wsInit ((rows.getD x []).take n)).wRelp := by
  rintro ⟨hok, -, -, -, -, -, -, hcnt, hper, hlb⟩
  have hx : x < rows.length := by
    refine Nat.lt_of_not_le (fun hge => ?_)
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge, Option.getD_none] at hlb
    cases hlb
  have h := hper x hx
  rw [hcnt] at h
  exact relpAgreeS S Lb x _ n hok.1 h

/-- **`hartStepOfSiteSD` — THE TWIN'S PER-STEP DATUM FROM THE SITE DATUM** (`CertZ13.hartStepOfSite`'s
twin): lockstep with an agreeing read — the emission's block re-timed (`twinBlkLock`); a poisoned read
(lockstep) or a tainted state — the Sail meaning `sailQ`; every step's label from the read datum
(`SilSite.readDatum`'s five families), `rmwQ`, `silentQD`, its fetches by `fetchQ`. -/
theorem hartStepOfSiteSD (d0 : Efab) (rows : List (List Lbl)) (Lb : Int → Prop) (L : List Geid)
    (D : Nat → CertZ7.EmData) (TR : CertZ9.HRel) (cpuOf : Nat → Nat) (isDev : Nat → Prop) :
    atStepsD d0 rows Lb L (relS TR) D (SilSite.ordQ (fun pc => pc ∈ SilSite.pinRdK) isDev) →
    atStepsD d0 rows Lb L (relS TR) D (SilSite.devQ isDev) →
    atStepsD d0 rows Lb L (relS TR) D (valQL cpuOf isDev) →
    atStepsD d0 rows Lb L (relS TR) D (SilSite.custQ isDev) →
    atStepsD d0 rows Lb L (relS TR) D (SilSite.drfQ isDev) →
    atStepsD d0 rows Lb L (relS TR) D (SilSite.rmwQ Lb) →
    atCtxD d0 rows Lb L (relS TR) D (fun S x _ lb pC _ => silentQD Lb S x lb pC) →
    atStepsD d0 rows Lb L (relS TR) D (fun S _ _ ls => fetchQ S ls) →
    atCtxD d0 rows Lb L (relS TR) D (sailQ TR cpuOf D) →
    hartStepRISD d0 rows Lb L (relS TR) D := by
  intro hord hdev hval hcust hdrf hrmw hsil hfq hsail S x n lb pC d' k hctx
  have hrd := readDatumPtL cpuOf isDev S x lb ((D x).g n) (hord S x n lb pC d' k hctx)
    (hdev S x n lb pC d' k hctx) (hval S x n lb pC d' k hctx) (hcust S x n lb pC d' k hctx)
    (hdrf S x n lb pC d' k hctx)
  have hrm := hrmw S x n lb pC d' k hctx
  have hsl := hsil S x n lb pC d' k hctx
  have hfe := hfq S x n lb pC d' k hctx
  have hsa := hsail S x n lb pC d' k hctx
  have hr := ctxRelp d0 rows Lb L _ D S x n lb pC d' k hctx
  have hrel := hctx.2.2.1
  have hshp := hctx.2.2.2.1
  have hblk := hctx.2.2.2.2.1
  -- the read: agreeing, or poisoned within its value rule
  by_cases hpois : ∃ (aq : Bool) (base : Int) (ts : List Nat) (vs : List (BitVec 8)),
      lb = .LLoad aq base ts vs ∧ ¬ SilSite.valAgree S x lb
  · obtain ⟨aq, base, ts, vs, rfl, hna⟩ := hpois
    rcases hrd ⟨aq, base, ts, vs, rfl⟩ with h | ⟨pc, base0, ts0, vs0, hbpc, hmem, he, vs', hvl,
        ⟨ts', hrdo⟩, hrule⟩
    · exact absurd h hna
    simp only [Lbl.LLoad.injEq] at he
    obtain ⟨rfl, rfl, rfl, rfl⟩ := he
    have hsh : vs.length = ts.length := hshp
    have hl : ts'.length = ts.length := by have := hrdo.1; omega
    have hpl : poisLbl (cpuOf x) (.LLoad false base ts vs) ((D x).g n) (.LLoad false base ts' vs') :=
      ⟨pc, base, ts, vs, ts', vs', hbpc, hmem, rfl, rfl, hl, hrdo.1, hrule⟩
    obtain ⟨pC', htb, hrel'⟩ := hsa _ (by
      rcases hrel with h | h
      · exact .inr ⟨h, hpl⟩
      · exact .inl ⟨h, .inr hpl⟩)
    obtain ⟨pa, da, ls', w', hst⟩ := stepOfTwinBlk S x _ _ none pC d' pC' htb hfe (fun _ => hrdo)
      (fun q h => by cases h) (fun q h => by cases h)
    refine ⟨.LLoad false base ts' vs', none, pa, da, ls', pC', w',
      ⟨lblReidxWPois (.LLoad false base ts vs) (.LLoad false base ts' vs') ⟨rfl, hrdo.1⟩,
        .inl ⟨fun hf => ?_, rfl⟩⟩, hst, hrel'⟩
    obtain ⟨_, _, _, _, _, _, _, he⟩ := failRmw Lb _ hf
    cases he
  · have hag : ∀ aq base ts vs, lb = .LLoad aq base ts vs → SilSite.valAgree S x lb := by
      intro aq base ts vs he
      exact Classical.byContradiction (fun h => hpois ⟨aq, base, ts, vs, he, h⟩)
    obtain ⟨ts', o, hre, hrx, hm, hsi, hdp, hl1, hl2⟩ :=
      memAgree d0 rows Lb L _ D S x n lb pC d' k hctx hag hrm hsl
    rcases hrel with rfl | htr
    · -- LOCKSTEP
      have htb := twinBlkLock S x D rows n lb d' ts' hr hblk hl1 hl2
      obtain ⟨pa, da, ls', w', hst⟩ := stepOfTwinBlk S x _ _ o _ d' _ htb hfe hm hsi hdp
      exact ⟨_, o, pa, da, ls', _, w', hre, hst, .inl rfl⟩
    · -- TAINTED
      obtain ⟨pC', htb, hrel'⟩ := hsa _ (.inl ⟨htr, .inl hrx⟩)
      obtain ⟨pa, da, ls', w', hst⟩ := stepOfTwinBlk S x _ _ o pC d' pC' htb hfe hm hsi hdp
      exact ⟨_, o, pa, da, ls', pC', w', hre, hst, hrel'⟩

/-- **THE ALL-AGREE STEP** (Q-6M-GFVAL (a): every census read AGREES; NO Sail premise): lockstep
throughout, from the agreeing read datum (`SilSite.valQOfAgree`'s form at the `tTabAll` rows),
`rmwQ`, `silentQD`, `fetchQ`. -/
theorem hartStepOfAgreeSD (d0 : Efab) (rows : List (List Lbl)) (Lb : Int → Prop) (L : List Geid)
    (D : Nat → CertZ7.EmData) (isDev : Nat → Prop) :
    atStepsD d0 rows Lb L (relS (fun _ _ _ _ => False)) D
      (SilSite.ordQ (fun pc => pc ∈ SilSite.pinRdK) isDev) →
    atStepsD d0 rows Lb L (relS (fun _ _ _ _ => False)) D (SilSite.devQ isDev) →
    atStepsD d0 rows Lb L (relS (fun _ _ _ _ => False)) D (fun S x lb ls =>
      ¬ isDev x → ∀ pc, SilSite.blockPc ls = some pc → pc ∈ SilSite.tPcsAll →
        SilSite.valAgree S x lb) →
    atStepsD d0 rows Lb L (relS (fun _ _ _ _ => False)) D (SilSite.custQ isDev) →
    atStepsD d0 rows Lb L (relS (fun _ _ _ _ => False)) D (SilSite.drfQ isDev) →
    atStepsD d0 rows Lb L (relS (fun _ _ _ _ => False)) D (SilSite.rmwQ Lb) →
    atCtxD d0 rows Lb L (relS (fun _ _ _ _ => False)) D
      (fun S x _ lb pC _ => silentQD Lb S x lb pC) →
    atStepsD d0 rows Lb L (relS (fun _ _ _ _ => False)) D (fun S _ _ ls => fetchQ S ls) →
    hartStepRISD d0 rows Lb L (relS (fun _ _ _ _ => False)) D := by
  intro hord hdev hval hcust hdrf hrmw hsil hfq S x n lb pC d' k hctx
  have hag : ∀ aq base ts vs, lb = .LLoad aq base ts vs → SilSite.valAgree S x lb := by
    intro aq base ts vs he
    have hrd := readDatumPt (fun _ => 0) isDev S x lb ((D x).g n) (hord S x n lb pC d' k hctx)
      (hdev S x n lb pC d' k hctx)
      (fun hd pc hb hm => .inl (hval S x n lb pC d' k hctx hd pc hb hm))
      (hcust S x n lb pC d' k hctx) (hdrf S x n lb pC d' k hctx) ⟨aq, base, ts, vs, he⟩
    rcases hrd with h | ⟨pc, base0, ts0, vs0, hbpc, hmem, he', -⟩
    · exact h
    · by_cases hd : isDev x
      · exact hdev S x n lb pC d' k hctx hd
      · exact hval S x n lb pC d' k hctx hd pc hbpc hmem
  have hr := ctxRelp d0 rows Lb L _ D S x n lb pC d' k hctx
  obtain ⟨ts', o, hre, -, hm, hsi, hdp, hl1, hl2⟩ := memAgree d0 rows Lb L _ D S x n lb pC d' k hctx
    hag (hrmw S x n lb pC d' k hctx) (hsil S x n lb pC d' k hctx)
  have hfe := hfq S x n lb pC d' k hctx
  obtain ⟨-, -, hrel, -, hblk, -⟩ := hctx
  rcases hrel with rfl | hf
  · have htb := twinBlkLock S x D rows n lb d' ts' hr hblk hl1 hl2
    obtain ⟨pa, da, ls', w', hst⟩ := stepOfTwinBlk S x _ _ o _ d' _ htb hfe hm hsi hdp
    exact ⟨_, o, pa, da, ls', _, w', hre, hst, .inl rfl⟩
  · exact hf.elim

end SilSiteStep

namespace CatLin

/-- **THE SITE SUPPLY (named, per graph)**: on every cyclic class graph with the residue facts, every
fitting emission datum and every walk order, a tainted relation `TR`, the harts' `&cpus[…]` and the
device rows, with the read datum's five families, `rmwQ`, `silentQD`, `fetchQ` and the Sail meaning
`sailQ`, all at the emission's blocks. -/
def SilSiteStep.siteSupplySD (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image)
    (P : Int → Int → Prop) : Prop :=
  ∀ (GF : Gfexec) (ad : List (Geid × Geid)) (z : Geid) (ss : List Seg),
    GF.gfGd.gdG.gxImg = im → rvwmoCatAD GF.gfGd ad → GraphFabConf.gfexecConfZF boot d0 fab GF →
    ioResidueGmo GF → gdiskRead14 GF.gfGd.gdG →
    ss ≠ [] → rawChainC GF.gfGd (ioCross GF) z z ss →
    ∀ D : Nat → CertZ7.EmData, CertZ7.emDataOk boot fab GF D →
    ∀ L : List Geid, CertZ8.walkOrd GF.gfGd.gdG.gxProg GF.gfDev L →
      CertZ23.ordCoSP GF.gfGd.gdG L (GraphFetchN2.lockBytes P) →
    ∃ (TR : CertZ9.HRel) (cpuOf : Nat → Nat) (isDev : Nat → Prop),
      SilSiteStep.atStepsD d0 GF.gfGd.gdG.gxProg (GraphFetchN2.lockBytes P) L (SilSiteStep.relS TR) D
        (SilSite.ordQ (fun pc => pc ∈ SilSite.pinRdK) isDev) ∧
      SilSiteStep.atStepsD d0 GF.gfGd.gdG.gxProg (GraphFetchN2.lockBytes P) L (SilSiteStep.relS TR) D
        (SilSite.devQ isDev) ∧
      SilSiteStep.atStepsD d0 GF.gfGd.gdG.gxProg (GraphFetchN2.lockBytes P) L (SilSiteStep.relS TR) D
        (SilSiteStep.valQL cpuOf isDev) ∧
      SilSiteStep.atStepsD d0 GF.gfGd.gdG.gxProg (GraphFetchN2.lockBytes P) L (SilSiteStep.relS TR) D
        (SilSite.custQ isDev) ∧
      SilSiteStep.atStepsD d0 GF.gfGd.gdG.gxProg (GraphFetchN2.lockBytes P) L (SilSiteStep.relS TR) D
        (SilSite.drfQ isDev) ∧
      SilSiteStep.atStepsD d0 GF.gfGd.gdG.gxProg (GraphFetchN2.lockBytes P) L (SilSiteStep.relS TR) D
        (SilSite.rmwQ (GraphFetchN2.lockBytes P)) ∧
      SilSiteStep.atCtxD d0 GF.gfGd.gdG.gxProg (GraphFetchN2.lockBytes P) L (SilSiteStep.relS TR) D
        (fun S x _ lb pC _ => SilSiteStep.silentQD (GraphFetchN2.lockBytes P) S x lb pC) ∧
      SilSiteStep.atStepsD d0 GF.gfGd.gdG.gxProg (GraphFetchN2.lockBytes P) L (SilSiteStep.relS TR) D
        (fun S _ _ ls => SilSiteStep.fetchQ S ls) ∧
      SilSiteStep.atCtxD d0 GF.gfGd.gdG.gxProg (GraphFetchN2.lockBytes P) L (SilSiteStep.relS TR) D
        (SilSiteStep.sailQ TR cpuOf D)

/-- **THE STEP SUPPLY FROM THE SITE SUPPLY** (the walk starts in lockstep). -/
theorem SilSiteStep.stepSupplyOfSiteSD (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab)
    (im : Image) (P : Int → Int → Prop) :
    SilSiteStep.siteSupplySD boot d0 fab im P → SilSiteStep.stepSupplySD boot d0 fab im P := by
  intro h GF ad z ss him hc hconf hres hdr hne hch D hD L hL hco
  obtain ⟨TR, cpuOf, isDev, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ :=
    h GF ad z ss him hc hconf hres hdr hne hch D hD L hL hco
  exact ⟨SilSiteStep.relS TR, fun _ _ => .inl rfl,
    SilSiteStep.hartStepOfSiteSD _ _ _ L D TR cpuOf isDev h1 h2 h3 h4 h5 h6 h7 h8 h9⟩


section glue

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode
open Language.Notation PrimStep
open LeanRV64D

/-- **`SilKillT.cycleKillS` AT THE RESTRICTED DATUM** — the trimmed kill′ with the twin step supply at
the emission's block (`stepSupplySD`, e.g. from `stepSupplyOfSiteSD`) in place of `SilOrd.stepSupplyS`. -/
theorem SilSiteStep.cycleKillSD (hlc : HasLC) (GF0 : BundledGFunctors) [MachGpreS hlc GF0]
    [WeakGpreS GF0] (gen : Nat) (σ0 : WGState) (D : CPU → List Register) (hD : ∀ c, (D c).Nodup)
    (Nm : Int → Int → Namespace) (P : Int → Int → Prop)
    (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (N : Nat) :
    freshEra gen σ0 →
    (List.range' 0 N).map boot = epsInit σ0 →
    d0 = efInit σ0.wgdev →
    SilKill.wpPackageS hlc GF0 gen σ0 D →
    (∀ a base, P a base → SilClose.wpPackageProtS hlc GF0 gen σ0 D (Nm a base) a base) →
    (∀ ρ, rtc SilEpf.epfRunS (epInit gen, σ0) ρ → efetchItvOk ρ.1 ρ.2) →
    (∀ (GF : Gfexec) (ad : List (Geid × Geid)), GF.gfGd.gdG.gxImg = imgZ σ0.wgimg →
      rvwmoCatAD GF.gfGd ad → GraphFabConf.gfexecConfZF boot d0 fab GF →
      GF.gfGd.gdG.gxProg.length ≤ N ∧ GraphFetchBlocks.emPremOk boot GF.gfGd.gdG) →
    orderSupplyCZ3 boot d0 fab (imgZ σ0.wgimg) P →
    SilClose.oneByteS boot d0 fab (imgZ σ0.wgimg) P →
    SilSiteStep.stepSupplySD boot d0 fab (imgZ σ0.wgimg) P →
    SilKill.acqAqS boot d0 fab (imgZ σ0.wgimg) N P →
    SilKill.relCoversS boot d0 fab (imgZ σ0.wgimg) N P →
    SilClose.regZeroS gen σ0 boot d0 fab N P →
    SilKillT.l2ClaimS boot d0 fab (imgZ σ0.wgimg) N P (SilKill.badRunS gen σ0) →
    cycleKillCZT boot d0 fab (imgZ σ0.wgimg) :=
  fun hfr hb1 hb2 hwp hwpp hcov hpre hordS h1b hstep hAQ hRC hrz hl2 =>
    SilKillT.cycleKillOfL2CloseS hlc GF0 gen σ0 D hD Nm P boot d0 fab N hfr hb1 hb2 hwp hwpp hcov
      (cutSupplyOfCycleCZC boot d0 fab _)
      (SilKillT.certSupplyOfWalkS boot d0 fab _ N P
        (SilSiteStep.walkSupplyOfOrdStepSD boot d0 fab _ N P hpre hordS
          (SilClose.spNfOfOneByte boot d0 fab _ P h1b) hstep))
      hAQ hRC hrz hl2

/-- **`SilKillT.cycleKillZS` AT THE RESTRICTED DATUM** (one `wpPackageProtZS`). -/
theorem SilSiteStep.cycleKillZSD (hlc : HasLC) (GF0 : BundledGFunctors) [MachGpreS hlc GF0]
    [WeakGpreS GF0] (gen : Nat) (σ0 : WGState) (D : CPU → List Register) (hD : ∀ c, (D c).Nodup)
    (Nm : Int → Int → Namespace) (P : Int → Int → Prop)
    (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (N : Nat) :
    freshEra gen σ0 →
    (List.range' 0 N).map boot = epsInit σ0 →
    d0 = efInit σ0.wgdev →
    SilKill.wpPackageS hlc GF0 gen σ0 D →
    (∀ a base, P a base → SilRegZero.wpPackageProtZS hlc GF0 gen σ0 D (Nm a base) a base) →
    (∀ ρ, rtc SilEpf.epfRunS (epInit gen, σ0) ρ → efetchItvOk ρ.1 ρ.2) →
    (∀ (GF : Gfexec) (ad : List (Geid × Geid)), GF.gfGd.gdG.gxImg = imgZ σ0.wgimg →
      rvwmoCatAD GF.gfGd ad → GraphFabConf.gfexecConfZF boot d0 fab GF →
      GF.gfGd.gdG.gxProg.length ≤ N ∧ GraphFetchBlocks.emPremOk boot GF.gfGd.gdG) →
    orderSupplyCZ3 boot d0 fab (imgZ σ0.wgimg) P →
    SilClose.oneByteS boot d0 fab (imgZ σ0.wgimg) P →
    SilSiteStep.stepSupplySD boot d0 fab (imgZ σ0.wgimg) P →
    SilKill.acqAqS boot d0 fab (imgZ σ0.wgimg) N P →
    SilKill.relCoversS boot d0 fab (imgZ σ0.wgimg) N P →
    SilKillT.l2ClaimS boot d0 fab (imgZ σ0.wgimg) N P (SilKill.badRunS gen σ0) →
    cycleKillCZT boot d0 fab (imgZ σ0.wgimg) :=
  fun hfr hb1 hb2 hwp hwpz hcov hpre hordS h1b hstep hAQ hRC hl2 =>
    SilSiteStep.cycleKillSD hlc GF0 gen σ0 D hD Nm P boot d0 fab N hfr hb1 hb2 hwp
      (fun a base hP => SilRegZero.wpPackageProtOfZ hlc GF0 gen σ0 D (Nm a base) a base
        (hwpz a base hP))
      hcov hpre hordS h1b hstep hAQ hRC
      (SilRegZero.regZeroOfZ hlc GF0 gen σ0 D hD Nm P boot d0 fab N hfr hwpz) hl2

end glue

end CatLin

end Weak
