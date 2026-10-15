/-
Weak: **W10 F1 [OWN.94] (N2′), decision (A), step 1 — the agreement and the transport UP TO FAILED
ACQUIRES** (`PROGRESS-W10N2p.md`).  Lean-only, no Rocq twin.

No candidate can replay a stale failed acquire (cross-spin graphs, `PROGRESS` FINDING), so the realized
member SKIPS failed acquires.  To keep event identities aligned, the member used by the transport is the
PADDED member: at a failed acquire's slot it carries the placeholder `CertZ24.skipLbl` (a no-op fence:
not a memory event, not a write, not in gmo); elsewhere its labels re-index `GF`'s.

  §1  `CertZ24.lblFail` (a label that writes AND reads a nonzero byte of a lock byte — a failed
      acquire), `CertZ24.nf` (an event that is no failed acquire), `CertZ24.lblRel4`,
      **`CertZ24.lblAgree4`**, **`CertZ24.agreeRP4`**, **`CertZ24.agreeW4`** (writes of the member are
      `GF`'s and never a failed acquire's; `GF`'s writes off failed acquires are the member's; class and
      read values off failed acquires; successful-protocol lock co) and `CertZ24.agreeW4OfRP4`;
  §2  `CertZ24.npAt4`, `CertZ24.poOfRowR4`;
  §3  **`CatLin.csChainedT4`** — `csChainedT3` at `agreeW4`, with the section's acquire and the plain
      write `nf` (xv6: a successful `amoswap.w.aq` and a plain store are no failed acquires).

Spec: FAITHFUL (proof organisation).
-/
import Weak.CertZ23

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open TsoShadow

/-! # 1. Failed acquires, the padded agreement -/

/-- A label of a FAILED ACQUIRE of a lock byte in `L`: it writes a nonzero byte there and reads a nonzero
byte there. -/
def CertZ24.lblFail (L : Int → Prop) (l : Lbl) : Prop :=
  ∃ b, L b ∧
    (∃ base vs j v, lbWr l = some (base, vs) ∧ vs[j]? = some v ∧ accAddr base j = b ∧
      v ≠ lockFree) ∧
    (∃ base ts vs j t v, lbRd l = some (base, ts, vs) ∧ ts[j]? = some t ∧ vs[j]? = some v ∧
      accAddr base j = b ∧ v ≠ lockFree)

/-- An event that is NO failed acquire of a lock byte in `L`. -/
def CertZ24.nf (G : Gexec) (L : Int → Prop) (e : Geid) : Prop :=
  ¬ ∃ b, L b ∧ CertZ18.failAcq G b e

theorem CertZ24.failIff (G : Gexec) (L : Int → Prop) (e : Geid) (l : Lbl) :
    gxLbl G e = some l → (CertZ24.lblFail L l ↔ ∃ b, L b ∧ CertZ18.failAcq G b e) := by
  intro hl
  constructor
  · rintro ⟨b, hb, ⟨base, vs, j, v, hwr, hv, ha, hne⟩, ⟨base', ts, vs', j', t, v', hrd, ht, hv', ha',
      hne'⟩⟩
    exact ⟨b, hb, ⟨v, ⟨l, base, vs, j, hl, hwr, hv, ha⟩, hne⟩,
      ⟨t, v', ⟨l, base', ts, vs', j', hl, hrd, ht, hv', ha'⟩, hne'⟩⟩
  · rintro ⟨b, hb, ⟨v, ⟨l0, base, vs, j, hl0, hwr, hv, ha⟩, hne⟩,
      ⟨t, v', ⟨l1, base', ts, vs', j', hl1, hrd, ht, hv', ha'⟩, hne'⟩⟩
    rw [hl, Option.some.injEq] at hl0 hl1
    subst hl0 hl1
    exact ⟨b, hb, ⟨base, vs, j, v, hwr, hv, ha, hne⟩, ⟨base', ts, vs', j', t, v', hrd, ht, hv', ha',
      hne'⟩⟩

/-- The placeholder at a failed acquire's slot: a no-op fence. -/
def CertZ24.skipLbl : Lbl := .LFence false false false false

/-- The per-slot relation of the padded member to `GF`. -/
def CertZ24.lblRel4 (L : Int → Prop) (pi : Nat → Nat) (l l' : Lbl) : Prop :=
  (¬ CertZ24.lblFail L l ∧ lblReidxW (lblRen pi l) l') ∨ (CertZ24.lblFail L l ∧ l' = CertZ24.skipLbl)

/-- **THE PADDED LABEL AGREEMENT.** -/
def CertZ24.lblAgree4 (G GR : Gexec) (pi : Nat → Nat) (L : Int → Prop) : Prop :=
  ∀ e, (gxLbl G e = none ∧ gxLbl GR e = none) ∨
    ∃ l l', gxLbl G e = some l ∧ gxLbl GR e = some l' ∧ CertZ24.lblRel4 L pi l l'

def CertZ24.agreeRP4 (G GR : Gexec) (pi : Nat → Nat) (L : Int → Prop) : Prop :=
  GR.gxImg = G.gxImg ∧ CertZ24.lblAgree4 G GR pi L ∧ CertZ18.lockCoSP G GR L

/-- Read values agree off failed acquires. -/
def CertZ24.rdAgree4 (G GR : Gexec) (L : Int → Prop) : Prop :=
  (∀ e a t v, CertZ24.nf G L e → glblIs G e lbIsW → greadsByte G e a t v →
    ∃ t', greadsByte GR e a t' v) ∧
  (∀ e a t v, glblIs GR e lbIsW → greadsByte GR e a t v → ∃ t', greadsByte G e a t' v)

/-- **THE AGREEMENT UP TO FAILED ACQUIRES.** -/
def CertZ24.agreeW4 (G GR : Gexec) (L : Int → Prop) : Prop :=
  GR.gxImg = G.gxImg ∧
  (∀ e a v, gwritesByte GR e a v → gwritesByte G e a v) ∧
  (∀ e a v, gwritesByte GR e a v → CertZ24.nf G L e) ∧
  (∀ e a v, CertZ24.nf G L e → gwritesByte G e a v → gwritesByte GR e a v) ∧
  (∀ e k, CertZ24.nf G L e → gcls G e k → glblIs G e lbIsW → gcls GR e k) ∧
  CertZ24.rdAgree4 G GR L ∧
  CertZ18.lockCoSP G GR L

theorem CertZ24.skipNoWr : lbWr CertZ24.skipLbl = none := rfl
theorem CertZ24.skipNoW : lbIsW CertZ24.skipLbl = false := rfl

/-- The per-event facts of the padded agreement. -/
theorem CertZ24.agreeW4OfRP4 (G GR : Gexec) (pi : Nat → Nat) (L : Int → Prop) :
    CertZ24.agreeRP4 G GR pi L → CertZ24.agreeW4 G GR L := by
  rintro ⟨himg, hlbl, hco⟩
  -- a member label writing is a re-index of a non-failed GF label
  have hwrR : ∀ e l', gxLbl GR e = some l' → lbIsW l' = true →
      ∃ l, gxLbl G e = some l ∧ ¬ CertZ24.lblFail L l ∧ lblReidxW (lblRen pi l) l' := by
    intro e l' hl' hW
    rcases hlbl e with ⟨-, h2⟩ | ⟨l, l'', h1, h2, hrel⟩
    · rw [h2] at hl'; cases hl'
    · rw [hl', Option.some.injEq] at h2
      subst h2
      rcases hrel with ⟨hnf, hre⟩ | ⟨-, rfl⟩
      · exact ⟨l, h1, hnf, hre⟩
      · exact absurd hW (by simp [CertZ24.skipNoW])
  -- a non-failed GF label has a re-indexed member label
  have hnfG : ∀ e l, gxLbl G e = some l → CertZ24.nf G L e →
      ∃ l', gxLbl GR e = some l' ∧ lblReidxW (lblRen pi l) l' := by
    intro e l hl hnf
    rcases hlbl e with ⟨h1, -⟩ | ⟨l0, l', h1, h2, hrel⟩
    · rw [h1] at hl; cases hl
    · rw [hl, Option.some.injEq] at h1
      subst h1
      rcases hrel with ⟨-, hre⟩ | ⟨hf, -⟩
      · exact ⟨l', h2, hre⟩
      · exact absurd ((CertZ24.failIff G L e _ hl).1 hf) hnf
  refine ⟨himg, ?_, ?_, ?_, ?_, ⟨?_, ?_⟩, hco⟩
  · rintro e a v ⟨l', base, vs, j, hl', hwr, hv, ha⟩
    obtain ⟨l, hl, -, hre⟩ := hwrR e l' hl' (lbWrIsW _ _ hwr)
    refine ⟨l, base, vs, j, hl, ?_, hv, ha⟩
    rw [← lblRenWr pi l, ← CertZ22.wrEq _ _ hre, hwr]
  · rintro e a v ⟨l', base, vs, j, hl', hwr, -, -⟩
    obtain ⟨l, hl, hnf, -⟩ := hwrR e l' hl' (lbWrIsW _ _ hwr)
    exact fun hf => hnf ((CertZ24.failIff G L e l hl).2 hf)
  · rintro e a v hnf ⟨l, base, vs, j, hl, hwr, hv, ha⟩
    obtain ⟨l', hl', hre⟩ := hnfG e l hl hnf
    refine ⟨l', base, vs, j, hl', ?_, hv, ha⟩
    rw [CertZ22.wrEq _ _ hre, lblRenWr, hwr]
  · rintro e k hnf ⟨l0, hl0, hk⟩ ⟨l1, hl1, hW⟩
    rw [hl0, Option.some.injEq] at hl1
    subst hl1
    obtain ⟨l', hl', hre⟩ := hnfG e l0 hl0 hnf
    have hW' : lbIsW (lblRen pi l0) = true := by rw [lblRenIsW]; exact hW
    obtain ⟨-, hcl'⟩ := GraphFetchWalkZ.lblReidxWWr _ _ hre hW'
    exact ⟨l', hl', by rw [hcl', lblRenCls]; exact hk⟩
  · rintro e a t v hnf ⟨l1, hl1, hW⟩ ⟨l0, base, ts, vs, j, hl0, hrd, ht, hv, ha⟩
    rw [hl1, Option.some.injEq] at hl0
    subst hl0
    obtain ⟨l', hl', hre⟩ := hnfG e l1 hl1 hnf
    obtain ⟨ts', hrd', hlen⟩ := CertZ18.reidxRd _ _ base (ts.map pi) vs hre
      (by rw [lblRenIsW]; exact hW) (lblRenRd pi _ base ts vs hrd)
    have hj : j < ts'.length := by rw [hlen, List.length_map]; exact lookup_lt_Some ht
    exact ⟨ts'[j], l', base, ts', vs, j, hl', hrd', List.getElem?_eq_getElem hj, hv, ha⟩
  · rintro e a t v ⟨l1, hl1, hW⟩ ⟨l0, base, ts', vs, j, hl0, hrd, ht, hv, ha⟩
    rw [hl1, Option.some.injEq] at hl0
    subst hl0
    obtain ⟨l, hl, -, hre⟩ := hwrR e l1 hl1 hW
    have hWl : lbIsW (lblRen pi l) = true := by rw [← lblReidxWIsw _ _ hre]; exact hW
    obtain ⟨ts1, hrd1, hlen1⟩ := CertZ18.reidxRdInv _ _ base ts' vs hre hWl hrd
    obtain ⟨ts, hrd0, hlen0⟩ := CertZ18.renRdInv pi l base ts1 vs hrd1
    have hj : j < ts.length := by rw [← hlen0, ← hlen1]; exact lookup_lt_Some ht
    exact ⟨ts[j], l, base, ts, vs, j, hl, hrd0, List.getElem?_eq_getElem hj, hv, ha⟩

/-! # 2. Window non-plainness, program order -/

theorem CertZ24.npAt4 (G GR : Gexec) (L : Int → Prop) (log : List Wmsg) (b : Int) (n0 r : Nat)
    (mr : Wmsg) (R : Geid) :
    gwf GR → CertZ24.agreeW4 G GR L → logOf GR log → wlpAt log b b n0 →
    log[r]? = some mr → n0 ≤ r → (msgByte mr b).isSome → gwriteAt GR (r + 1) = some R →
    CertZ14.np G R := by
  intro hwfR hag hlog hwin hr hn0 hs hat
  obtain ⟨w, hatw, hm, -, -⟩ := logOfLookup GR log r mr hwfR hlog hr
  rw [hat, Option.some.injEq] at hatw
  subst hatw
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hs
  have hwb := (WeakRvwmoKillArms.gmsgByte GR R mr b v hm).1 hv
  obtain ⟨-, hshape⟩ := hwin.2 r mr hr hn0 hs
  intro hpl
  have hplR := hag.2.2.2.2.1 R _ (hag.2.2.1 R b v hwb) hpl
    (gwritesByteGlblW G R b v (hag.2.1 R b v hwb))
  exact hshape.2.1 (gmsgCls GR R mr _ hplR hm)

theorem CertZ24.poOfRowR4 (G GR : Gexec) (x y : Geid) (a1 a2 : Int) (v1 v2 : BitVec 8) :
    gwrowGmo GR → gwritesByte GR x a1 v1 → gwritesByte GR y a2 v2 →
    gwritesByte G x a1 v1 → gwritesByte G y a2 v2 → x.1 = y.1 → x ≠ y →
    gwix GR x < gwix GR y → WeakRvwmoGraph.gpo G x y := by
  intro hrow hxR hyR hx hy h1 hne hlt
  have hsx : (gxLbl G x).isSome := by
    obtain ⟨l, -, -, -, hl, -⟩ := hx
    rw [hl]; rfl
  have hsy : (gxLbl G y).isSome := by
    obtain ⟨l, -, -, -, hl, -⟩ := hy
    rw [hl]; rfl
  rcases Nat.lt_trichotomy x.2 y.2 with h2 | h2 | h2
  · exact ⟨h1, h2, hsx, hsy⟩
  · exact absurd (Prod.ext h1 h2) hne
  · exfalso
    have hWx := gwritesByteGlblW GR x a1 v1 hxR
    have hWy := gwritesByteGlblW GR y a2 v2 hyR
    have e1 : (y.1, x.2) = x := Prod.ext h1.symm rfl
    have e2 : (y.1, y.2) = y := rfl
    have key := hrow y.1 y.2 x.2 h2 (by rw [e2]; exact hWy) (by rw [e1]; exact hWx)
    rw [e1, e2] at key
    omega

/-! # 3. The transport up to failed acquires -/

namespace CatLin

/-- **`csChainedT4` — THE TRANSPORT UP TO FAILED ACQUIRES**: `csChainedT3` at the padded agreement; the
section's acquire and the plain write are no failed acquires. -/
theorem csChainedT4 (GD : Gdexec) (ad : List (Geid × Geid)) (GR : Gexec) (L : Int → Prop)
    (log : List Wmsg) (b a : Int) (n0 r0 : Nat) (h : Option Nat)
    (w entry exit ACQ REL : Geid) :
    rvwmoCatAD GD ad → gwf GR → CertZ24.agreeW4 GD.gdG GR L → gwrowGmo GR → L b →
    CertZ18.rmwLatest GR log → CertZ18.regZeroAt GR.gxImg log b n0 →
    acqAqB GD.gdG GR log b n0 → relCoversB GD.gdG GR log b n0 →
    logOf GR log → lockWordByte log b → wlpAlt log b n0 h → wlpAt log b b n0 →
    acqRow GD.gdG b ACQ → CertZ24.nf GD.gdG L ACQ → CertZ24.nf GD.gdG L w →
    wprotAt log a b n0 r0 →
    (∃ v, gwritesByte GD.gdG w a v) → gcls GD.gdG w .WCplain →
    r0 < gwix GR w → gwix GR w ≤ log.length →
    (∀ v, ¬ gwritesByte GD.gdG w b v) →
    lockAcq GD.gdG b ACQ → glblIs GD.gdG ACQ lbAq →
    n0 < gwix GR ACQ → gwix GR ACQ ≤ log.length →
    lockCs GD.gdG b ACQ REL → CertZ14.np GD.gdG REL → WeakRvwmoGraph.gpo GD.gdG ACQ entry →
    gfenceCovers GD.gdG entry REL →
    gmoLt GD.gdG w entry → WeakRvwmoGraph.gpo GD.gdG ACQ exit → gmem GD.gdG exit →
    ACQ.1 ≠ w.1 →
    gmoLt GD.gdG w exit := by
  intro hcons hwfR hag hrowR hL hlat hz hAQ hRC hlog hlwb halt hwin hrow hnfA hnfw hpr hwa hcl hr0
    hlew hnob hacq haq hn0A hleA hcs hnpREL _hpoe hfen hcross hpox hmx hhart
  have hag' := hag
  obtain ⟨-, hRG, hRnf, hGR, hcls, hagRd, hagCo⟩ := hag'
  -- the reader's acquire is in the window
  obtain ⟨va, hva, hvane⟩ := id hacq
  have hvaR : gwritesByte GR ACQ b va := hGR ACQ b va hnfA hva
  have hAwR := lockAcqGwrites GR b ACQ hwfR ⟨va, hvaR, hvane⟩
  obtain ⟨mA, hmA, hgA⟩ := logOfWrite GR log ACQ hwfR hlog hAwR hleA
  have hbA := (WeakRvwmoKillArms.gmsgByte GR ACQ mA b va hgA).2 hvaR
  have hnpA : CertZ14.np GD.gdG ACQ :=
    CertZ24.npAt4 _ GR L log b n0 _ mA ACQ hwfR hag hlog hwin hmA (by omega) (by rw [hbA]; rfl)
      (by rw [show gwix GR ACQ - 1 + 1 = gwix GR ACQ by omega]; exact gwriteAtGwix GR ACQ hAwR)
  have hfreeA : wlpHolderAt log b n0 (gwix GR ACQ - 1) = some none := by
    obtain ⟨tA, hrdA⟩ := id hrow
    obtain ⟨tA', hrdA'⟩ :=
      hagRd.1 ACQ b tA lockFree hnfA (gwritesByteGlblW _ ACQ b va hva) hrdA
    obtain ⟨hlA, hvA⟩ := hlat ACQ b tA' lockFree (gwritesByteGlblW GR ACQ b va hvaR) hrdA'
    exact CertZ18.foldFreeOfLatest GR.gxImg log b n0 h _ tA' hlwb halt (by omega) hlA hvA
  have hspA : CertZ18.sp GD.gdG b ACQ := CertZ18.spRow _ b ACQ hnpA hrow
  obtain ⟨hwf, h6, hlv, -, -, -, -, -⟩ := hcons
  generalize GD.gdG = G at *
  have hndR := hwfR.1
  obtain ⟨vw, hvw⟩ := hwa
  have hvwR : gwritesByte GR w a vw := hGR w a vw hnfw hvw
  have hwR : w ∈ gwrites GR := gwritesByteGwrites GR w a vw hwfR hvwR
  have hclR : gcls GR w .WCplain := hcls w _ hnfw hcl (gwritesByteGlblW G w a vw hvw)
  have hnobR : ∀ v, ¬ gwritesByte GR w b v := fun v hv => hnob v (hRG w b v hv)
  obtain ⟨q, mq, hq, hlk, hs, hnz, ht, hfree, hno, ACQw, hatw, hacqwR, hixw, hhw⟩ :=
    holderAcqGraph GR log b a n0 r0 w hwfR hlog hlwb hpr hwR hr0 hlew ⟨vw, hvwR⟩ hclR
  have hrA := acqRowIsR G b ACQ hrow
  have hmoAx : gmoLt G ACQ exit := acqGmoAfterC G ACQ exit h6 hpox hrA haq hmx
  obtain ⟨vq, hvq, hvqne⟩ := id hacqwR
  have hvqG : gwritesByte G ACQw b vq := hRG ACQw b vq hvq
  have hacqw : lockAcq G b ACQw := ⟨vq, hvqG, hvqne⟩
  have hnpw : CertZ14.np G ACQw :=
    CertZ24.npAt4 _ GR L log b n0 q mq ACQw hwfR hag hlog hwin hlk hq.1 hs hatw
  have hAwwR : ACQw ∈ gwrites GR := lockAcqGwrites GR b ACQw hwfR hacqwR
  have hwne : ACQw ≠ w := fun he => hnob vq (he ▸ hvqG)
  have hpoAw : WeakRvwmoGraph.gpo G ACQw w :=
    CertZ24.poOfRowR4 G GR ACQw w b a vq vw hrowR hvq hvwR hvqG hvw hhw hwne (by omega)
  have hposA := WeakRvwmoGraph.gwixPos GR ACQ hAwR
  have hwinA : GraphFetchN2.inWin GR log n0 ACQw := ⟨by omega, by omega⟩
  by_cases heq : q = gwix GR ACQ - 1
  · exfalso
    have hA : ACQw = ACQ := gwixInj GR ACQw ACQ hndR hAwwR hAwR (by omega)
    apply hhart
    rw [← hA]
    exact hhw
  by_cases hlt : q < gwix GR ACQ - 1
  · -- WRITER-FIRST
    obtain ⟨r, R, mr, hr, hlkr, hsr, hzr, hatR, hRrel, hRix, -, hRh⟩ :=
      releaseBetweenGraph GR log b n0 q (gwix GR ACQ - 1) mq w.1 hwfR hlog hq.1 hlt hlk hs hnz ht
        hfree hfreeA
    obtain ⟨mw, hmw, hgw⟩ := logOfWrite GR log w hwfR hlog hwR hlew
    have hrp : gwix GR w - 1 ≤ r := by
      by_cases hc : r < gwix GR w - 1
      · exact absurd hzr (hno r mr ⟨hr.1, hc⟩ hlkr hsr)
      · omega
    have hrne : r ≠ gwix GR w - 1 := by
      intro hre
      rw [hre, hmw, Option.some.injEq] at hlkr
      subst hlkr
      rw [gmsgByteNone GR w mw b hgw hnobR] at hsr
      simp at hsr
    have hposw := WeakRvwmoGraph.gwixPos GR w hwR
    have hRG' : lockRel G b R := hRG R b lockFree hRrel
    have hnpR : CertZ14.np G R :=
      CertZ24.npAt4 _ GR L log b n0 r mr R hwfR hag hlog hwin hlkr (by omega) hsr hatR
    have hwRne : w ≠ R := fun he => hnob lockFree (he ▸ hRG')
    have hpowR : WeakRvwmoGraph.gpo G w R :=
      CertZ24.poOfRowR4 G GR w R a b vw lockFree hrowR hvwR hRrel hvw hRG' hRh.symm hwRne
        (by omega)
    have hfc : gfenceCovers G w R :=
      hRC ACQw R w hacqw hRG' hwinA ⟨by omega, by omega⟩ hpoAw hpowR
        (gwritesByteGlblW G w a vw hvw)
    have h1 : gmoLt G w R := fenceGmoAfterC G w R h6 hfc
    have h2 : gmoLt G R ACQ :=
      gwixLtGmo G R ACQ hwf (lockRelGwrites G b R hwf hRG') (lockAcqGwrites G b ACQ hwf hacq)
        ((hagCo b R ACQ lockFree va hL hRG' hva (CertZ18.spRel G b R hnpR hRG') hspA).2 (by omega))
    exact gmoLtTrans G w ACQ exit (gmoLtTrans G w R ACQ h1 h2) hmoAx
  · -- READER-FIRST
    have hltA : gwix GR ACQ - 1 < q := by omega
    have hnzA : mA.wmData ≠ wlockZero4 := fun hz => hvane (zero4Byte mA b va hz hbA)
    have htA := gmsgTid GR ACQ mA hgA
    obtain ⟨r', R', mr', hr', hlkr', hsr', -, hatR', hrelr', hixr', -, hhr'⟩ :=
      releaseBetweenGraph GR log b n0 (gwix GR ACQ - 1) q mA ACQ.1 hwfR hlog (by omega) hltA hmA
        (by rw [hbA]; rfl) hnzA htA hfreeA hfree
    obtain ⟨-, hRel, -, -, hnoin⟩ := hcs
    have hR'G : lockRel G b R' := hRG R' b lockFree hrelr'
    have hnpR' : CertZ14.np G R' :=
      CertZ24.npAt4 _ GR L log b n0 r' mr' R' hwfR hag hlog hwin hlkr' (by omega) hsr' hatR'
    have hspR' := CertZ18.spRel G b R' hnpR' hR'G
    have hspREL := CertZ18.spRel G b REL hnpREL hRel
    have hAR'G : gwix G ACQ < gwix G R' :=
      (hagCo b ACQ R' va lockFree hL hva hR'G hspA hspR').2 (by omega)
    have hRleG : gwix G REL ≤ gwix G R' := by
      by_cases hc : gwix G R' < gwix G REL
      · exact absurd ⟨hAR'G, hc⟩ (hnoin R' lockFree hR'G hhr')
      · omega
    have hRleR : gwix GR REL ≤ gwix GR R' :=
      CertZ18.coLeR3 G GR L b REL R' lockFree lockFree hwf hagCo hL hRel hR'G hspREL hspR' hRleG
    have hspw : CertZ18.sp G b ACQw := by
      refine ⟨hnpw, fun ⟨_, ⟨t, v, hrd, hne⟩⟩ => hne ?_⟩
      obtain ⟨t', hrd'⟩ := hagRd.1 ACQw b t v (hRnf ACQw b vq hvq)
        (gwritesByteGlblW G ACQw b vq hvqG) hrd
      obtain ⟨hl, hv⟩ := hlat ACQw b t' v (gwritesByteGlblW GR ACQw b vq hvq) hrd'
      rw [hixw, Nat.add_sub_cancel] at hl hv
      exact CertZ18.valFreeOfFold GR.gxImg log b n0 h q t' v hz hq.1 (by omega) hfree hl hv
    have hmoRA : gmoLt G REL ACQw :=
      gwixLtGmo G REL ACQw hwf (lockRelGwrites G b REL hwf hRel) (lockAcqGwrites G b ACQw hwf hacqw)
        ((hagCo b REL ACQw lockFree vq hL hRel hvqG hspREL hspw).2 (by omega))
    obtain ⟨hrw, haqw⟩ := hAQ ACQw hacqw hwinA
    have hmoAw : gmoLt G ACQw w :=
      acqGmoAfterC G ACQw w h6 hpoAw hrw haqw
        (WeakRvwmoGraph.glblIsWGmem G w (gwritesByteGlblW G w a vw hvw))
    have hmoeR := fenceGmoAfterC G entry REL h6 hfen
    exact absurd (gmoLtTrans G w entry w hcross
      (gmoLtTrans G entry REL w hmoeR (gmoLtTrans G REL ACQw w hmoRA hmoAw))) (gmoLtIrrefl G w)

end CatLin

end Weak
