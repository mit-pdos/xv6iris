/-
Weak: **W10 F1 [OWN.94] (N2′) — the transport at PROTOCOL lock co** (the coordinator's decision F1;
`PROGRESS-W10N2p.md` "(a) re-check").  Lean-only, no Rocq twin.

`GraphFetchN2.lockCoAgree` asks the realized member's co on the lock bytes to be `GF`'s for EVERY
write; xv6 writes lock bytes with PLAIN stores (`initlock`'s `lk->locked = 0`, kfree's memset of a dying
pipe), which no walk order can place consistently (`PROGRESS` FINDING).  This file restates the
transport at the PROTOCOL co, `GraphFetchN2.lockCoAgree` untouched (w1 edits `GraphFetch*`):

  §1  **`CertZ14.lockCoNP`** — co agreement among NON-PLAIN lock-byte writes, plus the one-way clause
      "a protocol write co-before a plain one is GR-before it" (F2's order constraint, which the walk
      supplies); `CertZ14.agreeW2`/`agreeRP2`; **`CertZ14.npOfWin`** — a member write in the export's
      registration window (`wlpAt`: at or after `n0` every lock-word message is lock-shaped, NOT
      `WCplain`) is non-plain at `GF` too;
  §2  **`CertZ14.acqFoldFreeR2`** — the fold is free before the reader's acquire, the quiet range
      starting at `max n0 t'` (a plain source of the acquire sits before `n0`, and a protocol write
      co-before it is GR-before it).

Spec: proof organisation; the export's `wlpAt` is the merged trusted export; FAITHFUL.  Lean-only
helpers file-qualified (`CertZ14.*`).
-/
import Weak.CertZ13

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open TsoShadow

/-! # 1. Protocol co -/

/-- A write is NON-PLAIN (an AMO / release-class write: the lock protocol's). -/
def CertZ14.np (G : Gexec) (e : Geid) : Prop := ¬ gcls G e .WCplain

/-- **PROTOCOL LOCK CO**: on the lock bytes, the non-plain writes are co-ordered in `GR` as in `G`,
and a non-plain write co-before a plain one is `GR`-before it. -/
def CertZ14.lockCoNP (G GR : Gexec) (L : Int → Prop) : Prop :=
  (∀ (b : Int) (x y : Geid) (vx vy : BitVec 8), L b →
    gwritesByte G x b vx → gwritesByte G y b vy → CertZ14.np G x → CertZ14.np G y →
    (gwix G x < gwix G y ↔ gwix GR x < gwix GR y)) ∧
  (∀ (b : Int) (x y : Geid) (vx vy : BitVec 8), L b →
    gwritesByte G x b vx → gwritesByte G y b vy → CertZ14.np G x → ¬ CertZ14.np G y →
    gwix G x < gwix G y → gwix GR x < gwix GR y)

def CertZ14.agreeW2 (G GR : Gexec) (L : Int → Prop) : Prop :=
  GR.gxImg = G.gxImg ∧
  (∀ e a v, gwritesByte GR e a v ↔ gwritesByte G e a v) ∧
  (∀ e k, gcls G e k → glblIs G e lbIsW → gcls GR e k) ∧
  CertZ14.lockCoNP G GR L

def CertZ14.agreeRP2 (G GR : Gexec) (pi : Nat → Nat) (L : Int → Prop) : Prop :=
  GR.gxImg = G.gxImg ∧
  List.Forall₂ (fun (r r' : List Lbl) => List.Forall₂ (fun l l' => lblReidxW (lblRen pi l) l') r r')
    G.gxProg GR.gxProg ∧
  CertZ14.lockCoNP G GR L

theorem CertZ14.agreeW2OfRP2 (G GR : Gexec) (pi : Nat → Nat) (L : Int → Prop) :
    CertZ14.agreeRP2 G GR pi L → CertZ14.agreeW2 G GR L := by
  rintro ⟨himg, hrows, hco⟩
  obtain ⟨h1, h2, h3, -⟩ := GraphFetchN2.agreeWOfRP G GR pi (fun _ => False)
    ⟨himg, hrows, fun _ _ _ _ _ hb => hb.elim⟩
  exact ⟨h1, h2, h3, hco⟩

/-- Full lock co gives protocol lock co. -/
theorem CertZ14.lockCoNPOf (G GR : Gexec) (L : Int → Prop) :
    gwf G → GraphFetchN2.lockCoAgree G GR L → CertZ14.lockCoNP G GR L :=
  fun _ h => ⟨fun b x y vx vy hb hx hy _ _ => h b x y vx vy hb hx hy,
    fun b x y vx vy hb hx hy _ _ hlt => (h b x y vx vy hb hx hy).1 hlt⟩

/-- A full log has one message per write. -/
theorem CertZ14.logLen (G : Gexec) (log : List Wmsg) :
    gwf G → logOf G log → log.length = (gwrites G).length := by
  intro hwf hlog
  apply Nat.le_antisymm
  · refine Nat.le_of_not_lt (fun hlt => ?_)
    obtain ⟨m, hm⟩ : ∃ m, log[(gwrites G).length]? = some m :=
      ⟨_, List.getElem?_eq_getElem hlt⟩
    obtain ⟨w, hw, -⟩ := (hlog _ m).1 hm
    change (gwrites G)[(gwrites G).length]? = some w at hw
    rw [List.getElem?_eq_none (Nat.le_refl _)] at hw
    cases hw
  · refine Nat.le_of_not_lt (fun hlt => ?_)
    obtain ⟨w, hw⟩ : ∃ w, (gwrites G)[log.length]? = some w := ⟨_, List.getElem?_eq_getElem hlt⟩
    have hwm := gwritesLookupElem G _ w hw
    obtain ⟨-, hisw⟩ := (gwritesElemOf G w).1 hwm
    unfold gisW at hisw
    cases hl : gxLbl G w with
    | none => rw [hl] at hisw; cases hisw
    | some l =>
      rw [hl] at hisw
      obtain ⟨base, vs, hwr⟩ := lbIsWWr l hisw
      have hgm : WeakRvwmoKillArms.gmsg G w = some ⟨base, vs, some w.1, lbCls l⟩ := by
        unfold WeakRvwmoKillArms.gmsg; simp only [hl, hwr]
      have := (hlog log.length _).2 ⟨w, hw, hgm⟩
      rw [List.getElem?_eq_none (Nat.le_refl _)] at this
      cases this

/-- A member write at or after the registration point is non-plain, at the member and at `G`. -/
theorem CertZ14.npOfWin (G GR : Gexec) (L : Int → Prop) (log : List Wmsg) (b : Int) (n0 : Nat)
    (r : Nat) (mr : Wmsg) :
    gwf GR → CertZ14.agreeW2 G GR L → logOf GR log → wlpAt log b b n0 →
    log[r]? = some mr → n0 ≤ r → (msgByte mr b).isSome →
    ∃ w, gwriteAt GR (r + 1) = some w ∧ gwix GR w = r + 1 ∧ w ∈ gwrites GR ∧
      (∃ v, gwritesByte G w b v) ∧ CertZ14.np G w := by
  intro hwfR hag hlog hwin hr hn0 hs
  obtain ⟨w, hat, hm, hix, hw⟩ := logOfLookup GR log r mr hwfR hlog hr
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hs
  have hwb := (WeakRvwmoKillArms.gmsgByte GR w mr b v hm).1 hv
  obtain ⟨-, hshape⟩ := hwin.2 r mr hr hn0 hs
  refine ⟨w, hat, hix, hw, ⟨v, (hag.2.1 w b v).1 hwb⟩, fun hpl => ?_⟩
  have hplR := hag.2.2.1 w _ hpl (gwritesByteGlblW G w b v ((hag.2.1 w b v).1 hwb))
  exact hshape.2.1 (gmsgCls GR w mr _ hplR hm)

/-! # 2. The fold before the reader's acquire -/

/-- The fold's value at the source `t` of an acquire is free (`acqFoldFreeG`'s second half): the
source is a release at index `t` above the registration point. -/
theorem CertZ14.foldAtSrc (G : Gexec) (log : List Wmsg) (b : Int) (n0 : Nat) (h : Option Nat)
    (t : Nat) (R : Geid) :
    gwf G → logOf G log → lockWordByte log b → wlpAlt log b n0 h →
    n0 < t → t ≤ log.length → lockRel G b R → R ∈ gwrites G → gwix G R = t →
    wlpHolderAt log b n0 t = some none := by
  intro hwf hlog hlwb halt hn0 htl hR hRw hRix
  obtain ⟨m, hm, hgm⟩ := logOfWrite G log R hwf hlog hRw (by omega)
  rw [hRix] at hm
  have hbz := (WeakRvwmoKillArms.gmsgByte G R m b lockFree hgm).2 hR
  have hzero := hlwb (t - 1) m lockFree hm hbz rfl
  obtain ⟨hlen, hf⟩ := halt
  obtain ⟨h2, ht2⟩ := wlpHolderIsSome log b n0 t log.length h (by omega) hf
  obtain ⟨h1, ht1⟩ := wlpHolderIsSome log b n0 (t - 1) log.length h (by omega) hf
  rw [ht2]
  have hstep := wlpHolderStep log b n0 (t - 1) m (by omega) hm
  rw [ht1] at hstep
  have ht' : t - 1 + 1 = t := by omega
  rw [ht', ht2] at hstep
  dsimp only at hstep
  rw [(mwritesTrue b m).2 (by rw [hbz]; rfl)] at hstep
  simp only [↓reduceIte] at hstep
  rw [(altStepZero h1 m h2 hzero hstep.symm).1]

/-- **`CertZ14.acqFoldFreeR2`** — the fold is free before the reader's acquire, at PROTOCOL co. -/
theorem CertZ14.acqFoldFreeR2 (GD : Gdexec) (ad : List (Geid × Geid)) (GR : Gexec)
    (L : Int → Prop) (log : List Wmsg) (b : Int) (n0 : Nat) (h : Option Nat) (ACQ : Geid) :
    CatLin.rvwmoCatAD GD ad → gwf GR → CertZ14.agreeW2 GD.gdG GR L → L b →
    logOf GR log → lockWordByte log b → wlpAlt log b n0 h → wlpAt log b b n0 →
    acqRow GD.gdG b ACQ → lockAcq GD.gdG b ACQ → CertZ14.np GD.gdG ACQ →
    n0 < gwix GR ACQ → gwix GR ACQ ≤ log.length →
    wlpHolderAt log b n0 (gwix GR ACQ - 1) = some none := by
  intro hcons hwfR hag hL hlog hlwb halt hwin hrow hacq hnpA hn0A hle
  obtain ⟨hwf, h6, hlv, hatm, -, -, -, -⟩ := hcons
  generalize GD.gdG = G at *
  obtain ⟨t, hrd⟩ := hrow
  obtain ⟨va, hva, -⟩ := id hacq
  have htlt := CatLin.acqTsLtC G b ACQ t hwf h6 hlv hacq hrd
  have hsrcG := CatLin.acqSrcC G b ACQ t hatm hacq hrd
  have hAw := lockAcqGwrites G b ACQ hwf hacq
  -- a window message touching `b` is a non-plain GF write, outside `(src, ACQ)` in GF
  have hwinW : ∀ r mr, n0 ≤ r → r < gwix GR ACQ - 1 → log[r]? = some mr → (msgByte mr b).isSome →
      ∃ w v, gwix GR w = r + 1 ∧ gwritesByte G w b v ∧ CertZ14.np G w ∧
        (gwix G w ≤ t ∨ gwix G ACQ ≤ gwix G w) := by
    intro r mr hn0 hr hmr hs
    obtain ⟨w, -, hix, -, ⟨v, hv⟩, hnp⟩ := CertZ14.npOfWin G GR L log b n0 r mr hwfR hag hlog hwin
      hmr hn0 hs
    exact ⟨w, v, hix, hv, hnp, hsrcG w v hv⟩
  -- a window write GF-after the acquire is GR-after it
  have hafter : ∀ w v, gwritesByte G w b v → CertZ14.np G w → gwix G ACQ ≤ gwix G w →
      gwix GR ACQ ≤ gwix GR w := by
    intro w v hw hnp hge
    rcases Nat.lt_or_eq_of_le hge with hlt | heq
    · exact Nat.le_of_lt ((hag.2.2.2.1 b ACQ w va v hL hva hw hnpA hnp).1 hlt)
    · have := gwixInj G ACQ w hwf.1 hAw (gwritesByteGwrites G w b v hwf hw) heq
      subst this; exact Nat.le_refl _
  -- the quiet range from `s`
  have hquietFrom : ∀ s, n0 ≤ s →
      (∀ w v, gwritesByte G w b v → CertZ14.np G w → gwix G w ≤ t → gwix GR w ≤ s) →
      wlpHolderAt log b n0 (gwix GR ACQ - 1) = wlpHolderAt log b n0 (min s (gwix GR ACQ - 1)) := by
    intro s hs hbelow
    apply wlpHolderQuiet log b n0 _ _ (Nat.min_le_right _ _)
    intro r mr ⟨hr1, hr2⟩ hmr
    cases hb : msgByte mr b with
    | none => rfl
    | some v =>
      exfalso
      have hr1' : s ≤ r := by
        rcases Nat.le_total s (gwix GR ACQ - 1) with h' | h'
        · rw [Nat.min_eq_left h'] at hr1; exact hr1
        · rw [Nat.min_eq_right h'] at hr1; omega
      obtain ⟨w, v', hix, hwv, hnp, hcase⟩ := hwinW r mr (by omega) hr2 hmr (by rw [hb]; rfl)
      rcases hcase with hlo | hhi
      · have := hbelow w v' hwv hnp hlo; omega
      · have := hafter w v' hwv hnp hhi; omega
  by_cases ht0 : t = 0
  · -- the source is the image: every window write is GF-after the acquire
    rw [hquietFrom n0 (Nat.le_refl _) (fun w v hw _ hlo => by
      have := WeakRvwmoGraph.gwixPos G w (gwritesByteGwrites G w b v hwf hw); omega)]
    exact wlpHolderSmall log b n0 _ (Nat.min_le_left _ _)
  · obtain ⟨R0, hR0, hR0w, hR0ix⟩ := CatLin.acqSrcRelC G b ACQ t hwf hlv hrd (by omega)
    -- a GF write `≤ t` other than `R0` is co-before `R0`
    have hle0 : ∀ w v, gwritesByte G w b v → gwix G w ≤ t → w = R0 ∨ gwix G w < gwix G R0 := by
      intro w v hw hlo
      rcases Nat.lt_or_eq_of_le hlo with h' | h'
      · exact .inr (by omega)
      · exact .inl (gwixInj G w R0 hwf.1 (gwritesByteGwrites G w b v hwf hw) hR0w (by omega))
    by_cases hnp0 : CertZ14.np G R0
    · -- a protocol source: the quiet range from `max n0 t'`
      have hbel : ∀ w v, gwritesByte G w b v → CertZ14.np G w → gwix G w ≤ t →
          gwix GR w ≤ max n0 (gwix GR R0) := by
        intro w v hw hnp hlo
        rcases hle0 w v hw hlo with rfl | hlt
        · exact Nat.le_max_right _ _
        · have := (hag.2.2.2.1 b w R0 v lockFree hL hw hR0 hnp hnp0).1 hlt; omega
      rw [hquietFrom _ (Nat.le_max_left _ _) hbel]
      have hR0lt : gwix GR R0 < gwix GR ACQ :=
        (hag.2.2.2.1 b R0 ACQ lockFree va hL hR0 hva hnp0 hnpA).1 (by omega)
      rw [Nat.min_eq_left (by omega)]
      by_cases hc : gwix GR R0 ≤ n0
      · rw [Nat.max_eq_left hc]; exact wlpHolderSmall log b n0 n0 (Nat.le_refl _)
      · rw [Nat.max_eq_right (by omega)]
        exact CertZ14.foldAtSrc GR log b n0 h (gwix GR R0) R0 hwfR hlog hlwb halt (by omega)
          (by omega) ((hag.2.1 R0 b lockFree).2 hR0)
          (gwritesByteGwrites GR R0 b lockFree hwfR ((hag.2.1 R0 b lockFree).2 hR0)) rfl
    · -- a PLAIN source (initlock's zero): it sits before `n0`; protocol writes co-before it are
      -- GR-before it
      have hR0wR := gwritesByteGwrites GR R0 b lockFree hwfR ((hag.2.1 R0 b lockFree).2 hR0)
      have hR0pos : gwix GR R0 ≤ n0 := by
        refine Nat.le_of_not_lt (fun hgt => ?_)
        obtain ⟨m, hm, hgm⟩ := logOfWrite GR log R0 hwfR hlog hR0wR (by
          rw [CertZ14.logLen GR log hwfR hlog]; exact gwixLe GR R0 hR0wR)
        have hs : (msgByte m b).isSome := by
          rw [(WeakRvwmoKillArms.gmsgByte GR R0 m b lockFree hgm).2 ((hag.2.1 R0 b lockFree).2 hR0)]
          rfl
        obtain ⟨-, hshape⟩ := hwin.2 _ m hm (by omega) hs
        have hplG : gcls G R0 .WCplain := by
          unfold CertZ14.np at hnp0; exact Classical.not_not.1 hnp0
        exact hshape.2.1 (gmsgCls GR R0 m _ (hag.2.2.1 R0 _ hplG (gwritesByteGlblW G R0 b lockFree
          hR0)) hgm)
      have hbel : ∀ w v, gwritesByte G w b v → CertZ14.np G w → gwix G w ≤ t → gwix GR w ≤ n0 := by
        intro w v hw hnp hlo
        rcases hle0 w v hw hlo with rfl | hlt
        · exact absurd hnp hnp0
        · have := hag.2.2.2.2 b w R0 v lockFree hL hw hR0 hnp hnp0 hlt; omega
      rw [hquietFrom n0 (Nat.le_refl _) hbel]
      exact wlpHolderSmall log b n0 _ (Nat.min_le_left _ _)

/-! # 3. The transport at protocol co -/

/-- The full-interface agreement at the EMPTY lock set (for the write / row lemmas of `GraphFetchN2`). -/
theorem CertZ14.agreeW0 (G GR : Gexec) (L : Int → Prop) :
    CertZ14.agreeW2 G GR L → GraphFetchN2.agreeW G GR (fun _ => False) :=
  fun ⟨h1, h2, h3, _⟩ => ⟨h1, h2, h3, fun _ _ _ _ _ hb => hb.elim⟩

theorem CertZ14.coLeR2 (G GR : Gexec) (L : Int → Prop) (b : Int) (x y : Geid) (vx vy : BitVec 8) :
    gwf G → CertZ14.agreeW2 G GR L → L b →
    gwritesByte G x b vx → gwritesByte G y b vy → CertZ14.np G x → CertZ14.np G y →
    gwix G x ≤ gwix G y → gwix GR x ≤ gwix GR y := by
  intro hwf hag hL hx hy hnx hny hle
  rcases Nat.lt_or_eq_of_le hle with hlt | heq
  · exact Nat.le_of_lt ((hag.2.2.2.1 b x y vx vy hL hx hy hnx hny).1 hlt)
  · have := gwixInj G x y hwf.1 (gwritesByteGwrites G x b vx hwf hx)
      (gwritesByteGwrites G y b vy hwf hy) heq
    subst this
    exact Nat.le_refl _

/-- A member write at a window position is the named one, non-plain at GF. -/
theorem CertZ14.npAt (G GR : Gexec) (L : Int → Prop) (log : List Wmsg) (b : Int) (n0 r : Nat)
    (mr : Wmsg) (R : Geid) :
    gwf GR → CertZ14.agreeW2 G GR L → logOf GR log → wlpAt log b b n0 →
    log[r]? = some mr → n0 ≤ r → (msgByte mr b).isSome → gwriteAt GR (r + 1) = some R →
    CertZ14.np G R := by
  intro hwfR hag hlog hwin hr hn0 hs hat
  obtain ⟨w, hw, -, -, -, hnp⟩ := CertZ14.npOfWin G GR L log b n0 r mr hwfR hag hlog hwin hr hn0 hs
  rw [hat, Option.some.injEq] at hw
  rw [hw]; exact hnp

namespace CatLin

/-- **`csChainedT2` — THE TRANSPORT AT PROTOCOL LOCK CO** (`csChainedT`'s restatement, F1): the lock co
used is among NON-PLAIN writes only — the reader's acquire, the writer's acquire and both releases found
in the member's log lie in the export's window (`wlpAt`), hence are non-plain; the section's release
`REL` is non-plain by hypothesis (xv6: `amoswap.w`). -/
theorem csChainedT2 (GD : Gdexec) (ad : List (Geid × Geid)) (GR : Gexec) (L : Int → Prop)
    (log : List Wmsg) (b a : Int) (n0 r0 : Nat) (h : Option Nat)
    (w entry exit ACQ REL : Geid) :
    rvwmoCatAD GD ad → gwf GR → CertZ14.agreeW2 GD.gdG GR L → gwrowGmo GR → L b →
    acqAqB GD.gdG GR log b n0 → relCoversB GD.gdG GR log b n0 →
    logOf GR log → lockWordByte log b → wlpAlt log b n0 h → wlpAt log b b n0 →
    acqRow GD.gdG b ACQ →
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
  intro hcons hwfR hag hrowR hL hAQ hRC hlog hlwb halt hwin hrow hpr hwa hcl hr0 hlew hnob hacq
    haq hn0A hleA hcs hnpREL _hpoe hfen hcross hpox hmx hhart
  have hag0 := CertZ14.agreeW0 _ _ L hag
  -- the reader's acquire is in the window
  obtain ⟨va, hva, hvane⟩ := id hacq
  have hvaR : gwritesByte GR ACQ b va := (hag.2.1 ACQ b va).2 hva
  have hAwR := lockAcqGwrites GR b ACQ hwfR ⟨va, hvaR, hvane⟩
  obtain ⟨mA, hmA, hgA⟩ := logOfWrite GR log ACQ hwfR hlog hAwR hleA
  have hbA := (WeakRvwmoKillArms.gmsgByte GR ACQ mA b va hgA).2 hvaR
  have hnpA : CertZ14.np GD.gdG ACQ :=
    CertZ14.npAt _ GR L log b n0 _ mA ACQ hwfR hag hlog hwin hmA (by omega) (by rw [hbA]; rfl)
      (by rw [show gwix GR ACQ - 1 + 1 = gwix GR ACQ by omega]; exact gwriteAtGwix GR ACQ hAwR)
  have hfreeA :=
    CertZ14.acqFoldFreeR2 GD ad GR L log b n0 h ACQ hcons hwfR hag hL hlog hlwb halt hwin hrow
      hacq hnpA hn0A hleA
  obtain ⟨hwf, h6, hlv, -, -, -, -, -⟩ := hcons
  generalize GD.gdG = G at *
  have hndR := hwfR.1
  obtain ⟨vw, hvw⟩ := hwa
  have hwR : w ∈ gwrites GR := GraphFetchN2.wrR G GR _ w a vw hwfR hag0 hvw
  have hclR : gcls GR w .WCplain := hag.2.2.1 w _ hcl (gwritesByteGlblW G w a vw hvw)
  have hnobR : ∀ v, ¬ gwritesByte GR w b v := fun v hv => hnob v ((hag.2.1 w b v).1 hv)
  obtain ⟨q, mq, hq, hlk, hs, hnz, ht, hfree, hno, ACQw, hatw, hacqwR, hixw, hhw⟩ :=
    holderAcqGraph GR log b a n0 r0 w hwfR hlog hlwb hpr hwR hr0 hlew ⟨vw, (hag.2.1 w a vw).2 hvw⟩
      hclR
  have hrA := acqRowIsR G b ACQ hrow
  have hmoAx : gmoLt G ACQ exit := acqGmoAfterC G ACQ exit h6 hpox hrA haq hmx
  obtain ⟨vq, hvq, hvqne⟩ := id hacqwR
  have hvqG : gwritesByte G ACQw b vq := (hag.2.1 ACQw b vq).1 hvq
  have hacqw : lockAcq G b ACQw := ⟨vq, hvqG, hvqne⟩
  have hnpw : CertZ14.np G ACQw := CertZ14.npAt _ GR L log b n0 q mq ACQw hwfR hag hlog hwin hlk hq.1 hs hatw
  have hAwwR : ACQw ∈ gwrites GR := lockAcqGwrites GR b ACQw hwfR hacqwR
  have hwne : ACQw ≠ w := fun he => hnob vq (he ▸ hvqG)
  have hpoAw : WeakRvwmoGraph.gpo G ACQw w :=
    GraphFetchN2.poOfRowR G GR _ ACQw w b a vq vw hag0 hrowR hvqG hvw hhw hwne (by omega)
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
    have hRG : lockRel G b R := (hag.2.1 R b lockFree).1 hRrel
    have hnpR : CertZ14.np G R :=
      CertZ14.npAt _ GR L log b n0 r mr R hwfR hag hlog hwin hlkr (by omega) hsr hatR
    have hwRne : w ≠ R := fun he => hnob lockFree (he ▸ hRG)
    have hpowR : WeakRvwmoGraph.gpo G w R :=
      GraphFetchN2.poOfRowR G GR _ w R a b vw lockFree hag0 hrowR hvw hRG hRh.symm hwRne
        (by omega)
    have hfc : gfenceCovers G w R :=
      hRC ACQw R w hacqw hRG hwinA ⟨by omega, by omega⟩ hpoAw hpowR (gwritesByteGlblW G w a vw hvw)
    have h1 : gmoLt G w R := fenceGmoAfterC G w R h6 hfc
    have h2 : gmoLt G R ACQ :=
      gwixLtGmo G R ACQ hwf (lockRelGwrites G b R hwf hRG) (lockAcqGwrites G b ACQ hwf hacq)
        ((hag.2.2.2.1 b R ACQ lockFree va hL hRG hva hnpR hnpA).2 (by omega))
    exact gmoLtTrans G w ACQ exit (gmoLtTrans G w R ACQ h1 h2) hmoAx
  · -- READER-FIRST
    have hltA : gwix GR ACQ - 1 < q := by omega
    have hnzA : mA.wmData ≠ wlockZero4 := fun hz => hvane (zero4Byte mA b va hz hbA)
    have htA := gmsgTid GR ACQ mA hgA
    obtain ⟨r', R', mr', hr', hlkr', hsr', -, hatR', hrelr', hixr', -, hhr'⟩ :=
      releaseBetweenGraph GR log b n0 (gwix GR ACQ - 1) q mA ACQ.1 hwfR hlog (by omega) hltA hmA
        (by rw [hbA]; rfl) hnzA htA hfreeA hfree
    obtain ⟨-, hRel, -, -, hnoin⟩ := hcs
    have hR'G : lockRel G b R' := (hag.2.1 R' b lockFree).1 hrelr'
    have hnpR' : CertZ14.np G R' :=
      CertZ14.npAt _ GR L log b n0 r' mr' R' hwfR hag hlog hwin hlkr' (by omega) hsr' hatR'
    have hAR'G : gwix G ACQ < gwix G R' :=
      (hag.2.2.2.1 b ACQ R' va lockFree hL hva hR'G hnpA hnpR').2 (by omega)
    have hRleG : gwix G REL ≤ gwix G R' := by
      by_cases hc : gwix G R' < gwix G REL
      · exact absurd ⟨hAR'G, hc⟩ (hnoin R' lockFree hR'G hhr')
      · omega
    have hRleR : gwix GR REL ≤ gwix GR R' :=
      CertZ14.coLeR2 G GR L b REL R' lockFree lockFree hwf hag hL hRel hR'G hnpREL hnpR' hRleG
    have hmoRA : gmoLt G REL ACQw :=
      gwixLtGmo G REL ACQw hwf (lockRelGwrites G b REL hwf hRel) (lockAcqGwrites G b ACQw hwf hacqw)
        ((hag.2.2.2.1 b REL ACQw lockFree vq hL hRel hvqG hnpREL hnpw).2 (by omega))
    obtain ⟨hrw, haqw⟩ := hAQ ACQw hacqw hwinA
    have hmoAw : gmoLt G ACQw w :=
      acqGmoAfterC G ACQw w h6 hpoAw hrw haqw
        (WeakRvwmoGraph.glblIsWGmem G w (gwritesByteGlblW G w a vw hvw))
    have hmoeR := fenceGmoAfterC G entry REL h6 hfen
    exact absurd (gmoLtTrans G w entry w hcross
      (gmoLtTrans G entry REL w hmoeR (gmoLtTrans G REL ACQw w hmoRA hmoAw))) (gmoLtIrrefl G w)

end CatLin

end Weak
