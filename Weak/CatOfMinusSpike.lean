/-
Weak: **W12-spike — the kill arms over RVWMO as riscv.cat states it** (Stage 0 scratch).

Report: `notes/W12-spike.md`.  Lean-only, no Rocq twin.  NOT part of the published chain;
it exists to make the spike's verdict checkable.

  §0  `rvwmoCatAD GD ad`: the hypothesis the chain should carry — the cat model's six arms,
      load value, atomicity, the dependency fragment, and RULE 12 over an addr/data SUBLIST
      `ad ⊆ gdDeps`.  It follows from the TAGGED model (`AxDeps.rvwmoCatConsistentT`, on
      `forget GT`), from the untagged `rvwmoCatConsistent` (`ad := gdDeps`) and from
      RVWMO⁻(+deps) (via `minusImpliesCat`) — so one restatement covers all three.
  §1  GATE 1: same-hart rf (rfi) is po-forward under cat (rule 1 alone), so rfi moves into
      the same-hart arm `rsameC`; `gcrossE` = rfe ∪ co ∪ fr is gmo-forward from load value.
  §2  The pinned segment, generalised to a same-hart CHAIN of ordered steps (the six cat
      arms, deps, rule 12 over `ad`), and the composition kill (`cycleKillArmsC`).
  §3  GATE 2: the lock kit (`acqSrc`/`acqTsLt`/`acqSrcRel`/`acqFoldFree`) and `csChained`,
      re-proved over `rvwmoCatAD` by changing the hypothesis only.
-/
import Weak.WeakRvwmoKillArms
import Weak.AxDeps

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Lbl

namespace CatOfMinusSpike

/-! # 0. The hypothesis -/

def rvwmoCatAD (GD : Gdexec) (ad : List (Geid × Geid)) : Prop :=
  gwf GD.gdG ∧ gppoCat6Gmo GD.gdG ∧ gloadValue GD.gdG ∧ gatomicity GD.gdG ∧
  gdepsWf GD.gdG GD.gdDeps ∧ gdepsGmo GD.gdG GD.gdDeps ∧
  (∀ p, p ∈ ad → p ∈ GD.gdDeps) ∧
  (∀ a b, gppo12 GD.gdG ad a b → gmoLt GD.gdG a b)

theorem catADOfCatT (GT : GdexecT) :
    rvwmoCatConsistentT GT → rvwmoCatAD (forget GT) (gtAd GT.gtG GT.gtDeps) := by
  intro h
  obtain ⟨hwf, h6, hlv, hat, hdw, hdg⟩ := catTForgetAxioms GT h
  exact ⟨hwf, h6, hlv, hat, hdw, hdg, fun p hp => gtAdSubForget _ _ p hp,
    fun a b h12 => h.2.1 a b (Or.inr h12)⟩

theorem catADOfCat (GD : Gdexec) :
    rvwmoCatConsistent GD → rvwmoCatAD GD GD.gdDeps := by
  rintro ⟨hwf, hppo, hlv, hat, hdw, hdg⟩
  exact ⟨hwf, fun e1 e2 h => hppo e1 e2 (Or.inl h), hlv, hat, hdw, hdg, fun _ h => h,
    fun a b h => hppo a b (Or.inr h)⟩

theorem catADOfMinus (GD : Gdexec) :
    rvwmoMinusDepsConsistent GD → rvwmoCatAD GD GD.gdDeps :=
  fun h => catADOfCat GD (minusImpliesCat GD h)

/-! # 1. GATE 1: rfi is same-hart and po-forward; the cross arms are rfe ∪ co ∪ fr -/

def grfi (G : Gexec) (w r : Geid) : Prop := WeakRvwmoAcyc.grf G w r ∧ w.1 = r.1

/-- Rule 1 (`[M];po-loc;[W]`) forbids a read of a po-LATER same-hart store, so rfi runs
forward in po.  Nothing else is used. -/
theorem grfiLex (G : Gexec) (w r : Geid) :
    gppoCat6Gmo G → gloadValue G → grfi G w r → w.1 = r.1 ∧ w.2 < r.2 := by
  rintro h6 hlv ⟨⟨a, t, v, hrd, hat⟩, hag⟩
  refine ⟨hag, ?_⟩
  cases t with
  | zero => simp [gwriteAt] at hat
  | succ i =>
    obtain ⟨w0, hat0, hwb, hvis⟩ := (hlv r a (i + 1) v hrd).1
    have hw0 : w0 = w := by rw [hat0] at hat; exact Option.some.inj hat
    subst hw0
    rcases hvis with hmo | hpo
    · rcases Nat.lt_trichotomy w0.2 r.2 with hlt | heq | hgt
      · exact hlt
      · exfalso
        have : w0 = r := Prod.ext hag heq
        subst this
        exact gmoLtIrrefl G _ hmo
      · exfalso
        have hlr : (gxLbl G r).isSome = true := by
          obtain ⟨l, _, _, _, _, hl, _⟩ := hrd
          simp [hl]
        have hlw : (gxLbl G w0).isSome = true := by
          obtain ⟨l, _, _, _, hl, _⟩ := hwb
          simp [hl]
        have hpo : WeakRvwmoGraph.gpo G r w0 := ⟨hag.symm, hgt, hlr, hlw⟩
        have hrw := h6 r w0 (Or.inl ⟨hpo, a, Or.inr ⟨i + 1, v, hrd⟩, v, hwb⟩)
        exact gmoLtIrrefl G _ (gmoLtTrans G _ _ _ hmo hrw)
    · exact hpo.2.1

/-- The same-hart arms, now WITH rfi. -/
def rsameC (GD : Gdexec) (x y : Geid) : Prop :=
  gpow GD.gdG x y ∨ gppo GD.gdG x y ∨ (x, y) ∈ GD.gdDeps ∨ grfi GD.gdG x y

/-- The cross arms, rf restricted to rfe. -/
def gcrossE (G : Gexec) (x y : Geid) : Prop :=
  grfe G x y ∨ gco G x y ∨ gfr G x y

theorem racyDSplitC (GD : Gdexec) (x y : Geid) :
    racyD GD x y → rsameC GD x y ∨ gcrossE GD.gdG x y := by
  rintro ((h | h | h | h | h) | h)
  · exact .inl (.inl h)
  · by_cases hag : x.1 = y.1
    · exact .inl (.inr (.inr (.inr ⟨h, hag⟩)))
    · exact .inr (.inl ⟨h, hag⟩)
  · exact .inr (.inr (.inl h))
  · exact .inr (.inr (.inr h))
  · exact .inl (.inr (.inl h))
  · exact .inl (.inr (.inr (.inl h)))

theorem rsameCLex (GD : Gdexec) (ad : List (Geid × Geid)) (x y : Geid) :
    rvwmoCatAD GD ad → rsameC GD x y → x.1 = y.1 ∧ x.2 < y.2 := by
  rintro hc (⟨⟨h1, h2, -⟩, -⟩ | h | h | h)
  · exact ⟨h1, h2⟩
  · rcases h with (⟨⟨h1, h2, -⟩, -⟩ | ⟨-, -, -, -, ⟨h1, h2, -⟩, -, -⟩ | ⟨⟨h1, h2, -⟩, -⟩ |
      ⟨⟨h1, h2, -⟩, -⟩) <;> exact ⟨h1, h2⟩
  · obtain ⟨h1, h2, -, -⟩ := hc.2.2.2.2.1 (x, y) h
    exact ⟨h1, h2⟩
  · exact grfiLex GD.gdG x y hc.2.1 hc.2.2.1 h

theorem rsameCAcyclic (GD : Gdexec) (ad : List (Geid × Geid)) (x : Geid) :
    rvwmoCatAD GD ad → ¬ tc (rsameC GD) x x := by
  intro hc hcyc
  have key : ∀ a b, tc (rsameC GD) a b → a.1 = b.1 ∧ a.2 < b.2 := by
    intro a b h
    induction h with
    | single h => exact rsameCLex GD ad _ _ hc h
    | tail _ h ih =>
      obtain ⟨h1, h2⟩ := rsameCLex GD ad _ _ hc h
      exact ⟨ih.1.trans h1, by omega⟩
  have := key x x hcyc
  omega

/-- Every cross arm is gmo-forward from `gwf` + load value ALONE. -/
theorem gcrossEGmo (G : Gexec) (x y : Geid) :
    gwf G → gloadValue G → gcrossE G x y → gmoLt G x y := by
  rintro hwf hlv (h | h | h)
  · exact grfeGmo G x y hlv h
  · exact gcoGmo G x y hwf h
  · exact gfrGmoLv G x y hwf hlv h

/-! # 2. The pinned segment as a same-hart ordered chain, and the kill -/

/-- One ORDERED same-hart step: any of the six cat arms (rules 1, 2, 3, 4, 5, 7-RCsc), a
dependency, or rule 12 over `ad`.  (Today's `segPin` is the one-step case restricted to
rules 4, 5 and deps.) -/
def pinStep (GD : Gdexec) (ad : List (Geid × Geid)) (x y : Geid) : Prop :=
  gppoCat6 GD.gdG x y ∨ (x, y) ∈ GD.gdDeps ∨ gppo12 GD.gdG ad x y

theorem pinStepGmo (GD : Gdexec) (ad : List (Geid × Geid)) (x y : Geid) :
    rvwmoCatAD GD ad → pinStep GD ad x y → gmoLt GD.gdG x y := by
  rintro ⟨-, h6, -, -, -, hdg, -, h12⟩ (h | h | h)
  · exact h6 _ _ h
  · exact hdg _ h
  · exact h12 _ _ h

/-- Today's one-step `segPin` arms are `pinStep`s. -/
theorem pinStepOfSegPinArm (GD : Gdexec) (ad : List (Geid × Geid)) (x y : Geid) :
    gacqPo GD.gdG x y ∨ gfenceCovers GD.gdG x y ∨ (x, y) ∈ GD.gdDeps → pinStep GD ad x y := by
  rintro (h | h | h)
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inl h)

def segPinC (GD : Gdexec) (ad : List (Geid × Geid)) (s : Seg) : Prop :=
  tc (pinStep GD ad) s.sgEntry s.sgExit

theorem segPinCGmo (GD : Gdexec) (ad : List (Geid × Geid)) (s : Seg) :
    rvwmoCatAD GD ad → segPinC GD ad s → gmoLt GD.gdG s.sgEntry s.sgExit := by
  intro hc h
  have key : ∀ x y, tc (pinStep GD ad) x y → gmoLt GD.gdG x y := by
    intro x y h
    induction h with
    | single h => exact pinStepGmo GD ad _ _ hc h
    | tail _ h ih => exact gmoLtTrans _ _ _ _ ih (pinStepGmo GD ad _ _ hc h)
  exact key _ _ h

/-- The rfi case the old split could not see: a dep-pinned entry, its dependent store
forwarded to a same-hart read, that read pinned to the exit — RULE 12 closes it. -/
theorem segPinCForward (GD : Gdexec) (ad : List (Geid × Geid)) (e m r x : Geid) :
    e.1 = r.1 → (e, m) ∈ ad → WeakRvwmoAcyc.grf GD.gdG m r →
    tc (pinStep GD ad) r x → segPinC GD ad ⟨e.1, e, x⟩ := by
  intro hag hd hrf hrx
  exact tc_l (Or.inr (Or.inr ⟨hag, m, hd, hrf⟩)) hrx

inductive CertC (G : Gexec) (prev : Geid) (s : Seg) : Prop where
  | Pinned : gcrossE G prev s.sgEntry → gmoLt G s.sgEntry s.sgExit → CertC G prev s
  | CSchained : gmoLt G prev s.sgExit → CertC G prev s
  | Bad : False → CertC G prev s

theorem certCGmo (G : Gexec) (prev : Geid) (s : Seg) :
    gwf G → gloadValue G → CertC G prev s → gmoLt G prev s.sgExit := by
  intro hwf hlv hc
  cases hc with
  | Pinned hx hp => exact gmoLtTrans G _ _ _ (gcrossEGmo G _ _ hwf hlv hx) hp
  | CSchained hcs => exact hcs
  | Bad h => exact h.elim

def chainC (G : Gexec) (x y : Geid) : List Seg → Prop
  | [] => x = y
  | s :: ss => CertC G x s ∧ chainC G s.sgExit y ss

theorem chainCGmo (G : Gexec) (x y : Geid) (ss : List Seg) :
    gwf G → gloadValue G → ss ≠ [] → chainC G x y ss → gmoLt G x y := by
  intro hwf hlv
  induction ss generalizing x with
  | nil => intro hne; exact absurd rfl hne
  | cons s ss ih =>
    intro _ hch
    obtain ⟨hc, hch⟩ := hch
    cases ss with
    | nil =>
      have h' : s.sgExit = y := hch
      rw [← h']
      exact certCGmo G x s hwf hlv hc
    | cons s' ss' =>
      exact gmoLtTrans G x s.sgExit y (certCGmo G x s hwf hlv hc) (ih s.sgExit (by simp) hch)

/-- THE COMPOSITION KILL over cat: needs `gwf` and load value only. -/
theorem cycleKillArmsC (G : Gexec) (x : Geid) (ss : List Seg) :
    gwf G → gloadValue G → ss ≠ [] → chainC G x x ss → False :=
  fun hwf hlv hne hch => gmoLtIrrefl G x (chainCGmo G x x ss hwf hlv hne hch)

/-! # 3. GATE 2: the lock kit and `csChained` over `rvwmoCatAD` -/

theorem acqGmoAfterC (G : Gexec) (a x : Geid) :
    gppoCat6Gmo G → WeakRvwmoGraph.gpo G a x → glblIs G a lbIsR → glblIs G a lbAq →
    gmem G x → gmoLt G a x :=
  fun h6 hpo hr haq hm => h6 a x (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hpo, hr, haq, hm⟩)))))

theorem fenceGmoAfterC (G : Gexec) (x y : Geid) :
    gppoCat6Gmo G → gfenceCovers G x y → gmoLt G x y :=
  fun h6 hf => h6 x y (Or.inr (Or.inr (Or.inr (Or.inl hf))))

theorem acqSrcC (G : Gexec) (b : Int) (A : Geid) (t : Nat) :
    gatomicity G → lockAcq G b A →
    greadsByte G A b t lockFree →
    ∀ w' v', gwritesByte G w' b v' → gwix G w' ≤ t ∨ gwix G A ≤ gwix G w' := by
  rintro hat ⟨v, hwb, _⟩ hrd w' v' hw'
  have hna := hat A b t lockFree hrd (gwritesByteGlblW _ _ _ _ hwb) w' v' hw'
  omega

/-- `acqTsLt` over cat: its one ppo use is W→W same byte = RULE 1. -/
theorem acqTsLtC (G : Gexec) (b : Int) (A : Geid) (t : Nat) :
    gwf G → gppoCat6Gmo G → gloadValue G → lockAcq G b A →
    greadsByte G A b t lockFree → t < gwix G A := by
  intro hwf h6 hlv hacq hrd
  have hnd := hwf.1
  have hA := lockAcqGwrites G b A hwf hacq
  cases t with
  | zero => exact WeakRvwmoGraph.gwixPos G A hA
  | succ t =>
    obtain ⟨⟨r, hat, hrb, hvis⟩, _⟩ := hlv A b (t + 1) lockFree hrd
    obtain ⟨hr, hrix⟩ := gwriteAtInv G (t + 1) r hnd hat
    rw [← hrix]
    apply gmoGwixLt G r A hwf hr hA
    rcases hvis with hmo | hpo
    · exact hmo
    · obtain ⟨v, hwb, _⟩ := hacq
      exact h6 r A (Or.inl ⟨hpo, b, Or.inl ⟨lockFree, hrb⟩, v, hwb⟩)

theorem acqSrcRelC (G : Gexec) (b : Int) (A : Geid) (t : Nat) :
    gwf G → gloadValue G → greadsByte G A b t lockFree → 0 < t →
    ∃ r, lockRel G b r ∧ r ∈ gwrites G ∧ gwix G r = t := by
  intro hwf hlv hrd hpos
  have hnd := hwf.1
  cases t with
  | zero => omega
  | succ t =>
    obtain ⟨⟨r, hat, hrb, _⟩, _⟩ := hlv A b (t + 1) lockFree hrd
    obtain ⟨hr, hrix⟩ := gwriteAtInv G (t + 1) r hnd hat
    exact ⟨r, hrb, hr, hrix⟩

/-- `acqFoldFree`, verbatim but for the hypothesis. -/
theorem acqFoldFreeC (G : Gexec) (log : List Wmsg) (b : Int) (n0 : Nat) (h : Option Nat)
    (ACQ : Geid) :
    gwf G → gppoCat6Gmo G → gloadValue G → gatomicity G →
    logOf G log → lockWordByte log b →
    wlpAlt log b n0 h → acqRow G b ACQ → lockAcq G b ACQ →
    gwix G ACQ ≤ log.length →
    wlpHolderAt log b n0 (gwix G ACQ - 1) = some none := by
  intro hwf h6 hlv hatm hlog hlwb halt hrow hacq hle
  have hAw := lockAcqGwrites G b ACQ hwf hacq
  have hpos := WeakRvwmoGraph.gwixPos G ACQ hAw
  obtain ⟨t, hrd⟩ := hrow
  have htlt := acqTsLtC G b ACQ t hwf h6 hlv hacq hrd
  have hquiet : ∀ r mr, (t ≤ r ∧ r < gwix G ACQ - 1) → log[r]? = some mr →
      msgByte mr b = none := by
    intro r mr hr hmr
    cases hb : msgByte mr b with
    | none => rfl
    | some v =>
      exfalso
      obtain ⟨w', -, hm', hix', -⟩ := logOfLookup G log r mr hwf hlog hmr
      have hwb := (WeakRvwmoKillArms.gmsgByte G w' mr b v hm').1 hb
      rcases acqSrcC G b ACQ t hatm hacq hrd w' v hwb with hlo | hhi <;> omega
  rw [wlpHolderQuiet log b n0 t (gwix G ACQ - 1) (by omega) hquiet]
  by_cases hn0 : t ≤ n0
  · exact wlpHolderSmall log b n0 t hn0
  obtain ⟨R, hR, hRw, hRix⟩ := acqSrcRelC G b ACQ t hwf hlv hrd (by omega)
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

/-- `csChained` over cat: rules 4 and 5, and the cross edge into the entry (cross-hart, so
`gcrossE`). -/
theorem csChainedC (GD : Gdexec) (ad : List (Geid × Geid)) (log : List Wmsg) (b a : Int)
    (n0 r0 : Nat) (h : Option Nat) (w entry exit ACQ REL : Geid) :
    rvwmoCatAD GD ad →
    logOf GD.gdG log → lockWordByte log b → wlpAlt log b n0 h →
    acqRow GD.gdG b ACQ →
    wprotAt log a b n0 r0 →
    (∃ v, gwritesByte GD.gdG w a v) → gcls GD.gdG w .WCplain →
    r0 < gwix GD.gdG w → gwix GD.gdG w ≤ log.length →
    (∀ v, ¬ gwritesByte GD.gdG w b v) →
    lockAcq GD.gdG b ACQ → glblIs GD.gdG ACQ lbAq →
    n0 < gwix GD.gdG ACQ → gwix GD.gdG ACQ ≤ log.length →
    lockCs GD.gdG b ACQ REL → WeakRvwmoGraph.gpo GD.gdG ACQ entry →
    gfenceCovers GD.gdG entry REL →
    gcrossE GD.gdG w entry → WeakRvwmoGraph.gpo GD.gdG ACQ exit → gmem GD.gdG exit →
    ACQ.1 ≠ w.1 →
    gmoLt GD.gdG w exit := by
  intro hcons hlog hlwb halt hrow hpr hwa hcl hr0 hlew hnob hacq haq hn0A hleA hcs _hpoe hfen
    hcross hpox hmx hhart
  obtain ⟨hwf, h6, hlv, hatm, -, -, -, -⟩ := hcons
  generalize GD.gdG = G at *
  have hnd := hwf.1
  have hAw := lockAcqGwrites G b ACQ hwf hacq
  have hposA := WeakRvwmoGraph.gwixPos G ACQ hAw
  have hw : w ∈ gwrites G := by
    obtain ⟨v, hv⟩ := hwa
    exact gwritesByteGwrites G w a v hwf hv
  have hposw := WeakRvwmoGraph.gwixPos G w hw
  obtain ⟨q, mq, hq, hlk, hs, hnz, ht, hfree, hno, -⟩ :=
    holderAcqGraph G log b a n0 r0 w hwf hlog hlwb hpr hw hr0 hlew hwa hcl
  have hfreeA := acqFoldFreeC G log b n0 h ACQ hwf h6 hlv hatm hlog hlwb halt hrow hacq hleA
  have hrA := acqRowIsR G b ACQ hrow
  have hmoAx : gmoLt G ACQ exit := acqGmoAfterC G ACQ exit h6 hpox hrA haq hmx
  obtain ⟨mw, hmw, hgw⟩ := logOfWrite G log w hwf hlog hw hlew
  by_cases heq : q = gwix G ACQ - 1
  · exfalso
    subst heq
    obtain ⟨A', -, hm', hix', hw'⟩ := logOfLookup G log (gwix G ACQ - 1) mq hwf hlog hlk
    have hA : A' = ACQ := gwixInj G A' ACQ hnd hw' hAw (by omega)
    rw [hA] at hm'
    apply hhart
    have htA := gmsgTid G ACQ mq hm'
    rw [ht, Option.some.injEq] at htA
    exact htA.symm
  by_cases hlt : q < gwix G ACQ - 1
  · obtain ⟨r, R, mr, hr, hlkr, hsr, hzr, -, -, -, -, -⟩ :=
      releaseBetweenGraph G log b n0 q (gwix G ACQ - 1) mq w.1 hwf hlog hq.1 hlt hlk hs hnz ht
        hfree hfreeA
    have hrp : gwix G w - 1 ≤ r := by
      by_cases hc : r < gwix G w - 1
      · exact absurd hzr (hno r mr ⟨hr.1, hc⟩ hlkr hsr)
      · omega
    have hrne : r ≠ gwix G w - 1 := by
      intro hre
      rw [hre, hmw, Option.some.injEq] at hlkr
      subst hlkr
      rw [gmsgByteNone G w mw b hgw hnob] at hsr
      simp at hsr
    exact gmoLtTrans G w ACQ exit (gwixLtGmo G w ACQ hwf hw hAw (by omega)) hmoAx
  · have hltA : gwix G ACQ - 1 < q := by omega
    obtain ⟨mA, hmA, hgA⟩ := logOfWrite G log ACQ hwf hlog hAw hleA
    obtain ⟨va, hva, hvane⟩ := id hacq
    have hbA := (WeakRvwmoKillArms.gmsgByte G ACQ mA b va hgA).2 hva
    have hnzA : mA.wmData ≠ wlockZero4 := fun hz => hvane (zero4Byte mA b va hz hbA)
    have htA := gmsgTid G ACQ mA hgA
    obtain ⟨r', R', mr', hr', -, -, -, -, hrelr', hixr', -, hhr'⟩ :=
      releaseBetweenGraph G log b n0 (gwix G ACQ - 1) q mA ACQ.1 hwf hlog (by omega) hltA hmA
        (by rw [hbA]; rfl) hnzA htA hfreeA hfree
    obtain ⟨-, hRel, -, -, hnoin⟩ := hcs
    have hRle : gwix G REL ≤ gwix G R' := by
      by_cases hc : gwix G R' < gwix G REL
      · exact absurd ⟨by omega, hc⟩ (hnoin R' lockFree hrelr' hhr')
      · omega
    have hmoRw : gmoLt G REL w :=
      gwixLtGmo G REL w hwf (lockRelGwrites G b REL hwf hRel) hw (by omega)
    have hmoWe := gcrossEGmo G w entry hwf hlv hcross
    have hmoeR := fenceGmoAfterC G entry REL h6 hfen
    exact absurd (gmoLtTrans G w entry w hmoWe (gmoLtTrans G entry REL w hmoeR hmoRw))
      (gmoLtIrrefl G w)

end CatOfMinusSpike

end Weak
