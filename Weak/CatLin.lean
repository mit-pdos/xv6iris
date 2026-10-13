/-
Weak: **W12 (1)–(2) — the kill over RVWMO as riscv.cat states it** (plan
`notes/weak-allocproc-plan.md` §C W12; D25 RULED (a) [OWN.5]; D33 (a) [OWN.13]).

Lean-only, no Rocq twin.  The spike's kit (`Weak/CatOfMinusSpike.lean`, merged [OWN.10]; report
`notes/W12-spike.md`) made part of the chain, in `namespace CatLin` (file-qualified: `CertC`
and `chainC` would clash with the AxSpin tier's names).

  §0  `rvwmoCatAD GD ad`: the chain's hypothesis — the cat model's six arms, load value,
      atomicity, the dependency fragment, and RULE 12 over an addr/data SUBLIST `ad ⊆ gdDeps`.
      Entries: `catADOfCatT` (the TAGGED model `AxDeps.rvwmoCatConsistentT` on `forget GT`,
      `ad := gtAd` — THE PUBLISHED QUANTIFIER, D33 (a)), `catADOfCat`, `catADOfMinus`;
      `catADCore`: it carries `WeakRvwmoAcyc.rvwmoCoreD` (the restated topo/normalize/hull kit).
  §1  GATE 1: same-hart rf (rfi) is po-forward under cat (rule 1 alone), so rfi moves into the
      same-hart arm `rsameC`; `gcrossE` = rfe ∪ co ∪ fr is gmo-forward from `gwf` + load value.
  §2  The pinned segment as a same-hart CHAIN of ordered steps (`pinStep`: the six cat arms,
      deps, rule 12 over `ad`; `segPinCForward` is why `ad` must be TAGGED), and the kill —
      `CertC`/`chainC`/`cycleKillArmsX` PARAMETERIZED BY THE CROSS ORDER `X` (any `X ⊆ gmo`;
      `cycleKillArmsC` at `X := gcrossE`), so W13 (K)'s I/O arms instantiate it unchanged.
  §3  GATE 2: the lock kit and `csChainedC` (its cross edge taken as `gmoLt w entry`).
  §4  Glue §1 re-instantiated: `segRunC`, `rawChainC`, `crunC`, `decomposeC` /
      `cycleSegmentsX` (any relation splitting into `rsameC ∪ X`), `cycleSegmentsC` (`racyD`,
      `X := gcrossE`), `segPinCCert`.

**Deviations from the spike.**  (1) `CertC`/`chainC`/the kill and the raw chain take the cross
order `X` as a parameter (plan: "parameterize the cross order").  (2) `csChainedC` takes
`gmoLt w entry` in place of `gcrossE w entry` (strictly more general).  (3) `catADCore` and §4
are new.  Everything else is the spike's text, re-namespaced.

**Spec notes (RVWMO / riscv.cat).**  `rvwmoCatAD` is implied by the tagged model; it is
WEAKER than RVWMO⁻ (`catADOfMinus`) and its forwarding witness is in `CatLinWit`.  It relies on
`AxDeps.gtdepsWf`'s RAM-endpoint shape only through `AxDeps.catTForgetAxioms` (the untagged
`gdepsWf` of `forget GT`) and `gtAdSubForget` (rule 12's domain inside `forgetDeps`).
-/
import Weak.WeakRvwmoKillArms
import Weak.AxDeps

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Lbl

namespace CatLin


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

/-- The cat hypothesis carries the CORE the topo / normalize / hull kit takes. -/
theorem catADCore (GD : Gdexec) (ad : List (Geid × Geid)) :
    rvwmoCatAD GD ad → rvwmoCoreD GD :=
  fun ⟨hwf, _, hlv, hat, hdw, _⟩ => ⟨hwf, hlv, hat, hdw⟩

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

/-- THE CERTIFICATE, parameterized by the CROSS ORDER `X` (plan §C W12: the cat arms are
written once; `X := gcrossE` today, W13 (K)'s I/O-extended cross order later). -/
inductive CertC (G : Gexec) (X : Geid → Geid → Prop) (prev : Geid) (s : Seg) : Prop where
  | Pinned : X prev s.sgEntry → gmoLt G s.sgEntry s.sgExit → CertC G X prev s
  | CSchained : gmoLt G prev s.sgExit → CertC G X prev s
  | Bad : False → CertC G X prev s

theorem certCGmo (G : Gexec) (X : Geid → Geid → Prop) (prev : Geid) (s : Seg) :
    (∀ x y, X x y → gmoLt G x y) → CertC G X prev s → gmoLt G prev s.sgExit := by
  intro hX hc
  cases hc with
  | Pinned hx hp => exact gmoLtTrans G _ _ _ (hX _ _ hx) hp
  | CSchained hcs => exact hcs
  | Bad h => exact h.elim

def chainC (G : Gexec) (X : Geid → Geid → Prop) (x y : Geid) : List Seg → Prop
  | [] => x = y
  | s :: ss => CertC G X x s ∧ chainC G X s.sgExit y ss

theorem chainCGmo (G : Gexec) (X : Geid → Geid → Prop) (x y : Geid) (ss : List Seg) :
    (∀ x y, X x y → gmoLt G x y) → ss ≠ [] → chainC G X x y ss → gmoLt G x y := by
  intro hX
  induction ss generalizing x with
  | nil => intro hne; exact absurd rfl hne
  | cons s ss ih =>
    intro _ hch
    obtain ⟨hc, hch⟩ := hch
    cases ss with
    | nil =>
      have h' : s.sgExit = y := hch
      rw [← h']
      exact certCGmo G X x s hX hc
    | cons s' ss' =>
      exact gmoLtTrans G x s.sgExit y (certCGmo G X x s hX hc) (ih s.sgExit (by simp) hch)

/-- THE COMPOSITION KILL, for any gmo-forward cross order. -/
theorem cycleKillArmsX (G : Gexec) (X : Geid → Geid → Prop) (x : Geid) (ss : List Seg) :
    (∀ x y, X x y → gmoLt G x y) → ss ≠ [] → chainC G X x x ss → False :=
  fun hX hne hch => gmoLtIrrefl G x (chainCGmo G X x x ss hX hne hch)

/-- THE COMPOSITION KILL over cat (`X := gcrossE`): needs `gwf` and load value only. -/
theorem cycleKillArmsC (G : Gexec) (x : Geid) (ss : List Seg) :
    gwf G → gloadValue G → ss ≠ [] → chainC G (gcrossE G) x x ss → False :=
  fun hwf hlv => cycleKillArmsX G (gcrossE G) x ss (fun a b => gcrossEGmo G a b hwf hlv)

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

/-- `csChained` over cat: rules 4 and 5, and the cross edge into the entry — taken as its
gmo-consequence `gmoLt w entry`, so any cross order with `X ⊆ gmo` feeds it (for `gcrossE` by
`gcrossEGmo`). -/
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
    gmoLt GD.gdG w entry → WeakRvwmoGraph.gpo GD.gdG ACQ exit → gmem GD.gdG exit →
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
    have hmoWe := hcross
    have hmoeR := fenceGmoAfterC G entry REL h6 hfen
    exact absurd (gmoLtTrans G w entry w hmoWe (gmoLtTrans G entry REL w hmoeR hmoRw))
      (gmoLtIrrefl G w)


/-! # 4. THE SEGMENT DECOMPOSITION over cat (Glue §1 re-instantiated at `rsameC` / a cross order) -/

/-- A segment's run: its entry reaches its exit by same-hart arms (rfi INCLUDED). -/
def segRunC (GD : Gdexec) (s : Seg) : Prop :=
  rtc (rsameC GD) s.sgEntry s.sgExit

/-- THE RAW CHAIN over cat: an `X`-edge into each entry, and an `rsameC` run to its exit. -/
def rawChainC (GD : Gdexec) (X : Geid → Geid → Prop) (x y : Geid) : List Seg → Prop
  | [] => x = y
  | s :: ss => X x s.sgEntry ∧ segRunC GD s ∧ rawChainC GD X s.sgExit y ss

def crunC (GD : Gdexec) (X : Geid → Geid → Prop) (u v : Geid) : Prop :=
  ∃ e, X u e ∧ rtc (rsameC GD) e v

theorem rawChainCSnoc (GD : Gdexec) (X : Geid → Geid → Prop) (x u e b : Geid) (ss : List Seg) :
    rawChainC GD X x u ss → X u e → rtc (rsameC GD) e b →
    rawChainC GD X x b (ss ++ [⟨e.1, e, b⟩]) := by
  induction ss generalizing x with
  | nil =>
    intro h hx hr
    have h' : x = u := h
    subst h'
    show X x e ∧ segRunC GD ⟨e.1, e, b⟩ ∧ rawChainC GD X b b []
    exact ⟨hx, hr, rfl⟩
  | cons s ss ih =>
    intro h hx hr
    obtain ⟨h1, h2, h3⟩ := h
    show X x s.sgEntry ∧ segRunC GD s ∧ rawChainC GD X s.sgExit b (ss ++ [⟨e.1, e, b⟩])
    exact ⟨h1, h2, ih _ h3 hx hr⟩

theorem crunCRawChain (GD : Gdexec) (X : Geid → Geid → Prop) (a b : Geid) :
    tc (crunC GD X) a b → ∃ ss, ss ≠ [] ∧ rawChainC GD X a b ss := by
  intro h
  induction h with
  | single h =>
    obtain ⟨e, hx, hr⟩ := h
    exact ⟨[] ++ [⟨e.1, e, _⟩], by simp,
      rawChainCSnoc GD X _ _ e _ [] (show rawChainC GD X a a [] from rfl) hx hr⟩
  | tail _ h ih =>
    obtain ⟨ss, -, hch⟩ := ih
    obtain ⟨e, hx, hr⟩ := h
    exact ⟨ss ++ [⟨e.1, e, _⟩], by simp, rawChainCSnoc GD X _ _ e _ ss hch hx hr⟩

theorem crunCAppend (GD : Gdexec) (X : Geid → Geid → Prop) (a b c : Geid) :
    tc (crunC GD X) a b → rtc (rsameC GD) b c → tc (crunC GD X) a c := by
  intro h hbc
  cases h with
  | single h =>
    obtain ⟨e, hx, hr⟩ := h
    exact tc_once ⟨e, hx, rtc_transitive hr hbc⟩
  | tail h1 h2 =>
    obtain ⟨e, hx, hr⟩ := h2
    exact tc_r h1 ⟨e, hx, rtc_transitive hr hbc⟩

/-- THE DECOMPOSITION, for any relation that splits into `rsameC` and a cross order `X`. -/
theorem decomposeC (GD : Gdexec) (R X : Geid → Geid → Prop)
    (hsplit : ∀ x y, R x y → rsameC GD x y ∨ X x y) (a b : Geid) :
    tc R a b →
    tc (rsameC GD) a b ∨ ∃ y, rtc (rsameC GD) a y ∧ tc (crunC GD X) y b := by
  intro h
  induction h with
  | single h =>
    rcases hsplit _ _ h with hs | hx
    · exact .inl (tc_once hs)
    · exact .inr ⟨a, rtc_refl _, tc_once ⟨_, hx, rtc_refl _⟩⟩
  | tail _ h ih =>
    rcases hsplit _ _ h with hs | hx
    · rcases ih with ih | ⟨y, hry, hty⟩
      · exact .inl (tc_r ih hs)
      · exact .inr ⟨y, hry, crunCAppend GD X _ _ _ hty (rtc_once hs)⟩
    · rcases ih with ih | ⟨y, hry, hty⟩
      · exact .inr ⟨_, tc_rtc ih, tc_once ⟨_, hx, rtc_refl _⟩⟩
      · exact .inr ⟨y, hry, tc_r hty ⟨_, hx, rtc_refl _⟩⟩

/-- A cycle of any `rsameC ∪ X`-split relation is a nonempty raw chain (cat: `rsameC` is
acyclic by rule 1). -/
theorem cycleSegmentsX (GD : Gdexec) (ad : List (Geid × Geid)) (R X : Geid → Geid → Prop)
    (hsplit : ∀ x y, R x y → rsameC GD x y ∨ X x y) (x : Geid) :
    rvwmoCatAD GD ad → tc R x x → ∃ z ss, ss ≠ [] ∧ rawChainC GD X z z ss := by
  intro hc hcyc
  rcases decomposeC GD R X hsplit x x hcyc with hbad | ⟨y, hry, hty⟩
  · exact absurd hbad (rsameCAcyclic GD ad x hc)
  · exact ⟨y, crunCRawChain GD X y y (crunCAppend GD X _ _ _ hty hry)⟩

/-- THE THEOREM over cat: an `racyD` cycle is a nonempty raw chain with `gcrossE` entries. -/
theorem cycleSegmentsC (GD : Gdexec) (ad : List (Geid × Geid)) (x : Geid) :
    rvwmoCatAD GD ad → tc (racyD GD) x x →
    ∃ z ss, ss ≠ [] ∧ rawChainC GD (gcrossE GD.gdG) z z ss :=
  cycleSegmentsX GD ad (racyD GD) (gcrossE GD.gdG) (racyDSplitC GD) x

/-- A pinned segment, with the cross edge its raw chain carries, IS a `Pinned` certificate. -/
theorem segPinCCert (GD : Gdexec) (ad : List (Geid × Geid)) (X : Geid → Geid → Prop)
    (prev : Geid) (s : Seg) :
    rvwmoCatAD GD ad → X prev s.sgEntry → segPinC GD ad s → CertC GD.gdG X prev s :=
  fun hc hx hp => .Pinned hx (segPinCGmo GD ad s hc hp)

/-! ## 4.1 Non-vacuity helpers: the raw chain is an `racyD` path -/

theorem rsameCRacyD (GD : Gdexec) (x y : Geid) : rsameC GD x y → racyD GD x y := by
  rintro (h | h | h | ⟨h, -⟩)
  · exact .inl (.inl h)
  · exact .inl (.inr (.inr (.inr (.inr h))))
  · exact .inr h
  · exact .inl (.inr (.inl h))

theorem gcrossERacyD (GD : Gdexec) (x y : Geid) : gcrossE GD.gdG x y → racyD GD x y := by
  rintro (⟨h, -⟩ | h | h)
  · exact .inl (.inr (.inl h))
  · exact .inl (.inr (.inr (.inl h)))
  · exact .inl (.inr (.inr (.inr (.inl h))))

end CatLin

end Weak
