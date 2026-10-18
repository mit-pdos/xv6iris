/-
Weak: **row 6l (W11-F), the OPTION-INDEPENDENT parts — the WINDOWED lock co at the complete member and
the windowed kill chain** (`PROGRESS-W10N2p.md`, row 6l "What DOES go through").  Lean-only, no Rocq twin.

The incremental gated order ([OWN.106]: built step by step, no order premise) never maintains a running
`coPrefix`; the lock co the transport needs follows, INSIDE each registration window, at the COMPLETE
member from three facts:
  (a) the RECORD of every successful window AMO (`SilOrd2.amoRecB`): its `GF` source at the byte is the
      member-latest write of the byte at append time (`srcEq` of the two read timestamps);
  (b) the ALTERNATION at the complete member (`wlpAlt`, from the export's `protReg`);
  (c) RVWMO: CoWW (rule 1, `[M];po-loc;[W]`) and atomicity / load value (`acqTsLtC`: rf ⇒ co at an AMO).
The window's writes A₁ R₁ A₂ R₂ … are then a `GF`-co chain in member order (`SilOrd2.coStep`).

  §1  `SilOrd2.srcEq`, **`SilOrd2.amoRecB`** / `amoRecLog` (the record), **`SilOrd2.lockCoW`** /
      `lockCoLog` (the windowed lock co, member order ⇒ `GF` co), `SilOrd2.agreeW4N` (CertZ24's
      `agreeW4` without lock co) and `agreeW4NOf` / **`agreeW4NOfS`**;
  §2  `SilOrd2.lastW`, `SilOrd2.latestLast`, `SilOrd2.srcVal`, **`SilOrd2.coStep`**,
      **`SilOrd2.lockCoWOf`** (the windowed lock co from (a)–(c));
  §3  the kill chain restated: **`CatLin.SilOrd2.csChainedT4W`** (no `regZeroAt`, no sp/np facts: the
      reader-first arm closes `REL <co ACQw` through `R′` in `GF`), `csHypsCertCR4W`,
      `rawChainChainW4W`;
  §4  `SilOrd2.agreeRRS` (img + silent label agreement + record), the named premises at it
      (`certSupplyRS`, `acqAqRS`, `relCoversRS`, `l2ClaimRS`), **`CatLin.SilOrd2.cycleKillCoreW`**
      (⇒ `cycleKillCZT`).

Spec: FAITHFUL (proof organisation; (c) is riscv.cat rule 1 + load value + atomicity, nothing stronger).
-/
import Weak.SilKillT
import Weak.SilSite

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open TsoShadow

/-! # 1. The record, the windowed lock co, the agreement without co -/

/-- The source of a read at `t` in `G` and at `t'` in `GR` is the same: both the image, or the same
write event. -/
def SilOrd2.srcEq (G GR : Gexec) (t t' : Nat) : Prop :=
  (t = 0 ∧ t' = 0) ∨ ∃ s, gwriteAt G t = some s ∧ gwriteAt GR t' = some s

/-- **THE RECORD OF THE GATE (successful window acquires)**: an acquire of `b` in the member's
registration window that reads `b` FREE in `G` reads it from the write that was the member-latest one
of `b` when its message was appended (the log prefix before it). -/
def SilOrd2.amoRecB (G GR : Gexec) (log : List Wmsg) (b : Int) (n0 : Nat) : Prop :=
  ∀ A t, lockAcq GR b A → CatLin.GraphFetchN2.inWin GR log n0 A → greadsByte G A b t lockFree →
    ∃ t', latest GR.gxImg (log.take (gwix GR A - 1)) b t' ∧ SilOrd2.srcEq G GR t t'

/-- The record at every registered byte of `P`, at its registration point in `log`. -/
def SilOrd2.amoRecLog (G GR : Gexec) (log : List Wmsg) (P : Int → Int → Prop) : Prop :=
  ∀ a b n0 r0 h, P a b → wprotAt log a b n0 r0 → wlpAt log b b n0 → wlpAlt log b n0 h →
    SilOrd2.amoRecB G GR log b n0

/-- **THE WINDOWED LOCK CO**: two member writes of `b` inside the registration window (and the log)
are `GF`-co-ordered as in the member. -/
def SilOrd2.lockCoW (G GR : Gexec) (log : List Wmsg) (b : Int) (n0 : Nat) : Prop :=
  ∀ x y vx vy, gwritesByte GR x b vx → gwritesByte GR y b vy →
    n0 < gwix GR x → n0 < gwix GR y → gwix GR y ≤ log.length →
    gwix GR x < gwix GR y → gwix G x < gwix G y

/-- The windowed lock co at every registered byte of `P` witnessing its word. -/
def SilOrd2.lockCoLog (G GR : Gexec) (log : List Wmsg) (P : Int → Int → Prop) : Prop :=
  ∀ a b n0 r0 h, P a b → wprotAt log a b n0 r0 → wlpAt log b b n0 → wlpAlt log b n0 h →
    lockWordByte log b → SilOrd2.lockCoW G GR log b n0

/-- CertZ24's `agreeW4` WITHOUT its lock co conjunct. -/
def SilOrd2.agreeW4N (G GR : Gexec) (L : Int → Prop) : Prop :=
  GR.gxImg = G.gxImg ∧
  (∀ e a v, gwritesByte GR e a v → gwritesByte G e a v) ∧
  (∀ e a v, gwritesByte GR e a v → CertZ24.nf G L e) ∧
  (∀ e a v, CertZ24.nf G L e → gwritesByte G e a v → gwritesByte GR e a v) ∧
  (∀ e k, CertZ24.nf G L e → gcls G e k → glblIs G e lbIsW → gcls GR e k) ∧
  CertZ24.rdAgree4 G GR L

theorem SilOrd2.agreeW4NOf (G GR : Gexec) (L : Int → Prop) :
    CertZ24.agreeW4 G GR L → SilOrd2.agreeW4N G GR L :=
  fun ⟨h1, h2, h3, h4, h5, h6, _⟩ => ⟨h1, h2, h3, h4, h5, h6⟩

/-- The silent label agreement (no lock co) gives `agreeW4N` (`SilAgree.agreeW4OfRPS` minus co). -/
theorem SilOrd2.agreeW4NOfS (G GR : Gexec) (pi : Nat → Nat) (L : Int → Prop) :
    GR.gxImg = G.gxImg → SilAgree.lblAgreeS G GR pi L → SilOrd2.agreeW4N G GR L := by
  intro himg hlbl
  have hwrR : ∀ e l', gxLbl GR e = some l' → lbIsW l' = true →
      ∃ l, gxLbl G e = some l ∧ ¬ CertZ24.lblFail L l ∧ lblReidxW (lblRen pi l) l' := by
    intro e l' hl' hW
    rcases hlbl e with ⟨-, h2⟩ | ⟨l, l'', h1, h2, hrel⟩
    · rw [h2] at hl'; cases hl'
    · rw [hl', Option.some.injEq] at h2
      subst h2
      rcases hrel with ⟨hnf, hre⟩ | ⟨-, _, _, _, _, _, _, _, _, -, rfl, -⟩
      · exact ⟨l, h1, hnf, hre⟩
      · simp [lbIsW] at hW
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
  refine ⟨himg, ?_, ?_, ?_, ?_, ⟨?_, ?_⟩⟩
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

/-! # 2. The windowed lock co from the record, the alternation and RVWMO -/

/-- A READING writer of `a` reads `a` (a fused RMW's read footprint covers its write footprint). -/
theorem SilOrd2.readOfWrite (G : Gexec) (e : Geid) (a : Int) (v : BitVec 8) :
    gwf G → glblIs G e lbIsR → gwritesByte G e a v → ∃ t v', greadsByte G e a t v' := by
  rintro hwf ⟨l0, hl0, hR⟩ ⟨l, base, vs, j, hl, hwr, hv, ha⟩
  rw [hl, Option.some.injEq] at hl0
  subst hl0
  have hsh := gwfLblShape G e l hwf hl
  cases l with
  | LLoad => simp [lbWr] at hwr
  | LStore => simp [lbIsR] at hR
  | LFence => simp [lbWr] at hwr
  | LIo => simp [lbWr] at hwr
  | LRmw aq rl b0 ts rvs wvs k =>
    have hsh' : wvs ≠ [] ∧ wvs.length = ts.length ∧ rvs.length = ts.length := hsh
    simp only [lbWr, Option.some.injEq, Prod.mk.injEq] at hwr
    obtain ⟨rfl, rfl⟩ := hwr
    have hj : j < ts.length := by rw [← hsh'.2.1]; exact lookup_lt_Some hv
    have hj' : j < rvs.length := by rw [hsh'.2.2]; exact hj
    exact ⟨ts[j], rvs[j], _, b0, ts, rvs, j, hl, rfl, List.getElem?_eq_getElem hj,
      List.getElem?_eq_getElem hj', ha⟩

/-- The LAST message writing `b` before position `q`, at or after a known one at `p`. -/
theorem SilOrd2.lastW (log : List Wmsg) (b : Int) (p : Nat) :
    ∀ q, p < q → (∃ m, log[p]? = some m ∧ (msgByte m b).isSome) →
    ∃ q' m', p ≤ q' ∧ q' < q ∧ log[q']? = some m' ∧ (msgByte m' b).isSome ∧
      ∀ r mr, q' < r → r < q → log[r]? = some mr → msgByte mr b = none := by
  intro q
  induction q with
  | zero => intro h; omega
  | succ q ih =>
    intro hpq hp
    by_cases hw : ∃ m, log[q]? = some m ∧ (msgByte m b).isSome
    · obtain ⟨m, hm, hs⟩ := hw
      exact ⟨q, m, by omega, by omega, hm, hs, fun r mr h1 h2 _ => absurd h2 (by omega)⟩
    · have hpq' : p < q := by
        rcases Nat.lt_or_ge p q with h | h
        · exact h
        · exfalso
          have : p = q := by omega
          subst this
          exact hw hp
      obtain ⟨q', m', h1, h2, h3, h4, h5⟩ := ih hpq' hp
      refine ⟨q', m', h1, by omega, h3, h4, fun r mr hr1 hr2 hmr => ?_⟩
      by_cases hrq : r = q
      · subst hrq
        cases hb : msgByte mr b with
        | none => rfl
        | some v => exact absurd ⟨mr, hmr, by rw [hb]; rfl⟩ hw
      · exact h5 r mr hr1 (by omega) hmr

/-- The last `b`-message before `q` is the latest of the prefix of length `q`. -/
theorem SilOrd2.latestLast (img : Image) (log : List Wmsg) (b : Int) (q' q : Nat) (m' : Wmsg) :
    q' < q → q ≤ log.length → log[q']? = some m' → (msgByte m' b).isSome →
    (∀ r mr, q' < r → r < q → log[r]? = some mr → msgByte mr b = none) →
    latest img (log.take q) b (q' + 1) := by
  intro hlt hle hm hs hq
  refine ⟨?_, ?_⟩
  · rw [logByteS, lookup_take hlt, hm]
    simpa using hs
  · rintro ⟨t, hlo, hhi, m, hmt, hst⟩
    rw [List.length_take, Nat.min_eq_left hle] at hhi
    rw [lookup_take (by omega)] at hmt
    rw [hq (t - 1) m (by omega) (by omega) hmt] at hst
    cases hst

/-- A `GF` read and a member-latest timestamp with the same source carry the same value. -/
theorem SilOrd2.srcVal (G GR : Gexec) (log : List Wmsg) (A : Geid) (b : Int) (q t t' : Nat)
    (v : BitVec 8) :
    gloadValue G → logOf GR log → GR.gxImg = G.gxImg →
    (∀ e a v, gwritesByte GR e a v → gwritesByte G e a v) → q ≤ log.length →
    greadsByte G A b t v → latest GR.gxImg (log.take q) b t' → SilOrd2.srcEq G GR t t' →
    logByte GR.gxImg (log.take q) t' b = some v := by
  intro hlv hlog himg hRG hq hrd hlat hsrc
  rcases hsrc with ⟨rfl, rfl⟩ | ⟨s, hsG, hsR⟩
  · obtain ⟨h0, -⟩ := hlv A b 0 v hrd
    show GR.gxImg b = some v
    rw [himg]
    exact h0
  · cases t' with
    | zero => simp [gwriteAt] at hsR
    | succ i =>
      have hiq : i + 1 ≤ q := by
        have := logByteBounded _ _ _ _ hlat.1
        rw [List.length_take, Nat.min_eq_left hq] at this
        exact this
      obtain ⟨vb, hvb⟩ := Option.isSome_iff_exists.1 hlat.1
      rw [hvb]
      rw [CertZ18.logByteTake GR.gxImg log q (i + 1) b hiq, logByteS] at hvb
      cases hm : log[i]? with
      | none => rw [hm] at hvb; cases hvb
      | some m =>
        rw [hm] at hvb
        have hvb' : msgByte m b = some vb := by simpa using hvb
        obtain ⟨w, hat, hgm⟩ := (hlog i m).1 hm
        have hsw : s = w := Option.some.inj (hsR.symm.trans hat)
        subst hsw
        have hwG := hRG s b vb ((WeakRvwmoKillArms.gmsgByte GR s m b vb hgm).1 hvb')
        cases t with
        | zero => simp [gwriteAt] at hsG
        | succ j =>
          obtain ⟨⟨w0, hat0, hw0, -⟩, -⟩ := hlv A b (j + 1) v hrd
          have hs0 : s = w0 := Option.some.inj (hsG.symm.trans hat0)
          subst hs0
          rw [gwritesByteDet G s b vb v hwG hw0]

/-- **THE CHAIN STEP**: two CONSECUTIVE member messages of `b` in the window are `GF`-co-ordered —
an acquire through its record (its `GF` source is the previous write, `acqTsLtC`), a release
through the alternation (the previous write is its own hart's acquire, CoWW). -/
theorem SilOrd2.coStep (G GR : Gexec) (L : Int → Prop) (log : List Wmsg) (b : Int) (n0 : Nat)
    (h : Option Nat) (q' q : Nat) (m' m : Wmsg) (w' w : Geid) :
    gwf G → gppoCat6Gmo G → gloadValue G → gwf GR → SilOrd2.agreeW4N G GR L → L b →
    gwrowGmo GR → logOf GR log → lockWordByte log b → wlpAlt log b n0 h →
    CatLin.acqAqB G GR log b n0 → SilOrd2.amoRecB G GR log b n0 →
    n0 ≤ q' → q' < q → q < log.length →
    log[q']? = some m' → (msgByte m' b).isSome → log[q]? = some m → (msgByte m b).isSome →
    (∀ r mr, q' < r → r < q → log[r]? = some mr → msgByte mr b = none) →
    gwriteAt GR (q' + 1) = some w' → gwriteAt GR (q + 1) = some w →
    gwix G w' < gwix G w := by
  intro hwf h6 hlv hwfR hag hL hrowR hlog hlwb halt hAQ hrec hn0 hlt hq hm' hs' hm hs hquiet hat' hat
  obtain ⟨himg, hRG, hRnf, -, -, -⟩ := hag
  obtain ⟨w1, hat1, hg, hix, -⟩ := logOfLookup GR log q m hwfR hlog hm
  have hw1 : w = w1 := Option.some.inj (hat.symm.trans hat1)
  subst hw1
  obtain ⟨w2, hat2, hg', hix', -⟩ := logOfLookup GR log q' m' hwfR hlog hm'
  have hw2 : w' = w2 := Option.some.inj (hat'.symm.trans hat2)
  subst hw2
  obtain ⟨vb, hvb⟩ := Option.isSome_iff_exists.1 hs
  obtain ⟨vb', hvb'⟩ := Option.isSome_iff_exists.1 hs'
  have hwb : gwritesByte GR w b vb := (WeakRvwmoKillArms.gmsgByte GR w m b vb hg).1 hvb
  have hwb' : gwritesByte GR w' b vb' := (WeakRvwmoKillArms.gmsgByte GR w' m' b vb' hg').1 hvb'
  -- a member acquire of `b` reads `b` free in `G` (it is no failed acquire)
  have hfreeRd : ∀ A va t v, gwritesByte GR A b va → va ≠ lockFree → greadsByte G A b t v →
      v = lockFree := by
    intro A va t v hA hne hrd
    by_cases hv : v = lockFree
    · exact hv
    · exact absurd ⟨b, hL, ⟨va, hRG A b va hA, hne⟩, ⟨t, v, hrd, hv⟩⟩ (hRnf A b va hA)
  -- a member acquire of `b` in the window reads `b` free (`acqAqB`: it is a read)
  have hrdOf : ∀ A va, gwritesByte GR A b va → va ≠ lockFree → n0 < gwix GR A →
      gwix GR A ≤ log.length → ∃ t, greadsByte G A b t lockFree := by
    intro A va hA hne h1 h2
    obtain ⟨hR, -⟩ := hAQ A ⟨va, hRG A b va hA, hne⟩ ⟨h1, h2⟩
    obtain ⟨t, v, hrd⟩ := SilOrd2.readOfWrite G A b va hwf hR (hRG A b va hA)
    exact ⟨t, by rw [← hfreeRd A va t v hA hne hrd]; exact hrd⟩
  by_cases hz : vb = lockFree
  · -- a RELEASE at `q`: the fold is held by its author
    have hd : m.wmData = wlockZero4 := hlwb q m vb hm hvb hz
    have htid := gmsgTid GR w m hg
    have htid' := gmsgTid GR w' m' hg'
    obtain ⟨hlen, hf⟩ := halt
    obtain ⟨H1, hH1⟩ := wlpHolderIsSome log b n0 q' log.length h (by omega) hf
    obtain ⟨H2, hH2⟩ := wlpHolderIsSome log b n0 (q' + 1) log.length h (by omega) hf
    obtain ⟨H3, hH3⟩ := wlpHolderIsSome log b n0 (q + 1) log.length h (by omega) hf
    have hstep' := wlpHolderStep log b n0 q' m' hn0 hm'
    have hstep := wlpHolderStep log b n0 q m (by omega) hm
    have hqq : wlpHolderAt log b n0 q = wlpHolderAt log b n0 (q' + 1) :=
      wlpHolderQuiet log b n0 (q' + 1) q (by omega)
        (fun r mr hr hmr => hquiet r mr (by omega) hr.2 hmr)
    rw [hqq, hH2, hH3, (mwritesTrue b m).2 hs] at hstep
    simp only [↓reduceIte] at hstep
    obtain ⟨-, hH2ne, hH2t⟩ := altStepZero H2 m H3 hd hstep.symm
    rw [hH1, hH2, (mwritesTrue b m').2 hs'] at hstep'
    simp only [↓reduceIte] at hstep'
    by_cases hz' : vb' = lockFree
    · have hd' : m'.wmData = wlockZero4 := hlwb q' m' vb' hm' hvb' hz'
      obtain ⟨h0, -, -⟩ := altStepZero H1 m' H2 hd' hstep'.symm
      exact absurd h0 hH2ne
    · have hd' : m'.wmData ≠ wlockZero4 := fun hd0 => hz' (zero4Byte m' b vb' hd0 hvb')
      obtain ⟨t, hrd⟩ := hrdOf w' vb' hwb' hz' (by omega) (by omega)
      obtain ⟨t', hlat, hsrc⟩ := hrec w' t ⟨vb', hwb', hz'⟩ ⟨by omega, by omega⟩ hrd
      rw [hix', Nat.add_sub_cancel] at hlat
      have hval := SilOrd2.srcVal G GR log w' b q' t t' lockFree hlv hlog himg hRG (by omega) hrd
        hlat hsrc
      have hfree := CertZ18.foldFreeOfLatest GR.gxImg log b n0 h q' t' hlwb ⟨hlen, hf⟩ (by omega)
        hlat hval
      rw [hfree, Option.some.injEq] at hH1
      subst hH1
      obtain ⟨-, -, hH2e, -⟩ := altStepNonzero none m' H2 hd' hstep'.symm
      have hH2v := hH2e rfl
      rw [hH2v, htid', htid, Option.some.injEq] at hH2t
      have hne : w' ≠ w := fun he => by subst he; omega
      have hpo : WeakRvwmoGraph.gpo G w' w :=
        CertZ24.poOfRowR4 G GR w' w b b vb' vb hrowR hwb' hwb (hRG w' b vb' hwb') (hRG w b vb hwb)
          hH2t.symm hne (by omega)
      exact gmoGwixLt G w' w hwf (gwritesByteGwrites G w' b vb' hwf (hRG w' b vb' hwb'))
        (gwritesByteGwrites G w b vb hwf (hRG w b vb hwb))
        (h6 w' w (Or.inl ⟨hpo, b, Or.inl ⟨vb', hRG w' b vb' hwb'⟩, vb, hRG w b vb hwb⟩))
  · -- an ACQUIRE at `q`: its record names the previous write as its `GF` source
    obtain ⟨t, hrd⟩ := hrdOf w vb hwb hz (by omega) (by omega)
    obtain ⟨t', hlat, hsrc⟩ := hrec w t ⟨vb, hwb, hz⟩ ⟨by omega, by omega⟩ hrd
    rw [hix, Nat.add_sub_cancel] at hlat
    have hlat2 := SilOrd2.latestLast GR.gxImg log b q' q m' hlt (by omega) hm' hs' hquiet
    have ht' := latestUnique _ _ _ _ _ hlat hlat2
    subst ht'
    rcases hsrc with ⟨-, h0⟩ | ⟨s, hsG, hsR⟩
    · omega
    · have hsw : w' = s := Option.some.inj (hat'.symm.trans hsR)
      subst hsw
      obtain ⟨-, hgix⟩ := gwriteAtInv G t w' hwf.1 hsG
      have := CatLin.acqTsLtC G b w t hwf h6 hlv ⟨vb, hRG w b vb hwb, hz⟩ hrd
      omega

/-- **THE WINDOWED LOCK CO AT THE COMPLETE MEMBER** from the record, the alternation and RVWMO
(rule 1, load value; no `coPrefix` invariant, no NF1′/NF2a, no Lemma 3). -/
theorem SilOrd2.lockCoWOf (G GR : Gexec) (L : Int → Prop) (log : List Wmsg) (b : Int) (n0 : Nat)
    (h : Option Nat) :
    gwf G → gppoCat6Gmo G → gloadValue G → gwf GR → SilOrd2.agreeW4N G GR L → L b →
    gwrowGmo GR → logOf GR log → lockWordByte log b → wlpAlt log b n0 h →
    CatLin.acqAqB G GR log b n0 → SilOrd2.amoRecB G GR log b n0 → SilOrd2.lockCoW G GR log b n0 := by
  intro hwf h6 hlv hwfR hag hL hrowR hlog hlwb halt hAQ hrec
  have key : ∀ n q p x y, q < n → n0 ≤ p → p < q → q < log.length →
      gwriteAt GR (p + 1) = some x → gwriteAt GR (q + 1) = some y →
      (∃ m, log[p]? = some m ∧ (msgByte m b).isSome) →
      (∃ m, log[q]? = some m ∧ (msgByte m b).isSome) → gwix G x < gwix G y := by
    intro n
    induction n with
    | zero => intros; omega
    | succ n ih =>
      intro q p x y hqn hn0 hpq hql hx hy hpx hqy
      obtain ⟨q', m', h1, h2, hm', hs', hquiet⟩ := SilOrd2.lastW log b p q hpq hpx
      obtain ⟨m, hm, hs⟩ := hqy
      obtain ⟨w', hat', -, -, -⟩ := logOfLookup GR log q' m' hwfR hlog hm'
      have hstep := SilOrd2.coStep G GR L log b n0 h q' q m' m w' y hwf h6 hlv hwfR hag hL hrowR hlog
        hlwb halt hAQ hrec (by omega) h2 hql hm' hs' hm hs hquiet hat' hy
      rcases Nat.lt_or_ge p q' with hlt | hge
      · have := ih q' p x w' (by omega) hn0 hlt (by omega) hx hat' hpx ⟨m', hm', hs'⟩
        omega
      · have hpq' : q' = p := by omega
        subst hpq'
        have hxw : x = w' := Option.some.inj (hx.symm.trans hat')
        subst hxw
        exact hstep
  intro x y vx vy hx hy hnx hny hle hlt
  have hxw := gwritesByteGwrites GR x b vx hwfR hx
  have hyw := gwritesByteGwrites GR y b vy hwfR hy
  obtain ⟨mx, hmx, hgx⟩ := logOfWrite GR log x hwfR hlog hxw (by omega)
  obtain ⟨my, hmy, hgy⟩ := logOfWrite GR log y hwfR hlog hyw hle
  refine key (gwix GR y) (gwix GR y - 1) (gwix GR x - 1) x y (by omega) (by omega) (by omega)
    (by omega) ?_ ?_ ⟨mx, hmx, ?_⟩ ⟨my, hmy, ?_⟩
  · rw [show gwix GR x - 1 + 1 = gwix GR x by omega]; exact gwriteAtGwix GR x hxw
  · rw [show gwix GR y - 1 + 1 = gwix GR y by omega]; exact gwriteAtGwix GR y hyw
  · rw [(WeakRvwmoKillArms.gmsgByte GR x mx b vx hgx).2 hx]; rfl
  · rw [(WeakRvwmoKillArms.gmsgByte GR y my b vy hgy).2 hy]; rfl

/-- The record at every registered byte gives the windowed lock co at every registered byte. -/
theorem SilOrd2.lockCoLogOf (G GR : Gexec) (log : List Wmsg) (P : Int → Int → Prop) :
    gwf G → gppoCat6Gmo G → gloadValue G → gwf GR →
    SilOrd2.agreeW4N G GR (GraphFetchN2.lockBytes P) → gwrowGmo GR → logOf GR log →
    CatLin.acqAqLog G GR log P → SilOrd2.amoRecLog G GR log P → SilOrd2.lockCoLog G GR log P :=
  fun hwf h6 hlv hwfR hag hrowR hlog hAQ hrec a b n0 r0 h hP hprot hat halt hlwb =>
    SilOrd2.lockCoWOf G GR _ log b n0 h hwf h6 hlv hwfR hag ⟨a, hP⟩ hrowR hlog hlwb halt
      (hAQ a b n0 r0 h hP hprot hat halt) (hrec a b n0 r0 h hP hprot hat halt)

/-! # 3. The kill chain at the windowed lock co -/

namespace CatLin

/-- **`csChainedT4W` — THE TRANSPORT AT THE WINDOWED LOCK CO**: `csChainedT4` with `agreeW4N` and the
windowed `lockCoW` in place of `agreeW4` (no `regZeroAt`, no non-plainness of the section's release:
the reader-first arm closes `REL <co ACQw` in `GF` through the release `R′` between the two acquires). -/
theorem SilOrd2.csChainedT4W (GD : Gdexec) (ad : List (Geid × Geid)) (GR : Gexec) (L : Int → Prop)
    (log : List Wmsg) (b a : Int) (n0 r0 : Nat) (h : Option Nat)
    (w entry exit ACQ REL : Geid) :
    rvwmoCatAD GD ad → gwf GR → SilOrd2.agreeW4N GD.gdG GR L → SilOrd2.lockCoW GD.gdG GR log b n0 →
    gwrowGmo GR →
    CertZ18.rmwLatest GR log →
    acqAqB GD.gdG GR log b n0 → relCoversB GD.gdG GR log b n0 →
    logOf GR log → lockWordByte log b → wlpAlt log b n0 h →
    acqRow GD.gdG b ACQ → CertZ24.nf GD.gdG L ACQ → CertZ24.nf GD.gdG L w →
    wprotAt log a b n0 r0 →
    (∃ v, gwritesByte GD.gdG w a v) → gcls GD.gdG w .WCplain →
    r0 < gwix GR w → gwix GR w ≤ log.length →
    (∀ v, ¬ gwritesByte GD.gdG w b v) →
    lockAcq GD.gdG b ACQ → glblIs GD.gdG ACQ lbAq →
    n0 < gwix GR ACQ → gwix GR ACQ ≤ log.length →
    lockCs GD.gdG b ACQ REL → gfenceCovers GD.gdG entry REL →
    gmoLt GD.gdG w entry → WeakRvwmoGraph.gpo GD.gdG ACQ exit → gmem GD.gdG exit →
    ACQ.1 ≠ w.1 →
    gmoLt GD.gdG w exit := by
  intro hcons hwfR hag hco hrowR hlat hAQ hRC hlog hlwb halt hrow hnfA hnfw hpr hwa hcl hr0
    hlew hnob hacq haq hn0A hleA hcs hfen hcross hpox hmx hhart
  obtain ⟨-, hRG, hRnf, hGR, hcls, hagRd⟩ := hag
  -- the reader's acquire is in the window
  obtain ⟨va, hva, hvane⟩ := id hacq
  have hvaR : gwritesByte GR ACQ b va := hGR ACQ b va hnfA hva
  have hAwR := lockAcqGwrites GR b ACQ hwfR ⟨va, hvaR, hvane⟩
  obtain ⟨mA, hmA, hgA⟩ := logOfWrite GR log ACQ hwfR hlog hAwR hleA
  have hbA := (WeakRvwmoKillArms.gmsgByte GR ACQ mA b va hgA).2 hvaR
  have hfreeA : wlpHolderAt log b n0 (gwix GR ACQ - 1) = some none := by
    obtain ⟨tA, hrdA⟩ := id hrow
    obtain ⟨tA', hrdA'⟩ :=
      hagRd.1 ACQ b tA lockFree hnfA (gwritesByteGlblW _ ACQ b va hva) hrdA
    obtain ⟨hlA, hvA⟩ := hlat ACQ b tA' lockFree (gwritesByteGlblW GR ACQ b va hvaR) hrdA'
    exact CertZ18.foldFreeOfLatest GR.gxImg log b n0 h _ tA' hlwb halt (by omega) hlA hvA
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
  have hqlen : q < log.length := lookup_lt_Some hlk
  have hrA := acqRowIsR G b ACQ hrow
  have hmoAx : gmoLt G ACQ exit := acqGmoAfterC G ACQ exit h6 hpox hrA haq hmx
  obtain ⟨vq, hvq, hvqne⟩ := id hacqwR
  have hvqG : gwritesByte G ACQw b vq := hRG ACQw b vq hvq
  have hacqw : lockAcq G b ACQw := ⟨vq, hvqG, hvqne⟩
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
        (hco R ACQ lockFree va hRrel hvaR (by omega) (by omega) hleA (by omega))
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
    have hAR'G : gwix G ACQ < gwix G R' :=
      hco ACQ R' va lockFree hvaR hrelr' (by omega) (by omega) (by omega) (by omega)
    have hRleG : gwix G REL ≤ gwix G R' := by
      by_cases hc : gwix G R' < gwix G REL
      · exact absurd ⟨hAR'G, hc⟩ (hnoin R' lockFree hR'G hhr')
      · omega
    have hR'w : gwix G R' < gwix G ACQw :=
      hco R' ACQw lockFree vq hrelr' hvq (by omega) (by omega) (by omega) (by omega)
    have hmoRA : gmoLt G REL ACQw :=
      gwixLtGmo G REL ACQw hwf (lockRelGwrites G b REL hwf hRel) (lockAcqGwrites G b ACQw hwf hacqw)
        (by omega)
    obtain ⟨hrw, haqw⟩ := hAQ ACQw hacqw hwinA
    have hmoAw : gmoLt G ACQw w :=
      acqGmoAfterC G ACQw w h6 hpoAw hrw haqw
        (WeakRvwmoGraph.glblIsWGmem G w (gwritesByteGlblW G w a vw hvw))
    have hmoeR := fenceGmoAfterC G entry REL h6 hfen
    exact absurd (gmoLtTrans G w entry w hcross
      (gmoLtTrans G entry REL w hmoeR (gmoLtTrans G REL ACQw w hmoRA hmoAw))) (gmoLtIrrefl G w)

/-- `csHypsCertCR4` at the windowed lock co. -/
theorem SilOrd2.csHypsCertCR4W (GD : Gdexec) (ad : List (Geid × Geid)) (X : Geid → Geid → Prop)
    (GR : Gexec) (P : Int → Int → Prop) (log : List Wmsg) (prev : Geid) (s : Seg) :
    rvwmoCatAD GD ad → (∀ x y, X x y → gmoLt GD.gdG x y) →
    gwf GR → SilOrd2.agreeW4N GD.gdG GR (GraphFetchN2.lockBytes P) →
    SilOrd2.lockCoLog GD.gdG GR log P → gwrowGmo GR →
    CertZ18.rmwLatest GR log →
    acqAqLog GD.gdG GR log P → relCoversLog GD.gdG GR log P →
    logOf GR log → protReg P log →
    csHypsR4 GD GR P log prev s → X prev s.sgEntry →
    CertC GD.gdG X prev s := by
  rintro hc hX hwfR hag hco hrowR hlat hAQ hRC hlog hpr
    ⟨⟨b, a, ACQ, REL, hP, hlwb, hwa, hcl, hlew, hnob, hacq, hrow, haq, hleA, hcs, -, hpoe, hfen,
      hpox, hmx, hhart, hside⟩, hnf⟩ hx
  obtain ⟨hnfA, hnfw⟩ := hnf b a ACQ hP hrow
  obtain ⟨n0, r0, h, hprot, hat, halt⟩ := hpr a b hP
  obtain ⟨hr0, hn0A⟩ := hside n0 r0 hprot
  exact .CSchained (SilOrd2.csChainedT4W GD ad GR (GraphFetchN2.lockBytes P) log b a n0 r0 h prev
    s.sgEntry s.sgExit ACQ REL hc hwfR hag (hco a b n0 r0 h hP hprot hat halt hlwb) hrowR hlat
    (hAQ a b n0 r0 h hP hprot hat halt) (hRC a b n0 r0 h hP hprot hat halt) hlog hlwb halt hrow
    hnfA hnfw hprot hwa hcl hr0 hlew hnob hacq haq hn0A hleA hcs hfen (hX _ _ hx) hpox hmx hhart)

/-- `SilKill.rawChainChainW4` at the windowed lock co. -/
theorem SilOrd2.rawChainChainW4W (GF : Gfexec) (ad : List (Geid × Geid)) (GR : Gexec)
    (P : Int → Int → Prop) (log : List Wmsg) (Bad : Prop) (ss : List Seg) :
    rvwmoCatAD GF.gfGd ad → ioResidueGmo GF → gdiskRead14 GF.gfGd.gdG →
    gwf GR → SilOrd2.agreeW4N GF.gfGd.gdG GR (GraphFetchN2.lockBytes P) →
    SilOrd2.lockCoLog GF.gfGd.gdG GR log P → gwrowGmo GR →
    CertZ18.rmwLatest GR log →
    acqAqLog GF.gfGd.gdG GR log P → relCoversLog GF.gfGd.gdG GR log P →
    logOf GR log → protReg P log → ¬ Bad →
    (∀ prev s, s ∈ ss → ioCross GF prev s.sgEntry → segRunC GF.gfGd s →
       segPinC GF.gfGd ad s ∨ csHypsR4 GF.gfGd GR P log prev s ∨ Bad) →
    ∀ (x y : Geid) (ss' : List Seg),
      ss' ⊆ ss → rawChainC GF.gfGd (ioCross GF) x y ss' →
      chainC GF.gfGd.gdG (ioCross GF) x y ss' := by
  intro hc hres hdr hwfR hag hco hrowR hlat hAQ hRC hlog hpr hnB hcl x y ss'
  have hX : ∀ x y, ioCross GF x y → gmoLt GF.gfGd.gdG x y :=
    ioCrossGmo GF hc.1 hc.2.2.1 hres hdr
  induction ss' generalizing x with
  | nil => intro _ hch; exact hch
  | cons s ss' ih =>
    intro hsub hch
    obtain ⟨hx, hrun, hrest⟩ := hch
    have hs : s ∈ ss := hsub (by simp)
    have hsub' : ss' ⊆ ss := by
      intro t ht
      exact hsub (List.mem_cons_of_mem s ht)
    show CertC GF.gfGd.gdG (ioCross GF) x s ∧ chainC GF.gfGd.gdG (ioCross GF) s.sgExit y ss'
    refine ⟨?_, ih _ hsub' hrest⟩
    rcases hcl x s hs hx hrun with hp | hcs | hb
    · exact segPinCCert GF.gfGd ad _ x s hc hx hp
    · exact SilOrd2.csHypsCertCR4W GF.gfGd ad _ GR P log x s hc hX hwfR hag hco hrowR hlat hAQ hRC
        hlog hpr hcs hx
    · exact absurd hb hnB

/-! # 4. The record agreement, its named premises, the kill core -/

end CatLin

/-- **THE RECORD AGREEMENT** at a realized member: image, the silent label agreement (no lock co),
and the gate's record at every registered byte (the windowed lock co FOLLOWS, `lockCoLogOf`). -/
def SilOrd2.agreeRRS (G GR : Gexec) (log : List Wmsg) (pi : Nat → Nat) (P : Int → Int → Prop) :
    Prop :=
  GR.gxImg = G.gxImg ∧ SilAgree.lblAgreeS G GR pi (GraphFetchN2.lockBytes P) ∧
  SilOrd2.amoRecLog G GR log P

namespace CatLin

/-- **(G-3) at the twin, TRIMMED, with the RECORD** (`SilKillT.certSupplyS` with `agreeRRS` at the
realized log in place of `agreeRPS`): discharged from the GATED walk (row 6l). -/
def SilOrd2.certSupplyRS (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image) (N : Nat)
    (P : Int → Int → Prop) : Prop :=
  ∀ (GF : Gfexec) (ad : List (Geid × Geid)) (cs : List Nat) (z : Geid) (ss : List Seg),
    GF.gfGd.gdG.gxImg = im → rvwmoCatAD GF.gfGd ad → GraphFabConf.gfexecConfZF boot d0 fab GF →
    ioResidueGmo GF → gdiskRead14 GF.gfGd.gdG →
    properCutF GF cs → GraphFetchHullZ.fetchSrcClosedCut boot fab GF cs →
    GraphFabConf.gfexecConfZF boot d0 fab (gfHull GF cs) →
    GraphFetchBlocks.emPremOk boot (gfHull GF cs).gfGd.gdG →
    (∀ x, ¬ tc (racyDIO (CapFetchProv.trimF boot (gfHull GF cs))) x x) →
    ss ≠ [] → rawChainC GF.gfGd (ioCross GF) z z ss →
    ∃ (c : SilCand.CandS) (pst : Nat → List Pexv6) (dv : Nat → Efab) (pi : Nat → Nat),
      SilAgree.RunDataS boot d0 N GF.gfGd.gdG c pst dv ∧
      SilOrd2.agreeRRS GF.gfGd.gdG (SilAgree.memberS N c) (SilAgree.logS c) pi P

/-- `SilKill.acqAqS` at the record agreement (row 6f; the lock fact does not read lock co). -/
def SilOrd2.acqAqRS (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image) (N : Nat)
    (P : Int → Int → Prop) : Prop :=
  ∀ (GF : Gfexec) (ad : List (Geid × Geid)) (c : SilCand.CandS) (pst : Nat → List Pexv6)
    (dv : Nat → Efab) (pi : Nat → Nat),
    GF.gfGd.gdG.gxImg = im → rvwmoCatAD GF.gfGd ad → GraphFabConf.gfexecConfZF boot d0 fab GF →
    SilAgree.RunDataS boot d0 N GF.gfGd.gdG c pst dv →
    SilOrd2.agreeRRS GF.gfGd.gdG (SilAgree.memberS N c) (SilAgree.logS c) pi P →
    CertZ18.protRegZ P (SilAgree.memberS N c).gxImg (SilAgree.logS c) →
    acqAqLog GF.gfGd.gdG (SilAgree.memberS N c) (SilAgree.logS c) P

/-- `SilKill.relCoversS` at the record agreement (row 6f). -/
def SilOrd2.relCoversRS (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image) (N : Nat)
    (P : Int → Int → Prop) : Prop :=
  ∀ (GF : Gfexec) (ad : List (Geid × Geid)) (c : SilCand.CandS) (pst : Nat → List Pexv6)
    (dv : Nat → Efab) (pi : Nat → Nat),
    GF.gfGd.gdG.gxImg = im → rvwmoCatAD GF.gfGd ad → GraphFabConf.gfexecConfZF boot d0 fab GF →
    SilAgree.RunDataS boot d0 N GF.gfGd.gdG c pst dv →
    SilOrd2.agreeRRS GF.gfGd.gdG (SilAgree.memberS N c) (SilAgree.logS c) pi P →
    CertZ18.protRegZ P (SilAgree.memberS N c).gxImg (SilAgree.logS c) →
    relCoversLog GF.gfGd.gdG (SilAgree.memberS N c) (SilAgree.logS c) P

/-- `SilKillT.l2ClaimS` at the record agreement (row 6n). -/
def SilOrd2.l2ClaimRS (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image) (N : Nat)
    (P : Int → Int → Prop) (Bad : Prop) : Prop :=
  ∀ (GF : Gfexec) (ad : List (Geid × Geid)) (c : SilCand.CandS) (pst : Nat → List Pexv6)
    (dv : Nat → Efab) (pi : Nat → Nat),
    GF.gfGd.gdG.gxImg = im → GraphFabConf.gfexecConfZF boot d0 fab GF →
    CapFetchProv.provAll boot GF.gfGd →
    SilAgree.RunDataS boot d0 N GF.gfGd.gdG c pst dv →
    SilOrd2.agreeRRS GF.gfGd.gdG (SilAgree.memberS N c) (SilAgree.logS c) pi P →
    l2ClaimAtCZR4 GF ad (SilAgree.memberS N c) P Bad

section glue

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode
open Language.Notation PrimStep
open LeanRV64D

/-- **THE TRIMMED TWIN KILL AT THE WINDOWED LOCK CO, CORE**: `SilKillT.cycleKillCore` with the cert
supply returning the RECORD agreement; the windowed lock co is DERIVED (`lockCoLogOf`). -/
theorem SilOrd2.cycleKillCoreW (gen : Nat) (σ0 : WGState) (P : Int → Int → Prop)
    (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (N : Nat) :
    freshEra gen σ0 →
    (List.range' 0 N).map boot = epsInit σ0 →
    d0 = efInit σ0.wgdev →
    ¬ SilKill.badRunS gen σ0 →
    (∀ ρ, rtc SilEpf.epfRunS (epInit gen, σ0) ρ → efetchItvOk ρ.1 ρ.2) →
    (∀ (GF : Gfexec) (ad : List (Geid × Geid)) (c : SilCand.CandS) (pst : Nat → List Pexv6)
      (dv : Nat → Efab) (pi : Nat → Nat) (t2 : List SilLang.EExprS) (σ2 : WGState),
      GF.gfGd.gdG.gxImg = imgZ σ0.wgimg → rvwmoCatAD GF.gfGd ad →
      GraphFabConf.gfexecConfZF boot d0 fab GF →
      SilAgree.RunDataS boot d0 N GF.gfGd.gdG c pst dv →
      SilOrd2.agreeRRS GF.gfGd.gdG (SilAgree.memberS N c) (SilAgree.logS c) pi P →
      (SilLang.epowerForkS gen, σ0) -·->ₜₚ* (t2, σ2) → σ2.wglog = SilAgree.logS c →
      CertZ18.protRegZ P (imgZ σ0.wgimg) (SilAgree.logS c)) →
    cutSupplyCZC boot d0 fab (imgZ σ0.wgimg) →
    SilOrd2.certSupplyRS boot d0 fab (imgZ σ0.wgimg) N P →
    SilOrd2.acqAqRS boot d0 fab (imgZ σ0.wgimg) N P →
    SilOrd2.relCoversRS boot d0 fab (imgZ σ0.wgimg) N P →
    SilOrd2.l2ClaimRS boot d0 fab (imgZ σ0.wgimg) N P (SilKill.badRunS gen σ0) →
    cycleKillCZT boot d0 fab (imgZ σ0.wgimg) := by
  intro hfr hb1 hb2 hnB hcov hprF hcut hcert hAQ hRC hl2
  intro GF ad him hc hconf hres hdr hprov hIH x hcyc
  obtain ⟨z, ss, hne, hch⟩ := cycleSegmentsIO GF ad x hc hcyc
  obtain ⟨cs, hcutok, hdc, hcl, hprem⟩ := hcut GF ad z ss him hc hconf hne hch
  have hcore := catADCore _ _ hc
  have hconfH :=
    GraphFetchHullZ.gfexecConfZFHull boot d0 fab GF cs hcore.1 hcore.2.1 hcutok.1 hdc hconf hcl
  have hpc := GraphFetchKill.properCutFOfCut GF cs hcutok hdc
  have hacyH := hIH cs hpc hcl
  obtain ⟨c, pst, dv, pi, hrd, hagR⟩ :=
    hcert GF ad cs z ss him hc hconf hres hdr hpc hcl hconfH hprem hacyH hne hch
  obtain ⟨hwfR, hrowR, hlog, hlat, himgR⟩ := SilAgree.memberFacts hrd
  obtain ⟨t2, σ2, hrtc, hlgeq⟩ :=
    SilAgree.runErasedS gen σ0 boot d0 N GF.gfGd.gdG c pst dv hfr hcov hb1 hb2 him hrd
  have hpr : CertZ18.protRegZ P (SilAgree.memberS N c).gxImg (SilAgree.logS c) := by
    rw [himgR, him]
    exact hprF GF ad c pst dv pi t2 σ2 him hc hconf hrd hagR hrtc hlgeq
  have hagN := SilOrd2.agreeW4NOfS _ _ _ _ hagR.1 hagR.2.1
  have hAQ' := hAQ GF ad c pst dv pi him hc hconf hrd hagR hpr
  have hco :=
    SilOrd2.lockCoLogOf _ _ _ P hc.1 hc.2.1 hc.2.2.1 hwfR hagN hrowR hlog hAQ' hagR.2.2
  exact cycleKillIOC GF ad z ss hc hres hdr hne
    (SilOrd2.rawChainChainW4W GF ad (SilAgree.memberS N c) P (SilAgree.logS c)
      (SilKill.badRunS gen σ0) ss hc hres hdr hwfR hagN hco hrowR hlat hAQ'
      (hRC GF ad c pst dv pi him hc hconf hrd hagR hpr) hlog (CertZ18.protRegOfZ _ _ _ hpr) hnB
      (hl2 GF ad c pst dv pi him hconf hprov hrd hagR (SilAgree.logS c) z ss hc hlog hpr hne hch)
      z z ss (fun _ h => h) hch)

end glue

end CatLin

end Weak
