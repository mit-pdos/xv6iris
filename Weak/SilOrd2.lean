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
      (⇒ `cycleKillCZT`);
  §5  THE GATE ([OWN.106] the order is the realized list `Lw`, built step by step — no order premise, no
      acyclicity assumption; [OWN.108] Q-6L-PIN (a)): **`SilOrd2.enb`** (fabric turn; a successful
      acquire waits until its `GF` source is the twin's member-latest write, `srcLatestAt`; a failed
      acquire and a pinned plain load (`pin`, row 6m's site predicate) wait only until their sources are
      REALIZED, `srcRealized`, and are replayed stale), the gated prefix `prefW`/`prefG` (with the record
      `recTr`), `noStuckG`, the gated step context **`stepCtxG`** / datum **`hartStepG`** / `atStepsG`,
      **`readDatumOfG`** (w2's `SilSite` premises `ordQ`/`devQ`/`valQ`/`custQ`/`drfQ` give the read datum
      at every GATED step), `enbOfCtx`, **`SilOrd2.walkPolG`** (the twin policy from NoStuck + the datum);
  §6  `walkOrdOfDone` (a complete realized list IS a walk order), **`recLogOfTr`** (the record at the
      complete member), the NAMED **`CatLin.SilOrd2.noStuck`** (row 6l, PENDING R44: needs
      Q-6L-REG's `regBeforeAmo`) and `CatLin.SilOrd2.stepSupplyG` (row 6m),
      **`CatLin.SilOrd2.certSupplyOfGate`** (⇒ `certSupplyRS`), **`CatLin.SilOrd2.cycleKillGZ`**
      (⇒ `cycleKillCZT`; no `orderSupplyCZ3`, `lockDiscCZ3`, GF-level `oneByteS`, `SilOrd.stepSupplyS`).

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

/-! # 5. The gate ([OWN.106], [OWN.108]) and the gated walk -/

/-- A `GF` read source is REALIZED in the walk prefix `Lw` (the image counts as realized). -/
def SilOrd2.srcRealized (G : Gexec) (Lw : List Geid) (t : Nat) : Prop :=
  t = 0 ∨ ∃ s, gwriteAt G t = some s ∧ s ∈ Lw

/-- A `GF` read source at `b` IS the twin's member-latest write of `b` at twin step `k` (the image when
no message writes `b`): the event `Lw[j]` of an earlier non-silent writing step `j`. -/
def SilOrd2.srcLatestAt (G : Gexec) (Lw : List Geid) (c : SilCand.CandS) (k : Nat) (b : Int)
    (t : Nat) : Prop :=
  (t = 0 ∧ latest (SilCand.stAt c k).msImg (SilCand.stAt c k).msLog b 0) ∨
  ∃ j s sp, j < k ∧ gwriteAt G t = some s ∧ Lw[j]? = some s ∧
    (SilCand.proj c).cdTr[j]? = some sp ∧ lbIsW sp.esLb = true ∧
    latest (SilCand.stAt c k).msImg (SilCand.stAt c k).msLog b
      ((SilCand.stAt c j).msLog.length + 1)

/-- A SUCCESSFUL ACQUIRE `e` of lock byte `b`, reading it free at `t`. -/
def SilOrd2.sAcq (G : Gexec) (L : Int → Prop) (e : Geid) (b : Int) (t : Nat) : Prop :=
  L b ∧ CertZ24.nf G L e ∧ lockAcq G b e ∧ greadsByte G e b t lockFree

/-- **THE GATE** at the realized list `Lw` and twin state `S`, for the row event `e`:
  * a FABRIC event waits for its turn (`dev[#fabric events realized] = e`);
  * a SUCCESSFUL ACQUIRE of a lock byte waits until its `GF` source is the twin's member-latest write of
    the byte (this is what the record `amoRecB` remembers);
  * a FAILED ACQUIRE and a PINNED plain load (`pin`: row 6m's site predicate) wait only until their `GF`
    sources are REALIZED ([OWN.108] Q-6L-PIN (a): replayed STALE; the value condition is the per-site
    datum's, w2's `SilSite.ordQ`/`silentQ`);
  * every other event is enabled. -/
def SilOrd2.enb (G : Gexec) (dev : List Geid) (L : Int → Prop) (pin : Geid → Prop)
    (Lw : List Geid) (S : SilWalk.St) (e : Geid) : Prop :=
  (e ∈ dev → dev[(Lw.filter (fun e' => decide (e' ∈ dev))).length]? = some e) ∧
  (∀ b t, SilOrd2.sAcq G L e b t → SilOrd2.srcLatestAt G Lw S.c S.c.tr.length b t) ∧
  ((¬ CertZ24.nf G L e ∨ pin e) → ∀ b t v, greadsByte G e b t v → SilOrd2.srcRealized G Lw t)

/-- The record so far: every realized successful acquire's source was member-latest at its step. -/
def SilOrd2.recTr (G : Gexec) (L : Int → Prop) (Lw : List Geid) (c : SilCand.CandS) : Prop :=
  ∀ k e b t, Lw[k]? = some e → SilOrd2.sAcq G L e b t → SilOrd2.srcLatestAt G Lw c k b t

/-- **THE GATED PREFIX** at an explicit realized list `Lw` ([OWN.106]: the order is the list of the
events realized so far, built step by step): per-hart counters, each hart's events a prefix of its
row, the fabric at the number of fabric events realized, the trace's agents, the fabric events
realized in fabric order, each hart's events in program order, and the record. -/
def SilOrd2.prefW (G : Gexec) (dev : List Geid) (fab : Nat → Efab) (L : Int → Prop)
    (S : SilWalk.St) (cnt : Nat → Nat) (Lw : List Geid) : Prop :=
  (∀ x, cnt x = (Lw.filter (fun e => decide (e.1 = x))).length) ∧
  (∀ e, e ∈ Lw → e.2 < cnt e.1) ∧ (∀ x a, a < cnt x → (x, a) ∈ Lw) ∧ Lw.Nodup ∧
  S.dv S.c.tr.length = fab ((Lw.filter (fun e => decide (e ∈ dev))).length) ∧
  S.c.tr.map Estep.esAg = Lw.map Prod.fst ∧
  (∀ m e, dev[m]? = some e → e ∈ Lw → m < (Lw.filter (fun e' => decide (e' ∈ dev))).length) ∧
  (∀ (i j x a b : Nat), Lw[i]? = some (x, a) → Lw[j]? = some (x, b) → a < b → i < j) ∧
  (∀ (m n i j : Nat) (e e' : Geid), dev[m]? = some e → dev[n]? = some e' → m < n →
    Lw[i]? = some e → Lw[j]? = some e' → i < j) ∧
  SilOrd2.recTr G L Lw S.c

def SilOrd2.prefG (G : Gexec) (dev : List Geid) (fab : Nat → Efab) (L : Int → Prop) :
    SilWalk.St → (Nat → Nat) → Prop :=
  fun S cnt => ∃ Lw, SilOrd2.prefW G dev fab L S cnt Lw

/-- **NoStuck at one graph** (the GF-local form of the named `CatLin.SilOrd2.noStuck`): at every gated
walk state with work left, some hart's next row event is ENABLED. -/
def SilOrd2.noStuckG (d0 : Efab) (G : Gexec) (dev : List Geid) (fab : Nat → Efab)
    (L : Int → Prop) (pin : Geid → Prop) : Prop :=
  ∀ (S : SilWalk.St) (cnt : Nat → Nat) (Lw : List Geid),
    SilWalk.ok d0 S → SilOrd2.prefW G dev fab L S cnt Lw →
    (∀ x, x < G.gxProg.length →
      cnt x ≤ (G.gxProg.getD x []).length ∧
      List.Forall₂ (SilWalk.relW L) ((G.gxProg.getD x []).take (cnt x))
        (SilWalk.hartPr (SilOrd.pairs S) x)) →
    (∀ s, s ∈ S.c.tr → s.esAg < G.gxProg.length) →
    (∃ x, x < G.gxProg.length ∧ cnt x < (G.gxProg.getD x []).length) →
    ∃ x, x < G.gxProg.length ∧ cnt x < (G.gxProg.getD x []).length ∧
      SilOrd2.enb G dev L pin Lw S (x, cnt x)

/-- **THE GATED STEP CONTEXT** (`SilSite.stepCtx` with the realized list `Lw` in place of an order
prefix, and the GATE at the next event as an extra hypothesis — what the per-site premises read). -/
def SilOrd2.stepCtxG (d0 : Efab) (G : Gexec) (dev : List Geid) (Lb : Int → Prop)
    (pin : Geid → Prop) (Rel : CertZ9.HRel) (S : SilWalk.St) (Lw : List Geid) (x n : Nat)
    (lb : Lbl) (ws : Wstate) (ls : List Wlabel) (l : Wlabel) (pE pE' pC : Pexv6) (d' : Efab) :
    Prop :=
  SilWalk.ok d0 S ∧
  (S.pst S.c.tr.length)[x]? = some pC ∧ Rel x n pE pC ∧ CertZ4.lblShape lb ∧
  ((lbFused l ∧ GraphFetchBlocks.blkOne (S.dv S.c.tr.length) d' ws lb ls l pE pE') ∨
    GraphFetchBlocks.blkPair (S.dv S.c.tr.length) d' ws lb ls l pE pE') ∧
  S.c.tr.map Estep.esAg = Lw.map Prod.fst ∧
  n = (Lw.filter (fun e => decide (e.1 = x))).length ∧
  (∀ y, y < G.gxProg.length →
    List.Forall₂ (SilWalk.relW Lb)
      ((G.gxProg.getD y []).take ((Lw.filter (fun e => decide (e.1 = y))).length))
      (SilWalk.hartPr (SilOrd.pairs S) y)) ∧
  (G.gxProg.getD x [])[n]? = some lb ∧
  SilOrd2.enb G dev Lb pin Lw S (x, n)

/-- **THE GATED PER-STEP DATUM** (`SilOrd.hartStepRIS` at an ENABLED next event; row 6m discharges it
from w2's `SilSite` read datum and its named per-route premises, `readDatumOfG`). -/
def SilOrd2.hartStepG (d0 : Efab) (G : Gexec) (dev : List Geid) (Lb : Int → Prop)
    (pin : Geid → Prop) (Rel : CertZ9.HRel) : Prop :=
  ∀ (S : SilWalk.St) (Lw : List Geid) (x n : Nat) (lb : Lbl) (ws : Wstate) (ls : List Wlabel)
    (l : Wlabel) (pE pE' pC : Pexv6) (d' : Efab),
    SilOrd2.stepCtxG d0 G dev Lb pin Rel S Lw x n lb ws ls l pE pE' pC d' →
    ∃ (lb' : Lbl) (o : Option Nat) (pa : Pexv6) (da : Efab) (ls' : List Wlabel) (pC' : Pexv6)
      (w' : Wstate),
      SilWalk.relW Lb lb (lb', o) ∧ SilWalk.stepOk S x lb' o pC pa da ls' pC' d' w' ∧
      Rel x (n + 1) pE' pC'

/-- `Q` at every gated step (`SilSite.atSteps`'s twin). -/
def SilOrd2.atStepsG (d0 : Efab) (G : Gexec) (dev : List Geid) (Lb : Int → Prop)
    (pin : Geid → Prop) (Rel : CertZ9.HRel)
    (Q : SilWalk.St → Nat → Lbl → List Wlabel → Prop) : Prop :=
  ∀ (S : SilWalk.St) (Lw : List Geid) (x n : Nat) (lb : Lbl) (ws : Wstate) (ls : List Wlabel)
    (l : Wlabel) (pE pE' pC : Pexv6) (d' : Efab),
    SilOrd2.stepCtxG d0 G dev Lb pin Rel S Lw x n lb ws ls l pE pE' pC d' → Q S x lb ls

/-- **w2's premises give the read datum at every GATED step** (`SilSite.readDatumOf`, verbatim in the
gated context: the same `ordQ`/`devQ`/`valQ`/`custQ`/`drfQ`). -/
theorem SilOrd2.readDatumOfG (d0 : Efab) (G : Gexec) (dev : List Geid) (Lb : Int → Prop)
    (pin : Geid → Prop) (Rel : CertZ9.HRel) (cpuOf : Nat → Nat) (isDev : Nat → Prop) :
    SilOrd2.atStepsG d0 G dev Lb pin Rel (SilSite.ordQ (fun pc => pc ∈ SilSite.pinRdK) isDev) →
    SilOrd2.atStepsG d0 G dev Lb pin Rel (SilSite.devQ isDev) →
    SilOrd2.atStepsG d0 G dev Lb pin Rel (SilSite.valQ cpuOf isDev) →
    SilOrd2.atStepsG d0 G dev Lb pin Rel (SilSite.custQ isDev) →
    SilOrd2.atStepsG d0 G dev Lb pin Rel (SilSite.drfQ isDev) →
    SilOrd2.atStepsG d0 G dev Lb pin Rel
      (fun S x lb ls => SilSite.readDatum S x (cpuOf x) lb ls) := by
  intro hord hdev hval hcust hdrf S Lw x n lb ws ls l pE pE' pC d' hctx _
  by_cases hd : isDev x
  · exact .inl (hdev S Lw x n lb ws ls l pE pE' pC d' hctx hd)
  · cases hb : SilSite.blockPc ls with
    | none =>
      refine .inl (hdrf S Lw x n lb ws ls l pE pE' pC d' hctx hd (fun pc hpc => ?_))
      rw [hb] at hpc
      cases hpc
    | some pc =>
      by_cases h1 : pc ∈ SilSite.pinRdK
      · exact .inl (hord S Lw x n lb ws ls l pE pE' pC d' hctx hd ⟨pc, hb, h1⟩)
      · by_cases h2 : pc ∈ SilSite.tPcsAll
        · exact hval S Lw x n lb ws ls l pE pE' pC d' hctx hd pc hb h2
        · by_cases h3 : pc ∈ SilSite.nPcs
          · exact .inl (hcust S Lw x n lb ws ls l pE pE' pC d' hctx hd pc hb h3)
          · refine .inl (hdrf S Lw x n lb ws ls l pE pE' pC d' hctx hd (fun pc' hpc' => ?_))
            rw [hb, Option.some.injEq] at hpc'
            subst hpc'
            exact ⟨h1, h2, h3⟩

/-- The gate's facts are visible to the per-site premises: at a gated step the next event is enabled
(a failed acquire's and a pinned load's sources are realized, a successful acquire's is member-latest). -/
theorem SilOrd2.enbOfCtx (d0 : Efab) (G : Gexec) (dev : List Geid) (Lb : Int → Prop)
    (pin : Geid → Prop) (Rel : CertZ9.HRel) :
    SilOrd2.atStepsG d0 G dev Lb pin Rel (fun S x _ _ =>
      ∃ Lw n, S.c.tr.map Estep.esAg = Lw.map Prod.fst ∧ SilOrd2.enb G dev Lb pin Lw S (x, n)) :=
  fun S Lw x n _ _ _ _ _ _ _ _ hctx => ⟨Lw, n, hctx.2.2.2.2.2.1, hctx.2.2.2.2.2.2.2.2.2⟩

theorem SilOrd2.snocLookup (Lw : List Geid) (e f : Geid) (i : Nat) :
    (Lw ++ [e])[i]? = some f → (i < Lw.length ∧ Lw[i]? = some f) ∨ (i = Lw.length ∧ f = e) := by
  intro h
  have hlt := lookup_lt_Some h
  simp only [List.length_append, List.length_singleton] at hlt
  by_cases hi : i < Lw.length
  · rw [List.getElem?_append_left hi] at h
    exact .inl ⟨hi, h⟩
  · have hie : i = Lw.length := by omega
    subst hie
    rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self] at h
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    exact .inr ⟨rfl, h.symm⟩

/-- The twin's projected trace is unchanged at the old positions by appending. -/
theorem SilOrd2.projSnoc (S : SilWalk.St) (x : Nat) (lb : Lbl) (o : Option Nat) (pC' : Pexv6)
    (d' : Efab) (w' : Wstate) (j : Nat) :
    S.c.sil.length = S.c.tr.length → j < S.c.tr.length →
    (SilCand.proj (SilWalk.snoc S x lb o pC' d' w').c).cdTr[j]? = (SilCand.proj S.c).cdTr[j]? := by
  intro hsl hj
  rw [SilCand.projTr, SilCand.projTr]
  have h1 : (SilWalk.snoc S x lb o pC' d' w').c.tr[j]? = S.c.tr[j]? := by
    show (S.c.tr ++ [⟨x, lb⟩])[j]? = _
    rw [List.getElem?_append_left hj]
  have h2 : (SilWalk.snoc S x lb o pC' d' w').c.sil.getD j none = S.c.sil.getD j none :=
    SilWalk.getDApp _ _ _ _ (by omega)
  rw [h1, h2]

/-- A member-latest source stays one after appending (old steps, old realized events unchanged). -/
theorem SilOrd2.srcLatestSnoc (G : Gexec) (Lw : List Geid) (e : Geid) (S : SilWalk.St) (x : Nat)
    (lb : Lbl) (o : Option Nat) (pC' : Pexv6) (d' : Efab) (w' : Wstate) (k : Nat) (b : Int)
    (t : Nat) :
    S.c.sil.length = S.c.tr.length → k ≤ S.c.tr.length →
    SilOrd2.srcLatestAt G Lw S.c k b t →
    SilOrd2.srcLatestAt G (Lw ++ [e]) (SilWalk.snoc S x lb o pC' d' w').c k b t := by
  intro hsl hk h
  have hst := SilWalk.stAtSnoc S x lb o pC' d' w' hsl
  rcases h with ⟨h0, hl⟩ | ⟨j, s, sp, hjk, hs, hLj, hsp, hW, hl⟩
  · exact .inl ⟨h0, by rw [hst k hk]; exact hl⟩
  · have hjL : j < Lw.length := lookup_lt_Some hLj
    refine .inr ⟨j, s, sp, hjk, hs, by rw [List.getElem?_append_left hjL]; exact hLj,
      by rw [SilOrd2.projSnoc S x lb o pC' d' w' j hsl (by omega)]; exact hsp, hW, ?_⟩
    rw [hst k hk, hst j (by omega)]
    exact hl

/-- **THE GATED TWIN POLICY** from NoStuck and the gated datum ([OWN.106]: no order premise — the walk
picks an ENABLED next event and appends it to the realized list; the record grows with it). -/
theorem SilOrd2.walkPolG (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (GF : Gfexec)
    (D : Nat → CertZ7.EmData) (Lb : Int → Prop) (pin : Geid → Prop) (Rel : CertZ9.HRel) :
    CertZ7.emDataOk boot fab GF D → GF.gfDev.Nodup →
    (∀ (x n : Nat) (lb : Lbl), (GF.gfGd.gdG.gxProg.getD x [])[n]? = some lb → CertZ4.lblShape lb) →
    SilOrd2.noStuckG d0 GF.gfGd.gdG GF.gfDev fab Lb pin →
    SilOrd2.hartStepG d0 GF.gfGd.gdG GF.gfDev Lb pin Rel →
    SilWalk.walkPol d0 GF.gfGd.gdG.gxProg Lb
      (SilOrd.inv GF.gfGd.gdG.gxProg Lb (fun x => (D x).f) Rel
        (SilOrd2.prefG GF.gfGd.gdG GF.gfDev fab Lb)) := by
  intro hD hdnd hshape hns hstep S cnt hok hinv hnd
  obtain ⟨hper, hagt, ⟨Lw, hW⟩⟩ := hinv
  obtain ⟨hcnt, hlt, hall, hnodup, hfab, hags, hdevlt, hpo, hdvo, hrec⟩ := id hW
  obtain ⟨x, hx, hcx, henb⟩ :=
    hns S cnt Lw hok hW (fun y hy => ⟨(hper y hy).1, (hper y hy).2.2⟩) hagt hnd
  obtain ⟨lb, hlb⟩ : ∃ lb, (GF.gfGd.gdG.gxProg.getD x [])[cnt x]? = some lb :=
    ⟨_, List.getElem?_eq_getElem hcx⟩
  obtain ⟨-, ⟨pC, hp, hrel⟩, -⟩ := hper x hx
  obtain ⟨em, -, hiff, hpin, -, -, hblk⟩ := hD x _ (CertZ7.getDSome _ x hx)
  have hnew : (x, cnt x) ∉ Lw := fun h => by have := hlt _ h; dsimp only at this; omega
  have hB : ∃ d', (((lbFused ((D x).r (cnt x)) ∧
      GraphFetchBlocks.blkOne (S.dv S.c.tr.length) d'
        (rowWsAux 0 wsInit ((GF.gfGd.gdG.gxProg.getD x []).take (cnt x))) lb ((D x).g (cnt x))
        ((D x).r (cnt x)) ((D x).f (cnt x)) ((D x).f (cnt x + 1))) ∨
      GraphFetchBlocks.blkPair (S.dv S.c.tr.length) d'
        (rowWsAux 0 wsInit ((GF.gfGd.gdG.gxProg.getD x []).take (cnt x))) lb ((D x).g (cnt x))
        ((D x).r (cnt x)) ((D x).f (cnt x)) ((D x).f (cnt x + 1))) ∧
      d' = fab (((Lw ++ [(x, cnt x)]).filter (fun e => decide (e ∈ GF.gfDev))).length)) := by
    rw [CertZ8.filterSnoc]
    by_cases htq : (D x).tq (cnt x) = true
    · have hin : (x, cnt x) ∈ GF.gfDev := (hiff _ hcx).2 (.inr (.inr htq))
      have hm := henb.1 hin
      have hD0 : (D x).dvi (cnt x) = S.dv S.c.tr.length := by
        rw [hfab]; exact (hpin _ _ hm).1
      refine ⟨(D x).dvo (cnt x), ?_, ?_⟩
      · rw [← hD0]
        rcases hblk (cnt x) lb hlb with ⟨hfu, h1, -⟩ | ⟨h1, -⟩
        · exact .inl ⟨hfu, h1⟩
        · exact .inr h1
      · rw [if_pos (decide_eq_true hin)]
        exact (hpin _ _ hm).2
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
        ((GF.gfGd.gdG.gxProg.getD y []).take ((Lw.filter (fun e => decide (e.1 = y))).length))
        (SilWalk.hartPr (SilOrd.pairs S) y) := by
    intro y hy
    rw [← hcnt y]
    exact (hper y hy).2.2
  obtain ⟨lb', o, pa, da, ls', pC', w', hre, hok', hrel'⟩ :=
    hstep S Lw x (cnt x) lb _ _ _ _ _ pC d'
      ⟨hok, hp, hrel, hshape x _ lb hlb, hblkD, hags, hcnt x, hperF, hlb, henb⟩
  have hsl : S.c.sil.length = S.c.tr.length := hok.1
  have hlenL : S.c.tr.length = Lw.length := by
    have := congrArg List.length hags
    simpa using this
  have hcntS : ∀ y, CertZ2.bump cnt x y =
      ((Lw ++ [(x, cnt x)]).filter (fun e => decide (e.1 = y))).length := by
    intro y
    rw [CertZ8.filterSnoc]
    by_cases hy : y = x
    · subst hy; rw [CertZ2.bumpSelf, hcnt y]; simp
    · rw [CertZ2.bumpNe cnt x y hy, hcnt y]
      simp [Ne.symm hy]
  have hdevS : ((Lw ++ [(x, cnt x)]).filter (fun e => decide (e ∈ GF.gfDev))).length =
      (Lw.filter (fun e => decide (e ∈ GF.gfDev))).length +
        (if decide ((x, cnt x) ∈ GF.gfDev) then 1 else 0) := CertZ8.filterSnoc _ _ _
  refine ⟨x, lb, hx, hlb, lb', o, pC, pa, da, ls', pC', d', w', hp, hre, hok',
    ⟨fun y hy => ?_, fun s hs => ?_, Lw ++ [(x, cnt x)], hcntS, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_⟩⟩
  · obtain ⟨hle, ⟨pCy, hpy, hrely⟩, hfy⟩ := hper y hy
    rw [SilOrd.snocPstEnd, SilOrd.pairsSnoc _ _ _ _ _ _ _ hsl, SilOrd.hartPrSnoc]
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
  · intro e he
    rcases List.mem_append.1 he with he | he
    · have := hlt e he
      by_cases h : e.1 = x
      · rw [h, CertZ2.bumpSelf]; rw [h] at this; omega
      · rw [CertZ2.bumpNe cnt x e.1 h]; exact this
    · simp only [List.mem_singleton] at he
      rw [he]
      show cnt x < CertZ2.bump cnt x x
      rw [CertZ2.bumpSelf]
      omega
  · intro y a ha
    by_cases hy : y = x
    · subst hy
      rw [CertZ2.bumpSelf] at ha
      by_cases hac : a = cnt y
      · subst hac
        exact List.mem_append_right _ (List.mem_singleton_self _)
      · exact List.mem_append_left _ (hall y a (by omega))
    · rw [CertZ2.bumpNe cnt x y hy] at ha
      exact List.mem_append_left _ (hall y a ha)
  · rw [List.nodup_append]
    refine ⟨hnodup, by simp, ?_⟩
    intro a ha b hb hab
    simp only [List.mem_singleton] at hb
    subst hb
    subst hab
    exact hnew ha
  · rw [SilOrd.snocDvEnd]
    exact hd'
  · show (S.c.tr ++ [(⟨x, lb'⟩ : Estep)]).map Estep.esAg = (Lw ++ [(x, cnt x)]).map Prod.fst
    rw [List.map_append, List.map_append, hags]
    rfl
  · intro m e hm he
    rw [hdevS]
    rcases List.mem_append.1 he with he | he
    · have := hdevlt m e hm he
      split <;> omega
    · simp only [List.mem_singleton] at he
      subst he
      have hin : (x, cnt x) ∈ GF.gfDev := List.mem_of_getElem? hm
      have := NoDup_lookup hdnd hm (henb.1 hin)
      rw [if_pos (decide_eq_true hin)]
      omega
  · intro i j y a b hi hj hab
    rcases SilOrd2.snocLookup Lw _ _ i hi with ⟨hiL, hi'⟩ | ⟨hie, hiv⟩ <;>
      rcases SilOrd2.snocLookup Lw _ _ j hj with ⟨hjL, hj'⟩ | ⟨hje, hjv⟩
    · exact hpo i j y a b hi' hj' hab
    · omega
    · simp only [Prod.mk.injEq] at hiv
      obtain ⟨rfl, rfl⟩ := hiv
      have := hlt _ (List.mem_of_getElem? hj')
      dsimp only at this
      omega
    · simp only [Prod.mk.injEq] at hiv hjv
      omega
  · intro m n i j e e' hm hn hmn hi hj
    rcases SilOrd2.snocLookup Lw _ _ i hi with ⟨hiL, hi'⟩ | ⟨hie, hiv⟩ <;>
      rcases SilOrd2.snocLookup Lw _ _ j hj with ⟨hjL, hj'⟩ | ⟨hje, hjv⟩
    · exact hdvo m n i j e e' hm hn hmn hi' hj'
    · omega
    · subst hiv
      have hin : (x, cnt x) ∈ GF.gfDev := List.mem_of_getElem? hm
      have h1 := NoDup_lookup hdnd hm (henb.1 hin)
      have h2 := hdevlt n e' hn (List.mem_of_getElem? hj')
      omega
    · subst hiv hjv
      have := NoDup_lookup hdnd hm hn
      omega
  · intro k e b t hk hacq
    rcases SilOrd2.snocLookup Lw _ _ k hk with ⟨hkL, hk'⟩ | ⟨hke, hkv⟩
    · exact SilOrd2.srcLatestSnoc _ Lw _ S x lb' o pC' d' w' k b t hsl (by omega)
        (hrec k e b t hk' hacq)
    · subst hkv
      rw [hke, ← hlenL]
      exact SilOrd2.srcLatestSnoc _ Lw _ S x lb' o pC' d' w' _ b t hsl (Nat.le_refl _)
        (henb.2.1 b t hacq)

/-! # 6. The complete gated walk: the walk order, the record at the member, the cert supply, the kill -/

/-- A COMPLETE gated walk's realized list IS a walk order of the rows (each event once, each hart in
program order, the fabric in fabric order) — the order was built step by step, never assumed. -/
theorem SilOrd2.walkOrdOfDone (G : Gexec) (dev : List Geid) (fab : Nat → Efab) (L : Int → Prop)
    (S : SilWalk.St) (cnt : Nat → Nat) (Lw : List Geid) :
    SilOrd2.prefW G dev fab L S cnt Lw → (∀ s, s ∈ S.c.tr → s.esAg < G.gxProg.length) →
    (∀ x, x < G.gxProg.length → cnt x ≤ (G.gxProg.getD x []).length) →
    (∀ x, x < G.gxProg.length → (G.gxProg.getD x []).length ≤ cnt x) →
    CertZ8.walkOrd G.gxProg dev Lw := by
  rintro ⟨-, hlt, hall, hnodup, -, hags, -, hpo, hdvo, -⟩ hagt hle hge
  refine ⟨hnodup, fun e => ⟨fun he => ?_, fun he => ?_⟩, hpo, hdvo⟩
  · have hm : e.1 ∈ S.c.tr.map Estep.esAg := by rw [hags]; exact List.mem_map_of_mem he
    obtain ⟨s, hs, hse⟩ := List.mem_map.1 hm
    have h1 : e.1 < G.gxProg.length := by have := hagt s hs; rw [hse] at this; exact this
    have := hlt e he
    have := hle e.1 h1
    exact ⟨h1, by omega⟩
  · obtain ⟨x, a⟩ := e
    obtain ⟨h1, h2⟩ := he
    have := hge x h1
    exact hall x a (by dsimp only at h2; omega)

/-- **THE RECORD AT THE COMPLETE MEMBER** from the walk's record: a successful acquire's `GF` source
is the write whose message was the latest of its byte when the acquire's message was appended. -/
theorem SilOrd2.recLogOfTr (G : Gexec) (dev : List Geid) (P : Int → Int → Prop) (N : Nat)
    (c : SilCand.CandS) (Lw : List Geid) :
    CertZ8.walkOrd G.gxProg dev Lw → c.tr.map Estep.esAg = Lw.map Prod.fst →
    (∀ s, s ∈ c.tr → s.esAg < N) → gwf (SilAgree.memberS N c) →
    SilOrd2.agreeW4N G (SilAgree.memberS N c) (GraphFetchN2.lockBytes P) →
    SilOrd2.recTr G (GraphFetchN2.lockBytes P) Lw c →
    SilOrd2.amoRecLog G (SilAgree.memberS N c) (SilAgree.logS c) P := by
  intro hord hags hagN hwfR hag hrec a b n0 r0 h hP _ _ _ A t hacqR _ hrd
  obtain ⟨va, hva, hvane⟩ := hacqR
  have hagP := SilCand.projAg c N hagN
  have hagsP : (SilCand.proj c).cdTr.map Estep.esAg = Lw.map Prod.fst := by
    rw [SilOrd.projAgs, hags]
  have hAw : A ∈ gwrites (SilAgree.memberS N c) :=
    gwritesByteGwrites _ A b va hwfR hva
  have hAw' := hAw
  rw [SilAgree.memberS, CertZ3.memberGwrites N _ hagP] at hAw'
  obtain ⟨hgmo, -⟩ := (gwritesElemOf _ _).1 hAw'
  obtain ⟨k, sk, hk, -, hAk⟩ := cgSurj (candExec (SilCand.proj c)) A hgmo
  have hkP : k < (SilCand.proj c).cdTr.length := lookup_lt_Some hk
  have hkL : k < Lw.length := by
    have := congrArg List.length hagsP
    simp only [List.length_map] at this
    omega
  obtain ⟨e, he⟩ : ∃ e, Lw[k]? = some e := ⟨_, List.getElem?_eq_getElem hkL⟩
  obtain ⟨sk', hk', -, hce⟩ := CertZ8.ceidOrd G.gxProg dev Lw (SilCand.proj c) k e hord hagsP he
  have heA : e = A := hce.symm.trans hAk.symm
  rw [heA] at he
  have hnf : CertZ24.nf G (GraphFetchN2.lockBytes P) A := hag.2.2.1 A b va hva
  have hvaG : gwritesByte G A b va := hag.2.1 A b va hva
  have hsrc := hrec k A b t he ⟨⟨a, hP⟩, hnf, ⟨va, hvaG, hvane⟩, hrd⟩
  -- the member label at `A` is the projected step's, a write
  have hlblA : gxLbl (SilAgree.memberS N c) A = some sk'.esLb := by
    rw [SilAgree.memberS, CertZ3.memberLbl N _ A hagP, hAk]
    exact (cgLbl _ k sk' hk').1
  have hW : lbIsW sk'.esLb = true := by
    obtain ⟨l, base, vs, j, hl, hwr, -, -⟩ := hva
    rw [hlblA, Option.some.injEq] at hl
    rw [hl]
    exact lbWrIsW _ _ hwr
  have hgix : gwix (SilAgree.memberS N c) A = (cdLog (SilCand.proj c) k).length + 1 := by
    rw [SilAgree.memberS, CertZ3.memberGwix N _ A hagP, hAk]
    exact SilMember.cgWixC _ k sk' hk' hW
  have hklen : k ≤ c.tr.length := by rw [← SilCand.projLen]; omega
  obtain ⟨hlogk, himgk⟩ := SilCand.projLog c k hklen
  have htake : (SilAgree.logS c).take (gwix (SilAgree.memberS N c) A - 1) =
      (SilCand.stAt c k).msLog := by
    obtain ⟨l, hl⟩ := cdLogSplit (SilCand.proj c) k (SilCand.proj c).cdTr.length (by omega)
    rw [hgix, Nat.add_sub_cancel, SilAgree.logS, hl, ← hlogk]
    exact List.take_left' rfl
  have himgR : (SilAgree.memberS N c).gxImg = (SilCand.stAt c k).msImg := by
    rw [himgk]; rfl
  rcases hsrc with ⟨rfl, hl0⟩ | ⟨j, s, sp, hjk, hs, hLj, hsp, hWs, hl⟩
  · exact ⟨0, by rw [htake, himgR]; exact hl0, .inl ⟨rfl, rfl⟩⟩
  · obtain ⟨sp', hsp', -, hcej⟩ := CertZ8.ceidOrd _ dev Lw (SilCand.proj c) j s hord hagsP hLj
    rw [hsp, Option.some.injEq] at hsp'
    subst hsp'
    have hgixs : gwix (SilAgree.memberS N c) s = (cdLog (SilCand.proj c) j).length + 1 := by
      rw [SilAgree.memberS, CertZ3.memberGwix N _ s hagP, ← hcej]
      exact SilMember.cgWixC _ j sp hsp hWs
    have hsW : s ∈ gwrites (SilAgree.memberS N c) := gwixPosElem _ s (by omega)
    obtain ⟨hlogj, -⟩ := SilCand.projLog c j (by omega)
    refine ⟨(SilCand.stAt c j).msLog.length + 1, by rw [htake, himgR]; exact hl, .inr ⟨s, hs, ?_⟩⟩
    rw [← hlogj, ← hgixs]
    exact gwriteAtGwix _ s hsW

namespace CatLin

/-- **NoStuck (row 6l, PENDING R44 — NAMED)**: on every class graph, at every gated walk state with work
left, some hart's next row event is ENABLED (`SilOrd2.enb`).  Its proof needs the pre-registration
publication fact of Q-6L-REG (F6l-2: a successful acquire's `GF` source co-≥ the byte's registration
write; `regBeforeAmo`, advisor's R44) besides cat, `prefixDiscS` and the per-site hop facts; it stays
named until R44 answers. -/
def SilOrd2.noStuck (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image)
    (P : Int → Int → Prop) (pin : Gfexec → Geid → Prop) : Prop :=
  ∀ (GF : Gfexec) (ad : List (Geid × Geid)) (z : Geid) (ss : List Seg),
    GF.gfGd.gdG.gxImg = im → rvwmoCatAD GF.gfGd ad → GraphFabConf.gfexecConfZF boot d0 fab GF →
    ioResidueGmo GF → gdiskRead14 GF.gfGd.gdG →
    ss ≠ [] → rawChainC GF.gfGd (ioCross GF) z z ss →
    SilOrd2.noStuckG d0 GF.gfGd.gdG GF.gfDev fab (GraphFetchN2.lockBytes P) (pin GF)

/-- **THE GATED STEP SUPPLY (row 6m, named)**: `SilOrd.stepSupplyS` with the gated datum (no order). -/
def SilOrd2.stepSupplyG (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image)
    (P : Int → Int → Prop) (pin : Gfexec → Geid → Prop) : Prop :=
  ∀ (GF : Gfexec) (ad : List (Geid × Geid)) (z : Geid) (ss : List Seg),
    GF.gfGd.gdG.gxImg = im → rvwmoCatAD GF.gfGd ad → GraphFabConf.gfexecConfZF boot d0 fab GF →
    ioResidueGmo GF → gdiskRead14 GF.gfGd.gdG →
    ss ≠ [] → rawChainC GF.gfGd (ioCross GF) z z ss →
    ∀ D : Nat → CertZ7.EmData, CertZ7.emDataOk boot fab GF D →
    ∃ Rel : CertZ9.HRel,
      (∀ x, x < GF.gfGd.gdG.gxProg.length → Rel x 0 (boot x) (boot x)) ∧
      SilOrd2.hartStepG d0 GF.gfGd.gdG GF.gfDev (GraphFetchN2.lockBytes P) (pin GF) Rel

/-- **THE CERT SUPPLY WITH THE RECORD, FROM THE GATED WALK** (no order premise, no acyclicity
assumption): the realized member, its silent agreement and the gate's record. -/
theorem SilOrd2.certSupplyOfGate (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image)
    (N : Nat) (P : Int → Int → Prop) (pin : Gfexec → Geid → Prop) :
    (∀ (GF : Gfexec) (ad : List (Geid × Geid)), GF.gfGd.gdG.gxImg = im → rvwmoCatAD GF.gfGd ad →
      GraphFabConf.gfexecConfZF boot d0 fab GF →
      GF.gfGd.gdG.gxProg.length ≤ N ∧ GraphFetchBlocks.emPremOk boot GF.gfGd.gdG) →
    SilOrd2.noStuck boot d0 fab im P pin → SilOrd2.stepSupplyG boot d0 fab im P pin →
    SilOrd2.certSupplyRS boot d0 fab im N P := by
  intro hpre hns hstep GF ad _ z ss him hc hconf hres hdr _ _ _ _ _ hne hch
  obtain ⟨hN, hp2⟩ := hpre GF ad him hc hconf
  obtain ⟨D, hD⟩ := CertZ7.emDataOfConf boot d0 fab GF hconf hp2
  obtain ⟨Rel, hR0, hsR⟩ := hstep GF ad z ss him hc hconf hres hdr hne hch D hD
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
  have hpol := SilOrd2.walkPolG boot d0 fab GF D _ (pin GF) Rel hD hconf.2.1 hshape
    (hns GF ad z ss him hc hconf hres hdr hne hch) hsR
  have hI0 : SilOrd.inv GF.gfGd.gdG.gxProg (GraphFetchN2.lockBytes P) (fun x => (D x).f) Rel
      (SilOrd2.prefG GF.gfGd.gdG GF.gfDev fab (GraphFetchN2.lockBytes P))
      (SilWalk.start boot d0 N GF.gfGd.gdG) (fun _ => 0) := by
    refine ⟨fun x hx => ⟨Nat.zero_le _, ⟨boot x, ?_, ?_⟩, ?_⟩, fun s hs => by
      simp [SilWalk.start] at hs, [], fun x => by simp, fun e he => by simp at he,
      fun x a ha => absurd ha (Nat.not_lt_zero _), List.nodup_nil, ?_, by simp [SilWalk.start],
      fun m e _ he => by simp at he, fun i j x a b hi => by simp at hi,
      fun m n i j e e' _ _ _ hi => by simp at hi, fun k e b t hk => by simp at hk⟩
    · show ((List.range' 0 N).map boot)[x]? = some (boot x)
      rw [List.getElem?_map, lookup_seq_lt (by omega), Nat.zero_add]
      rfl
    · obtain ⟨_, _, _, _, _, hf0, _⟩ := hD x _ (CertZ7.getDSome _ x hx)
      show Rel x 0 ((D x).f 0) (boot x)
      rw [hf0]
      exact hR0 x hx
    · simp [SilOrd.pairs, SilWalk.start, SilWalk.hartPr]
    · show d0 = fab _
      simp only [List.filter_nil, List.length_nil]
      exact hconf.1.symm
  obtain ⟨Sf, cntF, pr, hokF, hinvF, hdone, -, htr, hsil, hf2, -, himg, hpst⟩ :=
    SilWalk.walkRun d0 GF.gfGd.gdG.gxProg _ _ hpol _ (SilWalk.start boot d0 N GF.gfGd.gdG)
      (fun _ => 0) (Nat.le_refl _) (SilWalk.okStart boot d0 N GF.gfGd.gdG) hI0
  have hrd : SilAgree.RunDataS boot d0 N GF.gfGd.gdG Sf.c Sf.pst Sf.dv :=
    SilWalk.runDataOfOk boot d0 N GF.gfGd.gdG Sf hokF himg hpst
  have htr' : Sf.c.tr = pr.map Prod.fst := by rw [htr]; rfl
  have hsil' : Sf.c.sil = pr.map Prod.snd := by rw [hsil]; rfl
  have hprojTr : (SilCand.proj Sf.c).cdTr = pr.map (fun p => SilCand.projStep p.1 p.2) := by
    show Sf.c.tr.mapIdx (fun k s => SilCand.projStep s (Sf.c.sil.getD k none)) = _
    rw [htr', hsil']
    exact SilWalk.projMapIdx pr
  have himgR : (SilAgree.memberS N Sf.c).gxImg = GF.gfGd.gdG.gxImg := himg
  have hagr : SilAgree.lblAgreeS GF.gfGd.gdG (SilAgree.memberS N Sf.c) (fun t => t)
      (GraphFetchN2.lockBytes P) := by
    refine SilWalk.lblAgreeOfRows _ N _ Sf.c (SilCand.projAg Sf.c N (SilAgree.runAg hrd))
      (fun x => ?_)
    rw [hprojTr, SilWalk.hartTrProj]
    have hfx := hf2 x
    simp only [List.drop_zero, Nat.sub_zero] at hfx
    have hrow : (GF.gfGd.gdG.gxProg.getD x []).take (cntF x) = GF.gfGd.gdG.gxProg.getD x [] := by
      by_cases hx : x < GF.gfGd.gdG.gxProg.length
      · exact List.take_of_length_le (hdone x hx)
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; simp
    rw [hrow] at hfx
    exact SilWalk.forall₂Map _ _ _ _ _ hfx (fun a b h => SilWalk.relSOfW _ a b h)
  obtain ⟨hper, hagt, Lw, hW⟩ := hinvF
  have hord := SilOrd2.walkOrdOfDone _ _ _ _ Sf cntF Lw hW hagt (fun x hx => (hper x hx).1) hdone
  obtain ⟨hwfR, -, -, -, -⟩ := SilAgree.memberFacts hrd
  refine ⟨Sf.c, Sf.pst, Sf.dv, fun t => t, hrd, himgR, hagr, ?_⟩
  exact SilOrd2.recLogOfTr _ GF.gfDev P N Sf.c Lw hord hW.2.2.2.2.2.1 (SilAgree.runAg hrd) hwfR
    (SilOrd2.agreeW4NOfS _ _ _ _ himgR hagr) hW.2.2.2.2.2.2.2.2.2

section glue

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode
open Language.Notation PrimStep
open LeanRV64D

/-- **THE TRIMMED TWIN KILL FROM THE GATED WALK** ([OWN.106], [OWN.108]) — no walk order, no
`lockDiscCZ3`/`orderSupplyCZ3`, no GF-level `oneByteS`, no `SilOrd.stepSupplyS`: the twin WP packages
(the footprint with the zero in it), the fetch view, (harts ≤ N ∧ P2), the NAMED `noStuck` (row 6l,
pending R44), the gated step supply (row 6m), the lock facts (row 6f) and the L2′ claim (row 6n) at the
record agreement. -/
theorem SilOrd2.cycleKillGZ (hlc : HasLC) (GF0 : BundledGFunctors) [MachGpreS hlc GF0]
    [WeakGpreS GF0] (gen : Nat) (σ0 : WGState) (D : CPU → List Register) (hD : ∀ c, (D c).Nodup)
    (Nm : Int → Int → Namespace) (P : Int → Int → Prop) (pin : Gfexec → Geid → Prop)
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
    SilOrd2.noStuck boot d0 fab (imgZ σ0.wgimg) P pin →
    SilOrd2.stepSupplyG boot d0 fab (imgZ σ0.wgimg) P pin →
    SilOrd2.acqAqRS boot d0 fab (imgZ σ0.wgimg) N P →
    SilOrd2.relCoversRS boot d0 fab (imgZ σ0.wgimg) N P →
    SilOrd2.l2ClaimRS boot d0 fab (imgZ σ0.wgimg) N P (SilKill.badRunS gen σ0) →
    cycleKillCZT boot d0 fab (imgZ σ0.wgimg) :=
  fun hfr hb1 hb2 hwp hwpz hcov hpre hns hstep hAQ hRC hl2 =>
    SilOrd2.cycleKillCoreW gen σ0 P boot d0 fab N hfr hb1 hb2
      (SilKill.noBadRunS hlc GF0 gen σ0 D hD hfr hwp) hcov
      (fun _ _ _ _ _ _ t2 σ2 _ _ _ _ _ hrtc hlg => by
        rw [← hlg]
        exact SilRegZero.protRegZOfRunS hlc GF0 gen σ0 D hD Nm P t2 σ2 hfr hwpz hrtc)
      (cutSupplyOfCycleCZC boot d0 fab _)
      (SilOrd2.certSupplyOfGate boot d0 fab _ N P pin hpre hns hstep)
      hAQ hRC hl2

end glue

end CatLin

end Weak
