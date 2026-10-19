/-
Weak: **allocproc route P, increment P-W4 — THE KILL GLUE at the `SbCand` member** (plan rev 55 row
P-W4; design `notes/weak-allocproc-routeP-design.md` §3.5 "`SilKillT.cycleKillCore` → REWRITTEN once
for `SbCand`"; coordinator rulings F-6b′-1 → (A) the CLASS-BLIND lock transport, F-P-W2-2 (no
`gwrowGmo` at the P member), F-P-W2-3 (no `agreeW4` at real lock sets: full co via `agreeX`)).
Lean-only, no Rocq twin.

  §1  **THE CLASS-BLIND REGISTRY (A)**: `SbKill.wlockShapedB`/`wlpAtB` (`wlpAt` without the class
      clause `m.wmAk ≠ .WCplain`, which a release `sw` re-tagged `.WCplain` by the walker's A/D
      write-back breaks, F-6b′-1 (i)), `SbKill.protRegZB`, `SbKill.acqAqLogB`/`relCoversLogB`,
      `SbKill.lockRealB` (LockFacts2's interface at `wlpAtB`) and the two lock facts at the P member
      `SbKill.acqAqLogOfRealX`/`relCoversLogOfRealX` (`LockFacts2`'s proofs over `agreeX`: absorbs
      row 6f).
  §2  **`SbKill.csChainedTP`** — `CatLin.csChainedT4` at the P member: FULL co (`agreeX`'s third
      clause) replaces `lockCoSP`, so `CertZ14.np`/`sp`/`npAt4` and the `wlpAt` window are gone
      (F-6b′-1 (ii)); the two program-order facts route T read off `gwrowGmo GR` (`poOfRowR4`) come
      from the NAMED member interface **`SbKill.csIssue`** (finding F-P-W4-1: the P member's log is
      LANDING order, so they are issue-order facts of the realized run, not RVWMO ppo).
  §3  `SbKill.csHypsP` (`csHypsR2` without the section release's `np`, F-6b′-1 (ii)),
      `SbKill.csHypsCertCP`, `SbKill.l2ClaimAtP`, `SbKill.rawChainChainP`.
  §4  **THE KILL CORE `SbKill.cycleKillCoreP` → `CatLin.cycleKillCZT`**: the cycle's segments, the
      gated walk's member (`SbOrd.memberOfCat` under the value gate), the chain, `cycleKillIOC`.  Its
      named inputs: `SbKill.walkHypCZ` (image facts, device-row store order, the exempt reads),
      `SbKill.stateIfcCZ` (`HeadOrdRd`, `IrefTop` at every reachable state), `SbKill.memberRunCZ`
      (`protRegZB`, `lockRealB`, `csIssue` at every finished member — the export / realization,
      P-W5/P-W6/6j), `SbKill.l2ClaimP` (the L2′ classification at every finished member, with
      `provAll`, row 6n) and `¬ Bad`; plus `CatLin.gfDevWIoCZ` and the boot's hart rows.
      `SbKill.certSupplyP` (the member, any finished walk) is PROVED (`SbKill.certSupplyOfWalkP`).

Spec: FAITHFUL (proof organisation over riscv.cat's rules 4/5, co/rf ⊆ gmo, the trusted residue).
The named inputs are FAITHFUL statements (true of xv6 runs as far as checked) and WEAKER while named.
Lean-only helpers `SbKill.*`.
-/
import Weak.CapFetchProv
import Weak.SbOrdWalk
import Weak.LockFacts3
import Weak.CertZ25

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open TsoShadow
open Lbl SbWalk SbAgree SbReplay SbOrd

/-! # 1. The class-blind registry -/

/-- `wlockShaped` without the class clause: four bytes, exclusive or the zero word. -/
def SbKill.wlockShapedB (m : Wmsg) : Prop :=
  m.wmData.length = 4 ∧ (m.wmAk = .WCexcl ∨ m.wmData = wlockZero4)

/-- **`wlpAt` WITHOUT THE CLASS CLAUSE** (F-6b′-1 (A)). -/
def SbKill.wlpAtB (log : List Wmsg) (a base : Int) (n0 : Nat) : Prop :=
  (base ≤ a ∧ a < base + 4) ∧
  ∀ p m, log[p]? = some m → n0 ≤ p → (msgByte m a).isSome → m.wmPa = base ∧ SbKill.wlockShapedB m

theorem SbKill.wlpAtBOf (log : List Wmsg) (a base : Int) (n0 : Nat) :
    wlpAt log a base n0 → SbKill.wlpAtB log a base n0 :=
  fun ⟨h1, h2⟩ => ⟨h1, fun p m hp hn hs =>
    let ⟨hb, hl, _, he⟩ := h2 p m hp hn hs; ⟨hb, hl, he⟩⟩

/-- `CertZ18.protRegZ` at `wlpAtB`. -/
def SbKill.protRegZB (P : Int → Int → Prop) (img : Image) (log : List Wmsg) : Prop :=
  ∀ a base, P a base →
    ∃ (n0 r0 : Nat) (h : Option Nat),
      wprotAt log a base n0 r0 ∧ SbKill.wlpAtB log base base n0 ∧ wlpAlt log base n0 h ∧
      CertZ18.regZeroAt img log base n0

theorem SbKill.protRegZBOf (P : Int → Int → Prop) (img : Image) (log : List Wmsg) :
    CertZ18.protRegZ P img log → SbKill.protRegZB P img log := fun h a base hP =>
  let ⟨n0, r0, hh, h1, h2, h3, h4⟩ := h a base hP
  ⟨n0, r0, hh, h1, SbKill.wlpAtBOf _ _ _ _ h2, h3, h4⟩

/-- `acqAqLog` at `wlpAtB`. -/
def SbKill.acqAqLogB (G GR : Gexec) (log : List Wmsg) (P : Int → Int → Prop) : Prop :=
  ∀ a b n0 r0 h, P a b → wprotAt log a b n0 r0 → SbKill.wlpAtB log b b n0 → wlpAlt log b n0 h →
    CatLin.acqAqB G GR log b n0

/-- `relCoversLog` at `wlpAtB`. -/
def SbKill.relCoversLogB (G GR : Gexec) (log : List Wmsg) (P : Int → Int → Prop) : Prop :=
  ∀ a b n0 r0 h, P a b → wprotAt log a b n0 r0 → SbKill.wlpAtB log b b n0 → wlpAlt log b n0 h →
    CatLin.relCoversB G GR log b n0

/-- **`LockFacts2.lockReal` at `wlpAtB` (NAMED, the realization's; header (L1)–(L3) of
`Weak/LockFacts2.lean`).** -/
def SbKill.lockRealB (GR : Gexec) (log : List Wmsg) (P : Int → Int → Prop) : Prop :=
  ∃ ipc : Geid → Int,
    (∀ a b n0 r0 h, P a b → wprotAt log a b n0 r0 → SbKill.wlpAtB log b b n0 → wlpAlt log b n0 h →
      ∀ W v, CatLin.GraphFetchN2.inWin GR log n0 W → gwritesByte GR W b v →
        (ipc W = LockFacts.acqPc ∧ v ≠ lockFree) ∨ (ipc W = LockFacts.relPc ∧ v = lockFree)) ∧
    (∀ W, W ∈ gwrites GR → ipc W = LockFacts.acqPc →
      (∃ rl base ts rvs wvs k,
          gxLbl GR W = some (LRmw (wAmoAq (kw LockFacts.acqPc)) rl base ts rvs wvs k)) ∨
      (∃ l base vs, gxLbl GR W = some l ∧ lbWr l = some (base, vs) ∧ vs.length = 8)) ∧
    (∀ W, W ∈ gwrites GR → ipc W = LockFacts.relPc →
      ∃ kf, kf < W.2 ∧ gxLbl GR (W.1, kf) = some LockFacts2.relFenceLbl ∧
        ∀ k', kf < k' → k' < W.2 → ¬ glblIs GR (W.1, k') lbIsW)

/-! ## 1.1 Transfer along `agreeX` -/

theorem SbKill.isWX (G GR : Gexec) (X : Geid → Prop) (e : Geid) :
    agreeX G GR X → glblIs G e lbIsW → glblIs GR e lbIsW := by
  rintro ⟨-, hl, -⟩ ⟨l, hl0, hw⟩
  rcases hl e with ⟨h1, -⟩ | ⟨l1, l', h1, h2, hr⟩
  · rw [h1] at hl0; cases hl0
  · rw [h1, Option.some.injEq] at hl0
    subst hl0
    exact ⟨l', h2, by rw [relXIsW _ _ _ hr]; exact hw⟩

/-- An `.aq` read-write at the member is one at the class graph. -/
theorem SbKill.rmwAqOfX (G GR : Gexec) (X : Geid → Prop) (e : Geid) (rl : Bool) (base : Int)
    (ts : List Nat) (rvs wvs : List (BitVec 8)) (k : WmClass) :
    agreeX G GR X → gxLbl GR e = some (LRmw true rl base ts rvs wvs k) →
    glblIs G e lbIsR ∧ glblIs G e lbAq := by
  rintro ⟨-, hl, -⟩ hle
  rcases hl e with ⟨-, h2⟩ | ⟨l0, l', h1, h2, hr⟩
  · rw [h2] at hle; cases hle
  · rw [h2, Option.some.injEq] at hle
    subst hle
    rcases relXW _ _ _ hr (.inr rfl) with rfl | ⟨aq, rl', base', ts', ts'', rvs', wvs', kc, rfl, h, -⟩
    · exact ⟨⟨_, h1, rfl⟩, ⟨_, h1, rfl⟩⟩
    · simp only [LRmw.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact ⟨⟨_, h1, rfl⟩, ⟨_, h1, rfl⟩⟩

/-- A fence at the member is a fence at the class graph. -/
theorem SbKill.fenceAtX (G GR : Gexec) (X : Geid → Prop) (e : Geid) (pr pw sr sw : Bool) :
    agreeX G GR X → gxLbl GR e = some (LFence pr pw sr sw) →
    gxLbl G e = some (LFence pr pw sr sw) := by
  rintro ⟨-, hl, -⟩ hle
  rcases hl e with ⟨-, h2⟩ | ⟨l0, l', h1, h2, hr⟩
  · rw [h2] at hle; cases hle
  · rw [h2, Option.some.injEq] at hle
    subst hle
    rw [h1]
    rcases hr with ⟨-, h⟩ | ⟨-, h⟩
    · cases l0 <;> simp_all [lblReidx]
    · cases l0 <;> simp_all [lblReidxSub]

/-- **(1) `acqAq` at the P member** (`LockFacts2.acqAqLogOfReal` over `agreeX`). -/
theorem SbKill.acqAqLogOfRealX (G GR : Gexec) (X : Geid → Prop) (log : List Wmsg)
    (P : Int → Int → Prop) :
    agreeX G GR X → gwf GR → logOf GR log → SbKill.lockRealB GR log P →
    SbKill.acqAqLogB G GR log P := by
  rintro hag hwf hlog ⟨ipc, hL1, hL2, -⟩ a b n0 r0 h hP hprot hlp halt A ⟨v, hwA, hv⟩ hwin
  have hwA' := (agreeWrIff G GR X hag A b v).2 hwA
  rcases hL1 a b n0 r0 h hP hprot hlp halt A v hwin hwA' with ⟨hpc, -⟩ | ⟨-, hv0⟩
  · have hAw : A ∈ gwrites GR := gwritesByteGwrites GR A b v hwf hwA'
    rcases hL2 A hAw hpc with ⟨rl, base, ts, rvs, wvs, k, hl⟩ | ⟨l, base, vs, hl, hwr, hlen⟩
    · rw [LockFacts.acqAqBit] at hl
      exact SbKill.rmwAqOfX G GR X A rl base ts rvs wvs k hag hl
    · exfalso
      obtain ⟨m, hm, hgm⟩ := logOfWrite GR log A hwf hlog hAw hwin.2
      have hmb : (msgByte m b).isSome := by
        rw [(WeakRvwmoKillArms.gmsgByte GR A m b v hgm).2 hwA']; rfl
      obtain ⟨-, hsh⟩ := hlp.2 (gwix GR A - 1) m hm (by have := hwin.1; omega) hmb
      have hm' : m = ⟨base, vs, some A.1, lbCls l⟩ := by
        unfold WeakRvwmoKillArms.gmsg at hgm
        rw [hl] at hgm
        simp only [hwr, Option.some.injEq] at hgm
        exact hgm.symm
      have h4 := hsh.1
      rw [hm'] at h4
      simp only at h4
      omega
  · exact absurd hv0 hv

/-- **(2) `relCovers` at the P member** (`LockFacts2.relCoversLogOfReal` over `agreeX`). -/
theorem SbKill.relCoversLogOfRealX (G GR : Gexec) (X : Geid → Prop) (log : List Wmsg)
    (P : Int → Int → Prop) :
    agreeX G GR X → gwf GR → SbKill.lockRealB GR log P → SbKill.relCoversLogB G GR log P := by
  rintro hag hwf ⟨ipc, hL1, -, hL3⟩ a b n0 r0 h hP hprot hlp halt A R x _ hR _ hwinR _ hxR hxW
  have hR' := (agreeWrIff G GR X hag R b lockFree).2 hR
  rcases hL1 a b n0 r0 h hP hprot hlp halt R lockFree hwinR hR' with ⟨-, hne⟩ | ⟨hpc, -⟩
  · exact absurd rfl hne
  have hRw : R ∈ gwrites GR := gwritesByteGwrites GR R b lockFree hwf hR'
  obtain ⟨kf, hkf, hfl, hnone⟩ := hL3 R hRw hpc
  obtain ⟨hx1, hx2, -, -⟩ := hxR
  have hxW' := SbKill.isWX G GR X x hag hxW
  have hxk : x.2 < kf := by
    rcases Nat.lt_or_ge x.2 kf with hlt | hge
    · exact hlt
    · exfalso
      rcases Nat.lt_or_eq_of_le hge with hgt | heq
      · exact hnone x.2 hgt hx2 (by rw [← hx1]; exact hxW')
      · obtain ⟨l, hl, hw⟩ := hxW'
        have : gxLbl GR x = some LockFacts2.relFenceLbl := by
          rw [show x = (R.1, kf) from Prod.ext hx1 heq.symm]; exact hfl
        rw [this] at hl
        cases hl
        simp [LockFacts2.relFenceLbl, lbIsW] at hw
  have hfG := SbKill.fenceAtX G GR X (R.1, kf) _ _ _ _ hag hfl
  obtain ⟨-, hpw, -, hsw⟩ := LockFacts.relFenceBits.2
  refine ⟨wFencePr (kw (LockFacts.relPc - 4)), wFencePw (kw (LockFacts.relPc - 4)),
    wFenceSr (kw (LockFacts.relPc - 4)), wFenceSw (kw (LockFacts.relPc - 4)),
    ⟨hx1, by omega, kf, hxk, hkf, by rw [hx1]; exact hfG⟩,
    .inr ⟨hxW, hpw⟩, .inr ⟨gwritesByteGlblW G R b lockFree hR, hsw⟩⟩

/-! # 2. The chained critical section at the P member -/

/-- **THE ISSUE-ORDER CRITICAL SECTION (NAMED, F-P-W4-1; the realized run's)**: a protected write `x`
of a registered byte `a` (lock byte `b`) that LANDS inside a tenure of its own hart — the hart's
successful acquire `A` at log position `q`, no release of `b` in the log between — was ISSUED
po-after `A`, and po-before every later release of `b` by that hart.  In route T this was
`gwrowGmo GR` (the member's write order is program order, `CertZ24.poOfRowR4`); the P member's log
is LANDING order, and RVWMO's ppo does not give it (a store pending across a later `.aq` AMO of its
hart is legal; `PROGRESS` F-P-W4-1).  It is the buffered machine's: a protected store is issued
under the lock (the program logic's ownership at issue), the AMO lands at its issue, and the
tenure's release lands after every store of the tenure (its `fence rw,w` epoch).  FAITHFUL. -/
def SbKill.csIssue (P : Int → Int → Prop) (G GR : Gexec) (log : List Wmsg) (b : Int) (n0 : Nat) :
    Prop :=
  ∀ a r0 q A x vx, P a b → wprotAt log a b n0 r0 → r0 < gwix GR x → gwritesByte G x a vx →
    (∀ v, ¬ gwritesByte G x b v) → n0 ≤ q → q < gwix GR x - 1 → gwriteAt GR (q + 1) = some A →
    lockAcq G b A → A.1 = x.1 →
    (∀ r mr, q < r → r < gwix GR x - 1 → log[r]? = some mr → (msgByte mr b).isSome →
      mr.wmData ≠ wlockZero4) →
    WeakRvwmoGraph.gpo G A x ∧
    ∀ r R, gwix GR x - 1 < r → gwriteAt GR (r + 1) = some R → lockRel G b R → R.1 = x.1 →
      WeakRvwmoGraph.gpo G x R

/-- **`csChainedT4` AT THE P MEMBER** — full co (`agreeX`) for `lockCoSP`, no `np`/`sp`/`npAt4`/`wlpAt`,
the two program-order facts from `csIssue`. -/
theorem SbKill.csChainedTP (GD : Gdexec) (ad : List (Geid × Geid)) (GR : Gexec) (X : Geid → Prop)
    (P : Int → Int → Prop) (log : List Wmsg) (b a : Int) (n0 r0 : Nat) (h : Option Nat)
    (w entry exit ACQ REL : Geid) :
    CatLin.rvwmoCatAD GD ad → gwf GR → agreeX GD.gdG GR X → P a b →
    CertZ18.rmwLatest GR log → CertZ18.regZeroAt GR.gxImg log b n0 →
    CatLin.acqAqB GD.gdG GR log b n0 → CatLin.relCoversB GD.gdG GR log b n0 →
    SbKill.csIssue P GD.gdG GR log b n0 →
    logOf GR log → lockWordByte log b → wlpAlt log b n0 h →
    acqRow GD.gdG b ACQ →
    wprotAt log a b n0 r0 →
    (∃ v, gwritesByte GD.gdG w a v) → gcls GD.gdG w .WCplain →
    r0 < gwix GR w → gwix GR w ≤ log.length →
    (∀ v, ¬ gwritesByte GD.gdG w b v) →
    lockAcq GD.gdG b ACQ → glblIs GD.gdG ACQ lbAq →
    n0 < gwix GR ACQ → gwix GR ACQ ≤ log.length →
    lockCs GD.gdG b ACQ REL → WeakRvwmoGraph.gpo GD.gdG ACQ entry →
    gfenceCovers GD.gdG entry REL →
    gmoLt GD.gdG w entry → WeakRvwmoGraph.gpo GD.gdG ACQ exit → gmem GD.gdG exit →
    ACQ.1 ≠ w.1 →
    gmoLt GD.gdG w exit := by
  intro hcons hwfR hag hP hlat hz hAQ hRC hiss hlog hlwb halt hrow hpr hwa hcl hr0
    hlew hnob hacq haq hn0A hleA hcs _hpoe hfen hcross hpox hmx hhart
  have hRG : ∀ e a v, gwritesByte GR e a v → gwritesByte GD.gdG e a v :=
    fun e a v h => (agreeWrIff _ _ X hag e a v).1 h
  have hGR : ∀ e a v, gwritesByte GD.gdG e a v → gwritesByte GR e a v :=
    fun e a v h => (agreeWrIff _ _ X hag e a v).2 h
  have hcls := agreeClsW _ _ X hag
  have hagRd := agreeRmwRd _ _ X hag
  have hco := hag.2.2
  -- the reader's acquire is in the window
  obtain ⟨va, hva, hvane⟩ := id hacq
  have hvaR : gwritesByte GR ACQ b va := hGR ACQ b va hva
  have hAwR := lockAcqGwrites GR b ACQ hwfR ⟨va, hvaR, hvane⟩
  obtain ⟨mA, hmA, hgA⟩ := logOfWrite GR log ACQ hwfR hlog hAwR hleA
  have hbA := (WeakRvwmoKillArms.gmsgByte GR ACQ mA b va hgA).2 hvaR
  have hfreeA : wlpHolderAt log b n0 (gwix GR ACQ - 1) = some none := by
    obtain ⟨tA, hrdA⟩ := id hrow
    obtain ⟨tA', hrdA'⟩ := hagRd.1 ACQ b tA lockFree (gwritesByteGlblW _ ACQ b va hva) hrdA
    obtain ⟨hlA, hvA⟩ := hlat ACQ b tA' lockFree (gwritesByteGlblW GR ACQ b va hvaR) hrdA'
    exact CertZ18.foldFreeOfLatest GR.gxImg log b n0 h _ tA' hlwb halt (by omega) hlA hvA
  obtain ⟨hwf, h6, hlv, -, -, -, -, -⟩ := hcons
  generalize GD.gdG = G at *
  have hndR := hwfR.1
  obtain ⟨vw, hvw⟩ := hwa
  have hvwR : gwritesByte GR w a vw := hGR w a vw hvw
  have hwR : w ∈ gwrites GR := gwritesByteGwrites GR w a vw hwfR hvwR
  have hclR : gcls GR w .WCplain := hcls w _ hcl (gwritesByteGlblW G w a vw hvw)
  have hnobR : ∀ v, ¬ gwritesByte GR w b v := fun v hv => hnob v (hRG w b v hv)
  obtain ⟨q, mq, hq, hlk, hs, hnz, ht, hfree, hno, ACQw, hatw, hacqwR, hixw, hhw⟩ :=
    holderAcqGraph GR log b a n0 r0 w hwfR hlog hlwb hpr hwR hr0 hlew ⟨vw, hvwR⟩ hclR
  have hrA := acqRowIsR G b ACQ hrow
  have hmoAx : gmoLt G ACQ exit := CatLin.acqGmoAfterC G ACQ exit h6 hpox hrA haq hmx
  obtain ⟨vq, hvq, hvqne⟩ := id hacqwR
  have hvqG : gwritesByte G ACQw b vq := hRG ACQw b vq hvq
  have hacqw : lockAcq G b ACQw := ⟨vq, hvqG, hvqne⟩
  have hAwwR : ACQw ∈ gwrites GR := lockAcqGwrites GR b ACQw hwfR hacqwR
  obtain ⟨hpoAw, hpoR⟩ := hiss a r0 q ACQw w vw hP hpr hr0 hvw hnob hq.1 hq.2 hatw hacqw hhw
    (fun r mr h1 h2 => hno r mr ⟨h1, h2⟩)
  have hposA := WeakRvwmoGraph.gwixPos GR ACQ hAwR
  have hwinA : CatLin.GraphFetchN2.inWin GR log n0 ACQw := ⟨by omega, by omega⟩
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
    have hpowR : WeakRvwmoGraph.gpo G w R := hpoR r R (by omega) hatR hRG' hRh
    have hfc : gfenceCovers G w R :=
      hRC ACQw R w hacqw hRG' hwinA ⟨by omega, by omega⟩ hpoAw hpowR
        (gwritesByteGlblW G w a vw hvw)
    have h1 : gmoLt G w R := CatLin.fenceGmoAfterC G w R h6 hfc
    have h2 : gmoLt G R ACQ :=
      gwixLtGmo G R ACQ hwf (lockRelGwrites G b R hwf hRG') (lockAcqGwrites G b ACQ hwf hacq)
        ((hco b R ACQ lockFree va hRG' hva).2 (by omega))
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
    have hAR'G : gwix G ACQ < gwix G R' := (hco b ACQ R' va lockFree hva hR'G).2 (by omega)
    have hRleG : gwix G REL ≤ gwix G R' := by
      by_cases hc : gwix G R' < gwix G REL
      · exact absurd ⟨hAR'G, hc⟩ (hnoin R' lockFree hR'G hhr')
      · omega
    have hRleR : gwix GR REL ≤ gwix GR R' := by
      refine Nat.le_of_not_lt (fun hc => ?_)
      have := (hco b R' REL lockFree lockFree hR'G hRel).2 hc
      omega
    have hmoRA : gmoLt G REL ACQw :=
      gwixLtGmo G REL ACQw hwf (lockRelGwrites G b REL hwf hRel) (lockAcqGwrites G b ACQw hwf hacqw)
        ((hco b REL ACQw lockFree vq hRel hvqG).2 (by omega))
    obtain ⟨hrw, haqw⟩ := hAQ ACQw hacqw hwinA
    have hmoAw : gmoLt G ACQw w :=
      CatLin.acqGmoAfterC G ACQw w h6 hpoAw hrw haqw
        (WeakRvwmoGraph.glblIsWGmem G w (gwritesByteGlblW G w a vw hvw))
    have hmoeR := CatLin.fenceGmoAfterC G entry REL h6 hfen
    exact absurd (gmoLtTrans G w entry w hcross
      (gmoLtTrans G entry REL w hmoeR (gmoLtTrans G REL ACQw w hmoRA hmoAw))) (gmoLtIrrefl G w)

/-! # 3. The CS hypotheses, the claim and the chain -/

/-- `CatLin.csHypsR2` at the P member WITHOUT the section release's `np` (F-6b′-1 (ii): false on GF at a
release re-tagged `.WCplain`; full co makes it unnecessary). -/
def SbKill.csHypsP (GD : Gdexec) (GR : Gexec) (P : Int → Int → Prop) (log : List Wmsg) (prev : Geid)
    (s : Seg) : Prop :=
  ∃ (b a : Int) (ACQ REL : Geid),
    P a b ∧ lockWordByte log b ∧ (∃ v, gwritesByte GD.gdG prev a v) ∧
    gcls GD.gdG prev .WCplain ∧ gwix GR prev ≤ log.length ∧
    (∀ v, ¬ gwritesByte GD.gdG prev b v) ∧
    lockAcq GD.gdG b ACQ ∧ acqRow GD.gdG b ACQ ∧ glblIs GD.gdG ACQ lbAq ∧
    gwix GR ACQ ≤ log.length ∧
    lockCs GD.gdG b ACQ REL ∧ WeakRvwmoGraph.gpo GD.gdG ACQ s.sgEntry ∧
    gfenceCovers GD.gdG s.sgEntry REL ∧
    WeakRvwmoGraph.gpo GD.gdG ACQ s.sgExit ∧ gmem GD.gdG s.sgExit ∧ ACQ.1 ≠ prev.1 ∧
    (∀ n0 r0, wprotAt log a b n0 r0 → r0 < gwix GR prev ∧ n0 < gwix GR ACQ)

theorem SbKill.csHypsCertCP (GD : Gdexec) (ad : List (Geid × Geid)) (Xc : Geid → Geid → Prop)
    (GR : Gexec) (X : Geid → Prop) (P : Int → Int → Prop) (log : List Wmsg) (prev : Geid)
    (s : Seg) :
    CatLin.rvwmoCatAD GD ad → (∀ x y, Xc x y → gmoLt GD.gdG x y) →
    gwf GR → agreeX GD.gdG GR X → CertZ18.rmwLatest GR log →
    SbKill.acqAqLogB GD.gdG GR log P → SbKill.relCoversLogB GD.gdG GR log P →
    (∀ b n0, SbKill.csIssue P GD.gdG GR log b n0) →
    logOf GR log → SbKill.protRegZB P GR.gxImg log →
    SbKill.csHypsP GD GR P log prev s → Xc prev s.sgEntry →
    CatLin.CertC GD.gdG Xc prev s := by
  rintro hc hX hwfR hag hlat hAQ hRC hiss hlog hpr
    ⟨b, a, ACQ, REL, hP, hlwb, hwa, hcl, hlew, hnob, hacq, hrow, haq, hleA, hcs, hpoe, hfen,
      hpox, hmx, hhart, hside⟩ hx
  obtain ⟨n0, r0, h, hprot, hat, halt, hz⟩ := hpr a b hP
  obtain ⟨hr0, hn0A⟩ := hside n0 r0 hprot
  exact .CSchained (SbKill.csChainedTP GD ad GR X P log b a n0 r0 h prev s.sgEntry s.sgExit ACQ REL
    hc hwfR hag hP hlat hz (hAQ a b n0 r0 h hP hprot hat halt) (hRC a b n0 r0 h hP hprot hat halt)
    (hiss b n0) hlog hlwb halt hrow hprot hwa hcl hr0 hlew hnob hacq haq hn0A hleA hcs hpoe hfen
    (hX _ _ hx) hpox hmx hhart)

/-- **THE L2′ CLAIM AT A P MEMBER** (`CatLin.l2ClaimAtCZR4` at `protRegZB` / `csHypsP`). -/
def SbKill.l2ClaimAtP (GF : Gfexec) (ad : List (Geid × Geid)) (GR : Gexec) (P : Int → Int → Prop)
    (Bad : Prop) : Prop :=
  ∀ (log : List Wmsg) (z : Geid) (ss : List Seg),
    CatLin.rvwmoCatAD GF.gfGd ad →
    logOf GR log →
    SbKill.protRegZB P GR.gxImg log →
    ss ≠ [] → CatLin.rawChainC GF.gfGd (ioCross GF) z z ss →
    ∀ (prev : Geid) (s : Seg),
      s ∈ ss → ioCross GF prev s.sgEntry → CatLin.segRunC GF.gfGd s →
      CatLin.segPinC GF.gfGd ad s ∨ SbKill.csHypsP GF.gfGd GR P log prev s ∨ Bad

/-- `SilKill.rawChainChainW4` at the P member. -/
theorem SbKill.rawChainChainP (GF : Gfexec) (ad : List (Geid × Geid)) (GR : Gexec) (X : Geid → Prop)
    (P : Int → Int → Prop) (log : List Wmsg) (Bad : Prop) (ss : List Seg) :
    CatLin.rvwmoCatAD GF.gfGd ad → ioResidueGmo GF → gdiskRead14 GF.gfGd.gdG →
    gwf GR → agreeX GF.gfGd.gdG GR X → CertZ18.rmwLatest GR log →
    SbKill.acqAqLogB GF.gfGd.gdG GR log P → SbKill.relCoversLogB GF.gfGd.gdG GR log P →
    (∀ b n0, SbKill.csIssue P GF.gfGd.gdG GR log b n0) →
    logOf GR log → SbKill.protRegZB P GR.gxImg log → ¬ Bad →
    (∀ prev s, s ∈ ss → ioCross GF prev s.sgEntry → CatLin.segRunC GF.gfGd s →
       CatLin.segPinC GF.gfGd ad s ∨ SbKill.csHypsP GF.gfGd GR P log prev s ∨ Bad) →
    ∀ (x y : Geid) (ss' : List Seg),
      ss' ⊆ ss → CatLin.rawChainC GF.gfGd (ioCross GF) x y ss' →
      CatLin.chainC GF.gfGd.gdG (ioCross GF) x y ss' := by
  intro hc hres hdr hwfR hag hlat hAQ hRC hiss hlog hpr hnB hcl x y ss'
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
    show CatLin.CertC GF.gfGd.gdG (ioCross GF) x s ∧
      CatLin.chainC GF.gfGd.gdG (ioCross GF) s.sgExit y ss'
    refine ⟨?_, ih _ hsub' hrest⟩
    rcases hcl x s hs hx hrun with hp | hcs | hb
    · exact CatLin.segPinCCert GF.gfGd ad _ x s hc hx hp
    · exact SbKill.csHypsCertCP GF.gfGd ad _ GR X P log x s hc hX hwfR hag hlat hAQ hRC hiss hlog
        hpr hcs hx
    · exact absurd hb hnB

/-! # 4. The supply and the kill core -/

/-- **THE WALK'S CLASS-LEVEL INPUTS (NAMED)**: the image facts on GF's labels (`ImgFacts`, G1 — the image
halves are `SbOrd.imgAmoAq`/`imgFenceSw`), the device-row store order (`DevStOrd`, device model), the
exempt reads `Xof GF` are plain loads, and the image is defined at every byte read. -/
def SbKill.walkHypCZ (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image)
    (Xof : Gfexec → Geid → Prop) : Prop :=
  ∀ (GF : Gfexec) (ad : List (Geid × Geid)),
    GF.gfGd.gdG.gxImg = im → CatLin.rvwmoCatAD GF.gfGd ad → GraphFabConf.gfexecConfZF boot d0 fab GF →
    ImgFacts GF.gfGd.gdG ∧ DevStOrd GF.gfGd.gdG GF.gfDev ∧
    (∀ e l, Xof GF e → gxLbl GF.gfGd.gdG e = some l → ∃ base ts vs, l = LLoad false base ts vs) ∧
    (∀ e a t v, greadsByte GF.gfGd.gdG e a t v → (im a).isSome)

/-- **THE PER-STATE INTERFACES (NAMED)**: row H3 (`HeadOrdRd`, F-P-W3-3) and the exempt-value fact
(`IrefTop`, F-P-W2-1) at every reachable walk state, under the value gate. -/
def SbKill.stateIfcCZ (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image)
    (Xof : Gfexec → Geid → Prop) : Prop :=
  ∀ (GF : Gfexec) (ad : List (Geid × Geid)),
    GF.gfGd.gdG.gxImg = im → CatLin.rvwmoCatAD GF.gfGd ad → GraphFabConf.gfexecConfZF boot d0 fab GF →
    ioResidueGmo GF →
    ∀ c, validW SbPol.epoch c → c.img = im →
      PInv GF.gfGd.gdG.gxProg.length im GF.gfGd.gdG (Xof GF) GF.gfDev (cur c) →
      HeadOrdRd GF.gfGd.gdG (Xof GF) valGate GF.gfDev (cur c) ∧ IrefTop GF.gfGd.gdG (Xof GF) (cur c)

/-- A FINISHED P MEMBER of `GF`: a drained valid walk at GF's image whose member is well formed,
logs its log, has RMW atomicity and agrees with GF up to the exempt reads. -/
def SbKill.finishedP (GF : Gfexec) (X : Geid → Prop) (c : CandW) : Prop :=
  c.img = GF.gfGd.gdG.gxImg ∧ validW SbPol.epoch c ∧ drained (cur c) ∧
  gwf (memberP GF.gfGd.gdG.gxProg.length c) ∧
  logOf (memberP GF.gfGd.gdG.gxProg.length c) (logP c) ∧
  CertZ18.rmwLatest (memberP GF.gfGd.gdG.gxProg.length c) (logP c) ∧
  agreeX GF.gfGd.gdG (memberP GF.gfGd.gdG.gxProg.length c) X

/-- **(G-3) at the P member**: a finished member for every class graph. -/
def SbKill.certSupplyP (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image)
    (Xof : Gfexec → Geid → Prop) : Prop :=
  ∀ (GF : Gfexec) (ad : List (Geid × Geid)),
    GF.gfGd.gdG.gxImg = im → CatLin.rvwmoCatAD GF.gfGd ad → GraphFabConf.gfexecConfZF boot d0 fab GF →
    ioResidueGmo GF → ∃ c, SbKill.finishedP GF (Xof GF) c

/-- **THE SUPPLY FROM THE GATED WALK** (`SbOrd.memberOfCat` under the value gate). -/
theorem SbKill.certSupplyOfWalkP (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image)
    (Xof : Gfexec → Geid → Prop)
    (hbt : ∀ i, i < NCPU → GraphFabConf.isHart (boot i) = true)
    (hwio : CatLin.gfDevWIoCZ boot d0 fab im)
    (hW : SbKill.walkHypCZ boot d0 fab im Xof) (hS : SbKill.stateIfcCZ boot d0 fab im Xof) :
    SbKill.certSupplyP boot d0 fab im Xof := by
  intro GF ad him hc hconf hres
  obtain ⟨hI, hDS, hex, hdef⟩ := hW GF ad him hc hconf
  have hWH : WalkHyp GF GF.gfGd.gdG.gxProg.length im (Xof GF) :=
    { cat := ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1⟩
      io := hres
      wio := hwio GF ad him hc hconf
      imgF := hI
      devSt := hDS
      hart := LockFacts3.hartDevIo boot d0 fab GF hconf hbt
      len := rfl
      imgEq := him
      ex := hex
      def' := hdef }
  obtain ⟨c, hcimg, hv, hdr, hgwf, hlog, hlat, hagX, -⟩ :=
    memberOfCat GF _ im (Xof GF) valGate hWH (fun c hv hci hP =>
      let h := hS GF ad him hc hconf hres c hv hci hP
      let h' := valIfc GF _ im (Xof GF) hWH c hv hP
      ⟨h.1, h.2, h'.1, h'.2⟩)
  exact ⟨c, hcimg.trans him.symm, hv, hdr, hgwf, hlog, hlat, hagX⟩

/-- **THE RUN FACTS AT EVERY FINISHED P MEMBER (NAMED; the export / the buffered twin realization,
P-W5/P-W6/6j)**: the class-blind registration `protRegZB` of its log, the lock-site realization
`lockRealB`, and the issue-order critical sections `csIssue` (F-P-W4-1). -/
def SbKill.memberRunCZ (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image)
    (Xof : Gfexec → Geid → Prop) (P : Int → Int → Prop) : Prop :=
  ∀ (GF : Gfexec) (ad : List (Geid × Geid)) (c : CandW),
    GF.gfGd.gdG.gxImg = im → CatLin.rvwmoCatAD GF.gfGd ad → GraphFabConf.gfexecConfZF boot d0 fab GF →
    SbKill.finishedP GF (Xof GF) c →
    SbKill.protRegZB P im (logP c) ∧
    SbKill.lockRealB (memberP GF.gfGd.gdG.gxProg.length c) (logP c) P ∧
    ∀ b n0, SbKill.csIssue P GF.gfGd.gdG (memberP GF.gfGd.gdG.gxProg.length c) (logP c) b n0

/-- **THE L2′ CLAIM AT EVERY FINISHED P MEMBER OF A PROVENANT CLASS GRAPH (NAMED; W11-F, row 6n)**. -/
def SbKill.l2ClaimP (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image)
    (Xof : Gfexec → Geid → Prop) (P : Int → Int → Prop) (Bad : Prop) : Prop :=
  ∀ (GF : Gfexec) (ad : List (Geid × Geid)) (c : CandW),
    GF.gfGd.gdG.gxImg = im → GraphFabConf.gfexecConfZF boot d0 fab GF →
    CapFetchProv.provAll boot GF.gfGd →
    SbKill.finishedP GF (Xof GF) c →
    SbKill.l2ClaimAtP GF ad (memberP GF.gfGd.gdG.gxProg.length c) P Bad

/-- **`cycleKillCoreP` — THE TRIMMED CLASS KILL FROM ROUTE P'S MEMBER**: `CatLin.cycleKillCZT` (consumed by
`CapFetchProv.t2linSupplyCZTtagged`) from the supply, the run facts at the member, the L2′ claim and
`¬ Bad`.  The induction hypothesis over the trimmed hulls is not needed: the walk reads no hull. -/
theorem SbKill.cycleKillCoreP (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image)
    (Xof : Gfexec → Geid → Prop) (P : Int → Int → Prop) (Bad : Prop)
    (hsup : SbKill.certSupplyP boot d0 fab im Xof)
    (hM : SbKill.memberRunCZ boot d0 fab im Xof P)
    (hl2 : SbKill.l2ClaimP boot d0 fab im Xof P Bad) (hnB : ¬ Bad) :
    CatLin.cycleKillCZT boot d0 fab im := by
  intro GF ad him hc hconf hres hdr hprov _ x hcyc
  obtain ⟨z, ss, hne, hch⟩ := cycleSegmentsIO GF ad x hc hcyc
  obtain ⟨c, hfin⟩ := hsup GF ad him hc hconf hres
  have hfin' := hfin
  obtain ⟨hpr, hreal, hiss⟩ := hM GF ad c him hc hconf hfin
  obtain ⟨-, -, -, hwfR, hlog, hlat, hagX⟩ := hfin'
  have himR : (memberP GF.gfGd.gdG.gxProg.length c).gxImg = im := hagX.1.trans him
  have hprR : SbKill.protRegZB P (memberP GF.gfGd.gdG.gxProg.length c).gxImg (logP c) := by
    rw [himR]; exact hpr
  have hcl := hl2 GF ad c him hconf hprov hfin (logP c) z ss hc hlog hprR hne hch
  exact cycleKillIOC GF ad z ss hc hres hdr hne
    (SbKill.rawChainChainP GF ad _ (Xof GF) P (logP c) Bad ss hc hres hdr hwfR hagX hlat
      (SbKill.acqAqLogOfRealX _ _ (Xof GF) _ P hagX hwfR hlog hreal)
      (SbKill.relCoversLogOfRealX _ _ (Xof GF) _ P hagX hwfR hreal) hiss hlog hprR hnB
      hcl z z ss (fun _ h => h) hch)

/-- **… from the gated walk** (`certSupplyOfWalkP`): the kill with the walk's named inputs. -/
theorem SbKill.cycleKillOfWalkP (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image)
    (Xof : Gfexec → Geid → Prop) (P : Int → Int → Prop) (Bad : Prop)
    (hbt : ∀ i, i < NCPU → GraphFabConf.isHart (boot i) = true)
    (hwio : CatLin.gfDevWIoCZ boot d0 fab im)
    (hW : SbKill.walkHypCZ boot d0 fab im Xof) (hS : SbKill.stateIfcCZ boot d0 fab im Xof)
    (hM : SbKill.memberRunCZ boot d0 fab im Xof P)
    (hl2 : SbKill.l2ClaimP boot d0 fab im Xof P Bad) (hnB : ¬ Bad) :
    CatLin.cycleKillCZT boot d0 fab im :=
  SbKill.cycleKillCoreP boot d0 fab im Xof P Bad
    (SbKill.certSupplyOfWalkP boot d0 fab im Xof hbt hwio hW hS) hM hl2 hnB

/-- **THE SHAPE `CapFetchProv.t2linSupplyCZTtagged` CONSUMES** (`∀ fab, cycleKillCZT boot d0 fab im`). -/
theorem SbKill.cycleKillAllP (boot : Nat → Pexv6) (d0 : Efab) (im : Image)
    (Xof : Gfexec → Geid → Prop) (P : Int → Int → Prop) (Bad : Prop)
    (hbt : ∀ i, i < NCPU → GraphFabConf.isHart (boot i) = true)
    (hwio : ∀ fab, CatLin.gfDevWIoCZ boot d0 fab im)
    (hW : ∀ fab, SbKill.walkHypCZ boot d0 fab im Xof) (hS : ∀ fab, SbKill.stateIfcCZ boot d0 fab im Xof)
    (hM : ∀ fab, SbKill.memberRunCZ boot d0 fab im Xof P)
    (hl2 : ∀ fab, SbKill.l2ClaimP boot d0 fab im Xof P Bad) (hnB : ¬ Bad) :
    ∀ fab, CatLin.cycleKillCZT boot d0 fab im :=
  fun fab => SbKill.cycleKillOfWalkP boot d0 fab im Xof P Bad hbt (hwio fab) (hW fab) (hS fab) (hM fab)
    (hl2 fab) hnB

end Weak
