/-
Weak: **the S-R `DomAt` lift, increment I-5 (1/2) — `SbKillR`, THE KILL FROM THE S-R WALK** (ruling
[OWN.150]; `PROGRESS-DomAt.md` §0.2).  Lean-only, no Rocq twin.  A leaf: nothing registered imports this
file.

**Spec, stated first.**  The kill (`CatLin.cycleKillCZT`) needs, at every class graph, a FINISHED member of
the twin agreeing with GF (`SbKill.certSupplyP`).  This file supplies it from the S-R walk (`SbOrdR.walkRunR`,
`memberOfCatR`) instead of the top-read walk: the same consumer shape, with the S-R per-state interfaces
(`stateIfcCZR`: row H3′ `HeadOrdW` and the min-rule exempt value `ExValMin`) in place of `HeadOrdRd` and
`ExValTop`, and the census `NoAqLd` beside the image facts.  `HeadOrdW` follows from the per-head STATIC
WRITE HOP (`SbHeadHop.WrHop`, rules 11 / 4) and (R1) alone (`headOrdWOf`) — no (A2) read window.

  §1  **`SbOrdR.headOrdWOf`**: `HeadOrdW` from `WrHop` at every blocked head, (R1), `gfDevWIo`.
  §2  the consumer forms: `walkHypCZR`, `stateIfcCZR`, **`certSupplyOfWalkR`**, **`cycleKillOfWalkR`**,
      `cycleKillAllR` (`SbDevSt`'s `DevStOrd` discharge kept).
  §3  **row 6j via [OWN.155] (a) — THE CERTIFIED-HOP CRITICAL-SECTION ARM**: `SbKillR.hopsR` (the
      reader's certified sync path at the member: the first hop's release STAMPED, each hop's
      release → acquire in the lock byte's co, each acquire an `.aq` AMO), `SbKillR.csHypsH` (in place
      of `SbKill.csHypsP`), `SbKillR.csHypsHGmo` (rule 4 at the first release, co, rule 5).  No
      `lockRealB` (L1–L3 over the registration window), no `csIssue`, no `protRegZB`.
  §4  **(t3) [OWN.139] D2 — THE CYCLE SURGERY** (P-W6-free): `SbKillR.jumpKill` (a cycle whose every
      predecessor has a gmo-later exit has none), `SbKillR.rawChainPrev`; the claim with the corner
      arm `SbKillR.cornerJumpH`, `SbKillR.l2ClaimAtH`; **`SbKillR.cycleKillCoreH`**,
      `cycleKillOfWalkRH`, `cycleKillAllRH` (no `SbKill.memberRunCZ`).
  §5  the machine side: **`SbKillR.relHopPcAt`** (THE INTERIM INPUT, w1's MachCSL release stamp
      [OWN.155]), `SbKillR.HopReal` (the P-W6 realization at hop entries), `SbKillR.hopsROfChain` /
      `csHypsHOfChain` (the export's certified hop chain → the arm, PROVED from the two); (t3) D3
      wiring `SbKillR.g7FetchCertT` (G7's fetch certificate with the own-hart corners split off)
      and D1's named custody input `SbKillR.cornerLeaveP`.

Spec: FAITHFUL (proof organisation over riscv.cat's rules 4/5 and co ⊆ gmo; the named inputs are
xv6 run facts, FAITHFUL statements, WEAKER while named).  Lean-only helpers `SbOrdR.*`, `SbKillR.*`.
-/
import Weak.SbWalkR
import Weak.SbDevSt
import Weak.SbHeadHop
import Weak.CapSync
import Weak.G7FetchOwn

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Lbl SbWalk SbAgree SbReplay SbOrd

/-! # 1. Row H3′ from the static write hop -/

/-- **ROW H3′ FROM THE STATIC WRITE HOP**: if every blocked non-exempt plain-load head has `WrHop`
(rules 11 / 4 at its site), it is gmo-before every later write (that hop) and every later fabric member
(a write, or an I/O event: (R1)). -/
theorem SbOrdR.headOrdWOf (G : Gexec) (X : Geid → Prop) (dev : List Geid) (w : WS) (hc : CatH G)
    (hr1 : ∀ s m, WeakRvwmoGraph.gpo G s m → gmem G s → gisIo G s = false → gisIo G m = true →
      gmoLt G s m)
    (hwio2 : ∀ d, d ∈ dev → gisWIo G d = true)
    (hA1 : ∀ x base ts vs, gxLbl G (hd w x) = some (LLoad false base ts vs) → ¬ X (hd w x) →
      ¬ SbOrdR.srGate G w x false base ts vs → SbHeadHop.WrHop G (hd w x)) :
    SbOrdR.HeadOrdW G X dev w := by
  intro x base ts vs hl hX hns m hm hmx hlt hwo
  obtain ⟨lm, hlm, hmm⟩ := gwfGmoMem G m hc.wf hm
  have hpo : WeakRvwmoGraph.gpo G (hd w x) m :=
    SbHeadHop.gpoOfLbl G _ m _ lm hl hlm (by unfold hd; exact hmx.symm) hlt
  have hwr : gisW G m = true → gmoLt G (hd w x) m := fun h => hA1 x base ts vs hl hX hns m hpo h
  rcases hwo with hd' | hW
  · have hwi := hwio2 m hd'
    unfold gisWIo at hwi
    simp only [Bool.or_eq_true] at hwi
    rcases hwi with h | h
    · exact hwr h
    · exact hr1 _ m hpo ⟨_, hl, by simp [lbIsMem, lbIsR]⟩ (by unfold gisIo; rw [hl]; rfl) h
  · exact hwr hW

/-! # 2. The consumer forms -/

/-- **THE S-R WALK'S CLASS-LEVEL INPUTS (NAMED)**: `SbDevSt.walkHypCZD`'s (the image facts, exempt reads are
plain loads, the image defined at read bytes) and the census `NoAqLd` (finding F-DomAt-1). -/
def SbKillR.walkHypCZR (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image)
    (Xof : Gfexec → Geid → Prop) : Prop :=
  SbDevSt.walkHypCZD boot d0 fab im Xof ∧
  ∀ (GF : Gfexec) (ad : List (Geid × Geid)),
    GF.gfGd.gdG.gxImg = im → CatLin.rvwmoCatAD GF.gfGd ad → GraphFabConf.gfexecConfZF boot d0 fab GF →
    SbOrdR.NoAqLd GF.gfGd.gdG

/-- **THE S-R PER-STATE INTERFACES (NAMED)**: row H3′ (`HeadOrdW`) and the min-rule exempt value
(`ExValMin`) at every reachable GATED S-R candidate. -/
def SbKillR.stateIfcCZR (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image)
    (Xof : Gfexec → Geid → Prop) : Prop :=
  ∀ (GF : Gfexec) (ad : List (Geid × Geid)),
    GF.gfGd.gdG.gxImg = im → CatLin.rvwmoCatAD GF.gfGd ad → GraphFabConf.gfexecConfZF boot d0 fab GF →
    ioResidueGmo GF →
    ∀ c, validW SbPol.epoch c → SbOrdR.gatedWR GF.gfGd.gdG (Xof GF) GF.gfDev c → c.img = im →
      SbOrdR.PInvR GF.gfGd.gdG.gxProg.length im GF.gfGd.gdG (Xof GF) GF.gfDev (cur c) →
      SbOrdR.HeadOrdW GF.gfGd.gdG (Xof GF) GF.gfDev (cur c) ∧ SbOrdR.ExValMin GF.gfGd.gdG (Xof GF) (cur c)

/-- **THE SUPPLY FROM THE S-R WALK** (`DevStOrd` discharged as in `SbDevSt.certSupplyOfWalkPD`). -/
theorem SbKillR.certSupplyOfWalkR (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image)
    (Xof : Gfexec → Geid → Prop)
    (hbt : ∀ i, i < NCPU → GraphFabConf.isHart (boot i) = true)
    (hdb : ∀ i, NCPU ≤ i → boot i = .PDisk none)
    (hwio : CatLin.gfDevWIoCZ boot d0 fab im) (hdf : SbDevSt.diskFabPoCZ boot d0 fab im)
    (hW : SbKillR.walkHypCZR boot d0 fab im Xof) (hS : SbKillR.stateIfcCZR boot d0 fab im Xof) :
    SbKill.certSupplyP boot d0 fab im Xof := by
  intro GF ad him hc hconf hres
  obtain ⟨hI, hDS, hDF, hex, hdef⟩ :=
    SbDevSt.walkHypAt boot d0 fab im Xof hdb hwio hdf hW.1 GF ad him hc hconf hres
  have hWH : WalkHyp GF GF.gfGd.gdG.gxProg.length im (Xof GF) :=
    { cat := ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1⟩
      io := hres
      wio := hwio GF ad him hc hconf
      imgF := hI
      devSt := hDS
      devFab := hDF
      hart := LockFacts3.hartDevIo boot d0 fab GF hconf hbt
      len := rfl
      imgEq := him
      ex := hex
      def' := hdef }
  obtain ⟨c, hcimg, hv, hdr, hgwf, hlog, hlat, hagX, -⟩ :=
    SbOrdR.memberOfCatR GF _ im (Xof GF) hWH (hW.2 GF ad him hc hconf) (fun c hv hg hci hP =>
      let h := hS GF ad him hc hconf hres c hv hg hci hP
      ⟨h.1, h.2⟩)
  exact ⟨c, hcimg.trans him.symm, hv, hdr, hgwf, hlog, hlat, hagX⟩

/-- **… the kill** (`SbKill.cycleKillCoreP` from the S-R supply). -/
theorem SbKillR.cycleKillOfWalkR (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image)
    (Xof : Gfexec → Geid → Prop) (P : Int → Int → Prop) (Bad : Prop)
    (hbt : ∀ i, i < NCPU → GraphFabConf.isHart (boot i) = true)
    (hdb : ∀ i, NCPU ≤ i → boot i = .PDisk none)
    (hwio : CatLin.gfDevWIoCZ boot d0 fab im) (hdf : SbDevSt.diskFabPoCZ boot d0 fab im)
    (hW : SbKillR.walkHypCZR boot d0 fab im Xof) (hS : SbKillR.stateIfcCZR boot d0 fab im Xof)
    (hM : SbKill.memberRunCZ boot d0 fab im Xof P)
    (hl2 : SbKill.l2ClaimP boot d0 fab im Xof P Bad) (hnB : ¬ Bad) :
    CatLin.cycleKillCZT boot d0 fab im :=
  SbKill.cycleKillCoreP boot d0 fab im Xof P Bad
    (SbKillR.certSupplyOfWalkR boot d0 fab im Xof hbt hdb hwio hdf hW hS) hM hl2 hnB

/-- **THE SHAPE `CapFetchProv.t2linSupplyCZTtagged` CONSUMES**, from the S-R walk. -/
theorem SbKillR.cycleKillAllR (boot : Nat → Pexv6) (d0 : Efab) (im : Image)
    (Xof : Gfexec → Geid → Prop) (P : Int → Int → Prop) (Bad : Prop)
    (hbt : ∀ i, i < NCPU → GraphFabConf.isHart (boot i) = true)
    (hdb : ∀ i, NCPU ≤ i → boot i = .PDisk none)
    (hwio : ∀ fab, CatLin.gfDevWIoCZ boot d0 fab im) (hdf : ∀ fab, SbDevSt.diskFabPoCZ boot d0 fab im)
    (hW : ∀ fab, SbKillR.walkHypCZR boot d0 fab im Xof) (hS : ∀ fab, SbKillR.stateIfcCZR boot d0 fab im Xof)
    (hM : ∀ fab, SbKill.memberRunCZ boot d0 fab im Xof P)
    (hl2 : ∀ fab, SbKill.l2ClaimP boot d0 fab im Xof P Bad) (hnB : ¬ Bad) :
    ∀ fab, CatLin.cycleKillCZT boot d0 fab im :=
  fun fab => SbKillR.cycleKillOfWalkR boot d0 fab im Xof P Bad hbt hdb (hwio fab) (hdf fab) (hW fab)
    (hS fab) (hM fab) (hl2 fab) hnB

/-! # 3. Row 6j via [OWN.155] (a): THE CERTIFIED-HOP CRITICAL-SECTION ARM

`SbKill.csChainedTP` needs the two lock facts `CatLin.acqAqB` / `relCoversB` at lock-word writes it
finds by SCANNING THE LOG (the writer's holder acquire, the release between the two sections), so
`SbKill.memberRunCZ` asks `lockRealB` (L1: EVERY lock-word write in the registration window is the
swap or the fenced zero), `csIssue` (issue order at every protected write) and `protRegZB`.  The
export's twelfth conjunct `Xv6.AccessDiscipline.chainOkCertAtP` (Q2 [OWN.153] (D4)) certifies only
the READER's sync path.  This arm asks the lock facts there and nowhere else:

* the path's FIRST release `R` (on the writer's hart, issued after the observed entry) is
  `release+0x1a`'s store, after `release+0x16`'s `fence rw,w` (`relStampR`): rule 4 puts the
  predecessor gmo-before `R`;
* every hop's release → acquire is in the lock byte's co (the member's log order, transported by
  `agreeX`'s full co): co ⊆ gmo;
* every hop's acquire is an `.aq` AMO: rule 5 orders it before the next hop's release (po-after it
  on the same hart) and the last one before the segment's exit.

So the reader-first case of `csChainedTP` (refuted by a gmo cycle through the writer's acquire)
does not arise: the export's path is oriented.  Spec: rules 4/5 and co ⊆ gmo are riscv.cat's; the
arm is a fact of xv6's runs (true at every certified path, `hopsROfChain`).  FAITHFUL. -/

/-- An `.aq` AMO at the member (a certified hop's acquire: `acquire`'s `amoswap.w.aq`). -/
def SbKillR.acqAmo (GR : Gexec) (A : Geid) : Prop :=
  ∃ rl base ts rvs wvs k, gxLbl GR A = some (LRmw true rl base ts rvs wvs k)

/-- **THE FIRST HOP'S RELEASE, STAMPED** (at the member): `R` is on `x`'s hart, and an event `kf`
between them is `release+0x16`'s `fence rw,w` (`LockFacts2.relFenceLbl`). -/
def SbKillR.relStampR (GR : Gexec) (x R : Geid) : Prop :=
  x.1 = R.1 ∧ ∃ kf, x.2 < kf ∧ kf < R.2 ∧ gxLbl GR (R.1, kf) = some LockFacts2.relFenceLbl

/-- **THE READER'S CERTIFIED SYNC PATH AT THE MEMBER** from `x` to the acquire `A` (MachCSL's
`hopChain` read at the member): one hop from `x`'s stamped release, then hops from the previous
acquire's hart, release po-after that acquire. -/
inductive SbKillR.hopsR (GR : Gexec) (x : Geid) : Geid → Prop
  | base (b : Int) (R A : Geid) : SbKillR.relStampR GR x R → lockRel GR b R → lockAcq GR b A →
      gwix GR R < gwix GR A → SbKillR.acqAmo GR A → SbKillR.hopsR GR x A
  | step (b : Int) (A1 R A : Geid) : SbKillR.hopsR GR x A1 → A1.1 = R.1 → A1.2 < R.2 →
      lockRel GR b R → lockAcq GR b A → gwix GR R < gwix GR A → SbKillR.acqAmo GR A →
      SbKillR.hopsR GR x A

/-- **THE PATH ORDERS ITS SOURCE BEFORE ITS LAST ACQUIRE IN GF's gmo** (rule 4 at the stamped
release, co ⊆ gmo on each lock byte via `agreeX`, rule 5 at each acquire); the last acquire is an
`.aq` read of GF. -/
theorem SbKillR.hopsRGmo (GD : Gdexec) (ad : List (Geid × Geid)) (GR : Gexec) (X : Geid → Prop)
    (x A : Geid) (hc : CatLin.rvwmoCatAD GD ad) (hag : agreeX GD.gdG GR X)
    (hx : glblIs GD.gdG x lbIsR ∨ glblIs GD.gdG x lbIsW) (h : SbKillR.hopsR GR x A) :
    gmoLt GD.gdG x A ∧ glblIs GD.gdG A lbIsR ∧ glblIs GD.gdG A lbAq := by
  have hwf : gwf GD.gdG := hc.1
  have h6 := hc.2.1
  have hco := hag.2.2
  have hop : ∀ (b : Int) (R A : Geid), lockRel GR b R → lockAcq GR b A → gwix GR R < gwix GR A →
      SbKillR.acqAmo GR A →
      lockRel GD.gdG b R ∧ gmoLt GD.gdG R A ∧ glblIs GD.gdG A lbIsR ∧ glblIs GD.gdG A lbAq := by
    intro b R A hR hA hlt hq
    have hRG : lockRel GD.gdG b R := (agreeWrIff _ _ X hag R b lockFree).1 hR
    obtain ⟨va, hva, hne⟩ := hA
    have hvaG : gwritesByte GD.gdG A b va := (agreeWrIff _ _ X hag A b va).1 hva
    have hAG : lockAcq GD.gdG b A := ⟨va, hvaG, hne⟩
    obtain ⟨rl, base, ts, rvs, wvs, k, hl⟩ := hq
    exact ⟨hRG, gwixLtGmo _ R A hwf (lockRelGwrites _ b R hwf hRG) (lockAcqGwrites _ b A hwf hAG)
      ((hco b R A lockFree va hRG hvaG).2 hlt), SbKill.rmwAqOfX _ GR X A rl base ts rvs wvs k hag hl⟩
  induction h with
  | base b R A hst hR hA hlt hq =>
    obtain ⟨hRG, hRA, hAr, hAq⟩ := hop b R A hR hA hlt hq
    obtain ⟨hx1, kf, hxk, hkf, hfl⟩ := hst
    have hfG := SbKill.fenceAtX GD.gdG GR X (R.1, kf) _ _ _ _ hag hfl
    obtain ⟨-, hpr, hpw, -, hsw⟩ := LockFacts.relFenceBits
    have hfc : gfenceCovers GD.gdG x R :=
      ⟨_, _, _, _, ⟨hx1, by omega, kf, hxk, hkf, by rw [hx1]; exact hfG⟩,
        hx.elim (fun h => .inl ⟨h, hpr⟩) (fun h => .inr ⟨h, hpw⟩),
        .inr ⟨gwritesByteGlblW _ R b lockFree hRG, hsw⟩⟩
    exact ⟨gmoLtTrans _ _ _ _ (CatLin.fenceGmoAfterC _ x R h6 hfc) hRA, hAr, hAq⟩
  | step b A1 R A _ h1 h2 hR hA hlt hq ih =>
    obtain ⟨hxA1, hA1r, hA1q⟩ := ih
    obtain ⟨hRG, hRA, hAr, hAq⟩ := hop b R A hR hA hlt hq
    have hRW := gwritesByteGlblW _ R b lockFree hRG
    have hA1s : (gxLbl GD.gdG A1).isSome := by
      obtain ⟨l, hl, -⟩ := hA1r
      simp [hl]
    have hpo : WeakRvwmoGraph.gpo GD.gdG A1 R :=
      ⟨h1, h2, hA1s, WeakRvwmoLock.gwritesByteLbl _ R b lockFree hRG⟩
    have hA1R := CatLin.acqGmoAfterC _ A1 R h6 hpo hA1r hA1q (WeakRvwmoGraph.glblIsWGmem _ R hRW)
    exact ⟨gmoLtTrans _ _ _ _ (gmoLtTrans _ _ _ _ hxA1 hA1R) hRA, hAr, hAq⟩

/-- **THE CERTIFIED-HOP CS ARM** (row 6j (a), [OWN.155]; in place of `SbKill.csHypsP`): the
predecessor is a read or a write of GF, and the reader's certified sync path from it ends at an
acquire at or po-before the segment's exit. -/
def SbKillR.csHypsH (GD : Gdexec) (GR : Gexec) (prev : Geid) (s : Seg) : Prop :=
  (glblIs GD.gdG prev lbIsR ∨ glblIs GD.gdG prev lbIsW) ∧
  ∃ A, SbKillR.hopsR GR prev A ∧
    (A = s.sgExit ∨ (WeakRvwmoGraph.gpo GD.gdG A s.sgExit ∧ gmem GD.gdG s.sgExit))

/-- The arm's gmo consequence: the predecessor is gmo-before the exit. -/
theorem SbKillR.csHypsHGmo (GD : Gdexec) (ad : List (Geid × Geid)) (GR : Gexec) (X : Geid → Prop)
    (prev : Geid) (s : Seg) (hc : CatLin.rvwmoCatAD GD ad) (hag : agreeX GD.gdG GR X) :
    SbKillR.csHypsH GD GR prev s → gmoLt GD.gdG prev s.sgExit := by
  rintro ⟨hx, A, hh, hA⟩
  obtain ⟨h1, h2, h3⟩ := SbKillR.hopsRGmo GD ad GR X prev A hc hag hx hh
  rcases hA with hA | ⟨hpo, hm⟩
  · rw [← hA]; exact h1
  · exact gmoLtTrans _ _ _ _ h1 (CatLin.acqGmoAfterC _ A s.sgExit hc.2.1 hpo h2 h3 hm)

/-- …as a `CSchained` certificate, at any cross order. -/
theorem SbKillR.csHypsHCert (GD : Gdexec) (ad : List (Geid × Geid)) (Xc : Geid → Geid → Prop)
    (GR : Gexec) (X : Geid → Prop) (prev : Geid) (s : Seg) (hc : CatLin.rvwmoCatAD GD ad)
    (hag : agreeX GD.gdG GR X) (h : SbKillR.csHypsH GD GR prev s) : CatLin.CertC GD.gdG Xc prev s :=
  .CSchained (SbKillR.csHypsHGmo GD ad GR X prev s hc hag h)

/-! # 4. (t3) [OWN.139] D2 — THE CYCLE SURGERY, and the kill core

An own-hart RWX corner segment `s` of G7's fetch arm (F-6h-3) has no certificate of its own: RVWMO
orders neither its contributor before a later own event (corner (i), `fence.i` is not a data fence)
nor an own store before the hart's own later fetch (corner (ii)).  (t3) certifies it TOGETHER WITH
THE REST OF THE CYCLE: the cycle must leave hart `i` (user pages are private) through a kernel
hand-off whose release (`fence rw,w`, rule 4) is po-after the predecessor, and the hand-off's
certified path reaches the acquire of a LATER segment `t` of the cycle — the corner arm
`cornerJumpH` is `csHypsH` aimed at `t`'s exit instead of `s`'s.

The surgery is graph-level and P-W6-free: a cyclic raw chain in which every predecessor exit has a
gmo-LATER exit of the cycle (its own segment's, by a certificate; or a later segment's, by a jump)
is impossible — the exit of greatest gmo position has none (`jumpKill`).  No re-segmentation of
`rawChainC` is needed, and segments certified as before are untouched.  Spec: FAITHFUL (gmo is a
strict order on the cycle's events). -/

/-- **THE CORNER ARM** ((t3) D2): the predecessor's certified path reaches a segment of the cycle. -/
def SbKillR.cornerJumpH (GD : Gdexec) (GR : Gexec) (prev : Geid) (ss : List Seg) : Prop :=
  ∃ t, t ∈ ss ∧ SbKillR.csHypsH GD GR prev t

/-- **THE L2′ CLAIM AT A MEMBER, (a) + (t3) FORM**: every segment entered from `prev` is certified
(any `CertC`: `segPinC` via `CatLin.segPinCCert`, G7's fetch certificate, W11-D's chain), or is the
certified-hop CS arm, or is a corner whose predecessor jumps to a later segment, or `Bad`. -/
def SbKillR.l2ClaimAtH (GF : Gfexec) (ad : List (Geid × Geid)) (GR : Gexec) (Bad : Prop) : Prop :=
  ∀ (log : List Wmsg) (z : Geid) (ss : List Seg),
    CatLin.rvwmoCatAD GF.gfGd ad → logOf GR log → ss ≠ [] →
    CatLin.rawChainC GF.gfGd (ioCross GF) z z ss →
    ∀ (prev : Geid) (s : Seg), s ∈ ss → ioCross GF prev s.sgEntry → CatLin.segRunC GF.gfGd s →
      CatLin.CertC GF.gfGd.gdG (ioCross GF) prev s ∨ SbKillR.csHypsH GF.gfGd GR prev s ∨
        SbKillR.cornerJumpH GF.gfGd GR prev ss ∨ Bad

/-- **THE L2′ CLAIM AT EVERY FINISHED MEMBER, (a) + (t3) FORM (NAMED; rows 6n / A5)**. -/
def SbKillR.l2ClaimH (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image)
    (Xof : Gfexec → Geid → Prop) (Bad : Prop) : Prop :=
  ∀ (GF : Gfexec) (ad : List (Geid × Geid)) (c : CandW),
    GF.gfGd.gdG.gxImg = im → GraphFabConf.gfexecConfZF boot d0 fab GF →
    CapFetchProv.provAll boot GF.gfGd →
    SbKill.finishedP GF (Xof GF) c →
    SbKillR.l2ClaimAtH GF ad (memberP GF.gfGd.gdG.gxProg.length c) Bad

/-- A nonempty list has an element of greatest `f`. -/
theorem SbKillR.maxPos (f : Geid → Nat) :
    ∀ (L : List Geid), L ≠ [] → ∃ m, m ∈ L ∧ ∀ q, q ∈ L → f q ≤ f m
  | [], h => absurd rfl h
  | [a], _ => ⟨a, List.mem_cons_self, fun q hq => by
      rw [List.mem_singleton] at hq
      rw [hq]
      exact Nat.le_refl _⟩
  | a :: b :: L, _ => by
    obtain ⟨m, hm, hmax⟩ := SbKillR.maxPos f (b :: L) (List.cons_ne_nil _ _)
    by_cases h : f a ≤ f m
    · refine ⟨m, List.mem_cons_of_mem _ hm, fun q hq => ?_⟩
      rcases List.mem_cons.1 hq with hq | hq
      · rw [hq]; exact h
      · exact hmax q hq
    · refine ⟨a, List.mem_cons_self, fun q hq => ?_⟩
      rcases List.mem_cons.1 hq with hq | hq
      · rw [hq]; exact Nat.le_refl _
      · have := hmax q hq
        omega

/-- **THE SURGERY KILL**: no nonempty set of events in which every element has a gmo-later one. -/
theorem SbKillR.jumpKill (G : Gexec) (L : List Geid) (hne : L ≠ [])
    (h : ∀ p, p ∈ L → ∃ q, q ∈ L ∧ gmoLt G p q) : False := by
  obtain ⟨m, hm, hmax⟩ := SbKillR.maxPos (gpos G) L hne
  obtain ⟨q, hq, hlt⟩ := h m hm
  have h1 := hmax q hq
  have h2 := hlt.2.2
  omega

/-- Every predecessor of a raw chain (its start, or a segment's exit) is its end or the source of
the cross edge into one of its segments. -/
theorem SbKillR.rawChainPrev (GD : Gdexec) (X : Geid → Geid → Prop) :
    ∀ (x y : Geid) (ss : List Seg), CatLin.rawChainC GD X x y ss →
      ∀ p, (p = x ∨ ∃ s, s ∈ ss ∧ p = s.sgExit) →
        p = y ∨ ∃ s, s ∈ ss ∧ X p s.sgEntry ∧ CatLin.segRunC GD s
  | x, y, [], h, p, hp => by
    have hxy : x = y := h
    rcases hp with hp | ⟨s, hs, -⟩
    · exact .inl (hp.trans hxy)
    · cases hs
  | x, y, s :: ss, h, p, hp => by
    obtain ⟨h1, h2, h3⟩ := h
    rcases hp with hp | ⟨s', hs', hp⟩
    · rw [hp]
      exact .inr ⟨s, List.mem_cons_self, h1, h2⟩
    · have hp' : p = s.sgExit ∨ ∃ s'', s'' ∈ ss ∧ p = s''.sgExit := by
        rcases List.mem_cons.1 hs' with he | hs''
        · rw [hp, he]; exact .inl rfl
        · exact .inr ⟨s', hs'', hp⟩
      rcases SbKillR.rawChainPrev GD X s.sgExit y ss h3 p hp' with h | ⟨t, ht, h4, h5⟩
      · exact .inl h
      · exact .inr ⟨t, List.mem_cons_of_mem _ ht, h4, h5⟩

/-- **`cycleKillCoreH` — THE KILL FROM THE (a) + (t3) CLAIM**: `CatLin.cycleKillCZT` from the member
supply, the claim and `¬ Bad`.  No `SbKill.memberRunCZ`: `lockRealB` (L1–L3), `csIssue` and
`protRegZB` are not consumed (the arm's lock facts are asked at the reader's path, inside the claim). -/
theorem SbKillR.cycleKillCoreH (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image)
    (Xof : Gfexec → Geid → Prop) (Bad : Prop)
    (hsup : SbKill.certSupplyP boot d0 fab im Xof)
    (hl2 : SbKillR.l2ClaimH boot d0 fab im Xof Bad) (hnB : ¬ Bad) :
    CatLin.cycleKillCZT boot d0 fab im := by
  intro GF ad him hc hconf hres hdr hprov _ x hcyc
  obtain ⟨z, ss, hne, hch⟩ := cycleSegmentsIO GF ad x hc hcyc
  obtain ⟨c, hfin⟩ := hsup GF ad him hc hconf hres
  have hcl := hl2 GF ad c him hconf hprov hfin (logP c) z ss hc hfin.2.2.2.2.1 hne hch
  have hagX := hfin.2.2.2.2.2.2
  have hX : ∀ x y, ioCross GF x y → gmoLt GF.gfGd.gdG x y := ioCrossGmo GF hc.1 hc.2.2.1 hres hdr
  have hmem : ∀ t, t ∈ ss → t.sgExit ∈ z :: ss.map Seg.sgExit :=
    fun t ht => List.mem_cons_of_mem _ (List.mem_map.2 ⟨t, ht, rfl⟩)
  have hstep : ∀ p s, s ∈ ss → ioCross GF p s.sgEntry → CatLin.segRunC GF.gfGd s →
      ∃ q, q ∈ z :: ss.map Seg.sgExit ∧ gmoLt GF.gfGd.gdG p q := by
    intro p s hs hx hrun
    rcases hcl p s hs hx hrun with hC | hH | ⟨t, ht, hH⟩ | hb
    · exact ⟨s.sgExit, hmem s hs, CatLin.certCGmo _ _ p s hX hC⟩
    · exact ⟨s.sgExit, hmem s hs, SbKillR.csHypsHGmo GF.gfGd ad _ (Xof GF) p s hc hagX hH⟩
    · exact ⟨t.sgExit, hmem t ht, SbKillR.csHypsHGmo GF.gfGd ad _ (Xof GF) p t hc hagX hH⟩
    · exact absurd hb hnB
  obtain ⟨s0, ss0, hss⟩ : ∃ s0 ss0, ss = s0 :: ss0 := by
    cases ss with
    | nil => exact absurd rfl hne
    | cons s0 ss0 => exact ⟨s0, ss0, rfl⟩
  have hhead : ioCross GF z s0.sgEntry ∧ CatLin.segRunC GF.gfGd s0 := by
    rw [hss] at hch
    exact ⟨hch.1, hch.2.1⟩
  have hs0 : s0 ∈ ss := by rw [hss]; exact List.mem_cons_self
  refine SbKillR.jumpKill GF.gfGd.gdG (z :: ss.map Seg.sgExit) (List.cons_ne_nil _ _) ?_
  intro p hp
  have hp' : p = z ∨ ∃ s, s ∈ ss ∧ p = s.sgExit := by
    rcases List.mem_cons.1 hp with h | h
    · exact .inl h
    · obtain ⟨s, hs, he⟩ := List.mem_map.1 h
      exact .inr ⟨s, hs, he.symm⟩
  rcases SbKillR.rawChainPrev GF.gfGd (ioCross GF) z z ss hch p hp' with h | ⟨s, hs, hx, hrun⟩
  · rw [h]; exact hstep z s0 hs0 hhead.1 hhead.2
  · exact hstep p s hs hx hrun

/-- **… from the S-R walk** (`certSupplyOfWalkR`). -/
theorem SbKillR.cycleKillOfWalkRH (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image)
    (Xof : Gfexec → Geid → Prop) (Bad : Prop)
    (hbt : ∀ i, i < NCPU → GraphFabConf.isHart (boot i) = true)
    (hdb : ∀ i, NCPU ≤ i → boot i = .PDisk none)
    (hwio : CatLin.gfDevWIoCZ boot d0 fab im) (hdf : SbDevSt.diskFabPoCZ boot d0 fab im)
    (hW : SbKillR.walkHypCZR boot d0 fab im Xof) (hS : SbKillR.stateIfcCZR boot d0 fab im Xof)
    (hl2 : SbKillR.l2ClaimH boot d0 fab im Xof Bad) (hnB : ¬ Bad) :
    CatLin.cycleKillCZT boot d0 fab im :=
  SbKillR.cycleKillCoreH boot d0 fab im Xof Bad
    (SbKillR.certSupplyOfWalkR boot d0 fab im Xof hbt hdb hwio hdf hW hS) hl2 hnB

/-- **THE SHAPE `CapFetchProv.t2linSupplyCZTtagged` CONSUMES**, (a) + (t3) form. -/
theorem SbKillR.cycleKillAllRH (boot : Nat → Pexv6) (d0 : Efab) (im : Image)
    (Xof : Gfexec → Geid → Prop) (Bad : Prop)
    (hbt : ∀ i, i < NCPU → GraphFabConf.isHart (boot i) = true)
    (hdb : ∀ i, NCPU ≤ i → boot i = .PDisk none)
    (hwio : ∀ fab, CatLin.gfDevWIoCZ boot d0 fab im) (hdf : ∀ fab, SbDevSt.diskFabPoCZ boot d0 fab im)
    (hW : ∀ fab, SbKillR.walkHypCZR boot d0 fab im Xof) (hS : ∀ fab, SbKillR.stateIfcCZR boot d0 fab im Xof)
    (hl2 : ∀ fab, SbKillR.l2ClaimH boot d0 fab im Xof Bad) (hnB : ¬ Bad) :
    ∀ fab, CatLin.cycleKillCZT boot d0 fab im :=
  fun fab => SbKillR.cycleKillOfWalkRH boot d0 fab im Xof Bad hbt hdb (hwio fab) (hdf fab) (hW fab)
    (hS fab) (hl2 fab) hnB

/-! # 5. The machine side: the interim input, the realization, the derivation; (t3) D1/D3

**THE INTERIM INPUT [OWN.155] (w1, MachCSL; NOT BUILT YET)** — `SbKillR.relHopPcAt`: every
certified hop's RELEASE was issued at `release+0x1a`.  The export has `relProvAt` (`pcAt ∈ relPcs =
{release+0x1a, main+0xb0}` at hop releases) and `certHopAt`'s `pcAt = -1` at hop ACQUIRES; the
stamp pins the release to the lock release site (`main+0xb0` stores `started`, never a lock
word).  w1 must export, append-only after conjunct 13, the conjunct

  `Xv6.AccessDiscipline.relHopPcAtP σ :=
     ∀ (b : PAddr) (A B : CPU) (r a : Nat), certHopAt σ b a →
       syncHop (σ.mem.landedOnly σ.lp) b A r B a → σ.pcAt r = (KernelSyms.«release» : Int) + 0x1a`

(stamped on the same `memModel_chainHop` lane as D4); `SbKillR.relHopPcAt` is its body verbatim, so
the discharge is `fun σ hD => <projection of conjunct 14>`.  Spec: the issuing pc is the `PC` of the
Sail instruction whose `memWrite` made the store; FAITHFUL.

**THE P-W6 INPUT** — `SbKillR.HopReal GR σ ev`: at a realized state `σ` of the member `GR`, the
issue stamps of landed entries map to member writes (`ev`) of their author and byte; a landed
history's order is the member's log order; a hart's issue order is its program order; a certified
hop's acquire is an AMO (`CapSync.exclHopReal`'s kind, F-6a-4 inside); a store issued at
`release+0x1a` follows `release+0x16`'s fence with no write between (`LockFacts2.lockReal`'s (L3),
asked at realized stores only).  It replaces `lockRealB`'s (L1) (every lock-word write) and (L2). -/

/-- **THE INTERIM INPUT (NAMED; w1's MachCSL release stamp, [OWN.155])**: a certified hop's release
was issued at `release+0x1a`. -/
def SbKillR.relHopPcAt (σ : MState) : Prop :=
  ∀ (b : PAddr) (A B : CPU) (r a : Nat), Xv6.AccessDiscipline.certHopAt σ b a →
    syncHop (σ.mem.landedOnly σ.lp) b A r B a → σ.pcAt r = (KernelSyms.«release» : Int) + 0x1a

/-- The stamp `t` is a landed entry above another (a post-power-on store). -/
def SbKillR.landedEnt (σ : MState) (t : Nat) : Prop :=
  ∃ (b : PAddr) (H1 H2 : Hist) (e : HEnt),
    (σ.mem.landedOnly σ.lp)[b]? = some (H1 ++ e :: H2) ∧ H2 ≠ [] ∧ e.t = t

/-- **THE REALIZATION AT HOP ENTRIES (NAMED; P-W6's step map)**. -/
structure SbKillR.HopReal (GR : Gexec) (σ : MState) (ev : Nat → Geid) : Prop where
  /-- a landed entry above another is the member write `ev e.t` of its author, writing its byte -/
  wr : ∀ (b : PAddr) (H1 H2 : Hist) (e : HEnt), (σ.mem.landedOnly σ.lp)[b]? = some (H1 ++ e :: H2) →
    H2 ≠ [] → ev e.t ∈ gwrites GR ∧ (ev e.t).1 = e.tid ∧ gwritesByte GR (ev e.t) (paZ b) e.v
  /-- a landed history is in the member's log order -/
  co : ∀ (b : PAddr) (H1 H2 : Hist) (e1 e2 : HEnt),
    (σ.mem.landedOnly σ.lp)[b]? = some (H1 ++ e1 :: e2 :: H2) → H2 ≠ [] →
    gwix GR (ev e2.t) < gwix GR (ev e1.t)
  /-- a hart's issue order is its program order -/
  po : ∀ t t', SbKillR.landedEnt σ t → SbKillR.landedEnt σ t' → t < t' → (ev t).1 = (ev t').1 →
    (ev t).2 < (ev t').2
  /-- a certified hop's acquire is an AMO -/
  acq : ∀ (b : PAddr) (A B : CPU) (r a : Nat), Xv6.AccessDiscipline.certHopAt σ b a →
    syncHop (σ.mem.landedOnly σ.lp) b A r B a →
    ∃ aq rl base ts rvs wvs kc, gxLbl GR (ev a) = some (LRmw aq rl base ts rvs wvs kc)
  /-- (L3) at realized stores: a store issued at `release+0x1a` follows `release+0x16`'s fence -/
  rel : ∀ t, SbKillR.landedEnt σ t → σ.pcAt t = LockFacts.relPc →
    ∃ kf, kf < (ev t).2 ∧ gxLbl GR ((ev t).1, kf) = some LockFacts2.relFenceLbl ∧
      ∀ k', kf < k' → k' < (ev t).2 → ¬ glblIs GR ((ev t).1, k') lbIsW

/-- (L3) puts a po-earlier WRITE before the fence: the stamp. -/
theorem SbKillR.relStampOf (GR : Gexec) (x R : Geid) (kf : Nat) (hx1 : x.1 = R.1) (hxR : x.2 < R.2)
    (hxW : glblIs GR x lbIsW) (hkf : kf < R.2)
    (hfl : gxLbl GR (R.1, kf) = some LockFacts2.relFenceLbl)
    (hnone : ∀ k', kf < k' → k' < R.2 → ¬ glblIs GR (R.1, k') lbIsW) : SbKillR.relStampR GR x R := by
  refine ⟨hx1, kf, ?_, hkf, hfl⟩
  rcases Nat.lt_or_ge x.2 kf with h | h
  · exact h
  · exfalso
    rcases Nat.lt_or_eq_of_le h with hgt | heq
    · exact hnone x.2 hgt hxR (by rw [← hx1]; exact hxW)
    · obtain ⟨l, hl, hw⟩ := hxW
      have hx : gxLbl GR x = some LockFacts2.relFenceLbl := by
        rw [show x = (R.1, kf) from Prod.ext hx1 heq.symm]; exact hfl
      rw [hx, Option.some.injEq] at hl
      subst hl
      simp [LockFacts2.relFenceLbl, lbIsW] at hw

/-- **THE DERIVATION**: the export's certified hop chain from author `A`'s entry at `t` (a write of
the member) is the arm's path at the member, from the interim stamp and the realization. -/
theorem SbKillR.hopsROfChain (GR : Gexec) (σ : MState) (ev : Nat → Geid)
    (hR : SbKillR.HopReal GR σ ev) (hpc : SbKillR.relHopPcAt σ) (hAq : CapSync.amoAqAt GR)
    {A : CPU} {t : Nat} {B : CPU} {a : Nat}
    (h : hopChain (σ.mem.landedOnly σ.lp) (Xv6.AccessDiscipline.certHopAt σ) A t B a) :
    SbKillR.landedEnt σ t → (ev t).1 = hartAgent A → glblIs GR (ev t) lbIsW →
    SbKillR.hopsR GR (ev t) (ev a) ∧ (ev a).1 = hartAgent B ∧ SbKillR.landedEnt σ a := by
  have hop : ∀ (b : PAddr) (C D : CPU) (r a : Nat), Xv6.AccessDiscipline.certHopAt σ b a →
      syncHop (σ.mem.landedOnly σ.lp) b C r D a →
      SbKillR.landedEnt σ r ∧ SbKillR.landedEnt σ a ∧ (ev r).1 = hartAgent C ∧
      (ev a).1 = hartAgent D ∧ lockRel GR (paZ b) (ev r) ∧ lockAcq GR (paZ b) (ev a) ∧
      gwix GR (ev r) < gwix GR (ev a) ∧ SbKillR.acqAmo GR (ev a) ∧ σ.pcAt r = LockFacts.relPc := by
    intro b C D r a hcert hsh
    have hpcr := hpc b C D r a hcert hsh
    obtain ⟨aq, rl, base, ts, rvs, wvs, kc, hl⟩ := hR.acq b C D r a hcert hsh
    have haq := hAq _ aq rl base ts rvs wvs kc hl
    subst haq
    obtain ⟨H1, H2, e0, va, hb, hva, -, -, -, -⟩ := hsh
    have hb' : (σ.mem.landedOnly σ.lp)[b]? =
        some ((H1 ++ [⟨a, hartAgent D, va⟩]) ++ ⟨r, hartAgent C, 0⟩ :: e0 :: H2) := by
      rw [hb]; simp
    obtain ⟨-, hr1, hrw⟩ := hR.wr b _ _ _ hb' (List.cons_ne_nil _ _)
    obtain ⟨-, ha1, haw⟩ := hR.wr b H1 _ _ hb (List.cons_ne_nil _ _)
    have hco := hR.co b H1 (e0 :: H2) _ _ hb (List.cons_ne_nil _ _)
    exact ⟨⟨b, _, _, _, hb', List.cons_ne_nil _ _, rfl⟩, ⟨b, H1, _, _, hb, List.cons_ne_nil _ _, rfl⟩,
      hr1, ha1, hrw, ⟨va, haw, hva⟩, hco, ⟨rl, base, ts, rvs, wvs, kc, hl⟩, hpcr⟩
  induction h with
  | base b hcert hsh htr =>
    intro ht hx1 hxW
    obtain ⟨hlr, hla, hr1, ha1, hrel, hacq, hlt, hamo, hpcr⟩ := hop b _ _ _ _ hcert hsh
    obtain ⟨kf, hkf, hfl, hnone⟩ := hR.rel _ hlr hpcr
    have hxR := hx1.trans hr1.symm
    exact ⟨.base (paZ b) _ _ (SbKillR.relStampOf GR _ _ kf hxR
      (hR.po _ _ ht hlr htr hxR) hxW hkf hfl hnone) hrel hacq hlt hamo, ha1, hla⟩
  | step b _ hcert hsh ha1r ih =>
    intro ht hx1 hxW
    obtain ⟨ih1, ih2, ih3⟩ := ih ht hx1 hxW
    obtain ⟨hlr, hla, hr1, ha1, hrel, hacq, hlt, hamo, -⟩ := hop b _ _ _ _ hcert hsh
    have hAR := ih2.trans hr1.symm
    exact ⟨.step (paZ b) _ _ _ ih1 hAR (hR.po _ _ ih3 hlr ha1r hAR) hrel hacq hlt
      hamo, ha1, hla⟩

/-- **…the arm** (row 6j (a)): the certified path from the observed entry, whose last acquire is at
or po-before the segment's exit (P-W6's in-order realization, as `CapSync.realBefore`). -/
theorem SbKillR.csHypsHOfChain (GD : Gdexec) (GR : Gexec) (σ : MState) (ev : Nat → Geid)
    (hR : SbKillR.HopReal GR σ ev) (hpc : SbKillR.relHopPcAt σ) (hAq : CapSync.amoAqAt GR)
    {A : CPU} {t : Nat} {B : CPU} {a : Nat}
    (h : hopChain (σ.mem.landedOnly σ.lp) (Xv6.AccessDiscipline.certHopAt σ) A t B a)
    (ht : SbKillR.landedEnt σ t) (hx1 : (ev t).1 = hartAgent A) (hxW : glblIs GR (ev t) lbIsW)
    (hxG : glblIs GD.gdG (ev t) lbIsR ∨ glblIs GD.gdG (ev t) lbIsW) (s : Seg)
    (hex : ev a = s.sgExit ∨ (WeakRvwmoGraph.gpo GD.gdG (ev a) s.sgExit ∧ gmem GD.gdG s.sgExit)) :
    SbKillR.csHypsH GD GR (ev t) s :=
  ⟨hxG, ev a, (SbKillR.hopsROfChain GR σ ev hR hpc hAq h ht hx1 hxW).1, hex⟩

/-! ## 5.1 (t3) D3 — G7's fetch certificate with the own-hart corners split off

`CapFetchProv.g7FetchCertP` asks the replay state (`fetchReplayOk`) and the after-direction
(`fetchLateChained`) at EVERY E2/E3 target; both are false for an own write on a user RWX page
(F-6h-2 / F-6h-3).  Here they are asked of FOREIGN targets only — the early half is the named
`fetchEarlyForeign` ([OWN.137]) verbatim, the late half `fetchLateChainedF` ([OWN.101], foreign
targets) — an own E3 edge at/after the slot is certified by (Z2) (`G7FetchOwn.ownLateE3`), and the
rest is the CORNER (`fetchOwnCorner`), which the claim classifies by `cornerJumpH` (D1).

**M-S2 re-check of corner (i)** ([OWN.156]: `fence.i` non-draining, ifetch forwarding the hart's own
pre-`fence.i` stores): a contributor may now be an own store still PENDING at the fetch.  D2's
certificate does not use a drain — it orders the contributor (po-before the hand-off release) by
rule 4 at the release's `fence rw,w` — so corner (i) is closed the same way on the M-S2 machine;
corner (ii) (an own store after the last `fence.i`, not forwarded) is unchanged.  Spec: Zifencei
untouched (no stronger `fence.i`, no scope premise); FAITHFUL. -/

/-- [OWN.101]'s after-direction asked of FOREIGN targets only. -/
def SbKillR.fetchLateChainedF (GD : Gdexec) (C : Geid → Prop) (i k : Nat) (base : Int)
    (tvs : List (Nat × BitVec 8)) : Prop :=
  ∀ (x y : Geid) (s : Seg), G7Fetch.fetchEdge23 GD.gdG C base tvs x y →
    gfcut GD.gdG i k < gwix GD.gdG y → y.1 ≠ i → s.sgEntry = y → CatLin.segRunC GD s →
    chainHyps GD x s

/-- **THE OWN-HART CORNER** of a fetch item (F-6h-3 (i)/(ii)): an E2/E3 edge into an own write. -/
def SbKillR.fetchOwnCorner (GD : Gdexec) (prev : Geid) (s : Seg) : Prop :=
  ∃ (C : Geid → Prop) (i k : Nat) (base : Int) (tvs : List (Nat × BitVec 8)),
    gzFetch GD.gdG C i k base tvs ∧ G7Fetch.fetchEdge23 GD.gdG C base tvs prev s.sgEntry ∧
    s.sgEntry.1 = i

/-- **G7's fetch certificate, (t3) form**: certified, or an own-hart corner. -/
theorem SbKillR.g7FetchCertT (boot : Nat → Pexv6) (GD : Gdexec) (ad : List (Geid × Geid))
    (X : Geid → Geid → Prop) (prev : Geid) (s : Seg) (hc : CatLin.rvwmoCatAD GD ad)
    (hx : gfetchE GD prev s.sgEntry) (hprov : CapFetchProv.provAll boot GD)
    (hrep : ∀ (i : Nat) (row : List Lbl) (em : Hemission) (dvi dvo : Nat → Efab) (tq : Nat → Bool)
      (n : Nat) (base : Int) (tvs : List (Nat × BitVec 8)),
      GD.gdG.gxProg[i]? = some row → hartConff i row (boot i) dvi dvo tq em →
      GraphFetch.emZif GD.gdG i em → em.emItems[n]? = some (Wlabel.LIFetch base tvs, none) →
      fetchEarlyForeign GD.gdG i (GraphFetchSpike.emSlot em.emItems n) base tvs)
    (hlate : ∀ (i : Nat) (row : List Lbl) (em : Hemission) (dvi dvo : Nat → Efab) (tq : Nat → Bool)
      (n : Nat) (base : Int) (tvs : List (Nat × BitVec 8)),
      GD.gdG.gxProg[i]? = some row → hartConff i row (boot i) dvi dvo tq em →
      GraphFetch.emZif GD.gdG i em → em.emItems[n]? = some (Wlabel.LIFetch base tvs, none) →
      SbKillR.fetchLateChainedF GD (GraphFetch.emContrib GD.gdG em i (GraphFetchSpike.emSlot em.emItems n))
        i (GraphFetchSpike.emSlot em.emItems n) base tvs)
    (hrun : CatLin.segRunC GD s) (hm : gmem GD.gdG s.sgExit) :
    CatLin.CertC GD.gdG X prev s ∨ SbKillR.fetchOwnCorner GD prev s := by
  obtain ⟨i, row, em, dvi, dvo, tq, hrow, hem, hzem, n, base, tvs, hn, he⟩ := hprov _ _ hx.1
  have hz := hzem n base tvs hn
  rcases G7Fetch.fetchEdgeCases _ _ i _ base tvs _ _ he with h1 | h23
  · exact .inl (g7E1Chained GD ad X _ i _ base tvs prev s hc hz h1 hrun hm)
  · by_cases hown : s.sgEntry.1 = i
    · obtain ⟨j, t, v, v', hj, hy, ht, hsrc⟩ := id h23
      rcases hsrc with _ | hE3
      · exact .inr ⟨_, i, _, base, tvs, hz, h23, hown⟩
      · by_cases hk : GraphFetchSpike.emSlot em.emItems n ≤ s.sgEntry.2
        · exact .inl (G7FetchOwn.ownLateE3 GD ad X _ i _ base tvs prev s hc hz hE3 hown hk hrun hm)
        · exact .inr ⟨_, i, _, base, tvs, hz, h23, hown⟩
    · by_cases hcut : gwix GD.gdG s.sgEntry ≤ gfcut GD.gdG i (GraphFetchSpike.emSlot em.emItems n)
      · exfalso
        obtain ⟨j, t, v, v', hj, hy, ht, -⟩ := h23
        have := hrep i row em dvi dvo tq n base tvs hrow hem hzem hn j t v hj s.sgEntry v' hy ht hown
        omega
      · exact .inl (chainHypsCertC GD ad X prev s hc
          (hlate i row em dvi dvo tq n base tvs hrow hem hzem hn prev s.sgEntry s h23 (by omega) hown
            rfl hrun))

/-- **(t3) D1 — THE CORNER'S CUSTODY INPUT (NAMED; P-W6-bound, rows A5 / 6n)**: at a finished member,
an own-hart fetch corner of a cyclic raw chain has its predecessor's certified hand-off path into a
segment of the cycle.  *Truth reason (xv6)*: user pages are private to their process, so the cycle
leaves hart `i` across a kernel hand-off (`p->lock` / `wait_lock` / `kmem.lock`) whose release is
po-after the corner; the leaving edge's target observes hart `i`'s entry on a user-page byte, whose
export custody is `.free` (`Xv6.AccessDiscipline.custAtP`: not a lock, publication or PTE byte), so
`chainOkCertAtP` gives the certified path; `hopChain_prefix` moves its source back to an own
contributor, and `csHypsHOfChain` makes it the arm (with `relHopPcAt`, `HopReal`).  P-W6 supplies:
the realized-read map at the leaving edge's target (`readAt … σ` at route P), `HopReal` there, the
mode / process / `satp` facts placing the corner in a user epoch of the page's process, and (for a
FOREIGN contributor) the contributor's own hand-off into hart `i` before `userret` (O2's argument,
as [OWN.137]). -/
def SbKillR.cornerLeaveP (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image)
    (Xof : Gfexec → Geid → Prop) : Prop :=
  ∀ (GF : Gfexec) (ad : List (Geid × Geid)) (c : CandW),
    GF.gfGd.gdG.gxImg = im → GraphFabConf.gfexecConfZF boot d0 fab GF →
    SbKill.finishedP GF (Xof GF) c →
    ∀ (z : Geid) (ss : List Seg), CatLin.rvwmoCatAD GF.gfGd ad →
      CatLin.rawChainC GF.gfGd (ioCross GF) z z ss →
      ∀ (prev : Geid) (s : Seg), s ∈ ss → ioCross GF prev s.sgEntry → CatLin.segRunC GF.gfGd s →
        SbKillR.fetchOwnCorner GF.gfGd prev s →
        SbKillR.cornerJumpH GF.gfGd (memberP GF.gfGd.gdG.gxProg.length c) prev ss

end Weak
