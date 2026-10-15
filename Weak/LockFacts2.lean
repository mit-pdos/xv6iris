/-
Weak: **W11-F part [OWN.98] — the per-pc lock facts (1) `acqAq` and (2) `relCovers`**, PROVED from
the kernel image (`Weak/LockFacts.lean`) and a NAMED realization interface at the realized member.
Lean-only, no Rocq twin.

**Why the member.**  The two facts W10's transport consumes (`CatLin.acqAqCZ`/`relCoversCZ`,
`GraphFetchN2` §2; `CatLin.acqAqCZ2`/`relCoversCZ2`, `CertZ15`) are about the class graph `GF`'s
WRITE events and FENCES, windowed by the member `GR`'s log.  An agreeing member has the same rows up
to read re-indexing (`agreeRP`/`agreeRP2`: `lblReidxW ∘ lblRen pi`), and that relation keeps every
write label (aq, rl, base, data, class) and every fence label verbatim and the program order
unchanged (`LockFacts2.reidxW`, `LockFacts2.fenceOf`).  So both facts at `GF` follow from the same
facts at `GR` (§2) — and `GR` is a REALIZED machine run, where the issuing pc of each write and the
MachCSL lock protocol are run facts the realization carries.  No `GF`-level program fact is used
(contrast `Weak/LockFacts3.lean`).

**THE NAMED INTERFACE `LockFacts2.lockReal GR log P`** (W11-F's composition supplies it; split by
lane like `RelSiteProv`): an issuing-pc map `ipc` on `GR`'s events (`ipc W` = the PC of the hart
state at `W`'s realizing step — `RelSiteProvPc.recPcLog` read through `gwix`) with
  (L1) [MachCSL lane — the lock-word provenance, `RelSiteProv.relProvExport`'s kind] inside each
       registration window of a registered lock word, a write of the word's byte `b` is
       `acquire`'s swap (`ipc = acquire+0x1c`) writing a NONZERO byte, or `release`'s store
       (`ipc = release+0x1a`) writing ZERO — what `lockWordDiscAt`'s lock-shaped writes are, with
       the issuing pc (`wp_s_amoswap`/`wp_s_sw_zero_release_gen`) and the value (`li a4,1`;
       `mv a5,a4` — `LockFacts.acqLoopWords`; `sw zero` — `LockFacts.relStoreWord`);
  (L2) [Sail lane — AMO execute, through the fetch facts r1–r3] a write issued at `acquire+0x1c`
       is the swap's `LRmw` whose `.aq` is the word's aq bit, or an 8-byte write (the page-table
       walker's A/D write-back for the swap's page, an implicit access issued at the same pc);
  (L3) [pf-run lane — release adjacency] a write issued at `release+0x1a` has, earlier in its
       row, a fence whose bits are the word's at `release+0x16`, with NO write of the row between
       — the fence is the immediately preceding instruction (`LockFacts.relAdj`), interrupts are
       off (`push_off`), no exception at the store, and no A/D write-back between (the lock's page
       is already dirty: the holder's own swap wrote it; Q-WCREL-2's layout fact).

**Proved here.**  `LockFacts2.acqAqLogOfReal` / `LockFacts2.relCoversLogOfReal` (per registry, any
agreeing member; the image supplies `wAmoAq = 1` at `acquire+0x1c` and `pw = sw = 1` at
`release+0x16`), and the four named premises discharged modulo the interface:
**`CatLin.acqAqCZOfSites`**, **`CatLin.relCoversCZOfSites`** (from `CatLin.lockSitesCZ`) and
**`CatLin.acqAqCZ2OfSites`**, **`CatLin.relCoversCZ2OfSites`** (from `CatLin.lockSitesCZ2`).  The
per-registry lemmas take only the agreement's image and rows, so W10's later agreements (`agreeRP3`,
`CertZ18`) reuse them unchanged.

**Image vs run.**  IMAGE: the aq bit, the fence bits, the release store's zero data register, the
fence/store adjacency, AMO uniqueness (`LockFacts`).  RUN (named in `lockReal`): which pc issued a
member write (L1), the label Sail emits at that pc (L2), the dynamic adjacency (L3).

Spec: rule 4 (`fence rw,w`: pw before, sw after) and the `.aq` bit are riscv.cat's; the interface is
a set of facts of xv6's runs (FAITHFUL once W11-F proves them, WEAKER while named).  Every name is
file-qualified (`LockFacts2.*`) except the `CatLin.*` premise discharges.
-/
import Weak.LockFacts
import Weak.CertZ15

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open TsoShadow
open Lbl

/-! # 1. The realization interface (NAMED) -/

/-- The bits of the fence at `release+0x16`, as a label. -/
def LockFacts2.relFenceLbl : Lbl :=
  LFence (wFencePr (kw (LockFacts.relPc - 4))) (wFencePw (kw (LockFacts.relPc - 4)))
    (wFenceSr (kw (LockFacts.relPc - 4))) (wFenceSw (kw (LockFacts.relPc - 4)))

/-- **THE REALIZATION INTERFACE (NAMED; W11-F supplies it)** — header (L1)–(L3). -/
def LockFacts2.lockReal (GR : Gexec) (log : List Wmsg) (P : Int → Int → Prop) : Prop :=
  ∃ ipc : Geid → Int,
    -- (L1) MachCSL lock-word provenance, inside each registration window
    (∀ a b n0 r0 h, P a b → wprotAt log a b n0 r0 → wlpAt log b b n0 → wlpAlt log b n0 h →
      ∀ W v, CatLin.GraphFetchN2.inWin GR log n0 W → gwritesByte GR W b v →
        (ipc W = LockFacts.acqPc ∧ v ≠ lockFree) ∨ (ipc W = LockFacts.relPc ∧ v = lockFree)) ∧
    -- (L2) Sail: the swap's label carries the word's aq bit (or it is the walker's 8-byte write-back)
    (∀ W, W ∈ gwrites GR → ipc W = LockFacts.acqPc →
      (∃ rl base ts rvs wvs k,
          gxLbl GR W = some (LRmw (wAmoAq (kw LockFacts.acqPc)) rl base ts rvs wvs k)) ∨
      (∃ l base vs, gxLbl GR W = some l ∧ lbWr l = some (base, vs) ∧ vs.length = 8)) ∧
    -- (L3) release adjacency: the `release+0x16` fence earlier in the row, no write between
    (∀ W, W ∈ gwrites GR → ipc W = LockFacts.relPc →
      ∃ kf, kf < W.2 ∧ gxLbl GR (W.1, kf) = some LockFacts2.relFenceLbl ∧
        ∀ k', kf < k' → k' < W.2 → ¬ glblIs GR (W.1, k') lbIsW)

/-! # 2. Transfer along the agreement -/

/-- What `lblReidxW ∘ lblRen pi` keeps: write-ness, and on writes aq / read-ness / write footprint. -/
theorem LockFacts2.reidxW (pi : Nat → Nat) (l l' : Lbl) :
    lblReidxW (lblRen pi l) l' → lbIsW l' = lbIsW l ∧
      (lbIsW l = true → lbAq l' = lbAq l ∧ lbIsR l' = lbIsR l ∧ lbWr l' = lbWr l) := by
  intro h
  rcases h with h | h | h
  · cases l <;> cases l' <;>
      simp_all [lblRen, lblReidx, lbIsW, lbAq, lbIsR, lbWr]
  · cases l <;> cases l' <;> simp_all [lblRen, lblReidxSub, lbIsW]
  · cases l <;> cases l' <;> simp_all [lblRen, lblPoisoned, lbIsW]

/-- A fence of the member is a fence of the class graph (fences are verbatim). -/
theorem LockFacts2.fenceOf (pi : Nat → Nat) (l : Lbl) (pr pw sr sw : Bool) :
    lblReidxW (lblRen pi l) (LFence pr pw sr sw) → l = LFence pr pw sr sw := by
  intro h
  rcases h with h | h | h
  · cases l <;> simp_all [lblRen, lblReidx]
  · cases l <;> simp_all [lblRen, lblReidxSub]
  · cases l <;> simp_all [lblRen, lblPoisoned]

/-- The agreement's image and rows, as an `agreeRP` at the empty lock set. -/
abbrev LockFacts2.rowsAg (G GR : Gexec) (pi : Nat → Nat) : Prop :=
  GraphFetchN2.agreeRP G GR pi (fun _ => False)

theorem LockFacts2.rowsAgOfRP (G GR : Gexec) (pi : Nat → Nat) (L : Int → Prop) :
    GraphFetchN2.agreeRP G GR pi L → LockFacts2.rowsAg G GR pi :=
  fun h => ⟨h.1, h.2.1, fun _ _ _ _ _ hb => hb.elim⟩

theorem LockFacts2.rowsAgOfRP2 (G GR : Gexec) (pi : Nat → Nat) (L : Int → Prop) :
    CertZ14.agreeRP2 G GR pi L → LockFacts2.rowsAg G GR pi :=
  fun h => ⟨h.1, h.2.1, fun _ _ _ _ _ hb => hb.elim⟩

theorem LockFacts2.wbyte (G GR : Gexec) (pi : Nat → Nat) (e : Geid) (a : Int) (v : BitVec 8) :
    LockFacts2.rowsAg G GR pi → gwritesByte G e a v → gwritesByte GR e a v :=
  fun hag h => ((GraphFetchN2.agreeWOfRP G GR pi _ hag).2.1 e a v).2 h

theorem LockFacts2.isW (G GR : Gexec) (pi : Nat → Nat) (e : Geid) :
    LockFacts2.rowsAg G GR pi → glblIs G e lbIsW → glblIs GR e lbIsW := by
  rintro hag ⟨l, hl, hw⟩
  rcases GraphFetchN2.agreeRPLbl G GR pi _ e hag with ⟨h1, -⟩ | ⟨l0, l', h1, h2, hr⟩
  · rw [h1] at hl; cases hl
  · rw [h1] at hl; cases hl
    exact ⟨l', h2, by rw [(LockFacts2.reidxW pi l l' hr).1]; exact hw⟩

/-- An `.aq` read-write at the member is one at the class graph. -/
theorem LockFacts2.rmwAqOf (G GR : Gexec) (pi : Nat → Nat) (e : Geid) (rl : Bool) (base : Int)
    (ts : List Nat) (rvs wvs : List (BitVec 8)) (k : WmClass) :
    LockFacts2.rowsAg G GR pi → gxLbl GR e = some (LRmw true rl base ts rvs wvs k) →
    glblIs G e lbIsR ∧ glblIs G e lbAq := by
  intro hag hl
  rcases GraphFetchN2.agreeRPLbl G GR pi _ e hag with ⟨-, h2⟩ | ⟨l0, l', h1, h2, hr⟩
  · rw [h2] at hl; cases hl
  · rw [h2] at hl; cases hl
    obtain ⟨hw, hrest⟩ := LockFacts2.reidxW pi l0 _ hr
    have hw0 : lbIsW l0 = true := by rw [← hw]; rfl
    obtain ⟨haq, hR, -⟩ := hrest hw0
    exact ⟨⟨l0, h1, by rw [← hR]; rfl⟩, ⟨l0, h1, by rw [← haq]; rfl⟩⟩

/-- A fence at the member is a fence at the class graph. -/
theorem LockFacts2.fenceAt (G GR : Gexec) (pi : Nat → Nat) (e : Geid) (pr pw sr sw : Bool) :
    LockFacts2.rowsAg G GR pi → gxLbl GR e = some (LFence pr pw sr sw) →
    gxLbl G e = some (LFence pr pw sr sw) := by
  intro hag hl
  rcases GraphFetchN2.agreeRPLbl G GR pi _ e hag with ⟨-, h2⟩ | ⟨l0, l', h1, h2, hr⟩
  · rw [h2] at hl; cases hl
  · rw [h2] at hl; cases hl
    rw [h1, LockFacts2.fenceOf pi l0 pr pw sr sw hr]

/-! # 3. The two facts, per registry -/

/-- **(1) `acqAq`** — every acquire of a registered lock byte inside its window is an `.aq` read,
from the interface and the image's aq bit. -/
theorem LockFacts2.acqAqLogOfReal (G GR : Gexec) (pi : Nat → Nat) (log : List Wmsg)
    (P : Int → Int → Prop) :
    LockFacts2.rowsAg G GR pi → gwf GR → logOf GR log → LockFacts2.lockReal GR log P →
    CatLin.acqAqLog G GR log P := by
  rintro hag hwf hlog ⟨ipc, hL1, hL2, -⟩ a b n0 r0 h hP hprot hlp halt A ⟨v, hwA, hv⟩ hwin
  have hwA' := LockFacts2.wbyte G GR pi A b v hag hwA
  rcases hL1 a b n0 r0 h hP hprot hlp halt A v hwin hwA' with ⟨hpc, -⟩ | ⟨-, hv0⟩
  · have hAw : A ∈ gwrites GR := gwritesByteGwrites GR A b v hwf hwA'
    rcases hL2 A hAw hpc with ⟨rl, base, ts, rvs, wvs, k, hl⟩ | ⟨l, base, vs, hl, hwr, hlen⟩
    · rw [LockFacts.acqAqBit] at hl
      exact LockFacts2.rmwAqOf G GR pi A rl base ts rvs wvs k hag hl
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

/-- **(2) `relCovers`** — a release of a registered lock byte inside its window fence-covers every
write of its row po-before it, from the interface and the image's fence bits. -/
theorem LockFacts2.relCoversLogOfReal (G GR : Gexec) (pi : Nat → Nat) (log : List Wmsg)
    (P : Int → Int → Prop) :
    LockFacts2.rowsAg G GR pi → gwf GR → LockFacts2.lockReal GR log P →
    CatLin.relCoversLog G GR log P := by
  rintro hag hwf ⟨ipc, hL1, -, hL3⟩ a b n0 r0 h hP hprot hlp halt A R x _ hR _ hwinR _ hxR hxW
  have hR' := LockFacts2.wbyte G GR pi R b lockFree hag hR
  rcases hL1 a b n0 r0 h hP hprot hlp halt R lockFree hwinR hR' with ⟨-, hne⟩ | ⟨hpc, -⟩
  · exact absurd rfl hne
  have hRw : R ∈ gwrites GR := gwritesByteGwrites GR R b lockFree hwf hR'
  obtain ⟨kf, hkf, hfl, hnone⟩ := hL3 R hRw hpc
  obtain ⟨hx1, hx2, -, -⟩ := hxR
  have hxW' := LockFacts2.isW G GR pi x hag hxW
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
  have hfG := LockFacts2.fenceAt G GR pi (R.1, kf) _ _ _ _ hag hfl
  obtain ⟨-, hpw, -, hsw⟩ := LockFacts.relFenceBits.2
  refine ⟨wFencePr (kw (LockFacts.relPc - 4)), wFencePw (kw (LockFacts.relPc - 4)),
    wFenceSr (kw (LockFacts.relPc - 4)), wFenceSw (kw (LockFacts.relPc - 4)),
    ⟨hx1, by omega, kf, hxk, hkf, by rw [hx1]; exact hfG⟩,
    .inr ⟨hxW, hpw⟩, .inr ⟨gwritesByteGlblW G R b lockFree hR, hsw⟩⟩

/-! # 4. The named premises, discharged modulo the interface -/

namespace CatLin

/-- **THE INTERFACE OVER THE CLASS (NAMED; W11-F)**, in `acqAqCZ`'s quantifier shape: every agreeing
member whose log carries the export realizes the lock sites. -/
def lockSitesCZ (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image)
    (P : Int → Int → Prop) : Prop :=
  ∀ (GF : Gfexec) (ad : List (Geid × Geid)) (GR : Gexec) (pi : Nat → Nat) (log : List Wmsg),
    GF.gfGd.gdG.gxImg = im → rvwmoCatAD GF.gfGd ad → GraphFabConf.gfexecConfZF boot d0 fab GF →
    gwf GR → GraphFetchN2.agreeRP GF.gfGd.gdG GR pi (GraphFetchN2.lockBytes P) → gwrowGmo GR →
    logOf GR log → protReg P log →
    LockFacts2.lockReal GR log P

/-- As `lockSitesCZ`, at the protocol agreement (`acqAqCZ2`'s shape). -/
def lockSitesCZ2 (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image)
    (P : Int → Int → Prop) : Prop :=
  ∀ (GF : Gfexec) (ad : List (Geid × Geid)) (GR : Gexec) (pi : Nat → Nat) (log : List Wmsg),
    GF.gfGd.gdG.gxImg = im → rvwmoCatAD GF.gfGd ad → GraphFabConf.gfexecConfZF boot d0 fab GF →
    gwf GR → CertZ14.agreeRP2 GF.gfGd.gdG GR pi (GraphFetchN2.lockBytes P) → gwrowGmo GR →
    logOf GR log → protReg P log →
    LockFacts2.lockReal GR log P

theorem acqAqCZOfSites (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image)
    (P : Int → Int → Prop) : lockSitesCZ boot d0 fab im P → acqAqCZ boot d0 fab im P :=
  fun hs GF ad GR pi log him hc hconf hwf hag hrow hlog hpr =>
    LockFacts2.acqAqLogOfReal _ GR pi log P (LockFacts2.rowsAgOfRP _ _ _ _ hag) hwf hlog
      (hs GF ad GR pi log him hc hconf hwf hag hrow hlog hpr)

theorem relCoversCZOfSites (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image)
    (P : Int → Int → Prop) : lockSitesCZ boot d0 fab im P → relCoversCZ boot d0 fab im P :=
  fun hs GF ad GR pi log him hc hconf hwf hag hrow hlog hpr =>
    LockFacts2.relCoversLogOfReal _ GR pi log P (LockFacts2.rowsAgOfRP _ _ _ _ hag) hwf
      (hs GF ad GR pi log him hc hconf hwf hag hrow hlog hpr)

theorem acqAqCZ2OfSites (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image)
    (P : Int → Int → Prop) : lockSitesCZ2 boot d0 fab im P → acqAqCZ2 boot d0 fab im P :=
  fun hs GF ad GR pi log him hc hconf hwf hag hrow hlog hpr =>
    LockFacts2.acqAqLogOfReal _ GR pi log P (LockFacts2.rowsAgOfRP2 _ _ _ _ hag) hwf hlog
      (hs GF ad GR pi log him hc hconf hwf hag hrow hlog hpr)

theorem relCoversCZ2OfSites (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image)
    (P : Int → Int → Prop) : lockSitesCZ2 boot d0 fab im P → relCoversCZ2 boot d0 fab im P :=
  fun hs GF ad GR pi log him hc hconf hwf hag hrow hlog hpr =>
    LockFacts2.relCoversLogOfReal _ GR pi log P (LockFacts2.rowsAgOfRP2 _ _ _ _ hag) hwf
      (hs GF ad GR pi log him hc hconf hwf hag hrow hlog hpr)

end CatLin

end Weak
