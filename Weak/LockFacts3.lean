/-
Weak: **W11-F part [OWN.98] — the per-pc lock facts at the CLASS GRAPH `GF`** (the facts W10's walk
ORDER uses: NF1–NF5 of `CertZ17`, the plain-store fact F2, the PLIC/fabric fact).  Lean-only, no Rocq
twin.  Companion of `Weak/LockFacts.lean` (image) and `Weak/LockFacts2.lean` (facts (1)(2) at the
member).

  §1  **(7) THE PLIC/FABRIC FACT — PROVED on hart rows** (`LockFacts3.hartDevIo`): on an xv6 bundle
      every fabric member of a hart row is an I/O event.  The PLIC wire step is NOT administrative
      (`lbAdmin`: `LDev` is a realizing step of its own, projecting to `LIo .dev`), a hart's
      non-`LDev` steps keep the fabric (`pdevEvOk`) — `GraphFabConf.hemitfHartIo`.  Hence no hart's
      lock-byte write is a fabric member and no hart row has a non-I/O member (`lockWNotDevHart`,
      `fabWNotHart`).  (W10's finding 2(ii) — "a CPU RAM write whose leading star contains a PLIC
      wire item is a fabric member" — does not arise in this model.)
  §2  NF3 from the hart half + two NAMED device-row facts (`LockFacts3.diskLockFree`: the virtio
      device never DMA-writes a lock byte; `LockFacts3.diskFabPo`: the device row's fabric RAM
      stores are gmo-ordered along its program order) — **`LockFacts3.nf3OfDisk`**.
  §3  **NF5 — PROVED per release site** (`LockFacts3.nf5Site`): a write with the `release+0x16`
      fence earlier in its row and no write between is gmo-after every po-earlier RAM write (rule 4,
      the image's `pw`/`sw` bits) and every po-earlier I/O event (the trusted residue's R2).  At lock
      releases (`LockFacts3.nf5`) through the NAMED `GF`-level site fact `LockFacts3.relSitesGF`.
  §4  NF1 RESTRICTED TO SUCCESSFUL OPERATIONS (`LockFacts3.nf1S`; CertZ17's unrestricted NF1 is
      FALSE on contended locks) and NF2 with a SUCCESSFUL section acquire (`LockFacts3.nf2S`), NAMED;
      the bundle **`LockFacts3.lockDiscGF`** and **`LockFacts3.lockDiscGFFacts`** (NF1′, NF2, NF3,
      NF5 from it); the class premise **`CatLin.lockDiscGFCZ`**.

**Why §2's device facts, `relSitesGF`, NF1′ and NF2 stay NAMED (spec-first finding).**  They are
facts about WHICH bytes a write touches (address provenance) or about cross-hart VALUES (mutual
exclusion, `holding()`'s `lk->cpu` test), quantified over EVERY class graph `GF`.  Such a fact
holds of xv6 executions — but at an arbitrary `GF` it is part of what the published theorem
establishes (a racy-cyclic `GF` is refuted only by the kill that consumes the order); the
realization supplies these facts at a REALIZED member (`Weak/LockFacts2.lean`), and the member is
built FROM the order (Q-W10-ORDER (a): "circular unless taken at GF").  So they cannot be proved per
pc at `GF` without either a well-founded construction (the order built along a realized prefix) or
a per-row value-independent argument; neither exists yet.  They are FAITHFUL statements (true of
xv6 under RVWMO, as far as checked) and WEAKER while named.

**F2 / CertZ17's NF4 are FALSE (spec-first, concrete).**  "A plain store to a lock byte is
gmo-before every later write of its hart to another lock byte": boot, hart 0 — `uartinitone`
(second UART) calls `initlock(&uarts[1].lock)`, whose `sw zero,0(a0)` (`initlock+0x0a`,
`LockFacts.initStoreWord`, plain) is followed, with only plain stores, returns, `csrr`/`csrc
sstatus` and loads in between (consoleinit's `devsw` stores, `printkinit`'s `initlock(&pr.lock)`,
`printk`'s prologue, `push_off`, `holding`), by `printk`'s `acquire(&pr.lock)` swap
(`printk+0x26` → `acquire+0x1c`, `amoswap.w.aq`, NO `.rl`); no fence (`LockFacts.fenceCensus`: none
there), no I/O, no same-address store between.  RVWMO: ppo rule 1 needs the same address, rule 4 a
fence, rules 5–7 an `.aq` on the EARLIER access or `.rl` on the later one — none applies, so the
swap may precede the plain store in gmo.  (Even `printkinit`'s own `pr.lock` init store is
followed by its first acquire of the SAME byte — fine by rule 1 — but the `uarts[1].lock` store is
not.)  Harmless for xv6 (only hart 0 runs; `started = 1` at `main+0xb0` follows `fence rw,w`).
Options: (a) DROP F2 — under W10's decision (i) the order respects co only among SUCCESSFUL
protocol writes, so plain stores carry no order edge and F2 is not used (FAITHFUL); (b) restrict F2
to what an order edge into a plain store would need (pipe locks' new life after `kfree`/`kalloc`:
the `kmem.lock` release fence in `kalloc` precedes `pipealloc`'s `initlock` — the protocol write
of the OLD life is gmo-before it through that release, not the plain store before later writes)
(FAITHFUL, +S); (c) assume F2 (STRONGER than RVWMO — it excludes the executions above; reject).

Every name is file-qualified (`LockFacts3.*`) except `CatLin.lockDiscGFCZ`.
-/
import Weak.LockFacts2
import Weak.CertZ17

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open TsoShadow
open Lbl

/-! # 1. (7) THE PLIC/FABRIC FACT on hart rows (PROVED) -/

/-- **Every fabric member of a hart row is an I/O event** (xv6 bundle). -/
theorem LockFacts3.hartDevIo (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (GF : Gfexec) :
    GraphFabConf.gfexecConfZF boot d0 fab GF →
    (∀ i, i < NCPU → GraphFabConf.isHart (boot i) = true) →
    ∀ e, e ∈ GF.gfDev → e.1 < NCPU → gisIo GF.gfGd.gdG e = true := by
  rintro ⟨-, -, hbnd, hc⟩ hboot ⟨i, k⟩ hmem hiN
  obtain ⟨n, hn⟩ := List.mem_iff_getElem?.1 hmem
  obtain ⟨row, hrow, hlt⟩ := hbnd n i k hn
  obtain ⟨em, dvi, dvo, tq, hem, hiff, -, -, -⟩ := hc i row hrow
  have hem' : hemitf dvi dvo tq 0 wsInit row (boot i) em.emItems em.emFin := hem
  have hio : ∀ lb, row[k]? = some lb → lbIsIo lb = true → gisIo GF.gfGd.gdG (i, k) = true := by
    intro lb hlk hlb
    unfold gisIo gxLbl
    rw [hrow]
    simp only [Option.bind_some, hlk]
    exact hlb
  rcases (hiff k hlt).1 hmem with h | h | h
  · exact h
  · obtain ⟨lb, hlk, hlb⟩ := GraphFabConf.hemitfHartIo _ _ _ _ _ _ _ _ _ hem' (hboot i hiN) k
      (Nat.zero_le _) (by omega) (Or.inl h)
    rw [Nat.sub_zero] at hlk
    exact hio lb hlk hlb
  · obtain ⟨lb, hlk, hlb⟩ := GraphFabConf.hemitfHartIo _ _ _ _ _ _ _ _ _ hem' (hboot i hiN) k
      (Nat.zero_le _) (by omega) (Or.inr h)
    rw [Nat.sub_zero] at hlk
    exact hio lb hlk hlb

/-- No hart's lock-byte write is a fabric member. -/
theorem LockFacts3.lockWNotDevHart (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab)
    (GF : Gfexec) (Lb : Int → Prop) :
    GraphFabConf.gfexecConfZF boot d0 fab GF →
    (∀ i, i < NCPU → GraphFabConf.isHart (boot i) = true) →
    ∀ e, CertZ17.lockW GF.gfGd.gdG Lb e → e.1 < NCPU → e ∉ GF.gfDev := by
  intro hc hb e hl hi hm
  have h := LockFacts3.hartDevIo boot d0 fab GF hc hb e hm hi
  rw [(CertZ17.lockWIo _ Lb e hl).1] at h
  cases h

/-- No hart row has a non-I/O fabric member. -/
theorem LockFacts3.fabWNotHart (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab)
    (GF : Gfexec) :
    GraphFabConf.gfexecConfZF boot d0 fab GF →
    (∀ i, i < NCPU → GraphFabConf.isHart (boot i) = true) →
    ∀ e, CertZ17.fabW GF e → NCPU ≤ e.1 := by
  rintro hc hb e ⟨hm, hio⟩
  refine Nat.le_of_not_lt (fun hi => ?_)
  rw [LockFacts3.hartDevIo boot d0 fab GF hc hb e hm hi] at hio
  cases hio

/-! # 2. NF3 from the hart half and the device-row facts -/

/-- **NAMED (device model, W14 / the virtio invariant, like `usedElemGateOk`)**: the device rows
never write a lock byte (DMA targets are buffer data, the used ring and the status bytes). -/
def LockFacts3.diskLockFree (GF : Gfexec) (Lb : Int → Prop) : Prop :=
  ∀ e, NCPU ≤ e.1 → ¬ CertZ17.lockW GF.gfGd.gdG Lb e

/-- **NAMED (device model)**: a device row's fabric RAM stores are gmo-ordered along its program
order. -/
def LockFacts3.diskFabPo (GF : Gfexec) : Prop :=
  ∀ f e, CertZ17.fabW GF f → CertZ17.fabW GF e → WeakRvwmoGraph.gpo GF.gfGd.gdG f e →
    gmoLt GF.gfGd.gdG f e

/-- **NF3** (CertZ17's text): no lock-byte write is a fabric member, and a fabric RAM write is
gmo-before every po-later lock-byte or fabric RAM write of its row. -/
theorem LockFacts3.nf3OfDisk (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (GF : Gfexec)
    (Lb : Int → Prop) :
    GraphFabConf.gfexecConfZF boot d0 fab GF →
    (∀ i, i < NCPU → GraphFabConf.isHart (boot i) = true) →
    LockFacts3.diskLockFree GF Lb → LockFacts3.diskFabPo GF →
    (∀ e, CertZ17.lockW GF.gfGd.gdG Lb e → e ∉ GF.gfDev) ∧
    (∀ f e, CertZ17.fabW GF f →
      (CertZ17.lockW GF.gfGd.gdG Lb e ∨ CertZ17.fabW GF e) →
      WeakRvwmoGraph.gpo GF.gfGd.gdG f e → gmoLt GF.gfGd.gdG f e) := by
  intro hc hb hdl hdp
  refine ⟨fun e hl => ?_, fun f e hf he hpo => ?_⟩
  · by_cases hi : e.1 < NCPU
    · exact LockFacts3.lockWNotDevHart boot d0 fab GF Lb hc hb e hl hi
    · exact absurd hl (hdl e (by omega))
  · have hfi := LockFacts3.fabWNotHart boot d0 fab GF hc hb f hf
    rcases he with hl | hfe
    · exact absurd hl (hdl e (by rw [← hpo.1]; exact hfi))
    · exact hdp f e hf hfe hpo

/-! # 3. NF5 at a release site (PROVED per row) -/

/-- The release-site shape at `GF`: the `release+0x16` fence earlier in the row, no write between. -/
def LockFacts3.relAdjAt (G : Gexec) (x : Geid) : Prop :=
  ∃ kf, kf < x.2 ∧ gxLbl G (x.1, kf) = some LockFacts2.relFenceLbl ∧
    ∀ k', kf < k' → k' < x.2 → ¬ glblIs G (x.1, k') lbIsW

/-- A po-earlier write lies before the site's fence. -/
theorem LockFacts3.writeBeforeFence (G : Gexec) (x e : Geid) (kf : Nat) :
    gxLbl G (x.1, kf) = some LockFacts2.relFenceLbl →
    (∀ k', kf < k' → k' < x.2 → ¬ glblIs G (x.1, k') lbIsW) →
    WeakRvwmoGraph.gpo G e x → glblIs G e lbIsW → e.2 < kf := by
  intro hfl hnone hpo hw
  obtain ⟨h1, h2, -, -⟩ := hpo
  rcases Nat.lt_or_ge e.2 kf with hlt | hge
  · exact hlt
  · exfalso
    rcases Nat.lt_or_eq_of_le hge with hgt | heq
    · exact hnone e.2 hgt h2 (by rw [← h1]; exact hw)
    · obtain ⟨l, hl, hwl⟩ := hw
      have : gxLbl G e = some LockFacts2.relFenceLbl := by
        rw [show e = (x.1, kf) from Prod.ext h1 heq.symm]; exact hfl
      rw [this] at hl
      cases hl
      simp [LockFacts2.relFenceLbl, lbIsW] at hwl

/-- **NF5 at a release site**: such a write is gmo-after every po-earlier RAM write (rule 4: the
fence's `pw`/`sw`, from the image) and every po-earlier I/O event (the residue's R2). -/
theorem LockFacts3.nf5Site (GF : Gfexec) (ad : List (Geid × Geid)) (x : Geid) :
    CatLin.rvwmoCatAD GF.gfGd ad → ioResidueGmo GF → glblIs GF.gfGd.gdG x lbIsW →
    LockFacts3.relAdjAt GF.gfGd.gdG x →
    ∀ e, WeakRvwmoGraph.gpo GF.gfGd.gdG e x →
      (glblIs GF.gfGd.gdG e lbIsW ∨ gisIo GF.gfGd.gdG e = true) → gmoLt GF.gfGd.gdG e x := by
  intro hc hres hxW ⟨kf, hkf, hfl, hnone⟩ e hpo he
  rcases he with hw | hio
  · have hek := LockFacts3.writeBeforeFence _ x e kf hfl hnone hpo hw
    obtain ⟨-, hpw, -, hsw⟩ := LockFacts.relFenceBits.2
    have hcov : gfenceCovers GF.gfGd.gdG e x :=
      ⟨_, _, _, _, ⟨hpo.1, hpo.2.1, kf, hek, hkf, by rw [hpo.1]; exact hfl⟩,
        .inr ⟨hw, hpw⟩, .inr ⟨hxW, hsw⟩⟩
    exact CatLin.fenceGmoAfterC _ e x hc.2.1 hcov
  · have hxw : gisW GF.gfGd.gdG x = true := by
      obtain ⟨l, hl, hwl⟩ := hxW
      unfold gisW; rw [hl]; exact hwl
    exact hres e x (.inr (.inl ⟨hpo, hio, hxw⟩))

/-- **NAMED (`GF`-level site fact; header)**: every non-plain release of a lock byte is a
release-site write. -/
def LockFacts3.relSitesGF (GF : Gfexec) (Lb : Int → Prop) : Prop :=
  ∀ b x, Lb b → lockRel GF.gfGd.gdG b x → CertZ14.np GF.gfGd.gdG x →
    LockFacts3.relAdjAt GF.gfGd.gdG x

/-- **NF5** at the lock releases. -/
theorem LockFacts3.nf5 (GF : Gfexec) (ad : List (Geid × Geid)) (Lb : Int → Prop) :
    CatLin.rvwmoCatAD GF.gfGd ad → ioResidueGmo GF → LockFacts3.relSitesGF GF Lb →
    ∀ b x, Lb b → lockRel GF.gfGd.gdG b x → CertZ14.np GF.gfGd.gdG x →
      ∀ e, WeakRvwmoGraph.gpo GF.gfGd.gdG e x →
        (glblIs GF.gfGd.gdG e lbIsW ∨ gisIo GF.gfGd.gdG e = true) → gmoLt GF.gfGd.gdG e x :=
  fun hc hres hs b x hb hx hnp =>
    LockFacts3.nf5Site GF ad x hc hres (gwritesByteGlblW _ x b lockFree hx) (hs b x hb hx hnp)

/-! # 4. NF1 at SUCCESSFUL operations, NF2, the bundle -/

/-- A SUCCESSFUL protocol write of `b`: non-plain, and not a failed acquire (a nonzero write that
read a nonzero byte). -/
def LockFacts3.succW (G : Gexec) (b : Int) (e : Geid) : Prop :=
  CertZ14.np G e ∧
  ¬ ((∃ v, gwritesByte G e b v ∧ v ≠ lockFree) ∧ (∃ t v, greadsByte G e b t v ∧ v ≠ lockFree))

/-- The release `x`'s critical-section acquire `a`, SUCCESSFUL (it read the free byte). -/
def LockFacts3.csAcqS (G : Gexec) (b : Int) (x a : Geid) : Prop :=
  CertZ17.csAcq G b x a ∧ ∃ t, greadsByte G a b t lockFree

/-- **NF1′ (NAMED, `GF`-level; header)**: critical sections of one lock do not overlap in co among
SUCCESSFUL protocol writes of other harts. -/
def LockFacts3.nf1S (GF : Gfexec) (Lb : Int → Prop) : Prop :=
  ∀ b x a w vw, Lb b → lockRel GF.gfGd.gdG b x → CertZ14.np GF.gfGd.gdG x →
    LockFacts3.csAcqS GF.gfGd.gdG b x a → gwritesByte GF.gfGd.gdG w b vw →
    LockFacts3.succW GF.gfGd.gdG b w → w.1 ≠ x.1 →
    gwix GF.gfGd.gdG w < gwix GF.gfGd.gdG a ∨ gwix GF.gfGd.gdG x < gwix GF.gfGd.gdG w

/-- **NF2 (NAMED, `GF`-level; header)**: a non-plain release has its own SUCCESSFUL section acquire;
a non-plain nonzero lock-byte write is an `.aq` read; a non-plain write touches one lock byte. -/
def LockFacts3.nf2S (GF : Gfexec) (Lb : Int → Prop) : Prop :=
  (∀ b x, Lb b → lockRel GF.gfGd.gdG b x → CertZ14.np GF.gfGd.gdG x →
    ∃ a, LockFacts3.csAcqS GF.gfGd.gdG b x a) ∧
  (∀ b e v, Lb b → gwritesByte GF.gfGd.gdG e b v → v ≠ lockFree → CertZ14.np GF.gfGd.gdG e →
    glblIs GF.gfGd.gdG e lbIsR ∧ glblIs GF.gfGd.gdG e lbAq) ∧
  (∀ b b' e v v', Lb b → Lb b' → gwritesByte GF.gfGd.gdG e b v → gwritesByte GF.gfGd.gdG e b' v' →
    CertZ14.np GF.gfGd.gdG e → b = b')

/-- **THE `GF`-LEVEL LOCK DISCIPLINE (NAMED parts)**: NF1′, NF2, the release-site fact, the two
device-row facts. -/
def LockFacts3.lockDiscGF (GF : Gfexec) (Lb : Int → Prop) : Prop :=
  LockFacts3.nf1S GF Lb ∧ LockFacts3.nf2S GF Lb ∧ LockFacts3.relSitesGF GF Lb ∧
  LockFacts3.diskLockFree GF Lb ∧ LockFacts3.diskFabPo GF

/-- **NF1′, NF2, NF3 and NF5** on an xv6 bundle from the named parts (NF3's hart half and NF5's
ordering are proved here). -/
theorem LockFacts3.lockDiscGFFacts (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab)
    (GF : Gfexec) (ad : List (Geid × Geid)) (Lb : Int → Prop) :
    GraphFabConf.gfexecConfZF boot d0 fab GF →
    (∀ i, i < NCPU → GraphFabConf.isHart (boot i) = true) →
    CatLin.rvwmoCatAD GF.gfGd ad → ioResidueGmo GF → LockFacts3.lockDiscGF GF Lb →
    LockFacts3.nf1S GF Lb ∧ LockFacts3.nf2S GF Lb ∧
    ((∀ e, CertZ17.lockW GF.gfGd.gdG Lb e → e ∉ GF.gfDev) ∧
      (∀ f e, CertZ17.fabW GF f →
        (CertZ17.lockW GF.gfGd.gdG Lb e ∨ CertZ17.fabW GF e) →
        WeakRvwmoGraph.gpo GF.gfGd.gdG f e → gmoLt GF.gfGd.gdG f e)) ∧
    (∀ b x, Lb b → lockRel GF.gfGd.gdG b x → CertZ14.np GF.gfGd.gdG x →
      ∀ e, WeakRvwmoGraph.gpo GF.gfGd.gdG e x →
        (glblIs GF.gfGd.gdG e lbIsW ∨ gisIo GF.gfGd.gdG e = true) → gmoLt GF.gfGd.gdG e x) := by
  rintro hconf hb hc hres ⟨h1, h2, hs, hdl, hdp⟩
  exact ⟨h1, h2, LockFacts3.nf3OfDisk boot d0 fab GF Lb hconf hb hdl hdp,
    LockFacts3.nf5 GF ad Lb hc hres hs⟩

namespace CatLin

/-- **THE CLASS PREMISE (NAMED; header)**: `LockFacts3.lockDiscGF` on every class graph at the
image. -/
def lockDiscGFCZ (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image)
    (P : Int → Int → Prop) : Prop :=
  ∀ (GF : Gfexec) (ad : List (Geid × Geid)),
    GF.gfGd.gdG.gxImg = im → rvwmoCatAD GF.gfGd ad → GraphFabConf.gfexecConfZF boot d0 fab GF →
    LockFacts3.lockDiscGF GF (GraphFetchN2.lockBytes P)

end CatLin

end Weak
