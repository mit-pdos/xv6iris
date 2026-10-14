/-
Weak: **W10 under N2′ [OWN.94] — the transport kill at a realized member** (the N2 spike
`~/dev/weak-orch/parked/PROGRESS-W10N2.md`, recommendation N2′, taken provisionally; the W10
increments `parked/PROGRESS-W10size.md`; W10-0 `parked/PROGRESS-W10-0.md`).  Lean-only, no Rocq
twin.

WHY.  `CatLin.cycleKillOfMemberCZC` (`GraphFetchWalkZ` §4) kills the cycle at a member whose
certified log IS the member's gmo order, which forces `gwrowGmo` of that member (W10 sizing).  The
spike: in EVERY realized member `GR` each hart's writes appear in program order (`gwrowGmo GR`), so
a 2+2W cycle is never a cycle of `GR` — classifying and killing at `GR` has nothing to kill.  N2′:
the classification and the kill STAY at `GF`; only the LOG moves to `GR`:

  §1  the agreement of a realized member with `GF` — `GraphFetchN2.agreeR` (rows renamed, the lock
      bytes' co), its poisoned form **`GraphFetchN2.agreeRP`** (rows related by `lblReidxW ∘
      lblRen pi`, writes verbatim — W10-4 fixes it with the poison set, risk (R3)), the interface
      `GraphFetchN2.agreeW` both give (images, write footprints, write classes, lock co);
  §2  THE TWO xv6 FACTS, per lock byte (`CatLin.acqAqB`: every acquire of `b` is an `.aq` read;
      `CatLin.relCoversB`: a release of `b` fence-covers the po-earlier writes of its hart after an
      acquire of `b`) and their GLOBAL named premises over the lock bytes of `P`
      (**`CatLin.acqAqCZ`**, **`CatLin.relCoversCZ`**; W11-F proves them per pc, Q-N2b);
  §3  **`CatLin.csChainedT`** — THE TRANSPORT (`csChainedC`'s twin with the log at `GR`): the
      holder facts are read off `GR`'s log, the order facts are taken at `GF` by rules 4 and 5, lock
      co (`agreeW`) and `gwrowGmo GR`; the fold is free before the reader's acquire at `GR` by
      `GraphFetchN2.acqFoldFreeR` (`acqFoldFreeC` with the source/quiet facts carried from `GF`
      through the lock co);
  §4  the restated classification and supply: `CatLin.csHypsR` (`csHyps` with ONLY its four
      log-indexed clauses at `GR`), `CatLin.l2ClaimAtCZR`/**`CatLin.l2ClaimCZR`**,
      **`CatLin.certSupplyCZR`**, the tail-walk policy **`CatLin.tailPolicyCZ`** (THE NAMED
      PREMISE, W10-2/W10-4's job) and its ZERO-CUT discharge `CatLin.certSupplyCZROfTail`;
  §5  the glue: `CatLin.rawChainChainCZR`, **`CatLin.cycleKillOfL2CZRC`** (the class kill, ending
      at the UNCHANGED `cycleKillIOC GF`) and what W11-F consumes, **`CatLin.cycleKillOfWalkCZRC`**
      (+ the guarded `CatLin.cycleKillOfWalkCZR` and T2-LIN `CatLin.t2linOfWalkCZR`).

**Deviations from the spike text.**  (1) ZERO CUT FIRST ([OWN.94] scope): `certSupplyCZROfTail`
starts the tail walk at the zero cut's (empty) hull, whatever cut `certSupplyCZR` is handed; the
MAXIMAL lock-co-closed cut (`hullRunZR`, the hull's realization as the walk's start, fewer poisoned
reads) is FOLLOW-UP — `certSupplyCZR` and `tailPolicyCZ` are already stated for any cut.  (2) The
member's well-formedness `gwf GR` is carried by the supply and the policy (the transport needs it;
the spike lists it as a premise of `csChainedT`).  (3) The consumer side is stated at the poisoned
agreement `agreeRP` (what the walk delivers), not `agreeR` (`agreeRP` is implied:
`GraphFetchN2.agreeRPOfR`).  (4) `relCoversB` asks the fence only for WRITES `x` po-between an
acquire of `b` and the release (the spike: "every po-earlier event"): a weaker obligation, and what
the transport uses — it excludes `initlock`'s plain `locked = 0` store, which no acquire of the
same hart precedes.  (5) The structural premises are GLOBAL over `lockBytes P` (Q-N2b, the cheaper
form), quantified over the class at the image.

Spec: `csChainedT` uses only, at `GF`: RVWMO rule 4 (fence) and rule 5 (acquire), co ⊆ gmo (the
lock co, transported by `agreeW`), and the cross edge's gmo consequence — FAITHFUL.  `gwrowGmo GR`
is a fact of the MACHINE's run (Sail emits a hart's stores in program order), never of `GF`:
assuming `gwrowGmo GF` would be STRONGER than RVWMO, and nothing here does.  `acqAqB`/`relCoversB`
are facts of xv6's text (`amoswap.w.aq`; `fence rw,rw` then the releasing store), FAITHFUL once
proved (W11-F), STRONGER if assumed.  Lean-only helpers file-qualified (`GraphFetchN2.*`).
-/
import Weak.GraphFetchWalkZ

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open TsoShadow
open Lbl

/-! # 1. The agreement of a realized member -/

/-- The lock bytes' co agrees: on every byte of `L`, two writes of it are co-ordered in `GR` as in
`G`. -/
def GraphFetchN2.lockCoAgree (G GR : Gexec) (L : Int → Prop) : Prop :=
  ∀ (b : Int) (x y : Geid) (vx vy : BitVec 8), L b →
    gwritesByte G x b vx → gwritesByte G y b vy → (gwix G x < gwix G y ↔ gwix GR x < gwix GR y)

/-- The realized member agrees with `G`: rows (renamed read sources) and co on the lock bytes `L`
(the spike's `agreeR`, typechecked there). -/
def GraphFetchN2.agreeR (G GR : Gexec) (pi : Nat → Nat) (L : Int → Prop) : Prop :=
  rowsRel pi G GR ∧ GraphFetchN2.lockCoAgree G GR L

/-- The lock bytes of a protection registry. -/
def GraphFetchN2.lockBytes (P : Int → Int → Prop) : Int → Prop := fun b => ∃ a, P a b

/-- **THE POISONED AGREEMENT** (`agreeRP`, risk (R3): W10-4 fixes it with the poison set): the
image, the rows related label-by-label by `lblReidxW ∘ lblRen pi` (a read may be re-indexed, its
values changed or poisoned; a write is verbatim), and the lock bytes' co. -/
def GraphFetchN2.agreeRP (G GR : Gexec) (pi : Nat → Nat) (L : Int → Prop) : Prop :=
  GR.gxImg = G.gxImg ∧
  List.Forall₂ (fun (r r' : List Lbl) => List.Forall₂ (fun l l' => lblReidxW (lblRen pi l) l') r r')
    G.gxProg GR.gxProg ∧
  GraphFetchN2.lockCoAgree G GR L

/-- What the transport reads off an agreement: the image, the write footprints, the write
classes, the lock co. -/
def GraphFetchN2.agreeW (G GR : Gexec) (L : Int → Prop) : Prop :=
  GR.gxImg = G.gxImg ∧
  (∀ e a v, gwritesByte GR e a v ↔ gwritesByte G e a v) ∧
  (∀ e k, gcls G e k → glblIs G e lbIsW → gcls GR e k) ∧
  GraphFetchN2.lockCoAgree G GR L

theorem GraphFetchN2.agreeWOfR (G GR : Gexec) (pi : Nat → Nat) (L : Int → Prop) :
    GraphFetchN2.agreeR G GR pi L → GraphFetchN2.agreeW G GR L := by
  rintro ⟨hrr, hco⟩
  refine ⟨hrr.1, fun e a v => rowsRelWrb pi G GR e a v hrr, ?_, hco⟩
  rintro e k ⟨l, hl, hk⟩ -
  exact ⟨lblRen pi l, by rw [rowsRelLbl pi G GR e hrr, hl]; rfl, by rw [lblRenCls]; exact hk⟩

/-- `Forall₂` at an index. -/
theorem GraphFetchN2.forall₂Get {α β : Type} (R : α → β → Prop) :
    ∀ (l1 : List α) (l2 : List β), List.Forall₂ R l1 l2 → ∀ i : Nat,
      (l1[i]? = none ∧ l2[i]? = none) ∨ ∃ x y, l1[i]? = some x ∧ l2[i]? = some y ∧ R x y := by
  intro l1 l2 h
  induction h with
  | nil => intro i; exact .inl ⟨rfl, rfl⟩
  | cons hxy _ ih =>
    intro i
    cases i with
    | zero => exact .inr ⟨_, _, rfl, rfl, hxy⟩
    | succ i => simpa using ih i

/-- The label-level form of the poisoned agreement. -/
theorem GraphFetchN2.agreeRPLbl (G GR : Gexec) (pi : Nat → Nat) (L : Int → Prop) (e : Geid) :
    GraphFetchN2.agreeRP G GR pi L →
    (gxLbl G e = none ∧ gxLbl GR e = none) ∨
      ∃ l l', gxLbl G e = some l ∧ gxLbl GR e = some l' ∧ lblReidxW (lblRen pi l) l' := by
  rintro ⟨-, hrows, -⟩
  unfold gxLbl
  rcases GraphFetchN2.forall₂Get _ _ _ hrows e.1 with ⟨h1, h2⟩ | ⟨r, r', h1, h2, hr⟩
  · rw [h1, h2]
    exact .inl ⟨rfl, rfl⟩
  · rw [h1, h2]
    simp only [Option.bind_some]
    rcases GraphFetchN2.forall₂Get _ _ _ hr e.2 with ⟨k1, k2⟩ | ⟨l, l', k1, k2, hl⟩
    · rw [k1, k2]
      exact .inl ⟨rfl, rfl⟩
    · rw [k1, k2]
      exact .inr ⟨l, l', rfl, rfl, hl⟩

theorem GraphFetchN2.agreeWOfRP (G GR : Gexec) (pi : Nat → Nat) (L : Int → Prop) :
    GraphFetchN2.agreeRP G GR pi L → GraphFetchN2.agreeW G GR L := by
  intro hag
  refine ⟨hag.1, fun e a v => ?_, ?_, hag.2.2⟩
  · rcases GraphFetchN2.agreeRPLbl G GR pi L e hag with ⟨h1, h2⟩ | ⟨l, l', h1, h2, hl⟩
    · constructor
      · rintro ⟨l, -, -, -, hl, -⟩
        rw [h2] at hl
        cases hl
      · rintro ⟨l, -, -, -, hl, -⟩
        rw [h1] at hl
        cases hl
    · have hw : lbIsW l' = lbIsW l := by rw [lblReidxWIsw _ _ hl, lblRenIsW]
      constructor
      · rintro ⟨l0, base, vs, j, hl0, hwr, hv, ha⟩
        rw [h2, Option.some.injEq] at hl0
        subst hl0
        have hW : lbIsW l = true := by rw [← hw]; exact lbWrIsW _ _ hwr
        have hW' : lbIsW (lblRen pi l) = true := by rw [lblRenIsW]; exact hW
        obtain ⟨hwr', -⟩ := GraphFetchWalkZ.lblReidxWWr _ _ hl hW'
        refine ⟨l, base, vs, j, h1, ?_, hv, ha⟩
        rw [← lblRenWr pi l, ← hwr', hwr]
      · rintro ⟨l0, base, vs, j, hl0, hwr, hv, ha⟩
        rw [h1, Option.some.injEq] at hl0
        subst hl0
        have hW' : lbIsW (lblRen pi l) = true := by rw [lblRenIsW]; exact lbWrIsW _ _ hwr
        obtain ⟨hwr', -⟩ := GraphFetchWalkZ.lblReidxWWr _ _ hl hW'
        refine ⟨l', base, vs, j, h2, ?_, hv, ha⟩
        rw [hwr', lblRenWr, hwr]
  · rintro e k ⟨l0, hl0, hk⟩ ⟨l1, hl1, hW⟩
    rw [hl0, Option.some.injEq] at hl1
    subst hl1
    rcases GraphFetchN2.agreeRPLbl G GR pi L e hag with ⟨h1, -⟩ | ⟨l, l', h1, h2, hl⟩
    · rw [h1] at hl0
      cases hl0
    · rw [h1, Option.some.injEq] at hl0
      subst hl0
      have hW' : lbIsW (lblRen pi l) = true := by rw [lblRenIsW]; exact hW
      obtain ⟨-, hcl'⟩ := GraphFetchWalkZ.lblReidxWWr _ _ hl hW'
      exact ⟨l', h2, by rw [hcl', lblRenCls]; exact hk⟩

/-- The exact agreement is a poisoned one (no read poisoned). -/
theorem GraphFetchN2.agreeRPOfR (G GR : Gexec) (pi : Nat → Nat) (L : Int → Prop) :
    GraphFetchN2.agreeR G GR pi L → GraphFetchN2.agreeRP G GR pi L := by
  rintro ⟨⟨himg, hprog, -⟩, hco⟩
  refine ⟨himg, ?_, hco⟩
  rw [hprog]
  generalize G.gxProg = p
  induction p with
  | nil => exact .nil
  | cons r p ih =>
    refine .cons ?_ ih
    induction r with
    | nil => exact .nil
    | cons l r ihr => exact .cons (lblReidxWRefl _) ihr

/-! ## 1.1 Order arithmetic across an agreement -/

/-- A `GR`-write of `G`'s write. -/
theorem GraphFetchN2.wrR (G GR : Gexec) (L : Int → Prop) (e : Geid) (a : Int) (v : BitVec 8) :
    gwf GR → GraphFetchN2.agreeW G GR L → gwritesByte G e a v → e ∈ gwrites GR :=
  fun hwfR hag h => gwritesByteGwrites GR e a v hwfR ((hag.2.1 e a v).2 h)

/-- The lock co's `≤`, from `G` to `GR`. -/
theorem GraphFetchN2.coLeR (G GR : Gexec) (L : Int → Prop) (b : Int) (x y : Geid)
    (vx vy : BitVec 8) :
    gwf G → GraphFetchN2.agreeW G GR L → L b →
    gwritesByte G x b vx → gwritesByte G y b vy → gwix G x ≤ gwix G y → gwix GR x ≤ gwix GR y := by
  intro hwf hag hL hx hy hle
  rcases Nat.lt_or_eq_of_le hle with hlt | heq
  · exact Nat.le_of_lt ((hag.2.2.2 b x y vx vy hL hx hy).1 hlt)
  · have := gwixInj G x y hwf.1 (gwritesByteGwrites G x b vx hwf hx)
      (gwritesByteGwrites G y b vy hwf hy) heq
    subst this
    exact Nat.le_refl _

/-- PROGRAM ORDER FROM THE MEMBER'S WRITE ORDER: two distinct same-hart writes of `G`, ordered in
`GR`'s write order, are po-ordered (`gwrowGmo GR`). -/
theorem GraphFetchN2.poOfRowR (G GR : Gexec) (L : Int → Prop) (x y : Geid) (a1 a2 : Int)
    (v1 v2 : BitVec 8) :
    GraphFetchN2.agreeW G GR L → gwrowGmo GR →
    gwritesByte G x a1 v1 → gwritesByte G y a2 v2 → x.1 = y.1 → x ≠ y →
    gwix GR x < gwix GR y → WeakRvwmoGraph.gpo G x y := by
  intro hag hrow hx hy h1 hne hlt
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
    have hWx := gwritesByteGlblW GR x a1 v1 ((hag.2.1 x a1 v1).2 hx)
    have hWy := gwritesByteGlblW GR y a2 v2 ((hag.2.1 y a2 v2).2 hy)
    have e1 : (y.1, x.2) = x := Prod.ext h1.symm rfl
    have e2 : (y.1, y.2) = y := rfl
    have key := hrow y.1 y.2 x.2 h2 (by rw [e2]; exact hWy) (by rw [e1]; exact hWx)
    rw [e1, e2] at key
    omega

/-! # 2. THE TWO xv6 FACTS (named, global over the lock bytes) -/

namespace CatLin

/-- Every acquire of `b` is an `.aq` READ (xv6: `amoswap.w.aq`, the image's only AMO on a lock
word; a failed swap is one too). -/
def acqAqB (G : Gexec) (b : Int) : Prop :=
  ∀ A, lockAcq G b A → glblIs G A lbIsR ∧ glblIs G A lbAq

/-- A release of `b` fence-covers every write of its hart po-between an acquire of `b` and it
(xv6: `release` is `fence rw,rw; fence iorw,ow; amoswap.w zero`; deviation (4): the writes
after an acquire only — `initlock`'s plain store follows no acquire of the same hart). -/
def relCoversB (G : Gexec) (b : Int) : Prop :=
  ∀ A R x, lockAcq G b A → lockRel G b R →
    WeakRvwmoGraph.gpo G A x → WeakRvwmoGraph.gpo G x R → glblIs G x lbIsW →
    gfenceCovers G x R

/-- **NAMED PREMISE (W11-F proves it per pc, Q-N2b)**: on every class graph at the image, every
acquire of a lock byte of `P` is an `.aq` read. -/
def acqAqCZ (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image)
    (P : Int → Int → Prop) : Prop :=
  ∀ (GF : Gfexec) (ad : List (Geid × Geid)),
    GF.gfGd.gdG.gxImg = im → rvwmoCatAD GF.gfGd ad → GraphFabConf.gfexecConfZF boot d0 fab GF →
    ∀ b, GraphFetchN2.lockBytes P b → acqAqB GF.gfGd.gdG b

/-- **NAMED PREMISE (W11-F proves it per pc, Q-N2b)**: on every class graph at the image, every
release of a lock byte of `P` fence-covers its hart's writes after an acquire of that byte. -/
def relCoversCZ (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image)
    (P : Int → Int → Prop) : Prop :=
  ∀ (GF : Gfexec) (ad : List (Geid × Geid)),
    GF.gfGd.gdG.gxImg = im → rvwmoCatAD GF.gfGd ad → GraphFabConf.gfexecConfZF boot d0 fab GF →
    ∀ b, GraphFetchN2.lockBytes P b → relCoversB GF.gfGd.gdG b

end CatLin

/-! # 3. THE TRANSPORT -/

/-- `acqFoldFreeC`'s body with its three consistency facts as hypotheses: the acquire's read
index `t` is below it, no `b`-write sits between, and a nonzero `t` names a release. -/
theorem GraphFetchN2.acqFoldFreeG (G : Gexec) (log : List Wmsg) (b : Int) (n0 : Nat)
    (h : Option Nat) (ACQ : Geid) (t : Nat) :
    gwf G → logOf G log → lockWordByte log b →
    wlpAlt log b n0 h → lockAcq G b ACQ →
    gwix G ACQ ≤ log.length → t < gwix G ACQ →
    (∀ w' v', gwritesByte G w' b v' → gwix G w' ≤ t ∨ gwix G ACQ ≤ gwix G w') →
    (0 < t → ∃ r, lockRel G b r ∧ r ∈ gwrites G ∧ gwix G r = t) →
    wlpHolderAt log b n0 (gwix G ACQ - 1) = some none := by
  intro hwf hlog hlwb halt hacq hle htlt hsrc hrel
  have hAw := lockAcqGwrites G b ACQ hwf hacq
  have hpos := WeakRvwmoGraph.gwixPos G ACQ hAw
  have hquiet : ∀ r mr, (t ≤ r ∧ r < gwix G ACQ - 1) → log[r]? = some mr →
      msgByte mr b = none := by
    intro r mr hr hmr
    cases hb : msgByte mr b with
    | none => rfl
    | some v =>
      exfalso
      obtain ⟨w', -, hm', hix', -⟩ := logOfLookup G log r mr hwf hlog hmr
      have hwb := (WeakRvwmoKillArms.gmsgByte G w' mr b v hm').1 hb
      rcases hsrc w' v hwb with hlo | hhi <;> omega
  rw [wlpHolderQuiet log b n0 t (gwix G ACQ - 1) (by omega) hquiet]
  by_cases hn0 : t ≤ n0
  · exact wlpHolderSmall log b n0 t hn0
  obtain ⟨R, hR, hRw, hRix⟩ := hrel (by omega)
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

/-- THE FOLD IS FREE BEFORE THE READER'S ACQUIRE, IN THE MEMBER'S LOG: the acquire's source and
quiet window are `GF`'s (cat: load value, rule 1, atomicity), carried to `GR` by the lock co. -/
theorem GraphFetchN2.acqFoldFreeR (GD : Gdexec) (ad : List (Geid × Geid)) (GR : Gexec)
    (L : Int → Prop) (log : List Wmsg) (b : Int) (n0 : Nat) (h : Option Nat) (ACQ : Geid) :
    CatLin.rvwmoCatAD GD ad → gwf GR → GraphFetchN2.agreeW GD.gdG GR L → L b →
    logOf GR log → lockWordByte log b → wlpAlt log b n0 h →
    acqRow GD.gdG b ACQ → lockAcq GD.gdG b ACQ → gwix GR ACQ ≤ log.length →
    wlpHolderAt log b n0 (gwix GR ACQ - 1) = some none := by
  intro hcons hwfR hag hL hlog hlwb halt hrow hacq hle
  obtain ⟨hwf, h6, hlv, hatm, -, -, -, -⟩ := hcons
  generalize GD.gdG = G at *
  obtain ⟨t, hrd⟩ := hrow
  obtain ⟨va, hva, hvane⟩ := id hacq
  have hacqR : lockAcq GR b ACQ := ⟨va, (hag.2.1 ACQ b va).2 hva, hvane⟩
  have hAwR := lockAcqGwrites GR b ACQ hwfR hacqR
  have htlt := CatLin.acqTsLtC G b ACQ t hwf h6 hlv hacq hrd
  have hsrcG := CatLin.acqSrcC G b ACQ t hatm hacq hrd
  by_cases ht0 : t = 0
  · subst ht0
    refine GraphFetchN2.acqFoldFreeG GR log b n0 h ACQ 0 hwfR hlog hlwb halt hacqR hle
      (WeakRvwmoGraph.gwixPos GR ACQ hAwR) ?_ (fun h0 => absurd h0 (Nat.lt_irrefl 0))
    intro w' v' hw'
    have hw'G := (hag.2.1 w' b v').1 hw'
    rcases hsrcG w' v' hw'G with hlo | hhi
    · exact absurd hlo (Nat.not_le.2 (WeakRvwmoGraph.gwixPos G w'
        (gwritesByteGwrites G w' b v' hwf hw'G)))
    · exact .inr (GraphFetchN2.coLeR G GR L b ACQ w' va v' hwf hag hL hva hw'G hhi)
  · obtain ⟨R0, hR0, hR0w, hR0ix⟩ := CatLin.acqSrcRelC G b ACQ t hwf hlv hrd (by omega)
    have hR0lt : gwix GR R0 < gwix GR ACQ :=
      (hag.2.2.2 b R0 ACQ lockFree va hL hR0 hva).1 (by omega)
    refine GraphFetchN2.acqFoldFreeG GR log b n0 h ACQ (gwix GR R0) hwfR hlog hlwb halt hacqR hle
      hR0lt ?_ (fun _ => ⟨R0, (hag.2.1 R0 b lockFree).2 hR0,
        GraphFetchN2.wrR G GR L R0 b lockFree hwfR hag hR0, rfl⟩)
    intro w' v' hw'
    have hw'G := (hag.2.1 w' b v').1 hw'
    rcases hsrcG w' v' hw'G with hlo | hhi
    · exact .inl (GraphFetchN2.coLeR G GR L b w' R0 v' lockFree hwf hag hL hw'G hR0
        (by omega))
    · exact .inr (GraphFetchN2.coLeR G GR L b ACQ w' va v' hwf hag hL hva hw'G hhi)

namespace CatLin

/-- **`csChainedT` — THE TRANSPORT** (`csChainedC`'s twin, N2′): the four log-indexed clauses are
read at the realized member `GR` (its log, `gwix GR`), every ORDER fact is concluded at `GF`.  The
writer's acquire `ACQw` and, in the writer-first case, its release `R` are found in `GR`'s log
(`holderAcqGraph`/`releaseBetweenGraph` at `GR`), placed in program order by `gwrowGmo GR`, and
ordered in `GF` by rule 4 (`relCoversB`: `w <gmo R`), rule 5 (`acqAqB`: `ACQw <gmo w`; `ACQ <gmo
exit`) and the lock co (`agreeW`).  WRITER-FIRST: `w <gmo R <co ACQ <gmo exit`.  READER-FIRST:
`w <gmo entry <gmo REL <co ACQw <gmo w`, absurd. -/
theorem csChainedT (GD : Gdexec) (ad : List (Geid × Geid)) (GR : Gexec) (L : Int → Prop)
    (log : List Wmsg) (b a : Int) (n0 r0 : Nat) (h : Option Nat)
    (w entry exit ACQ REL : Geid) :
    rvwmoCatAD GD ad → gwf GR → GraphFetchN2.agreeW GD.gdG GR L → gwrowGmo GR → L b →
    acqAqB GD.gdG b → relCoversB GD.gdG b →
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
  intro hcons hwfR hag hrowR hL hAQ hRC hlog hlwb halt hrow hpr hwa hcl hr0 hlew hnob hacq haq
    hn0A hleA hcs _hpoe hfen hcross hpox hmx hhart
  have hfreeA :=
    GraphFetchN2.acqFoldFreeR GD ad GR L log b n0 h ACQ hcons hwfR hag hL hlog hlwb halt hrow
      hacq hleA
  obtain ⟨hwf, h6, hlv, -, -, -, -, -⟩ := hcons
  generalize GD.gdG = G at *
  have hndR := hwfR.1
  obtain ⟨va, hva, hvane⟩ := id hacq
  have hvaR : gwritesByte GR ACQ b va := (hag.2.1 ACQ b va).2 hva
  have hAwR := lockAcqGwrites GR b ACQ hwfR ⟨va, hvaR, hvane⟩
  obtain ⟨vw, hvw⟩ := hwa
  have hwR : w ∈ gwrites GR := GraphFetchN2.wrR G GR L w a vw hwfR hag hvw
  have hclR : gcls GR w .WCplain := hag.2.2.1 w _ hcl (gwritesByteGlblW G w a vw hvw)
  have hnobR : ∀ v, ¬ gwritesByte GR w b v := fun v hv => hnob v ((hag.2.1 w b v).1 hv)
  obtain ⟨q, mq, hq, hlk, hs, hnz, ht, hfree, hno, ACQw, -, hacqwR, hixw, hhw⟩ :=
    holderAcqGraph GR log b a n0 r0 w hwfR hlog hlwb hpr hwR hr0 hlew ⟨vw, (hag.2.1 w a vw).2 hvw⟩
      hclR
  have hrA := acqRowIsR G b ACQ hrow
  have hmoAx : gmoLt G ACQ exit := acqGmoAfterC G ACQ exit h6 hpox hrA haq hmx
  -- the writer's acquire, at `GF`
  obtain ⟨vq, hvq, hvqne⟩ := id hacqwR
  have hvqG : gwritesByte G ACQw b vq := (hag.2.1 ACQw b vq).1 hvq
  have hacqw : lockAcq G b ACQw := ⟨vq, hvqG, hvqne⟩
  have hAwwR : ACQw ∈ gwrites GR := lockAcqGwrites GR b ACQw hwfR hacqwR
  have hwne : ACQw ≠ w := fun he => hnob vq (he ▸ hvqG)
  have hpoAw : WeakRvwmoGraph.gpo G ACQw w :=
    GraphFetchN2.poOfRowR G GR L ACQw w b a vq vw hag hrowR hvqG hvw hhw hwne (by omega)
  have hposA := WeakRvwmoGraph.gwixPos GR ACQ hAwR
  by_cases heq : q = gwix GR ACQ - 1
  · exfalso
    have hA : ACQw = ACQ := gwixInj GR ACQw ACQ hndR hAwwR hAwR (by omega)
    apply hhart
    rw [← hA]
    exact hhw
  by_cases hlt : q < gwix GR ACQ - 1
  · -- WRITER-FIRST: the writer's release sits between `w` and the reader's acquire in `GR`
    obtain ⟨r, R, mr, hr, hlkr, hsr, hzr, -, hRrel, hRix, -, hRh⟩ :=
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
    have hwRne : w ≠ R := fun he => hnob lockFree (he ▸ hRG)
    have hpowR : WeakRvwmoGraph.gpo G w R :=
      GraphFetchN2.poOfRowR G GR L w R a b vw lockFree hag hrowR hvw hRG hRh.symm hwRne
        (by omega)
    have hfc : gfenceCovers G w R :=
      hRC ACQw R w hacqw hRG hpoAw hpowR (gwritesByteGlblW G w a vw hvw)
    have h1 : gmoLt G w R := fenceGmoAfterC G w R h6 hfc
    have h2 : gmoLt G R ACQ :=
      gwixLtGmo G R ACQ hwf (lockRelGwrites G b R hwf hRG) (lockAcqGwrites G b ACQ hwf hacq)
        ((hag.2.2.2 b R ACQ lockFree va hL hRG hva).2 (by omega))
    exact gmoLtTrans G w ACQ exit (gmoLtTrans G w R ACQ h1 h2) hmoAx
  · -- READER-FIRST: the reader's release is co-before the writer's acquire
    have hltA : gwix GR ACQ - 1 < q := by omega
    obtain ⟨mA, hmA, hgA⟩ := logOfWrite GR log ACQ hwfR hlog hAwR hleA
    have hbA := (WeakRvwmoKillArms.gmsgByte GR ACQ mA b va hgA).2 hvaR
    have hnzA : mA.wmData ≠ wlockZero4 := fun hz => hvane (zero4Byte mA b va hz hbA)
    have htA := gmsgTid GR ACQ mA hgA
    obtain ⟨r', R', mr', hr', -, -, -, -, hrelr', hixr', -, hhr'⟩ :=
      releaseBetweenGraph GR log b n0 (gwix GR ACQ - 1) q mA ACQ.1 hwfR hlog (by omega) hltA hmA
        (by rw [hbA]; rfl) hnzA htA hfreeA hfree
    obtain ⟨-, hRel, -, -, hnoin⟩ := hcs
    have hR'G : lockRel G b R' := (hag.2.1 R' b lockFree).1 hrelr'
    have hAR'G : gwix G ACQ < gwix G R' :=
      (hag.2.2.2 b ACQ R' va lockFree hL hva hR'G).2 (by omega)
    have hRleG : gwix G REL ≤ gwix G R' := by
      by_cases hc : gwix G R' < gwix G REL
      · exact absurd ⟨hAR'G, hc⟩ (hnoin R' lockFree hR'G hhr')
      · omega
    have hRleR : gwix GR REL ≤ gwix GR R' :=
      GraphFetchN2.coLeR G GR L b REL R' lockFree lockFree hwf hag hL hRel hR'G hRleG
    have hmoRA : gmoLt G REL ACQw :=
      gwixLtGmo G REL ACQw hwf (lockRelGwrites G b REL hwf hRel) (lockAcqGwrites G b ACQw hwf hacqw)
        ((hag.2.2.2 b REL ACQw lockFree vq hL hRel hvqG).2 (by omega))
    obtain ⟨hrw, haqw⟩ := hAQ ACQw hacqw
    have hmoAw : gmoLt G ACQw w :=
      acqGmoAfterC G ACQw w h6 hpoAw hrw haqw
        (WeakRvwmoGraph.glblIsWGmem G w (gwritesByteGlblW G w a vw hvw))
    have hmoeR := fenceGmoAfterC G entry REL h6 hfen
    exact absurd (gmoLtTrans G w entry w hcross
      (gmoLtTrans G entry REL w hmoeR (gmoLtTrans G REL ACQw w hmoRA hmoAw))) (gmoLtIrrefl G w)

/-! # 4. The restated classification and supply -/

/-- `csHyps` (`WeakRvwmoGlue.lean`) with ONLY its four log-indexed clauses at the member `GR`
(the spike's `csHypsR`, typechecked there). -/
def csHypsR (GD : Gdexec) (GR : Gexec) (P : Int → Int → Prop) (log : List Wmsg) (prev : Geid)
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

/-- A CS-chained segment (log at the member) IS a `CSchained` certificate at `GF`, for any
gmo-forward cross order (`csHypsCertC`'s twin, through `csChainedT`). -/
theorem csHypsCertCR (GD : Gdexec) (ad : List (Geid × Geid)) (X : Geid → Geid → Prop)
    (GR : Gexec) (P : Int → Int → Prop) (log : List Wmsg) (prev : Geid) (s : Seg) :
    rvwmoCatAD GD ad → (∀ x y, X x y → gmoLt GD.gdG x y) →
    gwf GR → GraphFetchN2.agreeW GD.gdG GR (GraphFetchN2.lockBytes P) → gwrowGmo GR →
    (∀ b, GraphFetchN2.lockBytes P b → acqAqB GD.gdG b) →
    (∀ b, GraphFetchN2.lockBytes P b → relCoversB GD.gdG b) →
    logOf GR log → protReg P log →
    csHypsR GD GR P log prev s → X prev s.sgEntry →
    CertC GD.gdG X prev s := by
  rintro hc hX hwfR hag hrowR hAQ hRC hlog hpr
    ⟨b, a, ACQ, REL, hP, hlwb, hwa, hcl, hlew, hnob, hacq, hrow, haq, hleA, hcs, hpoe, hfen,
      hpox, hmx, hhart, hside⟩ hx
  obtain ⟨n0, r0, h, hprot, -, halt⟩ := hpr a b hP
  obtain ⟨hr0, hn0A⟩ := hside n0 r0 hprot
  have hL : GraphFetchN2.lockBytes P b := ⟨a, hP⟩
  exact .CSchained (csChainedT GD ad GR (GraphFetchN2.lockBytes P) log b a n0 r0 h prev
    s.sgEntry s.sgExit ACQ REL hc hwfR hag hrowR hL (hAQ b hL) (hRC b hL) hlog hlwb halt hrow
    hprot hwa hcl hr0 hlew hnob hacq haq hn0A hleA hcs hpoe hfen (hX _ _ hx) hpox hmx hhart)

/-- THE L2′ CLAIM, log at the member (the spike's `l2ClaimAtCZR`): the cycle and its segments are
`GF`'s; the CS arm's log clauses are `GR`'s. -/
def l2ClaimAtCZR (GF : Gfexec) (ad : List (Geid × Geid)) (GR : Gexec) (P : Int → Int → Prop)
    (Bad : Prop) : Prop :=
  ∀ (log : List Wmsg) (z : Geid) (ss : List Seg),
    rvwmoCatAD GF.gfGd ad →
    logOf GR log →
    protReg P log →
    ss ≠ [] → rawChainC GF.gfGd (ioCross GF) z z ss →
    ∀ (prev : Geid) (s : Seg),
      s ∈ ss → ioCross GF prev s.sgEntry → segRunC GF.gfGd s →
      segPinC GF.gfGd ad s ∨ csHypsR GF.gfGd GR P log prev s ∨ Bad

/-- **THE L2′ CLAIM AT EVERY AGREEING MEMBER** (W11-F's obligation, `l2ClaimAtB`): deviation (3),
at the poisoned agreement. -/
def l2ClaimCZR (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image)
    (P : Int → Int → Prop) (Bad : Prop) : Prop :=
  ∀ (GF : Gfexec) (ad : List (Geid × Geid)) (GR : Gexec) (pi : Nat → Nat),
    GF.gfGd.gdG.gxImg = im → GraphFabConf.gfexecConfZF boot d0 fab GF →
    gwf GR → GraphFetchN2.agreeRP GF.gfGd.gdG GR pi (GraphFetchN2.lockBytes P) → gwrowGmo GR →
    l2ClaimAtCZR GF ad GR P Bad

/-- (G-3) AT A MEMBER (the spike's `certSupplyCZR`, Q1 (b) widened): from the cut's acyclic hull, a
run datum whose log is a member `GR`'s, `GR` agreeing with `GF` (poisoned, deviation (3)), in
program write order, well-formed (deviation (2)). -/
def certSupplyCZR (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image) (N : Nat)
    (P : Int → Int → Prop) : Prop :=
  ∀ (GF : Gfexec) (ad : List (Geid × Geid)) (cs : List Nat) (z : Geid) (ss : List Seg),
    GF.gfGd.gdG.gxImg = im → rvwmoCatAD GF.gfGd ad → GraphFabConf.gfexecConfZF boot d0 fab GF →
    ioResidueGmo GF → gdiskRead14 GF.gfGd.gdG →
    properCutF GF cs → GraphFetchHullZ.fetchSrcClosedCut boot fab GF cs →
    GraphFabConf.gfexecConfZF boot d0 fab (gfHull GF cs) →
    GraphFetchBlocks.emPremOk boot (gfHull GF cs).gfGd.gdG →
    (∀ x, ¬ tc (racyDIO (gfHull GF cs)) x x) →
    ss ≠ [] → rawChainC GF.gfGd (ioCross GF) z z ss →
    ∃ (c : Cand) (pst : Nat → List Pexv6) (dv : Nat → Efab) (GR : Gexec) (pi : Nat → Nat),
      RunDataZ boot d0 N GF.gfGd.gdG c pst dv ∧
      logOf GR (cdLog c c.cdTr.length) ∧ gwf GR ∧
      GraphFetchN2.agreeRP GF.gfGd.gdG GR pi (GraphFetchN2.lockBytes P) ∧ gwrowGmo GR

/-- **THE TAIL-WALK POLICY — THE NAMED PREMISE (W10-2/W10-4's job, N2′)**: from a realized hull
`GH` (its run's end state `St`, `GH` agreeing exactly with the cut's hull, in program write
order), a walk over the tail ending at an agreeing member `GR` (poisoned).  `GR` is chosen by the
policy: its gmo is `GH`'s order followed by a linear extension of po ∪ co_L on the tail (one
exists for a cat graph: same-hart lock writes are ppo-ordered — aq, fence, same address — and co ⊆
gmo); a tail read whose source is not yet in the log is POISONED (W10-4; the spike's (3b)).  The
precondition is NOT `gwrowGmo GF` (STRONGER than RVWMO); `gwrowGmo GR` holds of the machine's run.
The walk reuses `wlkRunZ`'s engine from `n = |hull writes|` (W10-2: the step twin). -/
def tailPolicyCZ (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image) (N : Nat)
    (P : Int → Int → Prop) : Prop :=
  ∀ (GF : Gfexec) (ad : List (Geid × Geid)) (cs : List Nat) (St : CycState) (GH : Gexec)
    (piH : Nat → Nat),
    GF.gfGd.gdG.gxImg = im → rvwmoCatAD GF.gfGd ad → GraphFabConf.gfexecConfZF boot d0 fab GF →
    ioResidueGmo GF → gdiskRead14 GF.gfGd.gdG →
    properCutF GF cs → GraphFetchHullZ.fetchSrcClosedCut boot fab GF cs →
    wlkInvZ boot d0 N GH St (gwrites GH).length →
    GraphFetchN2.agreeR (gfHull GF cs).gfGd.gdG GH piH (GraphFetchN2.lockBytes P) →
    gwrowGmo GH →
    ∃ (l : List Segout) (Sf : CycState) (GR : Gexec) (pi : Nat → Nat),
      segsRunZ d0 l St Sf ∧ wlkInvZ boot d0 N GR Sf (gwrites GR).length ∧ gwf GR ∧
      GraphFetchN2.agreeRP GF.gfGd.gdG GR pi (GraphFetchN2.lockBytes P) ∧ gwrowGmo GR

end CatLin

/-! ## 4.1 The zero cut's hull, as the walk's start -/

/-- The zero cut's hull has no labelled event. -/
theorem GraphFetchN2.zcutHullLbl (GF : Gfexec) (e : Geid) :
    gxLbl (gfHull GF (zcut GF.gfGd.gdG)).gfGd.gdG e = none := by
  have h := zcutHullRows GF.gfGd.gdG e.1
  change (((gfHull GF (zcut GF.gfGd.gdG)).gfGd.gdG.gxProg[e.1]?).getD []) = [] at h
  unfold gxLbl
  cases hp : (gfHull GF (zcut GF.gfGd.gdG)).gfGd.gdG.gxProg[e.1]? with
  | none => rfl
  | some p =>
    rw [hp] at h
    simp only [Option.getD_some] at h
    subst h
    simp

theorem GraphFetchN2.zcutHullWrites (GF : Gfexec) :
    gwrites (gfHull GF (zcut GF.gfGd.gdG)).gfGd.gdG = [] := by
  simp [gwrites, gisW, GraphFetchN2.zcutHullLbl]

/-- The zero cut's hull, realized by the empty run, starts the walk: it is invariant, agrees with
itself exactly, and is (vacuously) in program write order. -/
theorem GraphFetchN2.zcutStart (boot : Nat → Pexv6) (d0 : Efab) (N : Nat) (GF : Gfexec)
    (L : Int → Prop) :
    let GH := (gfHull GF (zcut GF.gfGd.gdG)).gfGd.gdG
    wlkInvZ boot d0 N GH (wlkStart boot d0 N GH) (gwrites GH).length ∧
      GraphFetchN2.agreeR GH GH (fun t => t) L ∧ gwrowGmo GH := by
  intro GH
  refine ⟨?_, ⟨⟨rfl, (progRenId _).symm, rfl⟩, fun _ _ _ _ _ _ _ _ => Iff.rfl⟩, ?_⟩
  · rw [GraphFetchN2.zcutHullWrites GF]
    exact wlkStartInvZ boot d0 N GH
  · rintro x j k - ⟨l, hl, -⟩ -
    rw [GraphFetchN2.zcutHullLbl GF] at hl
    cases hl

/-- A run datum sees its graph only through the image. -/
theorem GraphFetchN2.runDataZImg (boot : Nat → Pexv6) (d0 : Efab) (N : Nat) (G G' : Gexec)
    (c : Cand) (pst : Nat → List Pexv6) (dv : Nat → Efab) :
    G'.gxImg = G.gxImg → RunDataZ boot d0 N G c pst dv → RunDataZ boot d0 N G' c pst dv :=
  fun himg h => ⟨h.rdCons, h.rdImg.trans himg.symm, h.rdPst0, h.rdDv0, h.rdSca, h.rdProg⟩

namespace CatLin

/-- **(G-3) AT A MEMBER FROM THE TAIL POLICY, AT THE ZERO CUT** (deviation (1)): the walk starts
at the zero cut's empty hull (in the class, `gfDev`-closed, a proper cut since the cycle names an
event); the policy's end state is a run datum whose log is the member's. -/
theorem certSupplyCZROfTail (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image)
    (N : Nat) (P : Int → Int → Prop) :
    tailPolicyCZ boot d0 fab im N P → certSupplyCZR boot d0 fab im N P := by
  intro htail GF ad _ z ss him hc hconf hres hdr _ _ _ _ _ hne hch
  obtain ⟨i, hi, hn⟩ := GraphFetchWalkZ.cycleHasEventCZ GF ad z ss hc hne hch
  have hzc : properCutF GF (zcut GF.gfGd.gdG) :=
    GraphFetchKill.properCutFOfCut GF _ (zcutCutOk _ i hi hn) (GraphFetchWalkZ.zcutDclosed _ _)
  obtain ⟨hinv0, hag0, hrow0⟩ := GraphFetchN2.zcutStart boot d0 N GF (GraphFetchN2.lockBytes P)
  obtain ⟨_, Sf, GR, pi, -, hinv, hwfR, hagR, hrowR⟩ :=
    htail GF ad (zcut GF.gfGd.gdG) _ _ (fun t => t) him hc hconf hres hdr hzc
      (GraphFetchWalkZ.zcutFetchSrcClosed boot d0 fab GF hconf) hinv0 hag0 hrow0
  exact ⟨Sf.cstC, Sf.cstPst, Sf.cstDv, GR, pi,
    GraphFetchN2.runDataZImg boot d0 N GR GF.gfGd.gdG _ _ _ hagR.1.symm
      (runDataZOfCyc boot d0 N GR Sf hinv.1 hinv.2.1 hinv.2.2.1),
    logOfOfPfx _ _ hinv.2.2.2, hwfR, hagR, hrowR⟩

/-! # 5. THE GLUE -/

/-- A classified `ioCross` raw chain IS a `chainC` at `ioCross` at `GF`, the CS arm's log at the
member (`rawChainChainCZ`'s twin, through `csChainedT`). -/
theorem rawChainChainCZR (GF : Gfexec) (ad : List (Geid × Geid)) (GR : Gexec) (pi : Nat → Nat)
    (P : Int → Int → Prop) (log : List Wmsg) (Bad : Prop) (ss : List Seg) :
    rvwmoCatAD GF.gfGd ad → ioResidueGmo GF → gdiskRead14 GF.gfGd.gdG →
    gwf GR → GraphFetchN2.agreeRP GF.gfGd.gdG GR pi (GraphFetchN2.lockBytes P) → gwrowGmo GR →
    (∀ b, GraphFetchN2.lockBytes P b → acqAqB GF.gfGd.gdG b) →
    (∀ b, GraphFetchN2.lockBytes P b → relCoversB GF.gfGd.gdG b) →
    logOf GR log → protReg P log → ¬ Bad →
    (∀ prev s, s ∈ ss → ioCross GF prev s.sgEntry → segRunC GF.gfGd s →
       segPinC GF.gfGd ad s ∨ csHypsR GF.gfGd GR P log prev s ∨ Bad) →
    ∀ (x y : Geid) (ss' : List Seg),
      ss' ⊆ ss → rawChainC GF.gfGd (ioCross GF) x y ss' →
      chainC GF.gfGd.gdG (ioCross GF) x y ss' := by
  intro hc hres hdr hwfR hagR hrowR hAQ hRC hlog hpr hnB hcl x y ss'
  have hX : ∀ x y, ioCross GF x y → gmoLt GF.gfGd.gdG x y :=
    ioCrossGmo GF hc.1 hc.2.2.1 hres hdr
  have hag := GraphFetchN2.agreeWOfRP _ _ _ _ hagR
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
    · exact csHypsCertCR GF.gfGd ad _ GR P log x s hc hX hwfR hag hrowR hAQ hRC hlog hpr hcs hx
    · exact absurd hb hnB

section glue

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode
open Language.Notation PrimStep
open LeanRV64D

/-- **`cycleKillOfL2CZRC`** — THE CLASS KILL, N2′ (`cycleKillOfL2CZC`'s body): the cut in the
class, the guarded induction hypothesis, the run datum at a MEMBER `GR` (`certSupplyCZR`), M2's
replay (`runErasedZ`) and the exports at `GR`'s log, the classification at `GR` (`l2ClaimCZR`),
and the UNCHANGED kill `cycleKillIOC GF` — the cycle is never moved off `GF`. -/
theorem cycleKillOfL2CZRC (hlc : HasLC) (GF0 : BundledGFunctors) [MachGpreS hlc GF0]
    [WeakGpreS GF0] (gen : Nat) (σ0 : WGState) (D : CPU → List Register) (hD : ∀ c, (D c).Nodup)
    (Nm : Int → Int → Namespace) (P : Int → Int → Prop)
    (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (N : Nat) :
    freshEra gen σ0 →
    (List.range' 0 N).map boot = epsInit σ0 →
    d0 = efInit σ0.wgdev →
    wpPackage hlc GF0 gen σ0 D →
    (∀ a base, P a base → wpPackageProt hlc GF0 gen σ0 D (Nm a base) a base) →
    (∀ ρ, rtc epfRun (epInit gen, σ0) ρ → efetchItvOk ρ.1 ρ.2) →
    cutSupplyCZC boot d0 fab (imgZ σ0.wgimg) →
    certSupplyCZR boot d0 fab (imgZ σ0.wgimg) N P →
    acqAqCZ boot d0 fab (imgZ σ0.wgimg) P →
    relCoversCZ boot d0 fab (imgZ σ0.wgimg) P →
    l2ClaimCZR boot d0 fab (imgZ σ0.wgimg) P (badRun gen σ0) →
    cycleKillCZC boot d0 fab (imgZ σ0.wgimg) := by
  intro hfr hb1 hb2 hwp hwpp hcov hcut hcert hAQ hRC hl2
  intro GF ad him hc hconf hres hdr hIH x hcyc
  -- (1) the cycle, as `ioCross`-entered segments (at `GF`, and it stays there)
  obtain ⟨z, ss, hne, hch⟩ := cycleSegmentsIO GF ad x hc hcyc
  -- (2) the cut in the class, its hull's bundle (the stability), the induction hypothesis
  obtain ⟨cs, hcutok, hdc, hcl, hprem⟩ := hcut GF ad z ss him hc hconf hne hch
  have hcore := catADCore _ _ hc
  have hconfH :=
    GraphFetchHullZ.gfexecConfZFHull boot d0 fab GF cs hcore.1 hcore.2.1 hcutok.1 hdc hconf hcl
  have hpc := GraphFetchKill.properCutFOfCut GF cs hcutok hdc
  have hacyH := hIH cs hpc hcl
  -- (3) the certified run datum, its log a member's
  obtain ⟨c, pst, dv, GR, pi, hrd, hlog, hwfR, hagR, hrowR⟩ :=
    hcert GF ad cs z ss him hc hconf hres hdr hpc hcl hconfH hprem hacyH hne hch
  -- (4) the erased run (M2's replay), and the exports at its log
  obtain ⟨t2, σ2, hrtc, hlgeq⟩ :=
    runErasedZ gen σ0 boot d0 N GF.gfGd.gdG c pst dv hfr hcov hb1 hb2 him hrd
  have hpr : protReg P (cdLog c c.cdTr.length) := by
    rw [← hlgeq]
    exact protRegOfRun hlc GF0 gen σ0 D hD Nm P t2 σ2 hfr hwpp hrtc
  -- (5) the classification at the member's log, and the kill at `ioCross` AT `GF`
  have hnB : ¬ badRun gen σ0 := noBadRun hlc GF0 gen σ0 D hD hfr hwp
  exact cycleKillIOC GF ad z ss hc hres hdr hne
    (rawChainChainCZR GF ad GR pi P (cdLog c c.cdTr.length) (badRun gen σ0) ss hc hres hdr hwfR
      hagR hrowR (hAQ GF ad him hc hconf) (hRC GF ad him hc hconf) hlog hpr hnB
      (hl2 GF ad GR pi him hconf hwfR hagR hrowR (cdLog c c.cdTr.length) z ss hc hlog hpr hne
        hch) z z ss (fun _ h => h) hch)

/-- **`cycleKillOfWalkCZRC` — WHAT W11-F CONSUMES (N2′, replacing `cycleKillOfWalkCZCw`)**: the
class kill from the WP package, the fetch-view premise, the TAIL-WALK POLICY (`tailPolicyCZ`,
W10-2/W10-4), the two xv6 facts (`acqAqCZ`, `relCoversCZ`, W11-F per pc) and the L2′ claim at the
member (`l2ClaimCZR`).  No `gwrowGmo GF` anywhere. -/
theorem cycleKillOfWalkCZRC (hlc : HasLC) (GF0 : BundledGFunctors) [MachGpreS hlc GF0]
    [WeakGpreS GF0] (gen : Nat) (σ0 : WGState) (D : CPU → List Register) (hD : ∀ c, (D c).Nodup)
    (Nm : Int → Int → Namespace) (P : Int → Int → Prop)
    (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (N : Nat) :
    freshEra gen σ0 →
    (List.range' 0 N).map boot = epsInit σ0 →
    d0 = efInit σ0.wgdev →
    wpPackage hlc GF0 gen σ0 D →
    (∀ a base, P a base → wpPackageProt hlc GF0 gen σ0 D (Nm a base) a base) →
    (∀ ρ, rtc epfRun (epInit gen, σ0) ρ → efetchItvOk ρ.1 ρ.2) →
    tailPolicyCZ boot d0 fab (imgZ σ0.wgimg) N P →
    acqAqCZ boot d0 fab (imgZ σ0.wgimg) P →
    relCoversCZ boot d0 fab (imgZ σ0.wgimg) P →
    l2ClaimCZR boot d0 fab (imgZ σ0.wgimg) P (badRun gen σ0) →
    cycleKillCZC boot d0 fab (imgZ σ0.wgimg) :=
  fun hfr hb1 hb2 hwp hwpp hcov htail hAQ hRC hl2 =>
    cycleKillOfL2CZRC hlc GF0 gen σ0 D hD Nm P boot d0 fab N hfr hb1 hb2 hwp hwpp hcov
      (cutSupplyOfCycleCZC boot d0 fab _) (certSupplyCZROfTail boot d0 fab _ N P htail) hAQ hRC
      hl2

/-- The guarded kill from the same premises (`cycleKillOfWalkCZRC` through `cycleKillCZOfC`). -/
theorem cycleKillOfWalkCZR (hlc : HasLC) (GF0 : BundledGFunctors) [MachGpreS hlc GF0]
    [WeakGpreS GF0] (gen : Nat) (σ0 : WGState) (D : CPU → List Register) (hD : ∀ c, (D c).Nodup)
    (Nm : Int → Int → Namespace) (P : Int → Int → Prop)
    (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (N : Nat) :
    freshEra gen σ0 →
    (List.range' 0 N).map boot = epsInit σ0 →
    d0 = efInit σ0.wgdev →
    wpPackage hlc GF0 gen σ0 D →
    (∀ a base, P a base → wpPackageProt hlc GF0 gen σ0 D (Nm a base) a base) →
    (∀ ρ, rtc epfRun (epInit gen, σ0) ρ → efetchItvOk ρ.1 ρ.2) →
    tailPolicyCZ boot d0 fab (imgZ σ0.wgimg) N P →
    acqAqCZ boot d0 fab (imgZ σ0.wgimg) P →
    relCoversCZ boot d0 fab (imgZ σ0.wgimg) P →
    l2ClaimCZR boot d0 fab (imgZ σ0.wgimg) P (badRun gen σ0) →
    cycleKillCZ boot d0 fab (imgZ σ0.wgimg) :=
  fun hfr hb1 hb2 hwp hwpp hcov htail hAQ hRC hl2 =>
    cycleKillCZOfC boot d0 fab _
      (cycleKillOfWalkCZRC hlc GF0 gen σ0 D hD Nm P boot d0 fab N hfr hb1 hb2 hwp hwpp hcov htail
        hAQ hRC hl2)

/-- **`t2linOfWalkCZR`**: T2-LIN at the Zifencei bundle from the tail-walk policy, the two xv6
facts and the L2′ claim at the member. -/
theorem t2linOfWalkCZR (hlc : HasLC) (GF0 : BundledGFunctors) [MachGpreS hlc GF0]
    [WeakGpreS GF0] (gen : Nat) (σ0 : WGState) (D : CPU → List Register) (hD : ∀ c, (D c).Nodup)
    (Nm : Int → Int → Namespace) (P : Int → Int → Prop)
    (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (N : Nat) :
    freshEra gen σ0 →
    (List.range' 0 N).map boot = epsInit σ0 →
    d0 = efInit σ0.wgdev →
    wpPackage hlc GF0 gen σ0 D →
    (∀ a base, P a base → wpPackageProt hlc GF0 gen σ0 D (Nm a base) a base) →
    (∀ ρ, rtc epfRun (epInit gen, σ0) ρ → efetchItvOk ρ.1 ρ.2) →
    tailPolicyCZ boot d0 fab (imgZ σ0.wgimg) N P →
    acqAqCZ boot d0 fab (imgZ σ0.wgimg) P →
    relCoversCZ boot d0 fab (imgZ σ0.wgimg) P →
    l2ClaimCZR boot d0 fab (imgZ σ0.wgimg) P (badRun gen σ0) →
    ∀ (GF : Gfexec) (ad : List (Geid × Geid)),
      GF.gfGd.gdG.gxImg = imgZ σ0.wgimg →
      rvwmoCatAD GF.gfGd ad → GraphFabConf.gfexecConfZF boot d0 fab GF →
      ioResidueGmo GF → gdiskRead14 GF.gfGd.gdG →
      ∀ x, ¬ tc (racyDIO GF) x x :=
  fun hfr hb1 hb2 hwp hwpp hcov htail hAQ hRC hl2 =>
    t2linOfCycleKillCZ boot d0 fab _
      (cycleKillOfWalkCZR hlc GF0 gen σ0 D hD Nm P boot d0 fab N hfr hb1 hb2 hwp hwpp hcov htail
        hAQ hRC hl2)

end glue

end CatLin

end Weak
