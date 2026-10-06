/-
Weak: **the graph-side lock-protocol kit** (route B, stage B2e-2).

Rocq: `iris/WeakRvwmoLock.v` @ xxvzwolszwmp.

The Rocq header, in substance (design: `claude-notes/design/weak-memory-route-b.md`
§4c).  `WeakRvwmoKill`'s racy residuals hand B2e-3 a configuration that pure
order theory cannot refute: a violation `gviol G e w` whose witness `e` reads a
write `w0` sitting gmo-between `w` and `e`.  The xv6 answer is that `e`/`w` and
`w0` live in DIFFERENT critical sections of one lock byte, and critical sections
do not overlap.  This file makes that argument pure order theory over one lock
byte `b`, parameterized by two hypotheses whose discharge is B2e-3's:

  - `lockPattern G b` — the VALUE protocol: every `b`-write either writes zero
    (a RELEASE) or is an RMW writing nonzero whose own read entry at `b` names
    a ZERO value (an ACQUIRE);
  - `lockPaired G b` — the CS PAIRING: every release is the closing write of a
    critical section of ITS OWN hart.

§2 is the window theory: ATOMICITY says no `b`-write is co-strictly-between an
acquire's read source and the acquire (`acqSrc`), LOAD-VALUE + rules 1–3 say the
source is co-BELOW the acquire (`acqTsLt`), so an acquire's co-predecessor on
`b` is exactly the zero write it read (`acqSrcRel`).  The pattern alone does NOT
give mutual exclusion (it admits `ACQ_h · REL_x · ACQ_j · REL_h · REL_j`);
`lockPaired` is the missing "only the holder releases", buildable from program
order through `lockCsIntro`.  §3's induction closes exclusion
(`winExclOfPattern`); §4 assembles `csKill` by a four-step gmo cycle, mirrored:

    j's CS first :  w  <  w0 <  REL_j < ACQ_h <  w
    h's CS first :  w0 <  e  <  REL_h < ACQ_j <  w0

**Deviations from Rocq.**

1. NAMES: lowerCamelCase as `Weak/WeakMem.lean` deviation 1.  The one name of
   this file in `notes/weak-port-dupnames.json`, `gwrites_byte_lbl`, is
   file-qualified (`WeakRvwmoLock.gwritesByteLbl`).
2. VOCABULARY: as `WeakRvwmoGraph` deviation 2 (`Z` ↦ `Int`, `bv 8` ↦
   `BitVec 8`, `is_Some o` ↦ `o.isSome`, `gx_img G b` ↦ `G.gxImg b`);
   `Z_to_bv 8 0` ↦ `0#8`; `gpo` ↦ `WeakRvwmoGraph.gpo`.
3. `lock_cs_intro`'s `injective_projections` is `Prod.ext`.

**Name map** (Rocq → Lean): `gwrites_byte_det` ↦ `gwritesByteDet`;
`gwrites_byte_lbl` ↦ `WeakRvwmoLock.gwritesByteLbl`; `gwrites_byte_glbl_w` ↦
`gwritesByteGlblW`; `gwrites_byte_gwrites` ↦ `gwritesByteGwrites`;
`gwix_lt_gmo` ↦ `gwixLtGmo`; `gmo_gwix_lt` ↦ `gmoGwixLt`; `gpo_of_lt` ↦
`gpoOfLt`; `acq_gmo_after` ↦ `acqGmoAfter`; `fence_gmo_after` ↦
`fenceGmoAfter`; `lock_free` ↦ `lockFree`; `lock_acq` ↦ `lockAcq`;
`lock_rel` ↦ `lockRel`; `lock_pattern` ↦ `lockPattern`; `lock_acq_not_rel` ↦
`lockAcqNotRel`; `lock_acq_gwrites` ↦ `lockAcqGwrites`; `lock_rel_gwrites` ↦
`lockRelGwrites`; `lock_acq_read` ↦ `lockAcqRead`; `acq_src` ↦ `acqSrc`;
`acq_ts_lt` ↦ `acqTsLt`; `acq_src_rel` ↦ `acqSrcRel`; `lock_cs` ↦ `lockCs`;
`lock_paired` ↦ `lockPaired`; `lock_po_gwix` ↦ `lockPoGwix`; `lock_cs_intro` ↦
`lockCsIntro`; `lock_cs_functional` ↦ `lockCsFunctional`; `acq_no_overlap` ↦
`acqNoOverlap`; `win_excl_of_pattern` ↦ `winExclOfPattern`; `cs_kill` ↦
`csKill`.

**Not ported:** nothing.

**Statements checked** (by hand, against Rocq): all of them.
-/
import Weak.WeakMem
import Weak.WeakAxiomatic
import Weak.WeakRvwmoGraph
import Weak.WeakRvwmoXchg

namespace Weak

/-! # 0. Bookkeeping — byte footprints, write indices, and gmo -/

/-- A write event's byte value is FUNCTIONAL (`accAddr` is injective in the
offset): the reason an acquire (nonzero) can never BE a release (zero). -/
theorem gwritesByteDet (G : Gexec) (e : Geid) (a : Int) (v1 v2 : BitVec 8) :
    gwritesByte G e a v1 → gwritesByte G e a v2 → v1 = v2 := by
  rintro ⟨l1, base1, vs1, j1, hl1, hwr1, hv1, ha1⟩ ⟨l2, base2, vs2, j2, hl2, hwr2, hv2, ha2⟩
  rw [hl1, Option.some.injEq] at hl2
  subst hl2
  rw [hwr1, Option.some.injEq, Prod.mk.injEq] at hwr2
  obtain ⟨rfl, rfl⟩ := hwr2
  have : j1 = j2 := accAddrInj base1 j1 j2 (by rw [ha1, ha2])
  subst this
  rw [hv1, Option.some.injEq] at hv2
  exact hv2

theorem WeakRvwmoLock.gwritesByteLbl (G : Gexec) (e : Geid) (a : Int) (v : BitVec 8) :
    gwritesByte G e a v → (gxLbl G e).isSome := by
  rintro ⟨l, _, _, _, hl, _⟩
  simp [hl]

theorem gwritesByteGlblW (G : Gexec) (e : Geid) (a : Int) (v : BitVec 8) :
    gwritesByte G e a v → glblIs G e lbIsW := by
  rintro ⟨l, _, _, _, hl, hwr, _, _⟩
  exact ⟨l, hl, lbWrIsW l _ hwr⟩

theorem gwritesByteGwrites (G : Gexec) (e : Geid) (a : Int) (v : BitVec 8) :
    gwf G → gwritesByte G e a v → e ∈ gwrites G := fun hwf hw =>
  gisWGwrites G e hwf (WeakRvwmoLock.gwritesByteLbl G e a v hw)
    (WeakRvwmoGraph.gwritesByteGisW G e a v hw)

/-- `gwix` and `gmoLt` agree on the writes, in both directions. -/
theorem gwixLtGmo (G : Gexec) (w1 w2 : Geid) :
    gwf G → w1 ∈ gwrites G → w2 ∈ gwrites G → gwix G w1 < gwix G w2 → gmoLt G w1 w2 :=
  fun hwf h1 h2 hlt =>
    ⟨((gwritesElemOf G w1).1 h1).1, ((gwritesElemOf G w2).1 h2).1,
     (gwixGposLt G w1 w2 hwf.1 h1 h2).1 hlt⟩

theorem gmoGwixLt (G : Gexec) (w1 w2 : Geid) :
    gwf G → w1 ∈ gwrites G → w2 ∈ gwrites G → gmoLt G w1 w2 → gwix G w1 < gwix G w2 :=
  fun hwf h1 h2 hlt => (gwixGposLt G w1 w2 hwf.1 h1 h2).2 hlt.2.2

/-- Program order from a same-hart offset comparison. -/
theorem gpoOfLt (G : Gexec) (x y : Geid) :
    x.1 = y.1 → x.2 < y.2 → (gxLbl G x).isSome → (gxLbl G y).isSome →
    WeakRvwmoGraph.gpo G x y :=
  fun h1 h2 h3 h4 => ⟨h1, h2, h3, h4⟩

/-- RULE 5 — an acquiring read is gmo-before every po-later MEMORY event. -/
theorem acqGmoAfter (G : Gexec) (a x : Geid) :
    gppoGmo G → WeakRvwmoGraph.gpo G a x → glblIs G a lbIsR → glblIs G a lbAq →
    gmem G x → gmoLt G a x :=
  fun hppo hpo hr haq hm => hppo a x (Or.inr (Or.inr (Or.inl ⟨hpo, hr, haq, hm⟩)))

/-- RULE 4 — a covering fence orders. -/
theorem fenceGmoAfter (G : Gexec) (x y : Geid) :
    gppoGmo G → gfenceCovers G x y → gmoLt G x y :=
  fun hppo hf => hppo x y (Or.inr (Or.inl hf))

/-! # 1. The value pattern -/

def lockFree : BitVec 8 := 0#8

/-- An ACQUIRE on `b`: a `b`-write of a NONZERO byte. -/
def lockAcq (G : Gexec) (b : Int) (w : Geid) : Prop :=
  ∃ v, gwritesByte G w b v ∧ v ≠ lockFree

/-- A RELEASE on `b`: a `b`-write of the free byte. -/
def lockRel (G : Gexec) (b : Int) (w : Geid) : Prop :=
  gwritesByte G w b lockFree

/-- THE PATTERN: the image starts the byte free, and every `b`-write is an
acquire (an RMW whose read entry at `b` names zero) or a release. -/
def lockPattern (G : Gexec) (b : Int) : Prop :=
  (∀ v0, G.gxImg b = some v0 → v0 = lockFree) ∧
  (∀ w v, gwritesByte G w b v →
     (glblIs G w lbIsR ∧ v ≠ lockFree ∧ (∃ t, greadsByte G w b t lockFree)) ∨
     v = lockFree)

theorem lockAcqNotRel (G : Gexec) (b : Int) (w : Geid) :
    lockAcq G b w → lockRel G b w → False := by
  rintro ⟨v, hw, hne⟩ hr
  exact hne (gwritesByteDet G w b v lockFree hw hr)

theorem lockAcqGwrites (G : Gexec) (b : Int) (w : Geid) :
    gwf G → lockAcq G b w → w ∈ gwrites G := by
  rintro hwf ⟨v, hw, _⟩
  exact gwritesByteGwrites G w b v hwf hw

theorem lockRelGwrites (G : Gexec) (b : Int) (w : Geid) :
    gwf G → lockRel G b w → w ∈ gwrites G :=
  fun hwf hw => gwritesByteGwrites G w b lockFree hwf hw

/-- THE PATTERN AT AN ACQUIRE: it is a read, and it read zero at `b`. -/
theorem lockAcqRead (G : Gexec) (b : Int) (w : Geid) :
    lockPattern G b → lockAcq G b w →
    glblIs G w lbIsR ∧ ∃ t, greadsByte G w b t lockFree := by
  rintro ⟨_, hpat⟩ ⟨v, hw, hne⟩
  rcases hpat w v hw with ⟨hr, _, ht⟩ | hz
  · exact ⟨hr, ht⟩
  · exact absurd hz hne

/-! # 2. The window: an acquire's co-predecessor is the zero write it read -/

/-- ATOMICITY, in window form. -/
theorem acqSrc (G : Gexec) (b : Int) (A : Geid) (t : Nat) :
    rvwmoMinusConsistent G → lockAcq G b A →
    greadsByte G A b t lockFree →
    ∀ w' v', gwritesByte G w' b v' → gwix G w' ≤ t ∨ gwix G A ≤ gwix G w' := by
  rintro ⟨_, _, _, hat⟩ ⟨v, hwb, _⟩ hrd w' v' hw'
  have hna := hat A b t lockFree hrd (gwritesByteGlblW _ _ _ _ hwb) w' v' hw'
  omega

/-- LOAD VALUE + rules 1–3: the acquire's read index is BELOW its own write
index. -/
theorem acqTsLt (G : Gexec) (b : Int) (A : Geid) (t : Nat) :
    rvwmoMinusConsistent G → lockAcq G b A →
    greadsByte G A b t lockFree → t < gwix G A := by
  intro hcons hacq hrd
  obtain ⟨hwf, hppo, hlv, _⟩ := hcons
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
      exact hppo r A (Or.inl ⟨hpo, b, Or.inl ⟨lockFree, hrb⟩, Or.inl ⟨v, hwb⟩⟩)

/-- For a nonzero read index the named source IS a release at index `t`. -/
theorem acqSrcRel (G : Gexec) (b : Int) (A : Geid) (t : Nat) :
    rvwmoMinusConsistent G → greadsByte G A b t lockFree → 0 < t →
    ∃ r, lockRel G b r ∧ r ∈ gwrites G ∧ gwix G r = t := by
  intro hcons hrd hpos
  obtain ⟨hwf, _, hlv, _⟩ := hcons
  have hnd := hwf.1
  cases t with
  | zero => omega
  | succ t =>
    obtain ⟨⟨r, hat, hrb, _⟩, _⟩ := hlv A b (t + 1) lockFree hrd
    obtain ⟨hr, hrix⟩ := gwriteAtInv G (t + 1) r hnd hat
    exact ⟨r, hrb, hr, hrix⟩

/-! # 3. Critical sections and their exclusion -/

def lockCs (G : Gexec) (b : Int) (A R : Geid) : Prop :=
  lockAcq G b A ∧ lockRel G b R ∧ A.1 = R.1 ∧
  gwix G A < gwix G R ∧
  (∀ x v, gwritesByte G x b v → x.1 = A.1 →
     ¬ (gwix G A < gwix G x ∧ gwix G x < gwix G R))

def lockPaired (G : Gexec) (b : Int) : Prop :=
  ∀ R, lockRel G b R → ∃ A, lockCs G b A R

/-- Same-hart `b`-writes are co-ordered as they are po-ordered (rules 1–3). -/
theorem lockPoGwix (G : Gexec) (b : Int) (x y : Geid) (v v' : BitVec 8) :
    rvwmoMinusConsistent G → gwritesByte G x b v → gwritesByte G y b v' →
    WeakRvwmoGraph.gpo G x y → gwix G x < gwix G y := by
  intro hcons hx hy hpo
  obtain ⟨hwf, hppo, _, _⟩ := hcons
  exact gmoGwixLt G x y hwf (gwritesByteGwrites G x b v hwf hx)
    (gwritesByteGwrites G y b v' hwf hy)
    (hppo x y (Or.inl ⟨hpo, b, Or.inl ⟨v, hx⟩, Or.inl ⟨v', hy⟩⟩))

/-- B2e-3's CONSTRUCTOR: a critical section from program order. -/
theorem lockCsIntro (G : Gexec) (b : Int) (A R : Geid) :
    rvwmoMinusConsistent G → WeakRvwmoGraph.gpo G A R →
    lockAcq G b A → lockRel G b R →
    (∀ x v, gwritesByte G x b v → x.1 = A.1 → A.2 < x.2 → x.2 < R.2 → False) →
    lockCs G b A R := by
  intro hcons hpo hacq hrel hno
  obtain ⟨va, hwa, _⟩ := id hacq
  have hlt : gwix G A < gwix G R := lockPoGwix G b A R va lockFree hcons hwa hrel hpo
  obtain ⟨hag, _, hsA, hsR⟩ := hpo
  refine ⟨hacq, hrel, hag, hlt, ?_⟩
  rintro x v hx hxag ⟨hlo, hhi⟩
  have hsx := WeakRvwmoLock.gwritesByteLbl G x b v hx
  -- place `x` po-after `A`
  have hxA : A.2 < x.2 := by
    rcases Nat.lt_trichotomy x.2 A.2 with hc | hc | hc
    · have := lockPoGwix G b x A v va hcons hx hwa (gpoOfLt G x A hxag hc hsx hsA)
      omega
    · have : x = A := Prod.ext hxag hc
      subst this
      omega
    · exact hc
  -- ... and po-before `R`
  have hxR : x.2 < R.2 := by
    rcases Nat.lt_trichotomy x.2 R.2 with hc | hc | hc
    · exact hc
    · have : x = R := Prod.ext (hxag.trans hag) hc
      subst this
      omega
    · have := lockPoGwix G b R x lockFree v hcons hrel hx
        (gpoOfLt G R x (hxag.trans hag).symm hc hsR hsx)
      omega
  exact hno x v hx hxag hxA hxR

/-- The pairing is FUNCTIONAL. -/
theorem lockCsFunctional (G : Gexec) (b : Int) (A R1 R2 : Geid) :
    gwf G → lockCs G b A R1 → lockCs G b A R2 → R1 = R2 := by
  rintro hwf ⟨_, hr1, hag1, hlt1, hno1⟩ ⟨_, hr2, hag2, hlt2, hno2⟩
  refine Classical.byContradiction fun hne => ?_
  have hix : gwix G R1 ≠ gwix G R2 := fun heq =>
    hne (gwixInj G R1 R2 hwf.1 (lockRelGwrites G b R1 hwf hr1)
      (lockRelGwrites G b R2 hwf hr2) heq)
  by_cases hlt : gwix G R1 < gwix G R2
  · exact hno2 R1 lockFree hr1 hag1.symm ⟨hlt1, hlt⟩
  · exact hno1 R2 lockFree hr2 hag2.symm ⟨hlt2, by omega⟩

/-! ## 3.1 The exclusion induction

NO ACQUIRE SITS STRICTLY INSIDE ANOTHER CRITICAL SECTION, by strong induction
on the intruding acquire's write index. -/

theorem acqNoOverlap (G : Gexec) (b : Int) :
    rvwmoMinusConsistent G → lockPattern G b → lockPaired G b →
    ∀ n A2, gwix G A2 ≤ n → lockAcq G b A2 →
    ∀ A1 R1, lockCs G b A1 R1 →
      gwix G A1 < gwix G A2 → gwix G A2 < gwix G R1 → False := by
  intro hcons hpat hpair
  have hwf := hcons.1
  intro n
  induction n with
  | zero =>
    intro A2 hle hA2 _ _ _ _ _
    have := WeakRvwmoGraph.gwixPos G A2 (lockAcqGwrites G b A2 hwf hA2)
    omega
  | succ n ih =>
    intro A2 hle hA2 A1 R1 hcs1 hlt1 hlt2
    obtain ⟨hA1, _, _, _, _⟩ := id hcs1
    -- the intruder read zero at `b`, at some index `t`
    obtain ⟨_, t, hrd2⟩ := lockAcqRead G b A2 hpat hA2
    have htlt := acqTsLt G b A2 t hcons hA2 hrd2
    -- the host acquire is not inside the intruder's window
    obtain ⟨v1, hwb1, _⟩ := id hA1
    have hle1 : gwix G A1 ≤ t := by
      rcases acqSrc G b A2 t hcons hA2 hrd2 A1 v1 hwb1 with h | h
      · exact h
      · omega
    have hpos1 := WeakRvwmoGraph.gwixPos G A1 (lockAcqGwrites G b A1 hwf hA1)
    -- so the window bottom names a real write: the intruder's co-predecessor
    obtain ⟨r, hr, hrw, hrix⟩ := acqSrcRel G b A2 t hcons hrd2 (by omega)
    have hner1 : A1 ≠ r := by
      rintro rfl
      exact lockAcqNotRel G b A1 hA1 hr
    have hlt1r : gwix G A1 < gwix G r := by
      by_cases heq : gwix G A1 = gwix G r
      · exact absurd (gwixInj G A1 r hwf.1 (lockAcqGwrites G b A1 hwf hA1) hrw heq) hner1
      · omega
    -- the co-predecessor closes SOME critical section
    obtain ⟨Ak, hcsk⟩ := hpair r hr
    by_cases hek : Ak = A1
    · -- it is the host's own release, but it is co-below the intruder
      subst hek
      have := lockCsFunctional G b Ak r R1 hwf hcsk hcs1
      subst this
      omega
    · obtain ⟨hAk, _, _, hltk, _⟩ := id hcsk
      have hixk : gwix G Ak ≠ gwix G A1 := fun heq =>
        hek (gwixInj G Ak A1 hwf.1 (lockAcqGwrites G b Ak hwf hAk)
          (lockAcqGwrites G b A1 hwf hA1) heq)
      by_cases hkl : gwix G Ak < gwix G A1
      · -- `A1` intrudes into `(Ak, r)`, and `A1` is co-earlier than `A2`
        exact ih A1 (by omega) hA1 Ak r hcsk hkl (by omega)
      · -- `Ak` intrudes into `(A1, R1)`, and `Ak` is co-earlier than `A2`
        exact ih Ak (by omega) hAk A1 R1 hcs1 (by omega) (by omega)

/-! ## 3.2 The export: two distinct critical sections are disjoint and totally
ordered -/

theorem winExclOfPattern (G : Gexec) (b : Int) :
    rvwmoMinusConsistent G → lockPattern G b → lockPaired G b →
    ∀ A1 R1 A2 R2, lockCs G b A1 R1 → lockCs G b A2 R2 → A1 ≠ A2 →
      gwix G R1 < gwix G A2 ∨ gwix G R2 < gwix G A1 := by
  intro hcons hpat hpair A1 R1 A2 R2 hcs1 hcs2 hne
  have hwf := hcons.1
  have hnd := hwf.1
  obtain ⟨hA1, hR1, _, hlt1, _⟩ := id hcs1
  obtain ⟨hA2, hR2, _, hlt2, _⟩ := id hcs2
  have hix : gwix G A1 ≠ gwix G A2 := fun heq =>
    hne (gwixInj G A1 A2 hnd (lockAcqGwrites G b A1 hwf hA1)
      (lockAcqGwrites G b A2 hwf hA2) heq)
  -- a release is never an acquire, so the boundaries never coincide
  have hb1 : gwix G R1 ≠ gwix G A2 := fun heq => by
    have := gwixInj G R1 A2 hnd (lockRelGwrites G b R1 hwf hR1)
      (lockAcqGwrites G b A2 hwf hA2) heq
    subst this
    exact lockAcqNotRel G b R1 hA2 hR1
  have hb2 : gwix G R2 ≠ gwix G A1 := fun heq => by
    have := gwixInj G R2 A1 hnd (lockRelGwrites G b R2 hwf hR2)
      (lockAcqGwrites G b A1 hwf hA1) heq
    subst this
    exact lockAcqNotRel G b R2 hA1 hR2
  by_cases hlt : gwix G A1 < gwix G A2
  · left
    by_cases hin : gwix G A2 < gwix G R1
    · exact (acqNoOverlap G b hcons hpat hpair (gwix G A2) A2 (Nat.le_refl _) hA2
        A1 R1 hcs1 hlt hin).elim
    · omega
  · right
    have hlt' : gwix G A2 < gwix G A1 := by omega
    by_cases hin : gwix G A1 < gwix G R2
    · exact (acqNoOverlap G b hcons hpat hpair (gwix G A1) A1 (Nat.le_refl _) hA1
        A2 R2 hcs2 hlt' hin).elim
    · omega

/-! # 4. `csKill` — the assembled contradiction

THE FOUR-STEP CYCLE, mirrored across the window order:

    ACQ_j first :  w  gmo< w0 gmo< REL_j gmo< ACQ_h gmo< w
    ACQ_h first :  w0 gmo< e  gmo< REL_h gmo< ACQ_j gmo< w0

with the release steps by ppo rule 4 and the acquire steps by ppo rule 5. -/

theorem csKill (G : Gexec) (b : Int) (e w w0 ACQh RELh ACQj RELj : Geid) :
    -- the declared model
    rvwmoMinusConsistent G →
    -- the lock-word protocol on byte `b`
    lockPattern G b → lockPaired G b →
    -- the configuration (`kill_K1_racy`'s core)
    gviol G e w → gmoLt G w w0 → gmoLt G w0 e →
    -- CS coverage on hart `e.1`
    lockCs G b ACQh RELh →
    WeakRvwmoGraph.gpo G ACQh e → glblIs G ACQh lbAq → gfenceCovers G e RELh →
    -- CS coverage on hart `w0.1`
    lockCs G b ACQj RELj →
    WeakRvwmoGraph.gpo G ACQj w0 → glblIs G ACQj lbAq → gfenceCovers G w0 RELj →
    -- the two sections are distinct
    e.1 ≠ w0.1 →
    False := by
  intro hcons hpat hpair hv hmoWw0 hmoW0e hcsh hpoh haqh hfh hcsj hpoj haqj hfj hhart
  obtain ⟨hwf, hppo, _, _⟩ := id hcons
  -- the acquires sit on the two harts, so they are distinct events
  have hne : ACQh ≠ ACQj := by
    intro heq
    apply hhart
    rw [← hpoh.1, heq, hpoj.1]
  obtain ⟨hAh, hRh, _, _, _⟩ := id hcsh
  obtain ⟨hAj, hRj, _, _, _⟩ := id hcsj
  -- the pattern makes both acquires READS, which is rule 5's other half
  obtain ⟨hrh, _⟩ := lockAcqRead G b ACQh hpat hAh
  obtain ⟨hrj, _⟩ := lockAcqRead G b ACQj hpat hAj
  -- rule 5, twice
  obtain ⟨hpoEw, _, hww, _⟩ := id hv
  have hpoHw : WeakRvwmoGraph.gpo G ACQh w := by
    refine ⟨hpoh.1.trans hpoEw.1, ?_, hpoh.2.2.1, hpoEw.2.2.2⟩
    have := hpoh.2.1
    have := hpoEw.2.1
    omega
  have hmoHw : gmoLt G ACQh w :=
    acqGmoAfter G ACQh w hppo hpoHw hrh haqh (WeakRvwmoGraph.glblIsWGmem G w hww)
  have hmoJw0 : gmoLt G ACQj w0 :=
    acqGmoAfter G ACQj w0 hppo hpoj hrj haqj (gwfGmoMem G w0 hwf hmoWw0.2.1)
  -- rule 4, twice
  have hmoErh := fenceGmoAfter G e RELh hppo hfh
  have hmoW0rj := fenceGmoAfter G w0 RELj hppo hfj
  -- the window order
  rcases winExclOfPattern G b hcons hpat hpair ACQh RELh ACQj RELj hcsh hcsj hne with
    hwin | hwin
  · -- `ACQh`'s section closes first: w0 < e < RELh < ACQj < w0
    have hmoRhj := gwixLtGmo G RELh ACQj hwf (lockRelGwrites G b RELh hwf hRh)
      (lockAcqGwrites G b ACQj hwf hAj) hwin
    exact gmoLtIrrefl G w0 (gmoLtTrans G w0 e w0 hmoW0e
      (gmoLtTrans G e RELh w0 hmoErh (gmoLtTrans G RELh ACQj w0 hmoRhj hmoJw0)))
  · -- `ACQj`'s section closes first: w < w0 < RELj < ACQh < w
    have hmoRjh := gwixLtGmo G RELj ACQh hwf (lockRelGwrites G b RELj hwf hRj)
      (lockAcqGwrites G b ACQh hwf hAh) hwin
    exact gmoLtIrrefl G w (gmoLtTrans G w w0 w hmoWw0
      (gmoLtTrans G w0 RELj w hmoW0rj (gmoLtTrans G RELj ACQh w hmoRjh hmoHw)))

end Weak
