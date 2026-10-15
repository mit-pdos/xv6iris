/-
Weak: **W10-4 [OWN.94] (N2′), decision (i) — the RACE-FREE READS theorem, graph half (D1)**
(`PROGRESS-W10N2p.md`).  Lean-only, no Rocq twin.

A plain load `r` of a byte `a` protected by the lock byte `b`, inside a critical section of `b`, walked
at position `k` of an order `L` that respects po and lock co (release → acquire), reads in `GF` the
`L`-LAST write of `a` before position `k` (or the image when none is walked before it).  This is what
the walk's value agreement (`CertZ11.readAgree`, the lockstep arm of `CertZ13.siteFacts`) needs at a
protected read; the walk-log half (D2: the walk's latest bytes are the `L`-last writes' values) is next.

  §1  **`CertZ21.secOf`** (an event inside a section of `b` opened by a SUCCESSFUL acquire: closed —
      `lockCs` and po-before the release — or open: the acquire is its hart's last `b`-write), **`CertZ21.drfFacts`** — (G1) every
      write of `a` is inside a section of `b`; acquires are acquire-RMWs (rule 5); releases
      fence-cover their section's memory events; (G2) distinct sections are disjoint in lock co — and
      **`CertZ21.ordFacts`** (the order: duplicate-free, every event, po, release→acquire lock co);
  §2  `CertZ21.visOfBefore` (a write walked before `r` is visible to `r`), `CertZ21.ordOfCo` (writes of
      `a` are walked in co order), `CertZ21.srcBefore` (`r`'s source is walked before it);
  §3  **`CertZ21.drfRead`**.

RVWMO first: the argument uses only RVWMO's load-value axiom (`gloadValue`: the source is the
co-latest VISIBLE write — gmo-before or po-before), ppo rule 1 (same-address po to a write), rule 5
(acquire), the release fence (`fence rw,w` before the release's plain `sw zero`), and co ⊆ gmo on writes —
FAITHFUL.  Restriction recorded: (G1) asks EVERY write of `a` to be inside a section; writes outside the
lock's life (`kalloc`'s junk fill, `kfree`'s memset) need a pre-life / post-life arm (next).
-/
import Weak.CertZ20

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open TsoShadow

/-! # 1. Sections, the DRF facts, the order facts -/

/-- `e` lies inside the section of `b` opened by the SUCCESSFUL acquire `A` (`acqRow`: it read the free
byte — a spinning hart's failed `amoswap` opens nothing): closed (`lockCs`, `e` po-before the release)
or OPEN (`A`'s hart writes `b` no more after `A`). -/
def CertZ21.secOf (G : Gexec) (b : Int) (e A : Geid) (oR : Option Geid) : Prop :=
  WeakRvwmoGraph.gpo G A e ∧ acqRow G b A ∧
  match oR with
  | some R => lockCs G b A R ∧ WeakRvwmoGraph.gpo G e R
  | none => lockAcq G b A ∧
      ∀ x v, gwritesByte G x b v → x.1 = A.1 → gwix G A < gwix G x → False

theorem CertZ21.secAcq (G : Gexec) (b : Int) (e A : Geid) (oR : Option Geid) :
    CertZ21.secOf G b e A oR → lockAcq G b A := by
  intro h
  cases oR with
  | some R => exact h.2.2.1.1
  | none => exact h.2.2.1

theorem CertZ21.secRel (G : Gexec) (b : Int) (e A R : Geid) :
    CertZ21.secOf G b e A (some R) → lockRel G b R ∧ WeakRvwmoGraph.gpo G e R :=
  fun h => ⟨h.2.2.1.2.1, h.2.2.2⟩

/-- **THE DRF FACTS** of the protected byte `a` under the lock byte `b` in `GF`. -/
def CertZ21.drfFacts (G : Gexec) (b a : Int) : Prop :=
  (∀ w v, gwritesByte G w a v → ∃ A oR, CertZ21.secOf G b w A oR) ∧
  (∀ e A oR, CertZ21.secOf G b e A oR → glblIs G A lbIsR ∧ glblIs G A lbAq) ∧
  (∀ e A R, CertZ21.secOf G b e A (some R) → gmem G e → gfenceCovers G e R) ∧
  (∀ e1 A1 oR1 e2 A2 oR2, CertZ21.secOf G b e1 A1 oR1 → CertZ21.secOf G b e2 A2 oR2 → A1 ≠ A2 →
    (∃ R1, oR1 = some R1 ∧ gwix G R1 < gwix G A2) ∨ (∃ R2, oR2 = some R2 ∧ gwix G R2 < gwix G A1))

/-- `x` is walked before `y`. -/
def CertZ21.ordBefore (L : List Geid) (x y : Geid) : Prop :=
  ∀ i j : Nat, L[i]? = some x → L[j]? = some y → i < j

/-- **THE ORDER FACTS**: duplicate-free, every event, po, and release → acquire lock co on `b`. -/
def CertZ21.ordFacts (G : Gexec) (b : Int) (L : List Geid) : Prop :=
  L.Nodup ∧
  (∀ e, (gxLbl G e).isSome → ∃ i : Nat, L[i]? = some e) ∧
  (∀ x y, WeakRvwmoGraph.gpo G x y → CertZ21.ordBefore L x y) ∧
  (∀ R A, lockRel G b R → lockAcq G b A → gwix G R < gwix G A → CertZ21.ordBefore L R A)

/-! # 2. The three lemmas -/

theorem CertZ21.poTri (G : Gexec) (x y z : Geid) :
    WeakRvwmoGraph.gpo G z x → WeakRvwmoGraph.gpo G z y → x ≠ y →
    WeakRvwmoGraph.gpo G x y ∨ WeakRvwmoGraph.gpo G y x := by
  rintro ⟨h1, -, -, hx⟩ ⟨h2, -, -, hy⟩ hne
  rcases Nat.lt_trichotomy x.2 y.2 with h | h | h
  · exact .inl ⟨h1.symm.trans h2, h, hx, hy⟩
  · exact absurd (Prod.ext (h1.symm.trans h2) h) hne
  · exact .inr ⟨h2.symm.trans h1, h, hy, hx⟩

theorem CertZ21.memOfPo1 (G : Gexec) (L : List Geid) (b : Int) (x y : Geid) :
    CertZ21.ordFacts G b L → WeakRvwmoGraph.gpo G x y → ∃ i : Nat, L[i]? = some x :=
  fun ho hpo => ho.2.1 x hpo.2.2.1

theorem CertZ21.memOfPo2 (G : Gexec) (L : List Geid) (b : Int) (x y : Geid) :
    CertZ21.ordFacts G b L → WeakRvwmoGraph.gpo G x y → ∃ i : Nat, L[i]? = some y :=
  fun ho hpo => ho.2.1 y hpo.2.2.2

/-- A write of `a` walked before the protected read is VISIBLE to it. -/
theorem CertZ21.visOfBefore (G : Gexec) (b a : Int) (L : List Geid) (w r Ar : Geid)
    (oRr : Option Geid) (i k : Nat) (v : BitVec 8) :
    gwf G → gppoCat6Gmo G → CertZ21.drfFacts G b a → CertZ21.ordFacts G b L →
    gwritesByte G w a v → ¬ glblIs G r lbIsW → glblIs G r lbIsR → CertZ21.secOf G b r Ar oRr →
    L[i]? = some w → L[k]? = some r → i < k → gvisible G w r := by
  intro hwf h6 hd ho hw hnW hR hsr hi hk hik
  have ho' := ho
  obtain ⟨hP, hAcq, hRel, hDisj⟩ := hd
  obtain ⟨-, -, hPo, hCo⟩ := ho
  obtain ⟨Aw, oRw, hsw⟩ := hP w v hw
  have hwW := gwritesByteGlblW G w a v hw
  by_cases hA : Aw = Ar
  · subst hA
    have hwr : w ≠ r := fun h => hnW (h ▸ hwW)
    rcases CertZ21.poTri G w r Aw hsw.1 hsr.1 hwr with h | h
    · exact .inr h
    · exact absurd (hPo r w h k i hk hi) (by omega)
  · rcases hDisj w Aw oRw r Ar oRr hsw hsr hA with ⟨Rw, rfl, hlt⟩ | ⟨Rr, rfl, hlt⟩
    · have hRw := (CertZ21.secRel G b w Aw Rw hsw).1
      have hAr := CertZ21.secAcq G b r Ar oRr hsr
      have h1 : gmoLt G w Rw :=
        CatLin.fenceGmoAfterC G w Rw h6 (hRel w Aw Rw hsw (WeakRvwmoGraph.glblIsWGmem G w hwW))
      have h2 : gmoLt G Rw Ar :=
        gwixLtGmo G Rw Ar hwf (lockRelGwrites G b Rw hwf hRw) (lockAcqGwrites G b Ar hwf hAr) hlt
      have h3 : gmoLt G Ar r :=
        CatLin.acqGmoAfterC G Ar r h6 hsr.1 (hAcq r Ar _ hsr).1 (hAcq r Ar _ hsr).2
          (WeakRvwmoGraph.glblIsRGmem G r hR)
      exact .inl (gmoLtTrans G w Ar r (gmoLtTrans G w Rw Ar h1 h2) h3)
    · exfalso
      obtain ⟨hRr, hpoR⟩ := CertZ21.secRel G b r Ar Rr hsr
      have hAw := CertZ21.secAcq G b w Aw _ hsw
      obtain ⟨iR, hiR⟩ := CertZ21.memOfPo2 G L b r Rr ho' hpoR
      obtain ⟨iA, hiA⟩ := CertZ21.memOfPo1 G L b Aw w ho' hsw.1
      have := hPo r Rr hpoR k iR hk hiR
      have := hCo Rr Aw hRr hAw hlt iR iA hiR hiA
      have := hPo Aw w hsw.1 iA i hiA hi
      omega

/-- Writes of `a` are walked in co order. -/
theorem CertZ21.ordOfCo (G : Gexec) (b a : Int) (L : List Geid) (w1 w2 : Geid) (i1 i2 : Nat)
    (v1 v2 : BitVec 8) :
    gwf G → gppoCat6Gmo G → CertZ21.drfFacts G b a → CertZ21.ordFacts G b L →
    gwritesByte G w1 a v1 → gwritesByte G w2 a v2 → gwix G w1 < gwix G w2 →
    L[i1]? = some w1 → L[i2]? = some w2 → i1 < i2 := by
  intro hwf h6 hd ho hw1 hw2 hlt12 hi1 hi2
  have ho' := ho
  obtain ⟨hP, hAcq, hRel, hDisj⟩ := hd
  obtain ⟨-, -, hPo, hCo⟩ := ho
  obtain ⟨A1, oR1, hs1⟩ := hP w1 v1 hw1
  obtain ⟨A2, oR2, hs2⟩ := hP w2 v2 hw2
  have hg1 := gwritesByteGwrites G w1 a v1 hwf hw1
  have hg2 := gwritesByteGwrites G w2 a v2 hwf hw2
  by_cases hA : A1 = A2
  · subst hA
    have hne : w1 ≠ w2 := fun h => by subst h; omega
    rcases CertZ21.poTri G w1 w2 A1 hs1.1 hs2.1 hne with h | h
    · exact hPo w1 w2 h i1 i2 hi1 hi2
    · exfalso
      have := gmoGwixLt G w2 w1 hwf hg2 hg1 (h6 w2 w1 (Or.inl ⟨h, a, .inl ⟨v2, hw2⟩, v1, hw1⟩))
      omega
  · rcases hDisj w1 A1 oR1 w2 A2 oR2 hs1 hs2 hA with ⟨R1, rfl, hlt⟩ | ⟨R2, rfl, hlt⟩
    · obtain ⟨hR1, hpoR⟩ := CertZ21.secRel G b w1 A1 R1 hs1
      have hA2 := CertZ21.secAcq G b w2 A2 _ hs2
      obtain ⟨iR, hiR⟩ := CertZ21.memOfPo2 G L b w1 R1 ho' hpoR
      obtain ⟨iA, hiA⟩ := CertZ21.memOfPo1 G L b A2 w2 ho' hs2.1
      have := hPo w1 R1 hpoR i1 iR hi1 hiR
      have := hCo R1 A2 hR1 hA2 hlt iR iA hiR hiA
      have := hPo A2 w2 hs2.1 iA i2 hiA hi2
      omega
    · exfalso
      have hR2 := (CertZ21.secRel G b w2 A2 R2 hs2).1
      have hA1 := CertZ21.secAcq G b w1 A1 _ hs1
      have h1 : gmoLt G w2 R2 :=
        CatLin.fenceGmoAfterC G w2 R2 h6 (hRel w2 A2 R2 hs2
          (WeakRvwmoGraph.glblIsWGmem G w2 (gwritesByteGlblW G w2 a v2 hw2)))
      have h2 : gmoLt G R2 A1 :=
        gwixLtGmo G R2 A1 hwf (lockRelGwrites G b R2 hwf hR2) (lockAcqGwrites G b A1 hwf hA1) hlt
      have h3 : gmoLt G A1 w1 :=
        CatLin.acqGmoAfterC G A1 w1 h6 hs1.1 (hAcq w1 A1 _ hs1).1 (hAcq w1 A1 _ hs1).2
          (WeakRvwmoGraph.glblIsWGmem G w1 (gwritesByteGlblW G w1 a v1 hw1))
      have := gmoGwixLt G w2 w1 hwf hg2 hg1 (gmoLtTrans G w2 A1 w1 (gmoLtTrans G w2 R2 A1 h1 h2) h3)
      omega

/-- The protected read's visible source is walked before it. -/
theorem CertZ21.srcBefore (G : Gexec) (b a : Int) (L : List Geid) (w0 r Ar : Geid)
    (oRr : Option Geid) (k t : Nat) (v0 v : BitVec 8) :
    gwf G → gppoCat6Gmo G → CertZ21.drfFacts G b a → CertZ21.ordFacts G b L →
    gwritesByte G w0 a v0 → gvisible G w0 r → greadsByte G r a t v →
    CertZ21.secOf G b r Ar oRr → L[k]? = some r → ∃ i, i < k ∧ L[i]? = some w0 := by
  intro hwf h6 hd ho hw hvis hrd hsr hk
  have ho' := ho
  obtain ⟨hP, hAcq, hRel, hDisj⟩ := hd
  obtain ⟨-, hMem, hPo, hCo⟩ := ho
  obtain ⟨i0, hi0⟩ := hMem w0 (by obtain ⟨l, -, -, -, hl, -⟩ := hw; rw [hl]; rfl)
  refine ⟨i0, ?_, hi0⟩
  have hR := greadsByteIsR G r a t v hrd
  rcases hvis with hmo | hpo
  · obtain ⟨Aw, oRw, hsw⟩ := hP w0 v0 hw
    have hwW := gwritesByteGlblW G w0 a v0 hw
    by_cases hA : Aw = Ar
    · subst hA
      have hne : w0 ≠ r := by
        intro h
        subst h
        exact gmoLtIrrefl G w0 hmo
      rcases CertZ21.poTri G w0 r Aw hsw.1 hsr.1 hne with h | h
      · exact hPo w0 r h i0 k hi0 hk
      · exfalso
        have h1 : gmoLt G r w0 := h6 r w0 (Or.inl ⟨h, a, .inr ⟨t, v, hrd⟩, v0, hw⟩)
        exact gmoLtIrrefl G w0 (gmoLtTrans G w0 r w0 hmo h1)
    · rcases hDisj w0 Aw oRw r Ar oRr hsw hsr hA with ⟨Rw, rfl, hlt⟩ | ⟨Rr, rfl, hlt⟩
      · obtain ⟨hRw, hpoR⟩ := CertZ21.secRel G b w0 Aw Rw hsw
        have hAr := CertZ21.secAcq G b r Ar _ hsr
        obtain ⟨iR, hiR⟩ := CertZ21.memOfPo2 G L b w0 Rw ho' hpoR
        obtain ⟨iA, hiA⟩ := CertZ21.memOfPo1 G L b Ar r ho' hsr.1
        have := hPo w0 Rw hpoR i0 iR hi0 hiR
        have := hCo Rw Ar hRw hAr hlt iR iA hiR hiA
        have := hPo Ar r hsr.1 iA k hiA hk
        omega
      · exfalso
        have hRr := (CertZ21.secRel G b r Ar Rr hsr).1
        have hAw := CertZ21.secAcq G b w0 Aw _ hsw
        have h1 : gmoLt G r Rr :=
          CatLin.fenceGmoAfterC G r Rr h6 (hRel r Ar Rr hsr (WeakRvwmoGraph.glblIsRGmem G r hR))
        have h2 : gmoLt G Rr Aw :=
          gwixLtGmo G Rr Aw hwf (lockRelGwrites G b Rr hwf hRr) (lockAcqGwrites G b Aw hwf hAw) hlt
        have h3 : gmoLt G Aw w0 :=
          CatLin.acqGmoAfterC G Aw w0 h6 hsw.1 (hAcq w0 Aw _ hsw).1 (hAcq w0 Aw _ hsw).2
            (WeakRvwmoGraph.glblIsWGmem G w0 hwW)
        exact gmoLtIrrefl G w0
          (gmoLtTrans G w0 r w0 hmo (gmoLtTrans G r Aw w0 (gmoLtTrans G r Rr Aw h1 h2) h3))
  · exact hPo w0 r hpo i0 k hi0 hk

/-! # 3. The theorem -/

/-- **`CertZ21.drfRead` — RACE-FREE READS (graph half)**: a plain read `r` of a protected byte `a`,
inside a section of `b`, walked at position `k`: when it reads the image, no write of `a` is walked
before it; otherwise its source `w0` (writing the value read) is walked before it and every other
write of `a` walked before it is walked before `w0` — `r` reads the walked-LAST write of `a`. -/
theorem CertZ21.drfRead (G : Gexec) (b a : Int) (L : List Geid) (k : Nat) (r Ar : Geid)
    (oRr : Option Geid) (t : Nat) (v : BitVec 8) :
    gwf G → gppoCat6Gmo G → gloadValue G → CertZ21.drfFacts G b a → CertZ21.ordFacts G b L →
    L[k]? = some r → greadsByte G r a t v → ¬ glblIs G r lbIsW → CertZ21.secOf G b r Ar oRr →
    (t = 0 → G.gxImg a = some v ∧
      ∀ w v' i, gwritesByte G w a v' → L[i]? = some w → k ≤ i) ∧
    (∀ w0, gwriteAt G t = some w0 → 0 < t →
      gwritesByte G w0 a v ∧ (∃ i, i < k ∧ L[i]? = some w0) ∧
      ∀ w v' i j, gwritesByte G w a v' → L[i]? = some w → i < k → L[j]? = some w0 → w ≠ w0 →
        i < j) := by
  intro hwf h6 hlv hd ho hk hrd hnW hsr
  have hR := greadsByteIsR G r a t v hrd
  obtain ⟨hsrc, hmax⟩ := hlv r a t v hrd
  constructor
  · intro ht0
    subst ht0
    refine ⟨hsrc, fun w v' i hw hi => Nat.le_of_not_lt (fun hlt => ?_)⟩
    have hvis := CertZ21.visOfBefore G b a L w r Ar oRr i k v' hwf h6 hd ho hw hnW hR hsr hi hk hlt
    have := hmax w v' hw hvis
    have := WeakRvwmoGraph.gwixPos G w (gwritesByteGwrites G w a v' hwf hw)
    omega
  · intro w0 hat ht0
    obtain ⟨n, rfl⟩ : ∃ n, t = n + 1 := ⟨t - 1, by omega⟩
    obtain ⟨w, hatw, hwv, hvis⟩ := hsrc
    rw [hat, Option.some.injEq] at hatw
    subst hatw
    have hix := (gwriteAtInv G _ w0 hwf.1 hat).2
    refine ⟨hwv, CertZ21.srcBefore G b a L w0 r Ar oRr k (n + 1) v v hwf h6 hd ho hwv hvis hrd hsr
      hk, fun w' v' i j hw' hi hik hj hne => ?_⟩
    have hvis' :=
      CertZ21.visOfBefore G b a L w' r Ar oRr i k v' hwf h6 hd ho hw' hnW hR hsr hi hk hik
    have hle := hmax w' v' hw' hvis'
    have hne' : gwix G w' ≠ gwix G w0 := fun h =>
      hne (gwixInj G w' w0 hwf.1 (gwritesByteGwrites G w' a v' hwf hw')
        (gwritesByteGwrites G w0 a v hwf hwv) h)
    exact CertZ21.ordOfCo G b a L w' w0 i j v' v hwf h6 hd ho hw' hwv (by omega) hi hj

end Weak
