/-
Weak: **pure graph-level (no Iris) LOCK SERIALIZATION** (AxSL tier, lock slice).

Rocq: `iris/AxLockSerial.v` @ xxvzwolszwmp.

The Rocq header, in substance (design: `claude-notes/design/weak-memory-lb-axsl.md`).
Builds on `AxLockGraph` and PORTS `WeakRvwmoLock`'s §1–3 lock-protocol order
theory (proved over `rvwmoMinusConsistent`) to the current
`rvwmoCatConsistent` / `gppoCat` model.  The port is sound because none of that
machinery uses ppo rule 7 (bare release-before-acquire, the arm the cat model
drops): every ppo fact it needs is rule 1 or pure load-value / atomicity, and
`acqTsLt`'s one ppo step is replaced by `catRmwTsLt`.

  §1  `csAcqSrc` / `csAcqSrcRel` — the window facts, re-hypothesised over
      `gatomicity` / `gloadValue` directly;
  §2  `csAcqNoOverlap` / `csWinExcl` — the exclusion induction and its export;
  §3  `csSerialized` — two critical sections on one lock byte `L` are
      gco-serialized, and the winning side's body writes are `gobCat`-before
      every po-later memory event of the loser's acquire;
  §4  `csOwnedWrite` — `lockHandoffGraph` with its discipline weakened to range
      only over writes VISIBLE to the read;
  §5  `csHandoffLast` — if B's acquire reads from A's release and every OTHER
      write to `x` sits inside a third hart's critical section, B's read of `x`
      sees A's write.

Hypotheses (discharged later by ownership): `lockPattern`, `lockPaired`, a
critical section is `lockCs` plus the acquire being `.aq` and every body write
covered to the release by `gppoCat`; `csHandoffLast`'s discipline is scoped to
third harts (see the Rocq header).

**Deviations from Rocq.**

1. NAMES: lowerCamelCase.  No name of this file is in
   `notes/weak-port-dupnames.json`; dependency duplicates are referred to
   qualified (`WeakRvwmoGraph.gpo`, `WeakRvwmoGraph.gwixPos`,
   `WeakRvwmoGraph.glblIsRGmem`, `WeakRvwmoGraph.glblIsWGmem`,
   `WeakRvwmoAcyc.grf`).
2. VOCABULARY: as `AxGraphCat` deviation 2 (`Z` ↦ `Int`, `bv 8` ↦ `BitVec 8`,
   `gd_g` ↦ `.gdG`, `lb_is_r`/`lb_aq` ↦ `lbIsR`/`lbAq`, `acq.1` ↦ `acq.1`).
3. `csAcqSrcRel` takes `gwf` (as Rocq) but only uses its `Nodup` component.
4. `csSerialized`'s two mirrored Rocq branches are factored through one private
   helper `csSerializedSide` (proof structure only; the statement is unchanged).

**Name map** (Rocq → Lean): `cs_acq_src` ↦ `csAcqSrc`; `cs_acq_src_rel` ↦
`csAcqSrcRel`; `cs_acq_no_overlap` ↦ `csAcqNoOverlap`; `cs_win_excl` ↦
`csWinExcl`; `cs_serialized` ↦ `csSerialized`; `cs_owned_write` ↦
`csOwnedWrite`; `cs_handoff_last` ↦ `csHandoffLast`.

**Not ported:** nothing.
-/
import Weak.AxLockGraph

namespace Weak

open MachCSL MachCSL.Stdpp
open Lbl

/-! # 1. The window facts, re-hypothesised over the cat model's pieces -/

/-- ATOMICITY alone bounds an acquire's co-window. -/
theorem csAcqSrc (GD : Gdexec) (L : Int) (A : Geid) (t : Nat) :
    gatomicity GD.gdG → lockAcq GD.gdG L A →
    greadsByte GD.gdG A L t lockFree →
    ∀ w' v', gwritesByte GD.gdG w' L v' →
      gwix GD.gdG w' ≤ t ∨ gwix GD.gdG A ≤ gwix GD.gdG w' := by
  rintro hat ⟨v, hwb, _⟩ hrd w' v' hw'
  have hna := hat A L t lockFree hrd (gwritesByteGlblW _ _ _ _ hwb) w' v' hw'
  omega

/-- LOAD-VALUE alone names the acquire's read source. -/
theorem csAcqSrcRel (GD : Gdexec) (L : Int) (A : Geid) (t : Nat) :
    gwf GD.gdG → gloadValue GD.gdG →
    greadsByte GD.gdG A L t lockFree → 0 < t →
    ∃ r, lockRel GD.gdG L r ∧ r ∈ gwrites GD.gdG ∧ gwix GD.gdG r = t := by
  intro hwf hlv hrd hpos
  cases t with
  | zero => omega
  | succ t =>
    obtain ⟨⟨r, hat, hrb, _⟩, _⟩ := hlv A L (t + 1) lockFree hrd
    obtain ⟨hr, hrix⟩ := gwriteAtInv GD.gdG (t + 1) r hwf.1 hat
    exact ⟨r, hrb, hr, hrix⟩

/-! # 2. The exclusion induction, ported -/

theorem csAcqNoOverlap (GD : Gdexec) (L : Int) :
    rvwmoCatConsistent GD → lockPattern GD.gdG L → lockPaired GD.gdG L →
    ∀ n A2, gwix GD.gdG A2 ≤ n → lockAcq GD.gdG L A2 →
    ∀ A1 R1, lockCs GD.gdG L A1 R1 →
      gwix GD.gdG A1 < gwix GD.gdG A2 → gwix GD.gdG A2 < gwix GD.gdG R1 → False := by
  intro hcons hpat hpair
  obtain ⟨hwf, _, hlv, hat, _, _⟩ := id hcons
  intro n
  induction n with
  | zero =>
    intro A2 hle hA2 _ _ _ _ _
    have := WeakRvwmoGraph.gwixPos GD.gdG A2 (lockAcqGwrites GD.gdG L A2 hwf hA2)
    omega
  | succ n ih =>
    intro A2 hle hA2 A1 R1 hcs1 hlt1 hlt2
    obtain ⟨hA1, _, _, _, _⟩ := id hcs1
    obtain ⟨_, t, hrd2⟩ := lockAcqRead GD.gdG L A2 hpat hA2
    obtain ⟨va2, hwb2, _⟩ := id hA2
    have htlt := catRmwTsLt GD A2 L t lockFree va2 hcons hrd2 hwb2
    obtain ⟨v1, hwb1, _⟩ := id hA1
    have hle1 : gwix GD.gdG A1 ≤ t := by
      rcases csAcqSrc GD L A2 t hat hA2 hrd2 A1 v1 hwb1 with h | h
      · exact h
      · omega
    have hpos1 := WeakRvwmoGraph.gwixPos GD.gdG A1 (lockAcqGwrites GD.gdG L A1 hwf hA1)
    obtain ⟨r, hr, hrw, hrix⟩ := csAcqSrcRel GD L A2 t hwf hlv hrd2 (by omega)
    have hner1 : A1 ≠ r := by
      rintro rfl
      exact lockAcqNotRel GD.gdG L A1 hA1 hr
    have hlt1r : gwix GD.gdG A1 < gwix GD.gdG r := by
      by_cases heq : gwix GD.gdG A1 = gwix GD.gdG r
      · exact absurd (gwixInj GD.gdG A1 r hwf.1 (lockAcqGwrites GD.gdG L A1 hwf hA1) hrw heq)
          hner1
      · omega
    obtain ⟨Ak, hcsk⟩ := hpair r hr
    by_cases hek : Ak = A1
    · subst hek
      have := lockCsFunctional GD.gdG L Ak r R1 hwf hcsk hcs1
      subst this
      omega
    · obtain ⟨hAk, _, _, hltk, _⟩ := id hcsk
      have hixk : gwix GD.gdG Ak ≠ gwix GD.gdG A1 := fun heq =>
        hek (gwixInj GD.gdG Ak A1 hwf.1 (lockAcqGwrites GD.gdG L Ak hwf hAk)
          (lockAcqGwrites GD.gdG L A1 hwf hA1) heq)
      by_cases hkl : gwix GD.gdG Ak < gwix GD.gdG A1
      · exact ih A1 (by omega) hA1 Ak r hcsk hkl (by omega)
      · exact ih Ak (by omega) hAk A1 R1 hcs1 (by omega) (by omega)

/-- Two distinct critical sections on `L` are gwix-disjoint and totally ordered. -/
theorem csWinExcl (GD : Gdexec) (L : Int) :
    rvwmoCatConsistent GD → lockPattern GD.gdG L → lockPaired GD.gdG L →
    ∀ A1 R1 A2 R2, lockCs GD.gdG L A1 R1 → lockCs GD.gdG L A2 R2 → A1 ≠ A2 →
      gwix GD.gdG R1 < gwix GD.gdG A2 ∨ gwix GD.gdG R2 < gwix GD.gdG A1 := by
  intro hcons hpat hpair A1 R1 A2 R2 hcs1 hcs2 hne
  have hwf := hcons.1
  have hnd := hwf.1
  obtain ⟨hA1, hR1, _, hlt1, _⟩ := id hcs1
  obtain ⟨hA2, hR2, _, hlt2, _⟩ := id hcs2
  have hix : gwix GD.gdG A1 ≠ gwix GD.gdG A2 := fun heq =>
    hne (gwixInj GD.gdG A1 A2 hnd (lockAcqGwrites GD.gdG L A1 hwf hA1)
      (lockAcqGwrites GD.gdG L A2 hwf hA2) heq)
  have hb1 : gwix GD.gdG R1 ≠ gwix GD.gdG A2 := fun heq => by
    have := gwixInj GD.gdG R1 A2 hnd (lockRelGwrites GD.gdG L R1 hwf hR1)
      (lockAcqGwrites GD.gdG L A2 hwf hA2) heq
    subst this
    exact lockAcqNotRel GD.gdG L R1 hA2 hR1
  have hb2 : gwix GD.gdG R2 ≠ gwix GD.gdG A1 := fun heq => by
    have := gwixInj GD.gdG R2 A1 hnd (lockRelGwrites GD.gdG L R2 hwf hR2)
      (lockAcqGwrites GD.gdG L A1 hwf hA1) heq
    subst this
    exact lockAcqNotRel GD.gdG L R2 hA1 hR2
  by_cases hlt : gwix GD.gdG A1 < gwix GD.gdG A2
  · left
    by_cases hin : gwix GD.gdG A2 < gwix GD.gdG R1
    · exact (csAcqNoOverlap GD L hcons hpat hpair (gwix GD.gdG A2) A2 (Nat.le_refl _) hA2
        A1 R1 hcs1 hlt hin).elim
    · omega
  · right
    have hlt' : gwix GD.gdG A2 < gwix GD.gdG A1 := by omega
    by_cases hin : gwix GD.gdG A1 < gwix GD.gdG R2
    · exact (csAcqNoOverlap GD L hcons hpat hpair (gwix GD.gdG A1) A1 (Nat.le_refl _) hA1
        A2 R2 hcs2 hlt' hin).elim
    · omega

/-! # 3. `csSerialized` — the commissioned theorem -/

/-- One side of `csSerialized`: if `(acq1, rel1)`'s release is gwix-below
`acq2`, the release is gco-before `acq2` and `rel1`'s covered body is
`gobCat`-before every po-later memory event of `acq2`. -/
private theorem csSerializedSide (GD : Gdexec) (L : Int) (acq1 rel1 acq2 rel2 : Geid) :
    lockPattern GD.gdG L →
    lockCs GD.gdG L acq1 rel1 → lockCs GD.gdG L acq2 rel2 →
    glblIs GD.gdG acq2 lbAq →
    gwix GD.gdG rel1 < gwix GD.gdG acq2 →
    gco GD.gdG rel1 acq2 ∧
      ∀ bw, gppoCat GD bw rel1 →
        ∀ e, WeakRvwmoGraph.gpo GD.gdG acq2 e → gmem GD.gdG e → gobCat GD bw e := by
  intro hpat hcs1 hcs2 haq2 hwin
  obtain ⟨_, hR1, _, _, _⟩ := id hcs1
  obtain ⟨hA2, _, _, _, _⟩ := id hcs2
  obtain ⟨va2, hwb2, _⟩ := id hA2
  have hco : gco GD.gdG rel1 acq2 := ⟨L, lockFree, va2, hR1, hwb2, hwin⟩
  refine ⟨hco, ?_⟩
  intro bw hbw e hpoe hmeme
  obtain ⟨hacq2r, _⟩ := lockAcqRead GD.gdG L acq2 hpat hA2
  have hgob1 : gobCat GD bw rel1 := gobCatStep GD _ _ (Or.inl hbw)
  have hgob2 : gobCat GD rel1 acq2 := gobCatStep GD _ _ (Or.inr (Or.inr (Or.inr (Or.inl hco))))
  have hgacq : gacqPo GD.gdG acq2 e := ⟨hpoe, hacq2r, haq2, hmeme⟩
  have hgob4 : gobCat GD acq2 e :=
    gobCatStep GD _ _ (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hgacq)))))))
  exact gobCatTrans GD _ _ _ (gobCatTrans GD _ _ _ hgob1 hgob2) hgob4

/-- Two critical sections on lock byte `L` with distinct acquires do not
overlap, and the earlier one's body is `gobCat`-before every memory event
po-after the later one's acquire. -/
theorem csSerialized (GD : Gdexec) (L : Int) (acq1 rel1 acq2 rel2 : Geid) :
    rvwmoCatConsistent GD →
    lockPattern GD.gdG L → lockPaired GD.gdG L →
    lockCs GD.gdG L acq1 rel1 → lockCs GD.gdG L acq2 rel2 →
    glblIs GD.gdG acq1 lbAq → glblIs GD.gdG acq2 lbAq →
    acq1 ≠ acq2 →
    (gco GD.gdG rel1 acq2 ∧
       ∀ bw, gppoCat GD bw rel1 →
         ∀ e, WeakRvwmoGraph.gpo GD.gdG acq2 e → gmem GD.gdG e → gobCat GD bw e)
    ∨
    (gco GD.gdG rel2 acq1 ∧
       ∀ bw, gppoCat GD bw rel2 →
         ∀ e, WeakRvwmoGraph.gpo GD.gdG acq1 e → gmem GD.gdG e → gobCat GD bw e) := by
  intro hcons hpat hpair hcs1 hcs2 haq1 haq2 hne
  rcases csWinExcl GD L hcons hpat hpair acq1 rel1 acq2 rel2 hcs1 hcs2 hne with hwin | hwin
  · exact Or.inl (csSerializedSide GD L acq1 rel1 acq2 rel2 hpat hcs1 hcs2 haq2 hwin)
  · exact Or.inr (csSerializedSide GD L acq2 rel2 acq1 rel1 hpat hcs2 hcs1 haq1 hwin)

/-! # 4. `csOwnedWrite` — `lockHandoffGraph` with a weaker discipline -/

/-- `lockHandoffGraph`, except the discipline is guarded by `gvisible _ w r_x`. -/
theorem csOwnedWrite (GD : Gdexec) (x : Int)
    (w_x r_x w_rel acq : Geid) (vx v : BitVec 8) (t : Nat) :
    rvwmoCatConsistent GD →
    gwritesByte GD.gdG w_x x vx →
    gppoCat GD w_x w_rel →
    grfe GD.gdG w_rel acq →
    glblIs GD.gdG acq lbIsR →
    glblIs GD.gdG acq lbAq →
    WeakRvwmoGraph.gpo GD.gdG acq r_x →
    greadsByte GD.gdG r_x x t v →
    (∀ w vw, gwritesByte GD.gdG w x vw → gvisible GD.gdG w r_x →
       w = w_x ∨ gmoLt GD.gdG w w_x) →
    WeakRvwmoAcyc.grf GD.gdG w_x r_x ∧ v = vx := by
  intro hcons hwx hrel hrf hacqR hacqAq hacqPo hrd hdisc
  obtain ⟨hwf, _, hlv, _, _, _⟩ := id hcons
  have hgob1 : gobCat GD w_x w_rel := gobCatStep GD _ _ (Or.inl hrel)
  have hgob2 : gobCat GD w_rel acq := gobCatStep GD _ _ (Or.inr (Or.inr (Or.inl hrf)))
  have hgmem : gmem GD.gdG r_x :=
    WeakRvwmoGraph.glblIsRGmem _ _ (greadsByteGlblR _ _ _ _ _ hrd)
  have hgacq : gacqPo GD.gdG acq r_x := ⟨hacqPo, hacqR, hacqAq, hgmem⟩
  have hgob4 : gobCat GD acq r_x :=
    gobCatStep GD _ _ (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hgacq)))))))
  have hgob5 := gobCatTrans GD _ _ _ (gobCatTrans GD _ _ _ hgob1 hgob2) hgob4
  have hvis : gvisible GD.gdG w_x r_x := catGobGvisible GD _ _ hcons hgob5
  have hwxW := gwritesByteGwrites GD.gdG w_x x vx hwf hwx
  cases t with
  | zero =>
    exfalso
    have hc := (hlv r_x x 0 v hrd).2 w_x vx hwx hvis
    have := WeakRvwmoGraph.gwixPos GD.gdG w_x hwxW
    omega
  | succ i =>
    obtain ⟨w, hat0, hwb, hvisw⟩ := (hlv r_x x (i + 1) v hrd).1
    have hcomax := (hlv r_x x (i + 1) v hrd).2 w_x vx hwx hvis
    obtain ⟨hwW, hwix⟩ := gwriteAtInv GD.gdG (i + 1) w hwf.1 hat0
    rcases hdisc w v hwb hvisw with rfl | hmo
    · exact ⟨⟨x, i + 1, v, hrd, hat0⟩, gwritesByteDet _ _ _ _ _ hwb hwx⟩
    · exfalso
      have := gmoGwixLt GD.gdG w w_x hwf hwW hwxW hmo
      omega

/-! # 5. `csHandoffLast` — the commissioned corollary -/

/-- Hart A's critical section `(acqA, relA)` writes `x` once (`w_x`, covered to
`relA`, po-after `acqA`); hart B's acquire reads `relA`'s byte on `L` at index
`t_B`; B's read `r_x` of `x` follows its acquire and is covered to `relB`.
Under the scoped discipline (every write to `x` is `w_x` or inside a third
hart's critical section), `r_x` reads from `w_x`. -/
theorem csHandoffLast (GD : Gdexec) (L x : Int)
    (acqA relA acqB relB w_x r_x : Geid) (vx v v0 : BitVec 8) (t_B t : Nat) :
    rvwmoCatConsistent GD →
    lockPattern GD.gdG L → lockPaired GD.gdG L →
    lockCs GD.gdG L acqA relA → glblIs GD.gdG acqA lbAq →
    gwritesByte GD.gdG w_x x vx →
    WeakRvwmoGraph.gpo GD.gdG acqA w_x → gppoCat GD w_x relA →
    lockCs GD.gdG L acqB relB → glblIs GD.gdG acqB lbAq →
    acqA.1 ≠ acqB.1 →
    greadsByte GD.gdG acqB L t_B v0 → gwriteAt GD.gdG t_B = some relA →
    WeakRvwmoGraph.gpo GD.gdG acqB r_x → greadsByte GD.gdG r_x x t v →
    gppoCat GD r_x relB →
    (∀ w vw, gwritesByte GD.gdG w x vw → w = w_x ∨
       (∃ acqk relk, lockCs GD.gdG L acqk relk ∧ glblIs GD.gdG acqk lbAq ∧
          acqk.1 ≠ acqA.1 ∧ acqk.1 ≠ acqB.1 ∧
          WeakRvwmoGraph.gpo GD.gdG acqk w ∧ gppoCat GD w relk)) →
    WeakRvwmoAcyc.grf GD.gdG w_x r_x ∧ v = vx := by
  intro hcons hpat hpair hcsA haqA hwx hwxPo hcovWx hcsB haqB hharts hrdAcqB hsrcAcqB
    hacqPo hrd hcovRx hdiscX
  obtain ⟨hwf, _, _, hat, _, _⟩ := id hcons
  obtain ⟨hAcqB, _, _, _, _⟩ := id hcsB
  obtain ⟨vaB, hwbB, _⟩ := id hAcqB
  have htltB := catRmwTsLt GD acqB L t_B v0 vaB hcons hrdAcqB hwbB
  obtain ⟨_, hrelAix⟩ := gwriteAtInv GD.gdG t_B relA hwf.1 hsrcAcqB
  have hrfe : grfe GD.gdG relA acqB := by
    refine ⟨⟨L, t_B, v0, hrdAcqB, hsrcAcqB⟩, ?_⟩
    obtain ⟨_, _, hagA, _, _⟩ := id hcsA
    rw [← hagA]
    exact hharts
  have hdisc' : ∀ w vw, gwritesByte GD.gdG w x vw →
      gvisible GD.gdG w r_x → w = w_x ∨ gmoLt GD.gdG w w_x := by
    intro w vw hw hvis
    rcases hdiscX w vw hw with h | ⟨acqk, relk, hcsk, haqk, hnekA, hnekB, hpok, hcovk⟩
    · exact Or.inl h
    right
    have hneKA : acqk ≠ acqA := fun heq => hnekA (by rw [heq])
    rcases csSerialized GD L acqk relk acqA relA hcons hpat hpair hcsk hcsA haqk haqA hneKA
      with ⟨_, hchain⟩ | ⟨hcoAinK, _⟩
    · -- `k` entirely BEFORE `A`
      have hgmemWx : gmem GD.gdG w_x :=
        WeakRvwmoGraph.glblIsWGmem _ _ (gwritesByteGlblW _ _ _ _ hwx)
      exact obCatSubGmo GD _ _ hcons (hchain w hcovk w_x hwxPo hgmemWx)
    · -- `k` entirely AFTER `A`: place it against B too
      exfalso
      have hneBK : acqB ≠ acqk := fun heq => hnekB (by rw [heq])
      rcases csSerialized GD L acqB relB acqk relk hcons hpat hpair hcsB hcsk haqB haqk hneBK
        with ⟨_, hchaink⟩ | ⟨hcoKrB, _⟩
      · -- B entirely BEFORE `k`
        have hgmemW : gmem GD.gdG w :=
          WeakRvwmoGraph.glblIsWGmem _ _ (gwritesByteGlblW _ _ _ _ hw)
        have hmoRxW := obCatSubGmo GD _ _ hcons (hchaink r_x hcovRx w hpok hgmemW)
        rcases hvis with hmoWRx | hpoWRx
        · exact gmoLtIrrefl _ _ (gmoLtTrans _ _ _ _ hmoRxW hmoWRx)
        · obtain ⟨hag, _⟩ := hpoWRx
          obtain ⟨hagk, _⟩ := hpok
          obtain ⟨hagB, _⟩ := hacqPo
          exact hnekB (by rw [hagk, hag, ← hagB])
      · -- `k` entirely BEFORE B: contradicts `acqB`'s atomicity against `relA`
        obtain ⟨_, _, _, _, _, hltAinK⟩ := hcoAinK
        obtain ⟨_, _, _, _, _, hltKrB⟩ := hcoKrB
        obtain ⟨hAcqk, _, _, hltkInternal, _⟩ := id hcsk
        obtain ⟨vaK, hwbk, _⟩ := hAcqk
        rw [hrelAix] at hltAinK
        exact hat acqB L t_B v0 hrdAcqB (gwritesByteGlblW _ _ _ _ hwbB) acqk vaK hwbk
          ⟨hltAinK, by omega⟩
  obtain ⟨hacqBr, _⟩ := lockAcqRead GD.gdG L acqB hpat hAcqB
  exact csOwnedWrite GD x w_x r_x relA acqB vx v t hcons hwx hcovWx hrfe hacqBr haqB hacqPo
    hrd hdisc'

end Weak
