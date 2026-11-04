/-
Weak/Prom: **G4 target (1) on track (a): the spinlock's per-step lemmas** (stage S4a part 2; plan rev 7 §3
"Acquire", "Atomicity", "The deposit", "Opening", R-a1; protocol and classes: OwnALockDefs.lean).

* `src_ge_lw`, `cld_cases` — THE OWNED READ of the counter (pure, plan R-a1): every byte of a load whose floor covers
  the latest owned write `lw` (or the image, `lw = 0`) was read from `lw`, or from a message ABOVE `lw` writing that
  byte (R-a1: the next owner's future write; its `pend` is in the points-to's bag), or through an invalidate above
  `lw` (a dead message).
* `lk_src` — a lock-word byte read below the frontier came from the image, an acquire or a release message, or the
  run is in free mode (junk and dead messages are never fulfilled outside free mode).
* `lk_chain` — THE ATOMICITY STEP (plan §3 "Atomicity"): an AMO at `ts` that read byte `Lk` from `s0` has
  `nxtL M s0 ts` (no write to `Lk` in between): another hart's write contradicts `exclOk`, an own write at or below
  the coherence floor `lo` contradicts the read's coherence, an own lock message above `lo` is still in the
  own-message bag (its `pend` or token contradicts its fulfilment, which the frontier `≥ ts` shows), a junk or dead
  one is free mode.
* `lk_claim` — THE CLAIM (plan §3 "Opening"): with `nxtL M s0 ts` and the token of `ts`, the acquirer takes `Rs s0`
  out of the slot of `s0` (the image's, or release `s0`'s, which the frontier shows fulfilled).
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.OwnALockDefs

namespace Weak.Prom.OA

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.PF Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Ref (Instr Test two64)
open Weak.Prom.Ref.Lit (X Y)
open PLabel
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode

/-! ## 1. The owned read of the counter (pure) -/

/-- An entry of a byte run. -/
theorem bytesAll_get {P : Int → Nat → BitVec 8 → Prop} : ∀ {a : Int} {tvs : List (Nat × BitVec 8)} {j t : Nat}
    {v : BitVec 8}, bytesAll P a tvs → tvs[j]? = some (t, v) → P (a + j) t v
  | _, [], _, _, _, _, h => by cases h
  | a, (t0, v0) :: r, j, t, v, ⟨h0, hr⟩, h => by
    cases j with
    | zero => simp at h; obtain ⟨rfl, rfl⟩ := h; simpa using h0
    | succ j =>
      have := bytesAll_get hr (by simpa using h)
      rw [show a + 1 + (j : Int) = a + ((j + 1 : Nat) : Int) by omega] at this
      exact this

/-- ONE BYTE: an answer whose floor covers `lw` (a non-cmo message writing `a`, or the image) is `lw`, a message
above `lw` writing `a`, or read through an invalidate above `lw`. -/
theorem src_ge_lw {img : Image} {M : List PMsg} {a : Int} {t lw fl : Nat} {v : BitVec 8}
    (hlwm : lw = 0 ∨ ∃ m, msgAt M lw = some m ∧ (m.byteAt a).isSome = true ∧ notCmo m.cls = true)
    (hfl : lw ≤ fl) (hb : memByte img M t a = some v) (hr : ¬ writesIn M a t fl ∨ invalRead M a t fl) :
    t = lw ∨ (lw < t ∧ wrB M a t) ∨ (∃ ti, lw < ti ∧ cmoAt M isInvalK ti a) := by
  have hwlw : ∀ lo, lo < lw → writesIn M a lo fl := by
    intro lo hlo
    rcases hlwm with h0 | ⟨m, hm, hba, _⟩
    · omega
    · obtain ⟨k, rfl⟩ : ∃ k, lw = k + 1 := ⟨lw - 1, by omega⟩
      exact ⟨k + 1, hlo, hfl, m, by simpa [msgAt] using hm, hba⟩
  rcases hr with hr | ⟨ti, ⟨mi, ki, leni, hmi, hcls, hp, h1, h2⟩, hlt, hnw, _, _⟩
  · by_cases h : t < lw
    · exact absurd (hwlw t h) hr
    · by_cases he : t = lw
      · exact .inl he
      · obtain ⟨k, rfl⟩ : ∃ k, t = k + 1 := ⟨t - 1, by omega⟩
        obtain ⟨m, hm, hba⟩ := Option.bind_eq_some_iff.1 (by simpa [memByte] using hb)
        exact .inr (.inl ⟨by omega, m, by simpa [msgAt] using hm, by rw [hba]; rfl⟩)
  · by_cases h : ti < lw
    · exact absurd (hwlw ti h) hnw
    · by_cases he : ti = lw
      · subst he
        rcases hlwm with h0 | ⟨m, hm, _, hnc⟩
        · omega
        · obtain ⟨k, hk⟩ : ∃ k, ti = k + 1 := ⟨ti - 1, by omega⟩
          rw [hk] at hmi hm
          simp only [msgAt, Nat.add_sub_cancel] at hmi hm
          rw [hmi] at hm; cases hm
          rw [hcls] at hnc; cases hnc
      · exact .inr (.inr ⟨ti, by omega, mi, ki, leni, hmi, hcls, hp, h1, h2⟩)

/-- **THE OWNED READ OF THE COUNTER** (plan R-a1): see the header. -/
theorem cld_cases {img : Image} {M : List PMsg} {vpre lw : Nat}
    (hlwm : lw = 0 ∨ isC M lw = true) (hv : lw ≤ vpre) :
    ∀ (k : Nat) (tvs : List (Nat × BitVec 8)), k + tvs.length ≤ 8 →
      bytesAll (fun a t v => memByte img M t a = some v ∧
        ((∃ fl, vpre ≤ fl ∧ ¬ writesIn M a t fl) ∨ (∃ fl, vpre ≤ fl ∧ invalRead M a t fl))) (Ct + k) tvs →
      (∀ p ∈ tvs, p.1 = lw) ∨
      (∃ (j t : Nat) (v : BitVec 8), tvs[j]? = some (t, v) ∧ lw < t ∧ wrB M (Ct + k + j) t) ∨
      (∃ ti, lw < ti ∧ ∃ j : Nat, j < 8 ∧ cmoAt M isInvalK ti (Ct + j)) := by
  intro k tvs
  induction tvs generalizing k with
  | nil => intro _ _; exact .inl (by simp)
  | cons tv r ih =>
    obtain ⟨t, v⟩ := tv
    intro hlen ⟨⟨hb, hr⟩, hrest⟩
    have hk : k < 8 := by simp at hlen; omega
    have hlwm' : lw = 0 ∨ ∃ m, msgAt M lw = some m ∧ (m.byteAt (Ct + k)).isSome = true ∧ notCmo m.cls = true := by
      rcases hlwm with h0 | hc
      · exact .inl h0
      · obtain ⟨m, hm, h1, h2, h3, _⟩ := clsB_iff.1 hc
        refine .inr ⟨m, hm, ?_, by rw [h3]; rfl⟩
        rw [← h1, byteAt_off rfl, List.getElem?_eq_getElem (by omega)]; rfl
    have hsrc : t = lw ∨ (lw < t ∧ wrB M (Ct + k) t) ∨ (∃ ti, lw < ti ∧ cmoAt M isInvalK ti (Ct + k)) := by
      rcases hr with ⟨fl, hfl, h⟩ | ⟨fl, hfl, h⟩
      · exact src_ge_lw hlwm' (by omega) hb (.inl h)
      · exact src_ge_lw hlwm' (by omega) hb (.inr h)
    rcases hsrc with heq | ⟨hlt, hw⟩ | ⟨ti, hti, hc⟩
    · have ih' := ih (k + 1) (by simp at hlen; omega)
        (by rw [(by omega : Ct + ((k + 1 : Nat) : Int) = Ct + k + 1)]; exact hrest)
      rcases ih' with h | ⟨j, t', v', hj, hlt', hw'⟩ | hci
      · refine .inl (fun p hp => ?_)
        rcases List.mem_cons.1 hp with rfl | hp
        · exact heq
        · exact h p hp
      · refine .inr (.inl ⟨j + 1, t', v', by simpa using hj, hlt', ?_⟩)
        rw [show Ct + k + ((j + 1 : Nat) : Int) = Ct + ((k + 1 : Nat) : Int) + j by omega]; exact hw'
      · exact .inr (.inr hci)
    · exact .inr (.inl ⟨0, t, v, rfl, hlt, by simpa using hw⟩)
    · exact .inr (.inr ⟨ti, hti, k, hk, hc⟩)

/-- A cmo message is dead. -/
theorem cmo_dead {M : List PMsg} {ti : Nat} {a : Int} (h1 : 1 ≤ ti) (h : cmoAt M isInvalK ti a) :
    isJ M ti = true ∧ isDd M ti = true ∧ ti ≤ M.length := by
  obtain ⟨m, k, len, hm, hc, _⟩ := h
  have hmt : msgAt M ti = some m := by
    obtain ⟨k', rfl⟩ : ∃ k', ti = k' + 1 := ⟨ti - 1, by omega⟩
    simpa [msgAt] using hm
  have hL : isL M ti = false := by
    rw [isL, clsB_of hmt]; simp only [decide_eq_false_iff_not]; intro h; rw [h.2.2.1] at hc; cases hc
  have hC : isC M ti = false := by
    rw [isC, clsB_of hmt]; simp only [decide_eq_false_iff_not]; intro h; rw [h.2.2.1] at hc; cases hc
  refine ⟨by simp [isJ, isDd, hL, hC], by simp [isDd, hL, hC], (msgAt_le hmt).2⟩

/-! ## 2. The lock step lemmas -/

section steps

variable {GF : BundledGFunctors} [GhostVarG GF HSt] [GhostVarG GF Bool] [TokenG GF] [InvGS GF]

/-- The frontier rule at one timestamp. -/
theorem frontA_get {g : AGN} {π : Proto} {img : Image} {M : List PMsg} {ws : PState} (t : Nat) :
    frontA (GF := GF) g π img M ws ⊢ ⌜1 ≤ t ∧ t ≤ M.length ∧ t ≤ wfr ws⌝ -∗ fulT g t := by
  unfold frontA
  iintro ⟨#H, _⟩ %h
  iapply H
  ipureintro; exact h

/-- Free mode from the context. -/
theorem lk_free_of (g : AGN) (M : List PMsg) (tk : Nat → GName) :
    lkCtx (GF := GF) g M tk ∗ dfree g ⊢ |={⊤}=> dfree g ∗ dshot g := by
  iintro ⟨#Hctx, #Hf⟩
  unfold lkCtx
  icases Hctx with ⟨Hdoom, -⟩
  imod dfree_dshot (E := ⊤) CoPset.subseteq_top g M $$ [] with #Hd
  · iframe Hdoom Hf
  imodintro
  iframe Hf Hd

/-- **A LOCK-WORD BYTE READ BELOW THE FRONTIER** came from the image, an acquire or a release message, or free mode. -/
theorem lk_src (g : AGN) (M : List PMsg) (tk : Nat → GName) {π : Proto} {img : Image} {ws1 : PState} {t j : Nat}
    {v : BitVec 8} (hj : j < 4) (hb : memByte img M t (Lk + j) = some v) (ht : t ≤ wfr ws1) :
    lkCtx (GF := GF) g M tk ∗ frontA g π img M ws1 ⊢
      |={⊤}=> (dfree g ∗ dshot g) ∨ ⌜t = 0 ∨ isA M t = true ∨ isR M t = true⌝ := by
  iintro ⟨#Hctx, #Hfr⟩
  cases t with
  | zero => imodintro; iright; ipureintro; exact .inl rfl
  | succ k =>
    obtain ⟨m, hm, hba⟩ := Option.bind_eq_some_iff.1 (by simpa [memByte] using hb)
    have hmt : msgAt M (k + 1) = some m := by simpa [msgAt] using hm
    have hw : wrB M (Lk + j) (k + 1) := ⟨m, hmt, by rw [hba]; rfl⟩
    rcases wrL_cls hj hw with hA | hR | hJ
    · imodintro; iright; ipureintro; exact .inr (.inl hA)
    · imodintro; iright; ipureintro; exact .inr (.inr hR)
    · unfold lkCtx
      icases Hctx with ⟨Hdoom, -, -, Hdd⟩
      ihave #Hd := bsl_mem (F := fun t => deadInv g t) (List.mem_filter.2 ⟨mem_rng.2 (msgAt_le hmt), hJ⟩) $$ Hdd
      ihave #Hft := frontA_get (k + 1) $$ Hfr %⟨(msgAt_le hmt).1, (msgAt_le hmt).2, ht⟩
      imod dead_shot g M (k + 1) $$ [] with ⟨#Hf, #Hs⟩
      · iframe Hdoom Hd Hft
      imodintro; ileft; iframe Hf Hs

/-- **THE ATOMICITY STEP** (plan §3 "Atomicity"; see the header). -/
theorem lk_chain (g : AGN) (M : List PMsg) (tk : Nat → GName) {π : Proto} {img : Image} {ws1 ws : PState}
    {h lo s0 ts vpre : Nat} (hs0 : s0 < ts) (hts : ts ≤ wfr ws1) (hwts : wrB M Lk ts) (hlo : lo ≤ coh ws Lk)
    (hr : ¬ writesIn M Lk s0 (max vpre (coh ws Lk)))
    (hx : ¬ writesInBy M (fun tid => tid ≠ some h) Lk s0 (ts - 1)) :
    lkCtx (GF := GF) g M tk ∗ frontA g π img M ws1 ∗ obag g M tk h lo ts ⊢
      |={⊤}=> (obag g M tk h lo ts ∗ ⌜nxtL M s0 ts⌝) ∨ (dfree g ∗ dshot g) := by
  iintro ⟨#Hctx, #Hfr, Hbag⟩
  by_cases hn : nxtL M s0 ts
  · imodintro; ileft; iframe Hbag; ipureintro; exact hn
  have hex : ∃ v, s0 < v ∧ v < ts ∧ wrB M Lk v := by
    apply Classical.byContradiction; intro hne
    exact hn ⟨hs0, hwts, fun v h1 h2 h3 => hne ⟨v, h1, h2, h3⟩⟩
  obtain ⟨v, hv1, hv2, hwv⟩ := hex
  have hvM : 1 ≤ v ∧ v ≤ M.length := by obtain ⟨m, hm, _⟩ := hwv; exact msgAt_le hm
  have htid : tidAt M v = some h := by
    apply Classical.byContradiction; intro hne
    exact chain_excl hv1 hv2 hwv hne hx
  have hvl : lo < v := by
    apply Classical.byContradiction; intro hle
    exact chain_coh hv1 (by omega) hwv hr
  have hbyH : byH M h v = true := by simp [byH, htid]
  ihave #Hft := frontA_get v $$ Hfr %⟨hvM.1, hvM.2, by omega⟩
  have hwv0 : wrB M (Lk + (0 : Nat)) v := by simpa using hwv
  rcases wrL_cls (by omega) hwv0 with hA | hR | hJ
  · -- an own acquire message above `lo`: its `pend` is in the bag
    unfold obag
    icases Hbag with ⟨HbA, -⟩
    unfold bagA
    icases bsl_filter_take (pend g) (fun t => decide (lo < t) && decide (t ≠ ts) && isA M t && byH M h t)
      (fun _ => false) v (by simp [hvl, show v ≠ ts by omega, hA, hbyH])
      (fun _ h => by cases h) (rng M) (mem_rng.2 hvM) (nodup_rng M) $$ HbA with ⟨Hp, -⟩
    unfold fulT
    icases Hft with (#Hsh | ⟨#Hf, _⟩)
    · iexfalso; iapply pend_shot; iframe Hp Hsh
    · imod lk_free_of g M tk $$ [] with ⟨#Hf', #Hd⟩
      · iframe Hctx Hf
      imodintro; iright; iframe Hf' Hd
  · -- an own release message above `lo`: its token is in the bag, and its slot holds the author's token once shot
    unfold obag
    icases Hbag with ⟨-, HbL⟩
    unfold bagL
    icases bsl_filter_take (fun t => token (tk t))
      (fun t => decide (lo < t) && decide (t ≠ ts) && (isA M t || isR M t) && byH M h t) (fun _ => false) v
      (by simp [hvl, show v ≠ ts by omega, hR, hbyH])
      (fun _ h => by cases h) (rng M) (mem_rng.2 hvM) (nodup_rng M) $$ HbL with ⟨Ht, -⟩
    unfold fulT
    icases Hft with (#Hsh | ⟨#Hf, _⟩)
    · unfold lkCtx
      icases Hctx with ⟨-, -, Hrs, -⟩
      ihave #Hslot := bsl_mem (F := fun r => rSlot g M tk r) (List.mem_filter.2 ⟨mem_rng.2 hvM, hR⟩) $$ Hrs
      unfold rSlot
      imod inv_acc_timeless (E := ⊤) CoPset.subseteq_top $$ Hslot with ⟨Hb, -⟩
      icases Hb with (Hp | ⟨_, Ht', _⟩)
      · iexfalso; iapply pend_shot; iframe Hp Hsh
      · iexfalso; iapply token_exclusive; iframe Ht Ht'
    · imod lk_free_of g M tk $$ [] with ⟨#Hf', #Hd⟩
      · iframe Hctx Hf
      imodintro; iright; iframe Hf' Hd
  · -- junk or dead: free mode
    unfold lkCtx
    icases Hctx with ⟨Hdoom, -, -, Hdd⟩
    ihave #Hd := bsl_mem (F := fun t => deadInv g t) (List.mem_filter.2 ⟨mem_rng.2 hvM, hJ⟩) $$ Hdd
    imod dead_shot g M v $$ [] with ⟨#Hf, #Hs⟩
    · iframe Hdoom Hd Hft
    imodintro; iright; iframe Hf Hs

/-- **THE CLAIM** (plan §3 "Opening"): the acquirer at `ts` (holding the token of `ts`), whose read source `s0` is the
image or a release with `nxtL M s0 ts`, takes `Rs s0` (or the run is in free mode). -/
theorem lk_claim (g : AGN) (M : List PMsg) (tk : Nat → GName) {π : Proto} {img : Image} {ws1 : PState}
    {s0 ts : Nat} (hn : nxtL M s0 ts) (hs0 : s0 = 0 ∨ isR M s0 = true) (hts : ts ≤ wfr ws1) :
    lkCtx (GF := GF) g M tk ∗ frontA g π img M ws1 ∗ token (tk ts) ⊢
      |={⊤}=> (dfree g ∗ dshot g) ∨ Rs g M s0 := by
  iintro ⟨#Hctx, #Hfr, Ht⟩
  rcases hs0 with rfl | hR
  · unfold lkCtx
    icases Hctx with ⟨-, Hi, -⟩
    unfold iSlot
    imod inv_acc_timeless (E := ⊤) CoPset.subseteq_top $$ Hi with ⟨Hb, Hclose⟩
    icases Hb with (HR | Hn)
    · imod Hclose $$ [Ht] with -
      · iright; unfold nxtTok; iexists ts; iframe Ht; ipureintro; exact hn
      imodintro; iright; iexact HR
    · unfold nxtTok
      icases Hn with ⟨%u, %hu, Ht'⟩
      rw [nxtL_unique hu hn] at *
      iexfalso; iapply token_exclusive; iframe Ht Ht'
  · have hsM : 1 ≤ s0 ∧ s0 ≤ M.length := by
      obtain ⟨m, hm, _⟩ := clsB_iff.1 hR; exact msgAt_le hm
    ihave #Hft := frontA_get s0 $$ Hfr %⟨hsM.1, hsM.2, by have := hn.1; omega⟩
    unfold fulT
    icases Hft with (#Hsh | ⟨#Hf, _⟩)
    · unfold lkCtx
      icases Hctx with ⟨-, -, Hrs, -⟩
      ihave #Hslot := bsl_mem (F := fun r => rSlot g M tk r) (List.mem_filter.2 ⟨mem_rng.2 hsM, hR⟩) $$ Hrs
      unfold rSlot
      imod inv_acc_timeless (E := ⊤) CoPset.subseteq_top $$ Hslot with ⟨Hb, Hclose⟩
      icases Hb with (Hp | ⟨_, Ha, (HR | Hn)⟩)
      · iexfalso; iapply pend_shot; iframe Hp Hsh
      · imod Hclose $$ [Ht Ha] with -
        · iright; iframe Hsh Ha; iright; unfold nxtTok; iexists ts; iframe Ht; ipureintro; exact hn
        imodintro; iright; iexact HR
      · unfold nxtTok
        icases Hn with ⟨%u, %hu, Ht'⟩
        rw [nxtL_unique hu hn] at *
        iexfalso; iapply token_exclusive; iframe Ht Ht'
    · imod lk_free_of g M tk $$ [] with ⟨#Hf', #Hd⟩
      · iframe Hctx Hf
      imodintro; ileft; iframe Hf' Hd

end steps

end Weak.Prom.OA
