/-
Weak/Prom: **G4 target (1a) on track (a): the critical section and the release** (stage S4a part 2; plan rev 7 §3
"The deposit", "Points-to", R-a1; §4 G4 (1)).

From `pc = 3` with the counter's points-to `cPts lw` (claimed at the acquire, latest write `lw ≤` the load floor):
* `ld t2,(a1)` — THE OWNED READ (`cld_cases`): every byte from `lw` (clean), or a byte from a counter message
  `u > lw` (R-a1: the next owner's future write; `u`'s `pend` is in the bag, so the hart DOOMS the branch with it
  and keeps the rest of the bag — its own store `ts_c` lies above `coh(Ct+j) ≥ u`, so `ts_c ≠ u`: the WRITE FLOOR),
  or a dead message (free mode, OwnALockFree.lean);
* `addi`, then `sd t2,(a1)` — the fulfil `ts_c` takes its `pend` out of the bag; any counter message strictly
  between `lw` and `ts_c` is still in the bag (doom), so the load read the LATEST counter message below `ts_c`
  (`qLk`); the points-to becomes `cPts ts_c`;
* `amoswap.w.rl x0,x0,(a0)` — the release `r` (release-class: rl puts `vwOld ≥ ts_c` in its pre-view, so
  `ts_c < r`) takes `pend r` out of its slot, shoots it and DEPOSITS `Rs r` (plan §3 "The deposit"); the author's
  token `tk r` goes into the slot (so a later read of `r` by its own author is absurd, `lk_chain`).
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.OwnALockFree

namespace Weak.Prom.OA

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.PF Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Ref (Instr Test two64)
open Weak.Prom.Ref.Lit (X Y)
open PLabel
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode

/-! ## 1. Pure helpers -/

theorem cohBelow_at : ∀ {ws : PState} {a : Int} {n ts j : Nat}, cohBelow ws a n ts → j < n → coh ws (a + j) < ts
  | _, _, 0, _, _, _, hj => by omega
  | ws, a, n + 1, ts, j, ⟨h0, hr⟩, hj => by
    cases j with
    | zero => simpa using h0
    | succ j =>
      have := cohBelow_at (j := j) hr (by omega)
      rw [show a + 1 + (j : Int) = a + ((j + 1 : Nat) : Int) by omega] at this
      exact this

/-- The counter's bag above `lw`, except `ex`. -/
def cBagX (M : List PMsg) (lw ex : Nat) : List Nat :=
  (rng M).filter (fun t => decide (lw < t) && decide (t ≠ ex) && isC M t)

theorem cBag_X (M : List PMsg) (lw : Nat) : cBag M lw = cBagX M lw 0 := by
  unfold cBag cBagX
  refine List.filter_congr (fun t ht => ?_)
  have := rng_ge ht
  simp [show t ≠ 0 by omega]

/-- A load at the counter is no store. -/
theorem qLk_ld {M : List PMsg} {ev : Trace} {e : PEv} (h : noC ev) (he : ∀ ts, ¬ isCSt e ts) :
    qLk M (ev ++ [e]) := by
  intro tvs ts _ h2
  obtain ⟨e2, h2, hs⟩ := h2
  rcases List.mem_append.1 h2 with h2 | h2
  · exact absurd hs ((h e2 h2).2 ts)
  · rw [List.mem_singleton] at h2; subst h2; exact absurd hs (he ts)

/-- The critical section's pair: the load read the latest counter message below the store. -/
theorem qLk_pair {M : List PMsg} {ev : Trace} {tvs : List (Nat × BitVec 8)} {a : List Dsrc} {d : List (BitVec 8)}
    {b c : List Dsrc} {ts lw : Nat} (h : noC ev) (hall : ∀ p ∈ tvs, p.1 = lw) (hl : latestC M lw ts) :
    qLk M (ev ++ [(LLoad false false Ct tvs a, none)] ++ [(LStore false false Ct d b c, some ts)]) := by
  intro tvs' ts' h1 h2
  obtain ⟨e1, h1, hl1⟩ := h1
  obtain ⟨e2, h2, hs2⟩ := h2
  have e1v : e1 = (LLoad false false Ct tvs a, none) := by
    rcases List.mem_append.1 h1 with h1 | h1
    · rcases List.mem_append.1 h1 with h1 | h1
      · exact absurd hl1 ((h e1 h1).1 tvs')
      · rw [List.mem_singleton] at h1; exact h1
    · rw [List.mem_singleton] at h1; subst h1; obtain ⟨_, h⟩ := hl1; cases h
  have e2v : e2 = (LStore false false Ct d b c, some ts) := by
    rcases List.mem_append.1 h2 with h2 | h2
    · rcases List.mem_append.1 h2 with h2 | h2
      · exact absurd hs2 ((h e2 h2).2 ts')
      · rw [List.mem_singleton] at h2; subst h2; obtain ⟨_, _, _, h⟩ := hs2; cases h
    · rw [List.mem_singleton] at h2; exact h2
  subst e1v e2v
  obtain ⟨_, h⟩ := hl1; cases h
  obtain ⟨_, _, _, h⟩ := hs2; cases h
  exact ⟨lw, hall, hl⟩

theorem isC_of_msg {M : List PMsg} {ts h : Nat} {d : List (BitVec 8)} (hh : h < 2) (hd : d.length = 8)
    (h1 : 1 ≤ ts) (hm : M[ts - 1]? = some ⟨Ct, d, some h, .plain⟩) : isC M ts = true := by
  have hmt : msgAt M ts = some ⟨Ct, d, some h, .plain⟩ := by
    obtain ⟨k, rfl⟩ : ∃ k, ts = k + 1 := ⟨ts - 1, by omega⟩
    simpa [msgAt] using hm
  rw [isC, clsB_of hmt]; simp only [decide_eq_true_eq]
  refine ⟨rfl, hd, rfl, ?_⟩
  simp only [Option.some.injEq]; omega

theorem isR_of_msg {M : List PMsg} {ts h : Nat} (hh : h < 2) (h1 : 1 ≤ ts)
    (hm : M[ts - 1]? = some ⟨Lk, toBytes 0 4, some h, .excl⟩) : isR M ts = true ∧ byH M h ts = true := by
  have hmt : msgAt M ts = some ⟨Lk, toBytes 0 4, some h, .excl⟩ := by
    obtain ⟨k, rfl⟩ : ∃ k, ts = k + 1 := ⟨ts - 1, by omega⟩
    simpa [msgAt] using hm
  refine ⟨?_, ?_⟩
  · rw [isR, clsB_of hmt]
    exact decide_eq_true ⟨⟨rfl, toBytes_length 0 4, rfl, by simp only [Option.some.injEq]; omega⟩, rfl⟩
  · simp [byH, tidAt, hmt]

theorem isA_of_msg {M : List PMsg} {ts h : Nat} (hh : h < 2) (h1 : 1 ≤ ts)
    (hm : M[ts - 1]? = some ⟨Lk, toBytes 1 4, some h, .excl⟩) : isA M ts = true ∧ byH M h ts = true := by
  have hmt : msgAt M ts = some ⟨Lk, toBytes 1 4, some h, .excl⟩ := by
    obtain ⟨k, rfl⟩ : ∃ k, ts = k + 1 := ⟨ts - 1, by omega⟩
    simpa [msgAt] using hm
  refine ⟨?_, ?_⟩
  · rw [isA, clsB_of hmt]
    exact decide_eq_true ⟨⟨rfl, toBytes_length 1 4, rfl, by simp only [Option.some.injEq]; omega⟩, rfl⟩
  · simp [byH, tidAt, hmt]

section cs

variable {GF : BundledGFunctors} [GhostVarG GF HSt] [GhostVarG GF Bool] [TokenG GF] [InvGS GF]

/-! ## 2. The release -/

/-- **THE RELEASE** (`pc = 6`, `amoswap.w.rl x0,x0,(a0)`) and the end: the deposit of `Rs r`. -/
theorem lk_rel (g : AGN) (M : List PMsg) (tk : Nat → GName) (h : Nat) (hh : h < 2) (hdd : g.dd = ddL M)
    (s : LP) (ws : PState) (pr : GSet Nat) (ev : Trace) (lo lw : Nat)
    (hs : s.prog = b1a ∧ s.q = [] ∧ s.pc = 6 ∧ s.rd 10 = X ∧ s.rd 11 = Y)
    (hlo : lo ≤ coh ws Lk) (hvw : lw ≤ ws.wVwOld) :
    lkCtx (GF := GF) g M tk ∗ obag g M tk h lo 0 ∗ cPts g M lw ∗ (⌜qLk M ev⌝ ∨ dshot g) ∗
      lhA g Proto.triv (wL M h) (qsLk M h) ws pr ev ⊢
      wpKA g Proto.triv (wL M h) (qsLk M) s (ΦL g M) := by
  obtain ⟨hprog, hq, hpc, h10, h11⟩ := hs
  have hw := litW_x xs1a imgL M h
  have hX := p1a_at hprog
  iintro ⟨#Hctx, Hbag, Hc, HQ, Hl⟩
  iapply (wpKA_amo (base := Lk) hw (litAg_x hq hX (by rw [hpc]; rfl) rfl) hq (by rw [hprog, hpc]; rfl)
    (by rw [h10]; decide) (by rw [h10]))
  iframe Hl
  inext
  iintro %tvs %r %_ %_ %hmsg %_ %_ %hcoh %hext _ _
  have hd0 : amoD .swap 4 (s.rd 0) tvs = toBytes 0 4 := by rw [amoD_swap]; rfl
  rw [hd0] at hmsg hcoh
  have hc0 : coh (loadRun ws false false (srcsView ws (srcR 10)) Lk tvs) Lk < r := by
    have := cohBelow_at (j := 0) hcoh (by decide)
    simpa using this
  have hcm := (loadRun_mono ws false false (srcsView ws (srcR 10)) Lk tvs).2.2.2.2.2.2.2.2.2.2.1 Lk
  have hr1 : 1 ≤ r := by omega
  obtain ⟨hR, hbyH⟩ := isR_of_msg hh hr1 hmsg
  have hmr : msgAt M r = some ⟨Lk, toBytes 0 4, some h, .excl⟩ := by
    obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
    simpa [msgAt] using hmsg
  have hrM : r ≤ M.length := (msgAt_le hmr).2
  have hlor : lo < r := by omega
  -- release-class: `vwOld ≥ lw` is in the pre-view
  have hlwr : lw ≤ r := by
    have h1 := (PF.stPre_ge (loadRun ws false false (srcsView ws (srcR 10)) Lk tvs) true
      (srcsView ws (srcR 10)) (srcsView ws (srcR 0))).2.2.2.2 rfl
    have h2 := (loadRun_mono ws false false (srcsView ws (srcR 10)) Lk tvs).2.2.1
    omega
  -- the author's token of `r`
  unfold obag
  icases Hbag with ⟨-, HbL⟩
  unfold bagL
  icases bsl_filter_take (fun t => token (tk t))
    (fun t => decide (lo < t) && decide (t ≠ 0) && (isA M t || isR M t) && byH M h t) (fun _ => false) r
    (by simp [hlor, show r ≠ 0 by omega, hR, hbyH]) (fun _ h => by cases h) (rng M) (mem_rng.2 ⟨hr1, hrM⟩)
    (nodup_rng M) $$ HbL with ⟨Ht, -⟩
  -- the deposit
  unfold lkCtx
  icases Hctx with ⟨-, -, Hrs, -⟩
  ihave #Hslot := bsl_mem (F := fun r => rSlot g M tk r) (List.mem_filter.2 ⟨mem_rng.2 ⟨hr1, hrM⟩, hR⟩) $$ Hrs
  unfold rSlot
  imod inv_acc_timeless (E := ⊤) CoPset.subseteq_top $$ Hslot with ⟨Hb, Hclose⟩
  icases Hb with (Hp | ⟨_, Ht', _⟩)
  rotate_left
  · iexfalso; iapply token_exclusive; iframe Ht Ht'
  imod shoot $$ Hp with #Hsh
  imod Hclose $$ [Ht Hc] with -
  · iright; iframe Hsh Ht; ileft; unfold Rs; iexists lw; iframe Hc; ipureintro; exact hlwr
  imodintro
  isplitl [HQ]
  · icases HQ with (%hQ | #Hd)
    · ileft; ipureintro
      exact ⟨⟨0, grd_intro (qLk_snoc hQ (rmw_nonC _ _ _ _ _ _ _))⟩, grd_intro trivial⟩
    · iright; iexact Hd
  isplitr
  · unfold fulT; ileft; iexact Hsh
  iintro %s' %hs' _ _
  imodintro
  iintro Hl
  obtain ⟨hP', hc', hq'⟩ := LPstep_at hs' hprog (by rw [hpc])
  have hend : s'.prog.length ≤ s'.pc := by rw [hP', hc']; decide
  iapply (wpKA_end (v := ()) (litAg_xn hq' (fun x hx => by rw [p1a_at hP', hc'] at hx; cases hx)) hq' hend
    (by show litDone s' = some (); unfold litDone; rw [if_pos ⟨hq', hend⟩]))
  iframe Hl
  imodintro
  ileft; ipureintro; exact ⟨0, grd_intro trivial⟩

/-! ## 3. `addi`, `sd`: the store moves the points-to -/

/-- `pc = 4..5`: `addi t2,t2,1; sd t2,(a1)`, then the release.  `ex` is the counter message a dooming read took out of
the bag (`0`: none, the read was clean). -/
theorem lk_cs2 (g : AGN) (M : List PMsg) (tk : Nat → GName) (h : Nat) (hh : h < 2) (hdd : g.dd = ddL M)
    (s : LP) (ws : PState) (pr : GSet Nat) (ev0 : Trace) (tvs1 : List (Nat × BitVec 8)) (lo lw ex : Nat)
    (hs : s.prog = b1a ∧ s.q = [] ∧ s.pc = 4 ∧ s.rd 10 = X ∧ s.rd 11 = Y)
    (hlo : lo ≤ coh ws Lk) (hnoC : noC ev0) (hlw : lw = 0 ∨ isC M lw = true) :
    lkCtx (GF := GF) g M tk ∗ obag g M tk h lo 0 ∗ ([∗list] t ∈ cBagX M lw ex, pend g t) ∗
      (⌜ex = 0 ∧ (∀ p ∈ tvs1, p.1 = lw) ∧ lw ≤ coh ws Ct⌝ ∨
        (dshot g ∗ ⌜lw < ex ∧ ∃ j : Nat, j < 8 ∧ ex ≤ coh ws (Ct + j)⌝)) ∗
      lhA g Proto.triv (wL M h) (qsLk M h) ws pr (ev0 ++ [(LLoad false false Ct tvs1 (srcR 11), none)]) ⊢
      wpKA g Proto.triv (wL M h) (qsLk M) s (ΦL g M) := by
  obtain ⟨hprog, hq, hpc, h10, h11⟩ := hs
  have hw := litW_x xs1a imgL M h
  have hX := p1a_at hprog
  iintro ⟨#Hctx, Hbag, Hb, Hmode, Hl⟩
  -- `addi t2,t2,1`
  iapply (wpKA_alui hw (litAg_x hq hX (by rw [hpc]; rfl) rfl) hq (by rw [hprog, hpc]; rfl) (by decide))
  iframe Hl
  inext
  iintro %s1 %hs1 _ _
  imodintro
  iintro Hl
  obtain ⟨hP1, hc1, hq1⟩ := LPstep_at hs1 hprog (by rw [hpc])
  have e11 : s1.rd 11 = Y := by rw [LPstep_rd hs1 11 (.inl (by decide)), h11]
  have e10 : s1.rd 10 = X := by rw [LPstep_rd hs1 10 (.inl (by decide)), h10]
  -- `sd t2,(a1)`
  iapply (wpKA_sw (sz := 8) (rs2 := 7) (rs1 := 11) (off := 0) (base := Ct) hw
    (litAg_x hq1 (p1a_at hP1) (by rw [hc1]; rfl) rfl) hq1 (by rw [hP1, hc1]; rfl)
    (alg_of e11 (by decide) (by decide)) (base_of e11 (by decide)))
  iframe Hl
  inext
  iintro %ts %_ %hmsg %hcoh %_ _ _
  rw [toBytes_length] at hcoh
  have hcj : ∀ j : Nat, j < 8 → coh ws (Ct + j) < ts := fun j hj => by
    have h := cohBelow_at hcoh hj; exact h
  have hts1 : 1 ≤ ts := by have := hcj 0 (by decide); omega
  have hC := isC_of_msg hh (toBytes_length _ _) hts1 hmsg
  have hmt : msgAt M ts = some ⟨Ct, toBytes (s1.rd 7) 8, some h, .plain⟩ := by
    obtain ⟨k, rfl⟩ : ∃ k, ts = k + 1 := ⟨ts - 1, by omega⟩
    simpa [msgAt] using hmsg
  have htsM := msgAt_le hmt
  -- take `pend ts` out of the bag; the rest, minus any gap, is the bag above `ts`
  ihave HQ : |={⊤}=> (⌜qLk M (ev0 ++ [(LLoad false false Ct tvs1 (srcR 11), none)] ++
      [(LStore false false Ct (toBytes (s1.rd 7) 8) (srcR 11) (srcR 7), some ts)])⌝ ∨ dshot g) ∗ shot g ts ∗
      ([∗list] t ∈ cBag M ts, pend g t) $$ [Hb Hmode]
  · icases Hmode with (%hcl | ⟨#Hd, %hra⟩)
    · obtain ⟨rfl, hall, hlc⟩ := hcl
      have hlts : lw < ts := by have := hcj 0 (by decide); simp at this; omega
      unfold cBagX
      icases bsl_filter_take (pend g) (fun t => decide (lw < t) && decide (t ≠ 0) && isC M t)
        (fun t => decide (lw < t) && decide (t ≠ ts) && isC M t) ts (by simp [hlts, hC]; omega)
        (fun t ht => by simp at ht; exact ⟨by simp [ht.1.1, ht.2]; omega, ht.1.2⟩) (rng M)
        (mem_rng.2 htsM) (nodup_rng M) $$ Hb with ⟨Hp, Hb⟩
      imod shoot $$ Hp with #Hsh
      by_cases hg : ∃ u, lw < u ∧ u < ts ∧ isC M u = true
      · obtain ⟨u, hu1, hu2, hu3⟩ := hg
        have huM : 1 ≤ u ∧ u ≤ M.length := by
          obtain ⟨m, hm, _⟩ := clsB_iff.1 hu3; exact msgAt_le hm
        icases bsl_filter_take (pend g) (fun t => decide (lw < t) && decide (t ≠ ts) && isC M t)
          (fun t => decide (lw < t) && decide (t ≠ ts) && decide (t ≠ u) && isC M t) u
          (by simp [hu1, hu3]; omega)
          (fun t ht => by simp at ht; exact ⟨by simp [ht.1.1.1, ht.1.1.2, ht.2], ht.1.2⟩) (rng M)
          (mem_rng.2 huM) (nodup_rng M) $$ Hb with ⟨Hu, Hb⟩
        unfold lkCtx
        icases Hctx with ⟨Hdoom, -⟩
        imod doom (E := ⊤) CoPset.subseteq_top g M u huM $$ [Hdoom Hu] with #Hd
        · iframe Hdoom Hu
        imodintro
        isplitr
        · iright; iexact Hd
        iframe Hsh
        unfold cBag
        iapply bsl_filter_mono (pend g) _ _ (fun t ht => by
          simp only [Bool.and_eq_true, decide_eq_true_eq] at ht ⊢
          exact ⟨⟨⟨by omega, by omega⟩, by omega⟩, ht.2⟩) (rng M) $$ Hb
      · have hl : latestC M lw ts := ⟨hlw, hlts, fun u h1 h2 => by
          cases h3 : isC M u
          · rfl
          · exact absurd ⟨u, h1, h2, h3⟩ hg⟩
        imodintro
        isplitr
        · ileft; ipureintro; exact qLk_pair hnoC hall hl
        iframe Hsh
        unfold cBag
        iapply bsl_filter_mono (pend g) _ _ (fun t ht => by
          simp only [Bool.and_eq_true, decide_eq_true_eq] at ht ⊢
          exact ⟨⟨by omega, by omega⟩, ht.2⟩) (rng M) $$ Hb
    · obtain ⟨hlex, j, hj, hexc⟩ := hra
      have hext : ex < ts := Nat.lt_of_le_of_lt hexc (hcj j hj)
      unfold cBagX
      icases bsl_filter_take (pend g) (fun t => decide (lw < t) && decide (t ≠ ex) && isC M t)
        (fun t => decide (lw < t) && decide (t ≠ ex) && decide (t ≠ ts) && isC M t) ts
        (by simp [hC]; omega)
        (fun t ht => by simp at ht; exact ⟨by simp [ht.1.1.1, ht.1.1.2, ht.2], ht.1.2⟩) (rng M)
        (mem_rng.2 htsM) (nodup_rng M) $$ Hb with ⟨Hp, Hb⟩
      imod shoot $$ Hp with #Hsh
      imodintro
      isplitr
      · iright; iexact Hd
      iframe Hsh
      unfold cBag
      iapply bsl_filter_mono (pend g) _ _ (fun t ht => by
        simp only [Bool.and_eq_true, decide_eq_true_eq] at ht ⊢
        exact ⟨⟨⟨by omega, by omega⟩, by omega⟩, ht.2⟩) (rng M) $$ Hb
  imod HQ with ⟨#HQ, #Hsh, Hb⟩
  imodintro
  isplitr
  · icases HQ with (%hQ | #Hd)
    · ileft; ipureintro; exact ⟨⟨0, grd_intro hQ⟩, grd_intro trivial⟩
    · iright; iexact Hd
  isplitr
  · unfold fulT; ileft; iexact Hsh
  iintro %s2 %hs2 _ _
  imodintro
  iintro Hl
  obtain ⟨hP2, hc2, hq2⟩ := LPstep_at hs2 hP1 (by rw [hc1])
  have e11' : s2.rd 11 = Y := by rw [LPstep_rd hs2 11 (.inr rfl), e11]
  have e10' : s2.rd 10 = X := by rw [LPstep_rd hs2 10 (.inr rfl), e10]
  have hst := storeRun_mono (instrR (regWP ws 7 (srcR 7))) false (srcsView (instrR (regWP ws 7 (srcR 7))) (srcR 11))
    (max (srcsView (instrR (regWP ws 7 (srcR 7))) (srcR 11)) (srcsView (instrR (regWP ws 7 (srcR 7))) (srcR 7)))
    Ct (toBytes (s1.rd 7) 8).length ts
  have hlo' : lo ≤ coh (instrR (acqPost (storeRun (instrR (regWP ws 7 (srcR 7))) false
      (srcsView (instrR (regWP ws 7 (srcR 7))) (srcR 11))
      (max (srcsView (instrR (regWP ws 7 (srcR 7))) (srcR 11)) (srcsView (instrR (regWP ws 7 (srcR 7))) (srcR 7)))
      Ct (toBytes (s1.rd 7) 8).length ts) false ts)) Lk := by
    have := hst.2.2.2.2.2.2.2.2.2.1 Lk
    have e : coh (instrR (regWP ws 7 (srcR 7))) Lk = coh ws Lk := rfl
    rw [acqPost_false]; simp only [instrR_coh]; omega
  have hvw' : ts ≤ (instrR (acqPost (storeRun (instrR (regWP ws 7 (srcR 7))) false
      (srcsView (instrR (regWP ws 7 (srcR 7))) (srcR 11))
      (max (srcsView (instrR (regWP ws 7 (srcR 7))) (srcR 11)) (srcsView (instrR (regWP ws 7 (srcR 7))) (srcR 7)))
      Ct (toBytes (s1.rd 7) 8).length ts) false ts)).wVwOld := by
    rw [acqPost_false, instrR_vwOld, hst.2.2.1]; omega
  iapply (lk_rel g M tk h hh hdd s2 _ _ _ lo ts ⟨hP2, hq2, by rw [hc2], e10', e11'⟩ hlo' hvw')
  iframe Hctx Hbag HQ Hl
  unfold cPts
  iframe Hb
  ipureintro; exact .inr hC

/-! ## 4. The critical section's load -/

/-- **THE CRITICAL SECTION** (`pc = 3`, `ld t2,(a1)`) and the rest: the owned read of the counter (R-a1). -/
theorem lk_cs (g : AGN) (M : List PMsg) (tk : Nat → GName) (h : Nat) (hh : h < 2) (hdd : g.dd = ddL M)
    (s : LP) (ws : PState) (pr : GSet Nat) (ev : Trace) (lo lw : Nat)
    (hs : s.prog = b1a ∧ s.q = [] ∧ s.pc = 3 ∧ s.rd 10 = X ∧ s.rd 11 = Y)
    (hlo : lo ≤ coh ws Lk) (hvr : lw ≤ ws.wVrNew) (hnoC : noC ev) :
    lkCtx (GF := GF) g M tk ∗ obag g M tk h lo 0 ∗ cPts g M lw ∗
      lhA g Proto.triv (wL M h) (qsLk M h) ws pr ev ⊢
      wpKA g Proto.triv (wL M h) (qsLk M) s (ΦL g M) := by
  obtain ⟨hprog, hq, hpc, h10, h11⟩ := hs
  have hw := litW_x xs1a imgL M h
  have hX := p1a_at hprog
  iintro ⟨#Hctx, Hbag, Hc, Hl⟩
  unfold cPts
  icases Hc with ⟨%hlw, Hb⟩
  rw [cBag_X]
  iapply (wpKA_ld (sz := 8) (sgn := true) (rd := 7) (rs1 := 11) (off := 0) (base := Ct) hw
    (litAg_x hq hX (by rw [hpc]; rfl) rfl) hq (by rw [hprog, hpc]; rfl) (alg_of h11 (by decide) (by decide))
    (base_of h11 (by decide)))
  iframe Hl
  inext
  iintro %tvs1 %hl1 %hlo1 _ _
  have hvp : lw ≤ ldPre ws false false (srcsView ws (srcR 11)) :=
    Nat.le_trans hvr (PF.ldPre_ge ws false false (srcsView ws (srcR 11))).2.1
  have hcases := cld_cases (img := imgL) hlw hvp 0 tvs1 (by rw [hl1]; decide)
    (by have := loadOk_weak hlo1; simpa using this)
  have hcohj := (loadBytes_coh false (ldPre ws false false (srcsView ws (srcR 11))) ws Ct tvs1).2
  -- THE MODE after the read: clean, R-a1 (doomed, one bag message out), or free
  ihave Hmode : |={⊤}=> (∃ ex, ([∗list] t ∈ cBagX M lw ex, pend g t) ∗
      (⌜ex = 0 ∧ (∀ p ∈ tvs1, p.1 = lw) ∧
          lw ≤ coh (loadRun ws false false (srcsView ws (srcR 11)) Ct tvs1) Ct⌝ ∨
        (dshot g ∗ ⌜lw < ex ∧ ∃ j : Nat, j < 8 ∧
          ex ≤ coh (loadRun ws false false (srcsView ws (srcR 11)) Ct tvs1) (Ct + j)⌝))) ∨
      (dfree g ∗ dshot g) $$ [Hb]
  · rcases hcases with hall | ⟨j, t, v, hj, hlt, hwt⟩ | ⟨ti, hti, j, hj, hc⟩
    · obtain ⟨t0, v0, r0, rfl⟩ := tvs_cons hl1 (by decide)
      have h0 := loadRun_coh0 ws false false (srcsView ws (srcR 11)) Ct t0 v0 r0
      have ht0 : t0 = lw := hall (t0, v0) (List.mem_cons_self ..)
      imodintro; ileft; iexists 0; iframe Hb; ileft; ipureintro
      exact ⟨rfl, hall, by rw [← ht0]; exact h0⟩
    · have hj8 : j < 8 := by rw [← hl1]; exact (List.getElem?_eq_some_iff.1 hj).1
      have htM : 1 ≤ t ∧ t ≤ M.length := by obtain ⟨m, hm, _⟩ := hwt; exact msgAt_le hm
      have hcoh : t ≤ coh (loadRun ws false false (srcsView ws (srcR 11)) Ct tvs1) (Ct + j) :=
        (bytesAll_get hcohj hj).2
      have hwt' : wrB M (Ct + j) t := by simpa using hwt
      by_cases hC : isC M t = true
      · unfold cBagX
        icases bsl_filter_take (pend g) (fun t => decide (lw < t) && decide (t ≠ 0) && isC M t)
          (fun x => decide (lw < x) && decide (x ≠ t) && isC M x) t (by simp [hlt, hC]; omega)
          (fun x hx => by
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hx ⊢
            exact ⟨⟨⟨hx.1.1, by omega⟩, hx.2⟩, hx.1.2⟩) (rng M) (mem_rng.2 htM) (nodup_rng M)
          $$ Hb with ⟨Hp, Hb⟩
        unfold lkCtx
        icases Hctx with ⟨Hdoom, -⟩
        imod doom (E := ⊤) CoPset.subseteq_top g M t htM $$ [Hdoom Hp] with #Hd
        · iframe Hdoom Hp
        imodintro; ileft; iexists t; iframe Hb; iright; iframe Hd; ipureintro
        exact ⟨hlt, j, hj8, hcoh⟩
      · -- not a counter message, and a lock message does not touch the counter: dead
        obtain ⟨m, hm, hb⟩ := hwt'
        have hL : isL M t = false := by
          cases hL : isL M t
          · rfl
          · rw [isL_noC hm hL j hj8] at hb; simp at hb
        have hD : isDd M t = true := by simp [isDd, hL, show isC M t = false by simpa using hC]
        have hJ : isJ M t = true := by simp [isJ, hD]
        unfold lkCtx
        icases Hctx with ⟨Hdoom, -, -, Hdd⟩
        ihave #Hdi := bsl_mem (F := fun t => deadInv g t) (List.mem_filter.2 ⟨mem_rng.2 htM, hJ⟩) $$ Hdd
        imod dead_doom g M t htM (by rw [hdd]; exact ⟨htM.1, hD⟩) $$ [] with ⟨#Hf, #Hd⟩
        · iframe Hdoom Hdi
        imodintro; iright; iframe Hf Hd
    · obtain ⟨hJ, hD, hti2⟩ := cmo_dead (by omega) hc
      unfold lkCtx
      icases Hctx with ⟨Hdoom, -, -, Hdd⟩
      ihave #Hdi := bsl_mem (F := fun t => deadInv g t) (List.mem_filter.2 ⟨mem_rng.2 ⟨by omega, hti2⟩, hJ⟩) $$ Hdd
      imod dead_doom g M ti ⟨by omega, hti2⟩ (by rw [hdd]; exact ⟨by omega, hD⟩) $$ [] with ⟨#Hf, #Hd⟩
      · iframe Hdoom Hdi
      imodintro; iright; iframe Hf Hd
  imod Hmode with Hmode
  imodintro
  isplitr
  · ileft; ipureintro
    exact ⟨0, grd_intro (qLk_ld hnoC (fun ts ⟨_, _, _, h⟩ => by cases h))⟩
  iintro %s1 %hs1 _ _
  imodintro
  iintro Hl
  obtain ⟨hP1, hc1, hq1⟩ := LPstep_at hs1 hprog (by rw [hpc])
  have e11 : s1.rd 11 = Y := by rw [LPstep_rd hs1 11 (.inl (by decide)), h11]
  have e10 : s1.rd 10 = X := by rw [LPstep_rd hs1 10 (.inl (by decide)), h10]
  icases Hmode with (⟨%ex, Hb, Hm⟩ | ⟨#Hf, #Hd⟩)
  · have hlo' : lo ≤ coh (qPosts (loadRun ws false false (srcsView ws (srcR 11)) Ct tvs1)
        (regWL 7 [.DLdRes] ++ [LInstr])) Lk := by
      have := (loadRun_mono ws false false (srcsView ws (srcR 11)) Ct tvs1).2.2.2.2.2.2.2.2.2.2.1 Lk
      exact Nat.le_trans hlo this
    have hq7 : ∀ a, coh (qPosts (loadRun ws false false (srcsView ws (srcR 11)) Ct tvs1)
        (regWL 7 [.DLdRes] ++ [LInstr])) a = coh (loadRun ws false false (srcsView ws (srcR 11)) Ct tvs1) a :=
      fun a => rfl
    iapply (lk_cs2 g M tk h hh hdd s1 _ _ ev tvs1 lo lw ex ⟨hP1, hq1, by rw [hc1], e10, e11⟩ hlo' hnoC hlw)
    iframe Hctx Hbag Hb Hl
    simp only [hq7]
    iexact Hm
  · ihave Hfree := lk_free (GF := GF) g M h hh hdd
    have hfr : frS s1 := ⟨hP1, hq1, by rw [hc1]; decide, by rw [hc1]; decide, e10, e11⟩
    iapply Hfree $$ %s1 %_ %_ %_ %hfr Hf Hd Hl

end cs

end Weak.Prom.OA
