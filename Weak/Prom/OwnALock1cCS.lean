/-
Weak/Prom: **G4 target (1c) on track (a): the critical section, the cpu field and the PLAIN release** (stage S4a
part 3; plan rev 7 §4 G4 (1c); §3 "Release-class, defined precisely", "The deposit", R-a1).

From `pc = 5` with the claimed `Rs s0` (counter points-to `cPts lw`, `lw ≤ s0`, and the cpu field's bag above `s0`):
* `sd a0,16(s1)` (`lk_cpu1`) — its timestamp lies above the pre-view `⊒ vwNew ≥ ts_acq > s0` (aq, M0(i)), so its
  `pend` is in the cpu field's bag; the bag above it remains;
* `ld; addi; sd` of the counter (`lk_cs1c`, `lk_cs2_1c`) — (1b)'s proofs (owned read, R-a1 doom, the store moving
  the points-to), carrying the cpu bag and its coherence floor;
* `sd zero,16(s1)` (`lk_cpu0`) — its timestamp lies above `coh(Pc) ≥` the first cpu store (coherence): its `pend` is
  in the bag;
* `fence rw,w` (`lk_fence1c`) — raises `vwNew` to `vrOld ⊔ vwOld ≥` both the counter store and the cpu store;
* `sw zero,0(s1)` (`lk_rel1c`) — A PLAIN STORE, RELEASE-CLASS by plan §3's definition (its pre-view `stPreA ⊒ vwNew`
  covers `vrOld ⊔ vwOld` after the fence): it takes `pend r` out of its slot, shoots it and DEPOSITS `Rs r` (the
  counter's points-to with latest write `< r` and the cpu bag above `r`).
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.OwnALock1cFree

namespace Weak.Prom.OA.C

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.PF Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Ref (Instr Test two64)
open Weak.Prom.Ref.Lit (X Y)
open PLabel
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode

/-! ## 1. Helpers -/

theorem st_coh (ws : PState) (va fv : Nat) (base : Int) (n ts : Nat) (a : Int) :
    coh ws a ≤ coh (instrR (acqPost (storeRun ws false va fv base n ts) false ts)) a := by
  rw [acqPost_false, instrR_coh]; exact (storeRun_mono ws false va fv base n ts).2.2.2.2.2.2.2.2.2.1 a

theorem st_coh0 (ws : PState) (va fv : Nat) (base : Int) (n ts : Nat) (hn : 0 < n) :
    ts ≤ coh (instrR (acqPost (storeRun ws false va fv base n ts) false ts)) base := by
  rw [acqPost_false, instrR_coh]; exact storeRun_coh0 ws false va fv base n ts hn

theorem st_vwOld (ws : PState) (va fv : Nat) (base : Int) (n ts : Nat) :
    (instrR (acqPost (storeRun ws false va fv base n ts) false ts)).wVwOld = max ws.wVwOld ts := by
  rw [acqPost_false, instrR_vwOld, storeRun_vwOld]

theorem st_vrNew (ws : PState) (va fv : Nat) (base : Int) (n ts : Nat) :
    (instrR (acqPost (storeRun ws false va fv base n ts) false ts)).wVrNew = ws.wVrNew := by
  rw [acqPost_false, instrR_vrNew, storeRun_vrNew]

section cs

variable {GF : BundledGFunctors} [GhostVarG GF HSt] [GhostVarG GF Bool] [TokenG GF] [InvGS GF]

/-- Take a cpu-field message's `pend` out of the bag; the bag above it remains. -/
theorem pPts_take (g : AGN) (M : List PMsg) {sp ts : Nat} (hlt : sp < ts) (hP : isP M ts = true)
    (htM : 1 ≤ ts ∧ ts ≤ M.length) : pPts (GF := GF) g M sp ⊢ pend g ts ∗ pPts g M ts := by
  unfold pPts pBag
  exact bsl_filter_take (pend g) (fun t => decide (sp < t) && isP M t) (fun t => decide (ts < t) && isP M t) ts
    (by simp [hP, hlt])
    (fun t ht => by
      simp only [Bool.and_eq_true, decide_eq_true_eq] at ht ⊢; exact ⟨⟨by omega, ht.2⟩, by omega⟩)
    (rng M) (mem_rng.2 htM) (nodup_rng M)

/-! ## 2. The release -/

/-- **THE RELEASE** (`pc = 11`, `sw zero,0(s1)`, a PLAIN store) and the end: the deposit of `Rs r`. -/
theorem lk_rel1c (g : AGN) (M : List PMsg) (tk : Nat → GName) (h : Nat) (hh : h < 2) (hdd : g.dd = ddL M)
    (s : LP) (ws : PState) (pr : GSet Nat) (ev : Trace) (lo lw sp : Nat)
    (hs : s.prog = b1c ∧ s.q = [] ∧ s.pc = 11 ∧ s.rd 9 = X ∧ s.rd 11 = Y)
    (hlo : lo ≤ coh ws Lk) (hvw : lw ≤ ws.wVwNew) (hsp : sp ≤ ws.wVwNew) :
    lkCtx (GF := GF) g M tk ∗ obag g M tk h lo 0 ∗ cPts g M lw ∗ pPts g M sp ∗ (⌜qLk M ev⌝ ∨ dshot g) ∗
      lhA g Proto.triv (wL1c M h) (qsLk M h) ws pr ev ⊢
      wpKA g Proto.triv (wL1c M h) (qsLk M) s (ΦL g M) := by
  obtain ⟨hprog, hq, hpc, h9, h11⟩ := hs
  have hw := litW_x xs1c imgL M h
  have hX := p1c_at hprog
  iintro ⟨#Hctx, Hbag, Hc, Hpp, HQ, Hl⟩
  iapply (wpKA_sw (sz := 4) (rs2 := 0) (rs1 := 9) (off := 0) (base := Lk) hw
    (litAg_x hq hX (by rw [hpc]; rfl) rfl) hq (by rw [hprog, hpc]; rfl) (alg_of h9 (by decide) (by decide))
    (base_of h9 (by decide)))
  iframe Hl
  inext
  iintro %r %_ %hmsg %hcoh %hext _ _
  have hd0 : toBytes (s.rd 0) 4 = toBytes 0 4 := rfl
  rw [hd0] at hmsg hcoh
  have hc0 : coh ws Lk < r := by
    have := cohBelow_at (j := 0) hcoh (by decide)
    simpa using this
  have hr1 : 1 ≤ r := by omega
  obtain ⟨hR, hbyH⟩ := isR_of_msg hh hr1 hmsg
  have hmr := msgAt_of hr1 hmsg
  have hrM : r ≤ M.length := (msgAt_le hmr).2
  have hlor : lo < r := by omega
  -- RELEASE-CLASS (plan §3): the plain store's pre-view contains `vwNew`, which the fence raised to `vrOld ⊔ vwOld`
  have hvr : ws.wVwNew < r := by
    have := (PF.stPreA_ge ws false false (srcsView ws (srcR 9)) (srcsView ws (srcR 0))).2.2.2.1
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
  ihave Hpr := pPts_mono (GF := GF) g M (s := sp) (s' := r) (by omega) $$ Hpp
  imod Hclose $$ [Ht Hc Hpr] with -
  · iright; iframe Hsh Ht; ileft; unfold Rs; iframe Hpr; iexists lw; iframe Hc; ipureintro; omega
  imodintro
  isplitl [HQ]
  · icases HQ with (%hQ | #Hd)
    · ileft; ipureintro
      exact ⟨⟨0, grd_intro (qLk_snoc hQ (st_nonC Lk_ne_Ct _ _ _ _))⟩, grd_intro trivial⟩
    · iright; iexact Hd
  isplitr
  · unfold fulT; ileft; iexact Hsh
  iintro %s' %hs' _ _
  imodintro
  iintro Hl
  obtain ⟨hP', hc', hq'⟩ := LPstep_at hs' hprog (by rw [hpc])
  have hend : s'.prog.length ≤ s'.pc := by rw [hP', hc']; decide
  iapply (wpKA_end (v := ()) (litAg_xn hq' (fun x hx => by rw [p1c_at hP', hc'] at hx; cases hx)) hq' hend
    (by show litDone s' = some (); unfold litDone; rw [if_pos ⟨hq', hend⟩]))
  iframe Hl
  imodintro
  ileft; ipureintro; exact ⟨0, grd_intro trivial⟩

/-- `pc = 10`: `fence rw,w` (mm-explanatory / xv6 `__sync_synchronize`): raises `vwNew` to `vrOld ⊔ vwOld`. -/
theorem lk_fence1c (g : AGN) (M : List PMsg) (tk : Nat → GName) (h : Nat) (hh : h < 2) (hdd : g.dd = ddL M)
    (s : LP) (ws : PState) (pr : GSet Nat) (ev : Trace) (lo lw sp : Nat)
    (hs : s.prog = b1c ∧ s.q = [] ∧ s.pc = 10 ∧ s.rd 9 = X ∧ s.rd 11 = Y)
    (hlo : lo ≤ coh ws Lk) (hvw : lw ≤ ws.wVwOld) (hsp : sp ≤ ws.wVwOld) :
    lkCtx (GF := GF) g M tk ∗ obag g M tk h lo 0 ∗ cPts g M lw ∗ pPts g M sp ∗ (⌜qLk M ev⌝ ∨ dshot g) ∗
      lhA g Proto.triv (wL1c M h) (qsLk M h) ws pr ev ⊢
      wpKA g Proto.triv (wL1c M h) (qsLk M) s (ΦL g M) := by
  obtain ⟨hprog, hq, hpc, h9, h11⟩ := hs
  have hw := litW_x xs1c imgL M h
  have hX := p1c_at hprog
  iintro ⟨#Hctx, Hbag, Hc, Hpp, HQ, Hl⟩
  iapply (wpKA_fence hw (litAg_x hq hX (by rw [hpc]; rfl) rfl) hq (by rw [hprog, hpc]; rfl))
  iframe Hl
  inext
  iintro %s1 %hs1 _ _
  imodintro
  iintro Hl
  obtain ⟨hP1, hc1, hq1⟩ := LPstep_at hs1 hprog (by rw [hpc])
  have hvw' : lw ≤ (instrR (fencePost ws true true false true)).wVwNew := by
    simp only [instrR_vwNew, fence_vwNew, ite_true]; omega
  have hsp' : sp ≤ (instrR (fencePost ws true true false true)).wVwNew := by
    simp only [instrR_vwNew, fence_vwNew, ite_true]; omega
  iapply (lk_rel1c g M tk h hh hdd s1 (instrR (fencePost ws true true false true)) _ ev lo lw sp
    ⟨hP1, hq1, hc1, by rw [LPstep_rd hs1 9 (.inr rfl), h9], by rw [LPstep_rd hs1 11 (.inr rfl), h11]⟩
    hlo hvw' hsp')
  iframe Hctx Hbag Hc Hpp HQ Hl

/-- `pc = 9`: `sd zero,16(s1)`: its `pend` is in the cpu bag (coherence above the first cpu store). -/
theorem lk_cpu0 (g : AGN) (M : List PMsg) (tk : Nat → GName) (h : Nat) (hh : h < 2) (hdd : g.dd = ddL M)
    (s : LP) (ws : PState) (pr : GSet Nat) (ev : Trace) (lo lw sp : Nat)
    (hs : s.prog = b1c ∧ s.q = [] ∧ s.pc = 9 ∧ s.rd 9 = X ∧ s.rd 11 = Y)
    (hlo : lo ≤ coh ws Lk) (hvw : lw ≤ ws.wVwOld) (hsp : sp ≤ coh ws Pc) :
    lkCtx (GF := GF) g M tk ∗ obag g M tk h lo 0 ∗ cPts g M lw ∗ (⌜qLk M ev⌝ ∨ dshot g) ∗
      lhA g Proto.triv (wL1c M h) (qsLk M h) ws pr ev ∗ pPts g M sp ⊢
      wpKA g Proto.triv (wL1c M h) (qsLk M) s (ΦL g M) := by
  obtain ⟨hprog, hq, hpc, h9, h11⟩ := hs
  have hw := litW_x xs1c imgL M h
  have hX := p1c_at hprog
  iintro ⟨#Hctx, Hbag, Hc, #HQ, Hl, Hpp⟩
  iapply (wpKA_sw (sz := 8) (rs2 := 0) (rs1 := 9) (off := 16) (base := Pc) hw
    (litAg_x hq hX (by rw [hpc]; rfl) rfl) hq (by rw [hprog, hpc]; rfl) (alg_pc h9) (base_pc h9))
  iframe Hl
  inext
  iintro %ts %_ %hmsg %hcoh %_ _ _
  rw [toBytes_length] at hcoh
  have hc0 : coh ws Pc < ts := by
    have := cohBelow_at (j := 0) hcoh (by decide)
    simpa using this
  have hts1 : 1 ≤ ts := by omega
  have hP := isP_of_msg hh (toBytes_length _ _) hts1 hmsg
  have htsM := msgAt_le (msgAt_of hts1 hmsg)
  icases pPts_take (GF := GF) g M (by omega : sp < ts) hP htsM $$ Hpp with ⟨Hpd, Hpp⟩
  imod shoot $$ Hpd with #Hsh
  imodintro
  isplitr
  · icases HQ with (%hQ | #Hd)
    · ileft; ipureintro
      exact ⟨⟨0, grd_intro (qLk_snoc hQ (st_nonC Pc_ne_Ct _ _ _ _))⟩, grd_intro trivial⟩
    · iright; iexact Hd
  isplitr
  · unfold fulT; ileft; iexact Hsh
  iintro %s1 %hs1 _ _
  imodintro
  iintro Hl
  obtain ⟨hP1, hc1, hq1⟩ := LPstep_at hs1 hprog (by rw [hpc])
  have hvo := st_vwOld ws (srcsView ws (srcR 9)) (max (srcsView ws (srcR 9)) (srcsView ws (srcR 0))) Pc
    (toBytes (s.rd 0) 8).length ts
  iapply (lk_fence1c g M tk h hh hdd s1 _ _ _ lo lw ts
    ⟨hP1, hq1, hc1, by rw [LPstep_rd hs1 9 (.inr rfl), h9], by rw [LPstep_rd hs1 11 (.inr rfl), h11]⟩
    (Nat.le_trans hlo (st_coh _ _ _ _ _ _ Lk)) (by rw [hvo]; omega) (by rw [hvo]; omega))
  iframe Hctx Hbag Hc Hpp Hl
  icases HQ with (%hQ | #Hd)
  · ileft; ipureintro; exact qLk_snoc hQ (st_nonC Pc_ne_Ct _ _ _ _)
  · iright; iexact Hd

/-! ## 3. `addi`, `sd`: the store moves the points-to -/

/-- `pc = 7..8`: `addi t2,t2,1; sd t2,(a1)`, then `sd zero,16(s1)` and the release.  `ex` is the counter message a dooming read took out of
the bag (`0`: none, the read was clean). -/
theorem lk_cs2_1c (g : AGN) (M : List PMsg) (tk : Nat → GName) (h : Nat) (hh : h < 2) (hdd : g.dd = ddL M)
    (s : LP) (ws : PState) (pr : GSet Nat) (ev0 : Trace) (tvs1 : List (Nat × BitVec 8)) (lo lw ex sp : Nat)
    (hs : s.prog = b1c ∧ s.q = [] ∧ s.pc = 7 ∧ s.rd 9 = X ∧ s.rd 11 = Y)
    (hlo : lo ≤ coh ws Lk) (hsp : sp ≤ coh ws Pc) (hnoC : noC ev0) (hlw : lw = 0 ∨ isC M lw = true) :
    lkCtx (GF := GF) g M tk ∗ obag g M tk h lo 0 ∗ pPts g M sp ∗ ([∗list] t ∈ cBagX M lw ex, pend g t) ∗
      (⌜ex = 0 ∧ (∀ p ∈ tvs1, p.1 = lw) ∧ lw ≤ coh ws Ct⌝ ∨
        (dshot g ∗ ⌜lw < ex ∧ ∃ j : Nat, j < 8 ∧ ex ≤ coh ws (Ct + j)⌝)) ∗
      lhA g Proto.triv (wL1c M h) (qsLk M h) ws pr (ev0 ++ [(LLoad false false Ct tvs1 (srcR 11), none)]) ⊢
      wpKA g Proto.triv (wL1c M h) (qsLk M) s (ΦL g M) := by
  obtain ⟨hprog, hq, hpc, h9, h11⟩ := hs
  have hw := litW_x xs1c imgL M h
  have hX := p1c_at hprog
  iintro ⟨#Hctx, Hbag, Hpp, Hb, Hmode, Hl⟩
  -- `addi t2,t2,1`
  iapply (wpKA_alui hw (litAg_x hq hX (by rw [hpc]; rfl) rfl) hq (by rw [hprog, hpc]; rfl) (by decide))
  iframe Hl
  inext
  iintro %s1 %hs1 _ _
  imodintro
  iintro Hl
  obtain ⟨hP1, hc1, hq1⟩ := LPstep_at hs1 hprog (by rw [hpc])
  have e11 : s1.rd 11 = Y := by rw [LPstep_rd hs1 11 (.inl (by decide)), h11]
  have e9 : s1.rd 9 = X := by rw [LPstep_rd hs1 9 (.inl (by decide)), h9]
  -- `sd t2,(a1)`
  iapply (wpKA_sw (sz := 8) (rs2 := 7) (rs1 := 11) (off := 0) (base := Ct) hw
    (litAg_x hq1 (p1c_at hP1) (by rw [hc1]; rfl) rfl) hq1 (by rw [hP1, hc1]; rfl)
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
  have e9' : s2.rd 9 = X := by rw [LPstep_rd hs2 9 (.inr rfl), e9]
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
  have hsp' : sp ≤ coh (instrR (acqPost (storeRun (instrR (regWP ws 7 (srcR 7))) false
      (srcsView (instrR (regWP ws 7 (srcR 7))) (srcR 11))
      (max (srcsView (instrR (regWP ws 7 (srcR 7))) (srcR 11)) (srcsView (instrR (regWP ws 7 (srcR 7))) (srcR 7)))
      Ct (toBytes (s1.rd 7) 8).length ts) false ts)) Pc := by
    have := hst.2.2.2.2.2.2.2.2.2.1 Pc
    have e : coh (instrR (regWP ws 7 (srcR 7))) Pc = coh ws Pc := rfl
    rw [acqPost_false]; simp only [instrR_coh]; omega
  iapply (lk_cpu0 g M tk h hh hdd s2 _ _ _ lo ts sp ⟨hP2, hq2, by rw [hc2], e9', e11'⟩ hlo' hvw' hsp')
  iframe Hctx Hbag HQ Hl Hpp
  unfold cPts
  iframe Hb
  ipureintro; exact .inr hC

/-! ## 4. The critical section's load -/

/-- **THE CRITICAL SECTION** (`pc = 6`, `ld t2,(a1)`) and the rest: the owned read of the counter (R-a1). -/
theorem lk_cs1c (g : AGN) (M : List PMsg) (tk : Nat → GName) (h : Nat) (hh : h < 2) (hdd : g.dd = ddL M)
    (s : LP) (ws : PState) (pr : GSet Nat) (ev : Trace) (lo lw sp : Nat)
    (hs : s.prog = b1c ∧ s.q = [] ∧ s.pc = 6 ∧ s.rd 9 = X ∧ s.rd 11 = Y)
    (hlo : lo ≤ coh ws Lk) (hsp : sp ≤ coh ws Pc) (hvr : lw ≤ ws.wVrNew) (hnoC : noC ev) :
    lkCtx (GF := GF) g M tk ∗ obag g M tk h lo 0 ∗ cPts g M lw ∗ pPts g M sp ∗
      lhA g Proto.triv (wL1c M h) (qsLk M h) ws pr ev ⊢
      wpKA g Proto.triv (wL1c M h) (qsLk M) s (ΦL g M) := by
  obtain ⟨hprog, hq, hpc, h9, h11⟩ := hs
  have hw := litW_x xs1c imgL M h
  have hX := p1c_at hprog
  iintro ⟨#Hctx, Hbag, Hc, Hpp, Hl⟩
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
        have hP : isP M t = false := by
          cases hP : isP M t
          · rfl
          · rw [isP_noC hm hP j hj8] at hb; simp at hb
        have hD : isDd M t = true := by simp [isDd, hL, hP, show isC M t = false by simpa using hC]
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
  have e9 : s1.rd 9 = X := by rw [LPstep_rd hs1 9 (.inl (by decide)), h9]
  icases Hmode with (⟨%ex, Hb, Hm⟩ | ⟨#Hf, #Hd⟩)
  · have hlo' : lo ≤ coh (qPosts (loadRun ws false false (srcsView ws (srcR 11)) Ct tvs1)
        (regWL 7 [.DLdRes] ++ [LInstr])) Lk := by
      have := (loadRun_mono ws false false (srcsView ws (srcR 11)) Ct tvs1).2.2.2.2.2.2.2.2.2.2.1 Lk
      exact Nat.le_trans hlo this
    have hq7 : ∀ a, coh (qPosts (loadRun ws false false (srcsView ws (srcR 11)) Ct tvs1)
        (regWL 7 [.DLdRes] ++ [LInstr])) a = coh (loadRun ws false false (srcsView ws (srcR 11)) Ct tvs1) a :=
      fun a => rfl
    have hsp' : sp ≤ coh (qPosts (loadRun ws false false (srcsView ws (srcR 11)) Ct tvs1)
        (regWL 7 [.DLdRes] ++ [LInstr])) Pc := by
      have := (loadRun_mono ws false false (srcsView ws (srcR 11)) Ct tvs1).2.2.2.2.2.2.2.2.2.2.1 Pc
      exact Nat.le_trans hsp this
    iapply (lk_cs2_1c g M tk h hh hdd s1 _ _ ev tvs1 lo lw ex sp ⟨hP1, hq1, by rw [hc1], e9, e11⟩ hlo' hsp' hnoC hlw)
    iframe Hctx Hbag Hpp Hb Hl
    simp only [hq7]
    iexact Hm
  · ihave Hfree := lk_free1c (GF := GF) g M h hh hdd
    have hfr : frS1c s1 := ⟨hP1, hq1, by rw [hc1]; decide, by rw [hc1]; decide, e9, e11⟩
    iapply Hfree $$ %s1 %_ %_ %_ %hfr Hf Hd Hl



/-! ## 5. The first cpu-field store -/

/-- **`pc = 5`: `sd a0,16(s1)`** (xv6 `lk->cpu = mycpu()`), then the critical section: its timestamp lies above
the pre-view `⊒ vwNew ≥ s0` (the aq AMO put `vwNew ≥ ts_acq > s0`), so its `pend` is in the claimed cpu bag. -/
theorem lk_cpu1 (g : AGN) (M : List PMsg) (tk : Nat → GName) (h : Nat) (hh : h < 2) (hdd : g.dd = ddL M)
    (s : LP) (ws : PState) (pr : GSet Nat) (ev : Trace) (lo lw s0 : Nat)
    (hs : s.prog = b1c ∧ s.q = [] ∧ s.pc = 5 ∧ s.rd 9 = X ∧ s.rd 11 = Y)
    (hlo : lo ≤ coh ws Lk) (hvr : lw ≤ ws.wVrNew) (hs0 : s0 ≤ ws.wVwNew) (hnoC : noC ev) :
    lkCtx (GF := GF) g M tk ∗ obag g M tk h lo 0 ∗ cPts g M lw ∗ pPts g M s0 ∗
      lhA g Proto.triv (wL1c M h) (qsLk M h) ws pr ev ⊢
      wpKA g Proto.triv (wL1c M h) (qsLk M) s (ΦL g M) := by
  obtain ⟨hprog, hq, hpc, h9, h11⟩ := hs
  have hw := litW_x xs1c imgL M h
  have hX := p1c_at hprog
  iintro ⟨#Hctx, Hbag, Hc, Hpp, Hl⟩
  iapply (wpKA_sw (sz := 8) (rs2 := 10) (rs1 := 9) (off := 16) (base := Pc) hw
    (litAg_x hq hX (by rw [hpc]; rfl) rfl) hq (by rw [hprog, hpc]; rfl) (alg_pc h9) (base_pc h9))
  iframe Hl
  inext
  iintro %ts %_ %hmsg %_ %hext _ _
  have hpre := (PF.stPreA_ge ws false false (srcsView ws (srcR 9)) (srcsView ws (srcR 10))).2.2.2.1
  have hts1 : 1 ≤ ts := by omega
  have hP := isP_of_msg hh (toBytes_length _ _) hts1 hmsg
  have htsM := msgAt_le (msgAt_of hts1 hmsg)
  icases pPts_take (GF := GF) g M (by omega : s0 < ts) hP htsM $$ Hpp with ⟨Hpd, Hpp⟩
  imod shoot $$ Hpd with #Hsh
  imodintro
  isplitr
  · ileft; ipureintro
    exact ⟨⟨0, grd_intro (qLk_noC (noC_snoc hnoC (st_nonC Pc_ne_Ct _ _ _ _)))⟩, grd_intro trivial⟩
  isplitr
  · unfold fulT; ileft; iexact Hsh
  iintro %s1 %hs1 _ _
  imodintro
  iintro Hl
  obtain ⟨hP1, hc1, hq1⟩ := LPstep_at hs1 hprog (by rw [hpc])
  have hvr' := st_vrNew ws (srcsView ws (srcR 9)) (max (srcsView ws (srcR 9)) (srcsView ws (srcR 10))) Pc
    (toBytes (s.rd 10) 8).length ts
  iapply (lk_cs1c g M tk h hh hdd s1 _ _ _ lo lw ts
    ⟨hP1, hq1, hc1, by rw [LPstep_rd hs1 9 (.inr rfl), h9], by rw [LPstep_rd hs1 11 (.inr rfl), h11]⟩
    (Nat.le_trans hlo (st_coh _ _ _ _ _ _ Lk)) (st_coh0 _ _ _ _ (toBytes (s.rd 10) 8).length _ (by rw [toBytes_length]; decide))
    (by rw [hvr']; exact hvr) (noC_snoc hnoC (st_nonC Pc_ne_Ct _ _ _ _)))
  iframe Hctx Hbag Hc Hpp Hl

end cs

end Weak.Prom.OA.C
