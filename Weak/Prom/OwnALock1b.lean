/-
Weak/Prom: **G4 target (1b) on track (a): the manual's Example 2, the spinlock with FENCES** (stage S4a part 2;
plan rev 7 §4 G4 (1b); mm-explanatory.adoc:723–741: `again: amoswap.w t0, t0, (a0); fence r, rw; bnez t0, again;
# critical section; fence rw, w; amoswap.w x0, x0, (a0)`).

The protocol, the classes and the per-step lemmas are (1a)'s (OwnALockDefs/OwnALockLib/OwnALockAcq.lean: the AMO
messages are `excl` in both forms).  What changes:
* the acquiring AMO has no `aq`: its write is not covered by the frontier at the next step; `fence r,rw` raises
  `vwNew` to `vrOld ≥ ts` (the AMO is one memory operation at `ts`, `amoPost`), so the CLAIM (`lk_acq`) happens at
  the fence's step — the same lemma, at a later frontier;
* the release AMO has no `rl`: `fence rw,w` makes it release-class (`vwNew ≥ vrOld ⊔ vwOld`, plan §3).
`own_lock1b`: the same mutual-exclusion invariant `qLk` as (1a).  0 named inputs; finite runs (a hart may stop
anywhere in its spin loop; the prefix lemma S3d is separate, [OWN.P4]).
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.OwnALock

namespace Weak.Prom.OA

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.PF Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Ref (Instr Test two64)
open Weak.Prom.Ref.Lit (X Y)
open PLabel
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode

/-! ## 1. The text -/

/-- **(1b) the manual's Example 2** (the "arbitrary unrelated" accesses omitted), with (1a)'s critical section:
`0: li t0,1  1: amoswap.w t0,t0,(a0)  2: fence r,rw  3: bnez t0,1  4: ld t2,(a1)  5: addi t2,t2,1  6: sd t2,(a1)
 7: fence rw,w  8: amoswap.w x0,x0,(a0)`. -/
def p1b : List XI :=
  [.i (Weak.Prom.Ref.Lit.li 5 1), .i (Weak.Prom.Ref.Lit.amoswapW false false 5 5 10), .i Weak.Prom.Ref.Lit.fRRW,
   .i (.br .ne 5 0 1), .i (Weak.Prom.Ref.Lit.ld 7 11), .i (Weak.Prom.Ref.Lit.addi 7 7 1),
   .i (Weak.Prom.Ref.Lit.sd 7 11), .i Weak.Prom.Ref.Lit.fRWW, .i (Weak.Prom.Ref.Lit.amoswapW false false 0 0 10)]

abbrev b1b : List Instr := p1b.map XI.base

def t1b : Test :=
  { harts := [b1b, b1b]
    regs0 := [[(10, X), (11, Y)], [(10, X), (11, Y)]]
    img := []
    cond := Weak.Prom.Ref.Lit.mpFF.cond }

abbrev xs1b : List (List XI) := [p1b]

theorem xOf_1b : xOf xs1b b1b = some p1b := by decide

theorem p1b_at {s : LP} (h : s.prog = b1b) : xOf xs1b s.prog = some p1b := by rw [h]; exact xOf_1b

/-- Hart `h`'s world (the image is the all-zero `imgL`). -/
abbrev wL1b (M : List PMsg) (h : Nat) : HW LP Unit Unit := xW xs1b imgL M h

def frS1b (s : LP) : Prop :=
  s.prog = b1b ∧ s.q = [] ∧ 1 ≤ s.pc ∧ s.pc ≤ 9 ∧ s.rd 10 = X ∧ s.rd 11 = Y

section free

variable {GF : BundledGFunctors} [GhostVarG GF HSt] [GhostVarG GF Bool] [TokenG GF] [InvGS GF]

/-- FREE MODE runs the rest of (1b)'s text (as `lk_free`). -/
theorem lk_free1b (g : AGN) (M : List PMsg) (h : Nat) (hh : h < 2) (hdd : g.dd = ddL M) :
    ⊢ ∀ (s : LP) (ws : PState) (pr : GSet Nat) (ev : Trace), ⌜frS1b s⌝ -∗ dfree (GF := GF) g -∗ dshot g -∗
      lhA g Proto.triv (wL1b M h) (qsLk M h) ws pr ev -∗ wpKA g Proto.triv (wL1b M h) (qsLk M) s (ΦL g M) := by
  have hw := litW_x xs1b imgL M h
  iloeb as IH
  iintro %s %ws %pr %ev %hs #Hf #Hd Hl
  obtain ⟨hprog, hq, hpc1, hpc9, h10, h11⟩ := hs
  have hX := p1b_at hprog
  have hpc : s.pc = 1 ∨ s.pc = 2 ∨ s.pc = 3 ∨ s.pc = 4 ∨ s.pc = 5 ∨ s.pc = 6 ∨ s.pc = 7 ∨ s.pc = 8 ∨
      s.pc = 9 := by omega
  have hfr : ∀ s' : LP, ∀ pc rd v, LPstep s s' pc rd v → rd ≠ 10 → rd ≠ 11 → 1 ≤ pc → pc ≤ 9 → frS1b s' :=
    fun s' pc rd v hs h1 h2 h3 h4 =>
      ⟨hs.1.trans hprog, hs.2.2.1, by rw [hs.2.1]; exact h3, by rw [hs.2.1]; exact h4,
        by rw [LPstep_rd hs 10 (.inl (Ne.symm h1)), h10], by rw [LPstep_rd hs 11 (.inl (Ne.symm h2)), h11]⟩
  rcases hpc with hpc | hpc | hpc | hpc | hpc | hpc | hpc | hpc | hpc
  · -- `amoswap.w t0,t0,(a0)`
    iapply (wpKA_amo (base := Lk) hw (litAg_x hq hX (by rw [hpc]; rfl) rfl) hq (by rw [hprog, hpc]; rfl)
      (by rw [h10]; decide) (by rw [h10]))
    iframe Hl
    inext
    iintro %tvs %ts %_ %_ %hmsg %_ %_ %_ %_ _ _
    imodintro
    isplitr
    · iright; iexact Hd
    isplitr
    · unfold fulT; iright; iframe Hf; ipureintro
      rw [hdd]; exact lm_notDd hh (by rw [amoD_swap]; exact toBytes_length _ _) hmsg
    iintro %s' %hs' _ _
    imodintro
    iintro Hl
    iapply IH $$ %s' %_ %_ %_ %(hfr s' _ _ _ hs' (by decide) (by decide) (by omega) (by omega)) Hf Hd Hl
  · -- `fence r,rw`
    iapply (wpKA_fence hw (litAg_x hq hX (by rw [hpc]; rfl) rfl) hq (by rw [hprog, hpc]; rfl))
    iframe Hl
    inext
    iintro %s' %hs' _ _
    imodintro
    iintro Hl
    iapply IH $$ %s' %_ %_ %_ %(hfr s' _ _ _ hs' (by decide) (by decide) (by omega) (by omega)) Hf Hd Hl
  · -- `bnez t0, again`
    iapply (wpKA_brx (Xs := xs1b) hw (xAg_x xs1b imgL M h s) hq hX (by rw [hpc]; rfl) (by rw [hprog]; decide))
    iframe Hl
    inext
    iintro %s' %hs' _ _
    imodintro
    iintro Hl
    iapply IH $$ %s' %_ %_ %_ %(hfr s' _ _ _ hs' (by decide) (by decide) (by split <;> omega)
      (by split <;> omega)) Hf Hd Hl
  · -- `ld t2,(a1)`
    iapply (wpKA_ld (sz := 8) (sgn := true) (rd := 7) (rs1 := 11) (off := 0) (base := Ct) hw
      (litAg_x hq hX (by rw [hpc]; rfl) rfl) hq (by rw [hprog, hpc]; rfl) (alg_of h11 (by decide) (by decide))
      (base_of h11 (by decide)))
    iframe Hl
    inext
    iintro %tvs %_ %_ _ _
    imodintro
    isplitr
    · iright; iexact Hd
    iintro %s' %hs' _ _
    imodintro
    iintro Hl
    iapply IH $$ %s' %_ %_ %_ %(hfr s' _ _ _ hs' (by decide) (by decide) (by omega) (by omega)) Hf Hd Hl
  · -- `addi t2,t2,1`
    iapply (wpKA_alui hw (litAg_x hq hX (by rw [hpc]; rfl) rfl) hq (by rw [hprog, hpc]; rfl) (by decide))
    iframe Hl
    inext
    iintro %s' %hs' _ _
    imodintro
    iintro Hl
    iapply IH $$ %s' %_ %_ %_ %(hfr s' _ _ _ hs' (by decide) (by decide) (by omega) (by omega)) Hf Hd Hl
  · -- `sd t2,(a1)`
    iapply (wpKA_sw (sz := 8) (rs2 := 7) (rs1 := 11) (off := 0) (base := Ct) hw
      (litAg_x hq hX (by rw [hpc]; rfl) rfl) hq (by rw [hprog, hpc]; rfl) (alg_of h11 (by decide) (by decide))
      (base_of h11 (by decide)))
    iframe Hl
    inext
    iintro %ts %_ %hmsg %_ %_ _ _
    imodintro
    isplitr
    · iright; iexact Hd
    isplitr
    · unfold fulT; iright; iframe Hf; ipureintro
      rw [hdd]; exact cm_notDd hh (toBytes_length _ _) hmsg
    iintro %s' %hs' _ _
    imodintro
    iintro Hl
    iapply IH $$ %s' %_ %_ %_ %(hfr s' _ _ _ hs' (by decide) (by decide) (by omega) (by omega)) Hf Hd Hl
  · -- `fence rw,w`
    iapply (wpKA_fence hw (litAg_x hq hX (by rw [hpc]; rfl) rfl) hq (by rw [hprog, hpc]; rfl))
    iframe Hl
    inext
    iintro %s' %hs' _ _
    imodintro
    iintro Hl
    iapply IH $$ %s' %_ %_ %_ %(hfr s' _ _ _ hs' (by decide) (by decide) (by omega) (by omega)) Hf Hd Hl
  · -- `amoswap.w x0,x0,(a0)`
    iapply (wpKA_amo (base := Lk) hw (litAg_x hq hX (by rw [hpc]; rfl) rfl) hq (by rw [hprog, hpc]; rfl)
      (by rw [h10]; decide) (by rw [h10]))
    iframe Hl
    inext
    iintro %tvs %ts %_ %_ %hmsg %_ %_ %_ %_ _ _
    imodintro
    isplitr
    · iright; iexact Hd
    isplitr
    · unfold fulT; iright; iframe Hf; ipureintro
      rw [hdd]; exact lm_notDd hh (by rw [amoD_swap]; exact toBytes_length _ _) hmsg
    iintro %s' %hs' _ _
    imodintro
    iintro Hl
    iapply IH $$ %s' %_ %_ %_ %(hfr s' _ _ _ hs' (by decide) (by decide) (by omega) (by omega)) Hf Hd Hl
  · -- the end
    have hend : s.prog.length ≤ s.pc := by rw [hprog, hpc]; decide
    iapply (wpKA_end (v := ()) (litAg_xn hq (fun x hx => by rw [hX, hpc] at hx; cases hx)) hq hend
      (by show litDone s = some (); unfold litDone; rw [if_pos ⟨hq, hend⟩]))
    iframe Hl
    imodintro
    iright; iexact Hd

end free

section cs

variable {GF : BundledGFunctors} [GhostVarG GF HSt] [GhostVarG GF Bool] [TokenG GF] [InvGS GF]

/-- **THE RELEASE AMO** (`pc = 8`, `amoswap.w x0,x0,(a0)`, after `fence rw,w`) and the end: the deposit of `Rs r`. -/
theorem lk_rel1b_amo (g : AGN) (M : List PMsg) (tk : Nat → GName) (h : Nat) (hh : h < 2) (hdd : g.dd = ddL M)
    (s : LP) (ws : PState) (pr : GSet Nat) (ev : Trace) (lo lw : Nat)
    (hs : s.prog = b1b ∧ s.q = [] ∧ s.pc = 8 ∧ s.rd 10 = X ∧ s.rd 11 = Y)
    (hlo : lo ≤ coh ws Lk) (hvw : lw ≤ ws.wVwNew) :
    lkCtx (GF := GF) g M tk ∗ obag g M tk h lo 0 ∗ cPts g M lw ∗ (⌜qLk M ev⌝ ∨ dshot g) ∗
      lhA g Proto.triv (wL1b M h) (qsLk M h) ws pr ev ⊢
      wpKA g Proto.triv (wL1b M h) (qsLk M) s (ΦL g M) := by
  obtain ⟨hprog, hq, hpc, h10, h11⟩ := hs
  have hw := litW_x xs1b imgL M h
  have hX := p1b_at hprog
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
  -- release-class through `fence rw,w`: `vwNew ≥ vwOld ≥ lw` is in the pre-view
  have hlwr : lw ≤ r := by
    have h1 := (PF.stPre_ge (loadRun ws false false (srcsView ws (srcR 10)) Lk tvs) false
      (srcsView ws (srcR 10)) (srcsView ws (srcR 0))).2.2.2.1
    have h2 := (loadRun_mono ws false false (srcsView ws (srcR 10)) Lk tvs).2.2.2.2.2.2.2.2.1
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
  iapply (wpKA_end (v := ()) (litAg_xn hq' (fun x hx => by rw [p1b_at hP', hc'] at hx; cases hx)) hq' hend
    (by show litDone s' = some (); unfold litDone; rw [if_pos ⟨hq', hend⟩]))
  iframe Hl
  imodintro
  ileft; ipureintro; exact ⟨0, grd_intro trivial⟩

/-- **THE RELEASE** (`pc = 7..8`, `fence rw,w; amoswap.w x0,x0,(a0)`, mm-explanatory.adoc:736–739): the fence makes
the AMO's write release-class (`fencePost` raises `vwNew` to `vrOld ⊔ vwOld ≥ lw`, plan §3). -/
theorem lk_rel1b (g : AGN) (M : List PMsg) (tk : Nat → GName) (h : Nat) (hh : h < 2) (hdd : g.dd = ddL M)
    (s : LP) (ws : PState) (pr : GSet Nat) (ev : Trace) (lo lw : Nat)
    (hs : s.prog = b1b ∧ s.q = [] ∧ s.pc = 7 ∧ s.rd 10 = X ∧ s.rd 11 = Y)
    (hlo : lo ≤ coh ws Lk) (hvw : lw ≤ ws.wVwOld) :
    lkCtx (GF := GF) g M tk ∗ obag g M tk h lo 0 ∗ cPts g M lw ∗ (⌜qLk M ev⌝ ∨ dshot g) ∗
      lhA g Proto.triv (wL1b M h) (qsLk M h) ws pr ev ⊢
      wpKA g Proto.triv (wL1b M h) (qsLk M) s (ΦL g M) := by
  obtain ⟨hprog, hq, hpc, h10, h11⟩ := hs
  have hw := litW_x xs1b imgL M h
  have hX := p1b_at hprog
  iintro ⟨#Hctx, Hbag, Hc, HQ, Hl⟩
  iapply (wpKA_fence hw (litAg_x hq hX (by rw [hpc]; rfl) rfl) hq (by rw [hprog, hpc]; rfl))
  iframe Hl
  inext
  iintro %s1 %hs1 _ _
  imodintro
  iintro Hl
  obtain ⟨hP1, hc1, hq1⟩ := LPstep_at hs1 hprog (by rw [hpc])
  have hvw' : lw ≤ (instrR (fencePost ws true true false true)).wVwNew := by
    simp only [instrR_vwNew, fence_vwNew, ite_true]; omega
  iapply (lk_rel1b_amo g M tk h hh hdd s1 (instrR (fencePost ws true true false true)) _ ev lo lw
    ⟨hP1, hq1, hc1, by rw [LPstep_rd hs1 10 (.inr rfl), h10], by rw [LPstep_rd hs1 11 (.inr rfl), h11]⟩
    hlo hvw')
  iframe Hctx Hbag Hc HQ Hl

/-! ## 3. `addi`, `sd`: the store moves the points-to -/

/-- `pc = 5..6`: `addi t2,t2,1; sd t2,(a1)`, then the release.  `ex` is the counter message a dooming read took out of
the bag (`0`: none, the read was clean). -/
theorem lk_cs2_1b (g : AGN) (M : List PMsg) (tk : Nat → GName) (h : Nat) (hh : h < 2) (hdd : g.dd = ddL M)
    (s : LP) (ws : PState) (pr : GSet Nat) (ev0 : Trace) (tvs1 : List (Nat × BitVec 8)) (lo lw ex : Nat)
    (hs : s.prog = b1b ∧ s.q = [] ∧ s.pc = 5 ∧ s.rd 10 = X ∧ s.rd 11 = Y)
    (hlo : lo ≤ coh ws Lk) (hnoC : noC ev0) (hlw : lw = 0 ∨ isC M lw = true) :
    lkCtx (GF := GF) g M tk ∗ obag g M tk h lo 0 ∗ ([∗list] t ∈ cBagX M lw ex, pend g t) ∗
      (⌜ex = 0 ∧ (∀ p ∈ tvs1, p.1 = lw) ∧ lw ≤ coh ws Ct⌝ ∨
        (dshot g ∗ ⌜lw < ex ∧ ∃ j : Nat, j < 8 ∧ ex ≤ coh ws (Ct + j)⌝)) ∗
      lhA g Proto.triv (wL1b M h) (qsLk M h) ws pr (ev0 ++ [(LLoad false false Ct tvs1 (srcR 11), none)]) ⊢
      wpKA g Proto.triv (wL1b M h) (qsLk M) s (ΦL g M) := by
  obtain ⟨hprog, hq, hpc, h10, h11⟩ := hs
  have hw := litW_x xs1b imgL M h
  have hX := p1b_at hprog
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
    (litAg_x hq1 (p1b_at hP1) (by rw [hc1]; rfl) rfl) hq1 (by rw [hP1, hc1]; rfl)
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
  iapply (lk_rel1b g M tk h hh hdd s2 _ _ _ lo ts ⟨hP2, hq2, by rw [hc2], e10', e11'⟩ hlo' hvw')
  iframe Hctx Hbag HQ Hl
  unfold cPts
  iframe Hb
  ipureintro; exact .inr hC

/-! ## 4. The critical section's load -/

/-- **THE CRITICAL SECTION** (`pc = 4`, `ld t2,(a1)`) and the rest: the owned read of the counter (R-a1). -/
theorem lk_cs1b (g : AGN) (M : List PMsg) (tk : Nat → GName) (h : Nat) (hh : h < 2) (hdd : g.dd = ddL M)
    (s : LP) (ws : PState) (pr : GSet Nat) (ev : Trace) (lo lw : Nat)
    (hs : s.prog = b1b ∧ s.q = [] ∧ s.pc = 4 ∧ s.rd 10 = X ∧ s.rd 11 = Y)
    (hlo : lo ≤ coh ws Lk) (hvr : lw ≤ ws.wVrNew) (hnoC : noC ev) :
    lkCtx (GF := GF) g M tk ∗ obag g M tk h lo 0 ∗ cPts g M lw ∗
      lhA g Proto.triv (wL1b M h) (qsLk M h) ws pr ev ⊢
      wpKA g Proto.triv (wL1b M h) (qsLk M) s (ΦL g M) := by
  obtain ⟨hprog, hq, hpc, h10, h11⟩ := hs
  have hw := litW_x xs1b imgL M h
  have hX := p1b_at hprog
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
    iapply (lk_cs2_1b g M tk h hh hdd s1 _ _ ev tvs1 lo lw ex ⟨hP1, hq1, by rw [hc1], e10, e11⟩ hlo' hnoC hlw)
    iframe Hctx Hbag Hb Hl
    simp only [hq7]
    iexact Hm
  · ihave Hfree := lk_free1b (GF := GF) g M h hh hdd
    have hfr : frS1b s1 := ⟨hP1, hq1, by rw [hc1]; decide, by rw [hc1]; decide, e10, e11⟩
    iapply Hfree $$ %s1 %_ %_ %_ %hfr Hf Hd Hl


end cs

section loop

variable {GF : BundledGFunctors} [GhostVarG GF HSt] [GhostVarG GF Bool] [TokenG GF] [InvGS GF]

/-- The hart's state at the loop head. -/
def lhS1b (s : LP) : Prop :=
  s.prog = b1b ∧ s.q = [] ∧ s.pc = 1 ∧ s.rd 5 = 1 ∧ s.rd 10 = X ∧ s.rd 11 = Y ∧ s.regs.length = 32

/-- **THE SPIN LOOP** of (1b) (Löb induction at the loop head `again:`); the claim at `fence r,rw`. -/
theorem lk_loop1b (g : AGN) (M : List PMsg) (tk : Nat → GName) (h : Nat) (hh : h < 2) (hdd : g.dd = ddL M) :
    ⊢ ∀ (s : LP) (ws : PState) (pr : GSet Nat) (ev : Trace) (lo : Nat), ⌜lhS1b s⌝ -∗
      ⌜lo ≤ coh ws Lk ∧ noC ev⌝ -∗ lkCtx (GF := GF) g M tk -∗ obag g M tk h lo 0 -∗
      lhA g Proto.triv (wL1b M h) (qsLk M h) ws pr ev -∗ wpKA g Proto.triv (wL1b M h) (qsLk M) s (ΦL g M) := by
  have hw := litW_x xs1b imgL M h
  iloeb as IH
  iintro %s %ws %pr %ev %lo %hs %hl0 #Hctx Hbag Hl
  obtain ⟨hprog, hq, hpc, h5, h10, h11, hlen⟩ := hs
  obtain ⟨hlo, hnoC⟩ := hl0
  have hX := p1b_at hprog
  iapply (wpKA_amo (base := Lk) hw (litAg_x hq hX (by rw [hpc]; rfl) rfl) hq (by rw [hprog, hpc]; rfl)
    (by rw [h10]; decide) (by rw [h10]))
  iframe Hl
  inext
  iintro %tvs %ts %hlen4 %_ %hmsg %hlo1 %hex %hcoh %_ _ _
  have hd1 : amoD .swap 4 (s.rd 5) tvs = toBytes 1 4 := by rw [amoD_swap, h5]
  have hlenD : (amoD .swap 4 (s.rd 5) tvs).length = 4 := by rw [hd1]; rfl
  rw [hd1] at hmsg
  rw [hlenD] at hcoh
  have hcohB : ∀ j : Nat, j < 4 → coh (loadRun ws false false (srcsView ws (srcR 10)) Lk tvs) (Lk + j) < ts :=
    fun j hj => cohBelow_at hcoh hj
  have hc0 : coh (loadRun ws false false (srcsView ws (srcR 10)) Lk tvs) Lk < ts := by
    simpa using hcohB 0 (by decide)
  have hcm := (loadRun_mono ws false false (srcsView ws (srcR 10)) Lk tvs).2.2.2.2.2.2.2.2.2.2.1 Lk
  have hts1 : 1 ≤ ts := by omega
  obtain ⟨hA, hbyH⟩ := isA_of_msg hh hts1 hmsg
  have hmt : msgAt M ts = some ⟨Lk, toBytes 1 4, some h, .excl⟩ := by
    obtain ⟨k, rfl⟩ : ∃ k, ts = k + 1 := ⟨ts - 1, by omega⟩
    simpa [msgAt] using hmsg
  have htsM := msgAt_le hmt
  have hlots : lo < ts := by omega
  -- the acquire message's `pend` and token
  unfold obag
  icases Hbag with ⟨HbA, HbL⟩
  unfold bagA
  icases bsl_filter_take (pend g) (fun t => decide (lo < t) && decide (t ≠ 0) && isA M t && byH M h t)
    (fun t => decide (lo < t) && decide (t ≠ ts) && isA M t && byH M h t) ts (by simp [hlots, hA, hbyH]; omega)
    (fun t ht => by
      simp only [Bool.and_eq_true, decide_eq_true_eq] at ht ⊢
      exact ⟨⟨⟨⟨ht.1.1.1, by omega⟩, ht.1.2⟩, ht.2⟩, ht.1.1.2⟩) (rng M) (mem_rng.2 htsM) (nodup_rng M)
    $$ HbA with ⟨Hp, HbA⟩
  unfold bagL
  icases bsl_filter_take (fun t => token (tk t))
    (fun t => decide (lo < t) && decide (t ≠ 0) && (isA M t || isR M t) && byH M h t)
    (fun t => decide (lo < t) && decide (t ≠ ts) && (isA M t || isR M t) && byH M h t) ts
    (by simp [hlots, hA, hbyH]; omega)
    (fun t ht => by
      simp only [Bool.and_eq_true, decide_eq_true_eq] at ht ⊢
      exact ⟨⟨⟨⟨ht.1.1.1, by omega⟩, ht.1.2⟩, ht.2⟩, ht.1.1.2⟩) (rng M) (mem_rng.2 htsM) (nodup_rng M)
    $$ HbL with ⟨Ht, HbL⟩
  imod shoot $$ Hp with #Hsh
  imodintro
  isplitr
  · ileft; ipureintro
    exact ⟨⟨0, grd_intro (qLk_noC (noC_snoc hnoC (rmw_nonC _ _ _ _ _ _ _)))⟩, grd_intro trivial⟩
  isplitr
  · unfold fulT; ileft; iexact Hsh
  iintro %s1 %hs1 _ _
  imodintro
  iintro Hl
  obtain ⟨hP1, hc1, hq1⟩ := LPstep_at hs1 hprog (by rw [hpc])
  have e10 : s1.rd 10 = X := by rw [LPstep_rd hs1 10 (.inl (by decide)), h10]
  have e11 : s1.rd 11 = Y := by rw [LPstep_rd hs1 11 (.inl (by decide)), h11]
  have hlen1 : s1.regs.length = 32 := hs1.2.2.2.1.trans hlen
  have e5 := LPstep_rd_eq hs1 (by decide) (by omega)
  -- `fence r,rw`: the frontier covers `ts` (the AMO put `vrOld ≥ ts`), THE CLAIM
  iapply (wpKA_fence hw (litAg_x hq1 (p1b_at hP1) (by rw [hc1]; rfl) rfl) hq1 (by rw [hP1, hc1]; rfl))
  iframe Hl
  inext
  iintro %s2 %hs2 #Hfr _
  obtain ⟨hP2, hc2, hq2⟩ := LPstep_at hs2 hP1 (by rw [hc1])
  have f10 : s2.rd 10 = X := by rw [LPstep_rd hs2 10 (.inr rfl), e10]
  have f11 : s2.rd 11 = Y := by rw [LPstep_rd hs2 11 (.inr rfl), e11]
  have f5 : s2.rd 5 = s1.rd 5 := LPstep_rd hs2 5 (.inr rfl)
  have hlen2 : s2.regs.length = 32 := hs2.2.2.2.1.trans hlen1
  have hts_f : ts ≤ wfr (fencePost (qPosts (amoPost (storeRun (loadRun ws false false (srcsView ws (srcR 10)) Lk tvs) false (srcsView ws (srcR 10)) ts Lk (amoD .swap 4 (s.rd 5) tvs).length ts) false ts) (regWL 5 [.DLdRes] ++ [LInstr])) true false true true) := by
    show ts ≤ stFloor _
    unfold stFloor
    simp only [regWL, show (5 : Nat) ≠ 0 by decide, if_false, List.singleton_append, qPosts, qPost,
      fence_vwNew, if_true, instrR_vrOld, regWP_vrOld, amoPost_vrOld, Bool.false_eq_true]
    omega
  have hsrc : bytesAll (fun x u _ => u ≤ coh (loadRun ws false false (srcsView ws (srcR 10)) Lk tvs) x) Lk tvs :=
    bytesAll_mono (fun _ _ _ hh => hh.2) _ _
      (loadBytes_coh false (ldPre ws false false (srcsView ws (srcR 10))) ws Lk tvs).2
  have hwts : wrB M Lk ts := by
    refine ⟨_, hmt, ?_⟩
    have := byteAt_off (m := ⟨Lk, toBytes 1 4, some h, .excl⟩) (p := Lk) (k := 0) rfl
    rw [show Lk + ((0 : Nat) : Int) = Lk by simp] at this
    rw [this]; rfl
  have hcs0 := storeRun_coh0 (loadRun ws false false (srcsView ws (srcR 10)) Lk tvs) false (srcsView ws (srcR 10))
    ts Lk (amoD .swap 4 (s.rd 5) tvs).length ts (by rw [hlenD]; decide)
  have hcs : ts ≤ coh (instrR (ctrlP (instrR (fencePost (qPosts (amoPost (storeRun (loadRun ws false false (srcsView ws (srcR 10)) Lk tvs) false (srcsView ws (srcR 10)) ts Lk (amoD .swap 4 (s.rd 5) tvs).length ts) false ts) (regWL 5 [.DLdRes] ++ [LInstr])) true false true true)) (srcR 5 ++ srcR 0))) Lk := hcs0
  imod lk_acq g M tk h hdd (π := Proto.triv) (ws := ws) (ws1 := fencePost (qPosts (amoPost (storeRun (loadRun ws false false (srcsView ws (srcR 10)) Lk tvs) false (srcsView ws (srcR 10)) ts Lk (amoD .swap 4 (s.rd 5) tvs).length ts) false ts) (regWL 5 [.DLdRes] ++ [LInstr])) true false true true) hlen4 hlo1 hex
    hsrc hcohB hlo hts_f hwts $$ [HbA HbL Ht] with (⟨#Hf, #Hd⟩ | ⟨Hbag, %hv⟩ | ⟨Hbag, %hv, %lw, %hlw, Hc⟩)
  · iframe Hctx Hfr Ht; unfold obag bagA bagL; iframe HbA HbL
  all_goals imodintro
  all_goals iintro Hl
  · -- free mode
    ihave Hfree := lk_free1b (GF := GF) g M h hh hdd
    have hfr : frS1b s2 := ⟨hP2, hq2, by rw [hc2]; decide, by rw [hc2]; decide, f10, f11⟩
    iapply Hfree $$ %s2 %_ %_ %_ %hfr Hf Hd Hl
  · -- held: back to the loop head
    have e5' : s2.rd 5 = 1 := by rw [f5, e5, hv]; decide
    iapply (wpKA_brx (Xs := xs1b) hw (xAg_x xs1b imgL M h s2) hq2 (p1b_at hP2) (by rw [hc2]; rfl)
      (by rw [hP2]; decide))
    iframe Hl
    inext
    iintro %s3 %hs3 _ _
    imodintro
    iintro Hl
    have hbr : (if Weak.Prom.Ref.brEval .ne (s2.rd 5) (s2.rd 0) then 1 else s2.pc + 1) = 1 := by
      rw [e5']; rfl
    rw [hbr] at hs3
    obtain ⟨hP3, hc3, hq3⟩ := LPstep_at hs3 hP2 rfl
    have hls : lhS1b s3 := ⟨hP3, hq3, hc3, by rw [LPstep_rd hs3 5 (.inr rfl), e5'],
      by rw [LPstep_rd hs3 10 (.inr rfl), f10], by rw [LPstep_rd hs3 11 (.inr rfl), f11],
      hs3.2.2.2.1.trans hlen2⟩
    iapply IH $$ %s3 %_ %_ %_ %ts %hls %⟨hcs, noC_snoc hnoC (rmw_nonC _ _ _ _ _ _ _)⟩ Hctx [Hbag] Hl
    unfold obag bagA bagL
    icases Hbag with ⟨HbA, HbL⟩
    isplitl [HbA]
    · iapply bsl_filter_mono (pend g) _ _ (fun t ht => by
        simp only [Bool.and_eq_true, decide_eq_true_eq] at ht ⊢
        exact ⟨⟨⟨by omega, by omega⟩, ht.1.2⟩, ht.2⟩) (rng M) $$ HbA
    · iapply bsl_filter_mono (fun t => token (tk t)) _ _ (fun t ht => by
        simp only [Bool.and_eq_true, decide_eq_true_eq] at ht ⊢
        exact ⟨⟨⟨by omega, by omega⟩, ht.1.2⟩, ht.2⟩) (rng M) $$ HbL
  · -- acquired: the critical section
    have e5' : s2.rd 5 = 0 := by rw [f5, e5, hv]; decide
    iapply (wpKA_brx (Xs := xs1b) hw (xAg_x xs1b imgL M h s2) hq2 (p1b_at hP2) (by rw [hc2]; rfl)
      (by rw [hP2]; decide))
    iframe Hl
    inext
    iintro %s3 %hs3 _ _
    imodintro
    iintro Hl
    have hbr : (if Weak.Prom.Ref.brEval .ne (s2.rd 5) (s2.rd 0) then 1 else s2.pc + 1) = 4 := by
      rw [e5', hc2]; rfl
    rw [hbr] at hs3
    obtain ⟨hP3, hc3, hq3⟩ := LPstep_at hs3 hP2 rfl
    have hvr : lw ≤ (instrR (ctrlP (instrR (fencePost (qPosts (amoPost (storeRun (loadRun ws false false (srcsView ws (srcR 10)) Lk tvs) false (srcsView ws (srcR 10)) ts Lk (amoD .swap 4 (s.rd 5) tvs).length ts) false ts) (regWL 5 [.DLdRes] ++ [LInstr])) true false true true)) (srcR 5 ++ srcR 0))).wVrNew := by
      simp only [regWL, show (5 : Nat) ≠ 0 by decide, if_false, List.singleton_append, qPosts, qPost,
        instrR_vrNew, ctrlP_vrNew, fence_vrNew, if_true, instrR_vrOld, regWP_vrOld, amoPost_vrOld,
        Bool.false_eq_true]
      omega
    iapply (lk_cs1b g M tk h hh hdd s3 _ _ _ ts lw
      ⟨hP3, hq3, hc3, by rw [LPstep_rd hs3 10 (.inr rfl), f10], by rw [LPstep_rd hs3 11 (.inr rfl), f11]⟩
      hcs hvr (noC_snoc hnoC (rmw_nonC _ _ _ _ _ _ _)))
    iframe Hctx Hc Hl
    unfold obag bagA bagL
    icases Hbag with ⟨HbA, HbL⟩
    isplitl [HbA]
    · iapply bsl_filter_mono (pend g) _ _ (fun t ht => by
        simp only [Bool.and_eq_true, decide_eq_true_eq] at ht ⊢
        exact ⟨⟨⟨by omega, by omega⟩, ht.1.2⟩, ht.2⟩) (rng M) $$ HbA
    · iapply bsl_filter_mono (fun t => token (tk t)) _ _ (fun t ht => by
        simp only [Bool.and_eq_true, decide_eq_true_eq] at ht ⊢
        exact ⟨⟨⟨by omega, by omega⟩, ht.1.2⟩, ht.2⟩) (rng M) $$ HbL

/-- **A HART** of (1b): `li t0, 1`, then the spin loop. -/
theorem lk_hart1b (g : AGN) (M : List PMsg) (tk : Nat → GName) (h : Nat) (hh : h < 2) (hdd : g.dd = ddL M)
    (s0 : LP) {P0 : GSet Nat} (hprog : s0.prog = b1b) (hpc : s0.pc = 0) (hq : s0.q = [])
    (hlen : s0.regs.length = 32) (h10 : s0.rd 10 = X) (h11 : s0.rd 11 = Y) :
    lkCtx (GF := GF) g M tk ∗ obag g M tk h 0 0 ∗ lhA g Proto.triv (wL1b M h) (qsLk M h) psInit P0 [] ⊢
      wpKA g Proto.triv (wL1b M h) (qsLk M) s0 (ΦL g M) := by
  have hw := litW_x xs1b imgL M h
  iintro ⟨#Hctx, Hbag, Hl⟩
  iapply (wpKA_alui hw (litAg_x hq (p1b_at hprog) (by rw [hpc]; rfl) rfl) hq (by rw [hprog, hpc]; rfl)
    (by decide))
  iframe Hl
  inext
  iintro %s1 %hs1 _ _
  imodintro
  iintro Hl
  obtain ⟨hP1, hc1, hq1⟩ := LPstep_at hs1 hprog (by rw [hpc])
  have hls : lhS1b s1 := ⟨hP1, hq1, hc1, li_val hs1 (by decide) (by omega) (by decide),
    by rw [LPstep_rd hs1 10 (.inl (by decide)), h10], by rw [LPstep_rd hs1 11 (.inl (by decide)), h11],
    hs1.2.2.2.1.trans hlen⟩
  ihave Hloop := lk_loop1b (GF := GF) g M tk h hh hdd
  iapply Hloop $$ %s1 %_ %_ %_ %0 %hls %⟨Nat.zero_le _, noC_nil⟩ Hctx Hbag Hl

end loop

/-! ## The verdict -/

theorem progs_1b : ∃ p0 p1 : LP, progs t1b = [p0, p1] := ⟨_, _, rfl⟩

/-- THE ADEQUACY PREMISE for (1b). -/
theorem lk_premise1b (M : List PMsg) :
    wpPremise .hasLC ownGF (xStep xs1b) litDone imgL M (progs t1b) Proto.triv (fun _ _ => True)
      (fun h => ΨK M (qsLk M h)) (ddL M) := by
  intro Hinv g P0 hn hm hdd hP0
  obtain ⟨p0, p1, hps⟩ := progs_1b
  have hg0 : (progs t1b)[0]? = some p0 := by rw [hps]; rfl
  have hg1 : (progs t1b)[1]? = some p1 := by rw [hps]; rfl
  obtain ⟨hpr0, hpc0, hq0, hl0, hrd0⟩ := progs_get hg0
  obtain ⟨hpr1, hpc1, hq1, hl1, hrd1⟩ := progs_get hg1
  have hlen : g.hn.length = 2 := by rw [hn, hps]; rfl
  obtain ⟨γ0, γ1, hgn⟩ : ∃ a b, g.hn = [a, b] := by
    match h : g.hn, hlen with
    | [a, b], _ => exact ⟨a, b, rfl⟩
  rw [hps]
  iintro #Hdoom Hh Hp
  imod lk_setup g M hm $$ [Hp] with ⟨%tk, #Hctx, Hb0, Hb1⟩
  · iframe Hdoom Hp
  have k0 := lk_hart1b (GF := ownGF) g M tk 0 (by decide) hdd p0 (P0 := P0 0) hpr0 hpc0 hq0 hl0
    (by rw [hrd0 10 (by decide) (by decide)]; rfl) (by rw [hrd0 11 (by decide) (by decide)]; rfl)
  have k1 := lk_hart1b (GF := ownGF) g M tk 1 (by decide) hdd p1 (P0 := P0 1) hpr1 hpc1 hq1 hl1
    (by rw [hrd1 10 (by decide) (by decide)]; rfl) (by rw [hrd1 11 (by decide) (by decide)]; rfl)
  have k0' : lkCtx (GF := ownGF) g M tk ∗ obag g M tk 0 0 0 ∗
      lhA g Proto.triv (wL1b M 0) (qsLk M 0) psInit (P0 0) [] ⊢
      wpA (hlc := .hasLC) g Proto.triv (hw (xStep xs1b) litDone imgL M 0) (fun h => ΨK M (qsLk M h)) p0
        (fun v => iprop(⌜∃ V, grd Proto.triv imgL M V ((fun (_ : Nat) (_ : Unit) => True) 0 v)⌝ ∨ dshot g)) := k0
  have k1' : lkCtx (GF := ownGF) g M tk ∗ obag g M tk 1 0 0 ∗
      lhA g Proto.triv (wL1b M 1) (qsLk M 1) psInit (P0 1) [] ⊢
      wpA (hlc := .hasLC) g Proto.triv (hw (xStep xs1b) litDone imgL M (0 + 1)) (fun h => ΨK M (qsLk M h)) p1
        (fun v => iprop(⌜∃ V, grd Proto.triv imgL M V ((fun (_ : Nat) (_ : Unit) => True) (0 + 1) v)⌝ ∨
          dshot g)) := k1
  rw [hgn]
  icases (BigSepL.bigSepL_cons).1 $$ Hh with ⟨H0, Hh⟩
  icases (BigSepL.bigSepL_cons).1 $$ Hh with ⟨H1, -⟩
  imodintro
  have s0 := lhA_start (GF := ownGF) (g := g) (π := Proto.triv) (w := wL1b M 0) (Qs := qsLk M) (P0 := P0 0)
    (qLk_noC noC_nil)
  have s1 := lhA_start (GF := ownGF) (g := g) (π := Proto.triv) (w := wL1b M 1) (Qs := qsLk M) (P0 := P0 (0 + 1))
    (qLk_noC noC_nil)
  iapply (BigSepL.bigSepL_cons).2
  isplitl [H0 Hb0]
  · iapply k0'
    iframe Hctx Hb0
    iapply s0
    iexact H0
  iapply (BigSepL.bigSepL_cons).2
  isplitl [H1 Hb1]
  · iapply k1'
    iframe Hctx Hb1
    iapply s1
    iexact H1
  iapply (BigSepL.bigSepL_nil).2
  itrivial

/-- **G4 TARGET (1b) ON TRACK (a): THE SPINLOCK WITH FENCES (the manual's Example 2) AND A MUTUAL-EXCLUSION CLIENT**
(plan §4 G4 (1b)).  Over every final memory `M` and every valid run of machine v2 of two harts running `p1b`
(`li t0,1; again: amoswap.w.aq t0,t0,(a0); bnez t0,again; ld t2,(a1); addi t2,t2,1; sd t2,(a1);
amoswap.w.rl x0,x0,(a0)`), each hart's trace satisfies `qLk`: its critical section's load read, in every byte, the
latest counter message below its store (or the initial memory) — no counter write by anybody lies in between.
Proved in the logic (OwnALock*.lean): the lock's resource (the counter's points-to) moves through the release slots
and the image's slot, claimed by the unique AMO reading each release.  0 named inputs; finite runs (a hart may stop
anywhere in its spin loop; the prefix lemma S3d is separate, [OWN.P4]). -/
theorem own_lock1b (M : List PMsg) (run : PFRun LP Unit)
    (hrun : PF.validRun (xStep xs1b) imgL () (progs t1b) M run) : ∀ h, qLk M (run.trace h) := by
  obtain ⟨_, hΨ, _⟩ := adequacyA (hlc := .hasLC) (GF := ownGF) Proto.triv (fun _ _ => True)
    (fun h => ΨK M (qsLk M h)) (ddL M) trivial (fun h => ⟨qLk_noC noC_nil, wrOk_nil M⟩) (lk_premise1b M) hrun
  intro h
  have hq := (hΨ h (run.trace h).length).1
  rw [List.take_length] at hq
  exact qLk_of_memEv hq

/-- **MUTUAL EXCLUSION, ordered**: if hart `h`'s critical section loaded `tvs` and stored at `ts`, every counter
message `ts0 < ts` (another critical section's store, or any) is at or below the load's source in every byte — the
critical section that stores later READ the earlier one's write or a later one. -/
theorem own_lock1b_excl (M : List PMsg) (run : PFRun LP Unit)
    (hrun : PF.validRun (xStep xs1b) imgL () (progs t1b) M run) (h : Nat) (tvs : List (Nat × BitVec 8))
    (ts ts0 : Nat) (hl : ∃ e ∈ run.trace h, isCLd e tvs) (hs : ∃ e ∈ run.trace h, isCSt e ts)
    (hc : isC M ts0 = true) (hlt : ts0 < ts) : ∀ p ∈ tvs, ts0 ≤ p.1 := by
  obtain ⟨lw, hall, _, _, hno⟩ := own_lock1b M run hrun h tvs ts hl hs
  intro p hp
  rw [hall p hp]
  apply Classical.byContradiction; intro hne
  have := hno ts0 (by omega) hlt
  rw [hc] at this; cases this

#print axioms own_lock1b

end Weak.Prom.OA
