/-
Weak/Prom: **G4 target (1c) on track (a): xv6's EXACT acquire/release text, PROVED** (stage S4a part 3; plan rev 7
§4 G4 (1c); §3 "Release-class, defined precisely", "Acquire", "Atomicity", "The deposit", "Opening", R-a1).

`own_lock1c`: in every valid run of two harts running `p1c` (OwnALock1cDefs.lean: xv6's `acquire` spin loop
`mv a5,a4; amoswap.w.aq a5,a5,(s1); sext.w a5,a5; bnez a5,again; sd a0,16(s1)` and `release`
`sd zero,16(s1); fence rw,w; sw zero,0(s1)` around (1a)'s counter client) on machine v2 through the loop front end,
each hart's trace satisfies `qLk` (as (1a)).  `own_lock1c_excl`: the critical sections are ordered.
The proof (as (1a), OwnALock.lean): the spin loop by Löb induction (`lk_loop1c`); the aq AMO's claim at its own step
(`lk_acq` over (1c)'s classes); the cpu-field stores take their `pend`s from the lock resource's second bag
(`lk_cpu1`, `lk_cpu0`); the counter's critical section is (1b)'s; the PLAIN release `sw` deposits (`lk_rel1c`),
release-class through `fence rw,w`; dead reads put the run in free mode (`lk_free1c`).
Setup (`lk_setup`, plan R-a5): as (1a)'s, the cpu-field messages' `pend`s start in the image's slot.
0 named inputs; the runs are finite (the prefix lemma S3d is separate, [OWN.P4]).
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.OwnALock1cCS

namespace Weak.Prom.OA.C

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.PF Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Ref (Instr Test two64)
open Weak.Prom.Ref.Lit (X Y)
open PLabel
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode

section loop

variable {GF : BundledGFunctors} [GhostVarG GF HSt] [GhostVarG GF Bool] [TokenG GF] [InvGS GF]

/-- The hart's state at the loop head `again:` (`mv a5,a4`). -/
def lhS1c (s : LP) : Prop :=
  s.prog = b1c ∧ s.q = [] ∧ s.pc = 1 ∧ s.rd 14 = 1 ∧ s.rd 9 = X ∧ s.rd 11 = Y ∧ s.regs.length = 32

/-- **THE SPIN LOOP** of (1c) (Löb induction at `again:`): `mv a5,a4; amoswap.w.aq a5,a5,(s1); sext.w a5,a5;
bnez a5,again`; the claim at the AMO's step (aq: the frontier covers `ts`, plan §3 "Acquire"). -/
theorem lk_loop1c (g : AGN) (M : List PMsg) (tk : Nat → GName) (h : Nat) (hh : h < 2) (hdd : g.dd = ddL M) :
    ⊢ ∀ (s : LP) (ws : PState) (pr : GSet Nat) (ev : Trace) (lo : Nat), ⌜lhS1c s⌝ -∗
      ⌜lo ≤ coh ws Lk ∧ noC ev⌝ -∗ lkCtx (GF := GF) g M tk -∗ obag g M tk h lo 0 -∗
      lhA g Proto.triv (wL1c M h) (qsLk M h) ws pr ev -∗ wpKA g Proto.triv (wL1c M h) (qsLk M) s (ΦL g M) := by
  have hw := litW_x xs1c imgL M h
  iloeb as IH
  iintro %s0 %ws0 %pr0 %ev %lo %hs %hl0 #Hctx Hbag Hl
  obtain ⟨hprog0, hq0, hpc0, h14, h9_0, h11_0, hlen0⟩ := hs
  obtain ⟨hlo0, hnoC⟩ := hl0
  -- `mv a5,a4`
  iapply (wpKA_alu hw (litAg_x hq0 (p1c_at hprog0) (by rw [hpc0]; rfl) rfl) hq0 (by rw [hprog0, hpc0]; rfl)
    (by decide))
  iframe Hl
  inext
  iintro %s %hsA _ _
  imodintro
  iintro Hl
  obtain ⟨hprog, hpc, hq⟩ := LPstep_at hsA hprog0 (by rw [hpc0])
  have h9 : s.rd 9 = X := by rw [LPstep_rd hsA 9 (.inl (by decide)), h9_0]
  have h11 : s.rd 11 = Y := by rw [LPstep_rd hsA 11 (.inl (by decide)), h11_0]
  have h14' : s.rd 14 = 1 := by rw [LPstep_rd hsA 14 (.inl (by decide)), h14]
  have hlen : s.regs.length = 32 := hsA.2.2.2.1.trans hlen0
  have h15 : s.rd 15 = 1 := by
    have e := LPstep_rd_eq hsA (by decide) (by omega)
    have h0 : s0.rd 0 = 0 := rfl
    rw [e, h0, h14]; decide
  have hlo : lo ≤ coh (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) Lk := hlo0
  have hX := p1c_at hprog
  -- `amoswap.w.aq a5,a5,(s1)`
  iapply (wpKA_amo (base := Lk) hw (litAg_x hq hX (by rw [hpc]; rfl) rfl) hq (by rw [hprog, hpc]; rfl)
    (by rw [h9]; decide) (by rw [h9]))
  iframe Hl
  inext
  iintro %tvs %ts %hlen4 %_ %hmsg %hlo1 %hex %hcoh %_ _ _
  have hd1 : amoD .swap 4 (s.rd 15) tvs = toBytes 1 4 := by rw [amoD_swap, h15]
  have hlenD : (amoD .swap 4 (s.rd 15) tvs).length = 4 := by rw [hd1]; rfl
  rw [hd1] at hmsg
  rw [hlenD] at hcoh
  have hcohB : ∀ j : Nat, j < 4 → coh (loadRun (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) true false
      (srcsView (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) (srcR 9)) Lk tvs) (Lk + j) < ts :=
    fun j hj => cohBelow_at hcoh hj
  have hc0 : coh (loadRun (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) true false
      (srcsView (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) (srcR 9)) Lk tvs) Lk < ts := by
    simpa using hcohB 0 (by decide)
  have hcm := (loadRun_mono (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) true false
    (srcsView (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) (srcR 9)) Lk tvs).2.2.2.2.2.2.2.2.2.2.1 Lk
  have hts1 : 1 ≤ ts := by omega
  obtain ⟨hA, hbyH⟩ := isA_of_msg hh hts1 hmsg
  have hmt := msgAt_of hts1 hmsg
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
  iintro %s1 %hs1 #Hfr _
  -- the frontier covers `ts` (aq: `vwNew ≥ ts`)
  have hts_f : ts ≤ wfr (qPosts (amoPost (storeRun (loadRun (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) true false
      (srcsView (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) (srcR 9)) Lk tvs) false
      (srcsView (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) (srcR 9)) ts Lk (amoD .swap 4 (s.rd 15) tvs).length ts)
      true ts) (regWL 15 [.DLdRes] ++ [LInstr]).dropLast) := by
    show ts ≤ stFloor _
    unfold stFloor
    simp only [regWL, show (15 : Nat) ≠ 0 by decide, if_false, List.singleton_append, List.dropLast, qPosts, qPost,
      regWP_vwNew, amoPost_vwNew, if_true]
    omega
  have hsrc : bytesAll (fun x u _ => u ≤ coh (loadRun (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) true false
      (srcsView (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) (srcR 9)) Lk tvs) x) Lk tvs :=
    bytesAll_mono (fun _ _ _ hh => hh.2) _ _
      (loadBytes_coh true (ldPre (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) true false
        (srcsView (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) (srcR 9))) (instrR (regWP ws0 15 (srcR 0 ++ srcR 14)))
        Lk tvs).2
  have hwts : wrB M Lk ts := by
    refine ⟨_, hmt, ?_⟩
    have := byteAt_off (m := ⟨Lk, toBytes 1 4, some h, .excl⟩) (p := Lk) (k := 0) rfl
    rw [show Lk + ((0 : Nat) : Int) = Lk by simp] at this
    rw [this]; rfl
  obtain ⟨hP1, hc1, hq1⟩ := LPstep_at hs1 hprog (by rw [hpc])
  have e9 : s1.rd 9 = X := by rw [LPstep_rd hs1 9 (.inl (by decide)), h9]
  have e11 : s1.rd 11 = Y := by rw [LPstep_rd hs1 11 (.inl (by decide)), h11]
  have e14 : s1.rd 14 = 1 := by rw [LPstep_rd hs1 14 (.inl (by decide)), h14']
  have hlen1 : s1.regs.length = 32 := hs1.2.2.2.1.trans hlen
  have e15 := LPstep_rd_eq hs1 (by decide) (by omega)
  have hcs0 := storeRun_coh0 (loadRun (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) true false
    (srcsView (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) (srcR 9)) Lk tvs) false
    (srcsView (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) (srcR 9))
    ts Lk (amoD .swap 4 (s.rd 15) tvs).length ts (by rw [hlenD]; decide)
  have hcs : ts ≤ coh (instrR (ctrlP (instrR (regWP (qPosts (amoPost (storeRun (loadRun
      (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) true false
      (srcsView (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) (srcR 9)) Lk tvs) false
      (srcsView (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) (srcR 9)) ts Lk (amoD .swap 4 (s.rd 15) tvs).length ts)
      true ts) (regWL 15 [.DLdRes] ++ [LInstr])) 15 (srcR 15))) (srcR 15 ++ srcR 0))) Lk := hcs0
  imod lk_acq g M tk h hdd (π := Proto.triv) (ws := instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) hlen4 hlo1 hex hsrc
    hcohB hlo hts_f hwts $$ [HbA HbL Ht] with (⟨#Hf, #Hd⟩ | ⟨Hbag, %hv⟩ | ⟨Hbag, %hv, %s0r, %hs0r, HR⟩)
  · iframe Hctx Hfr Ht; unfold obag bagA bagL; iframe HbA HbL
  all_goals imodintro
  all_goals iintro Hl
  · -- free mode
    ihave Hfree := lk_free1c (GF := GF) g M h hh hdd
    have hfr : frS1c s1 := ⟨hP1, hq1, by rw [hc1]; decide, by rw [hc1]; decide, e9, e11⟩
    iapply Hfree $$ %s1 %_ %_ %_ %hfr Hf Hd Hl
  · -- held: `sext.w`, `bnez` back to the loop head
    iapply (wpKA_addiw (Xs := xs1c) hw (xAg_x xs1c imgL M h s1) hq1 (p1c_at hP1) (by rw [hc1]; rfl) (by decide))
    iframe Hl
    inext
    iintro %s2 %hs2 _ _
    imodintro
    iintro Hl
    obtain ⟨hP2, hc2, hq2⟩ := LPstep_at hs2 hP1 (by rw [hc1])
    have f15 : s2.rd 15 = 1 := by
      rw [LPstep_rd_eq hs2 (by decide) (by omega), e15, hv]; decide
    have f9 : s2.rd 9 = X := by rw [LPstep_rd hs2 9 (.inl (by decide)), e9]
    have f11 : s2.rd 11 = Y := by rw [LPstep_rd hs2 11 (.inl (by decide)), e11]
    have f14 : s2.rd 14 = 1 := by rw [LPstep_rd hs2 14 (.inl (by decide)), e14]
    have hlen2 : s2.regs.length = 32 := hs2.2.2.2.1.trans hlen1
    iapply (wpKA_brx (Xs := xs1c) hw (xAg_x xs1c imgL M h s2) hq2 (p1c_at hP2) (by rw [hc2]; rfl)
      (by rw [hP2]; decide))
    iframe Hl
    inext
    iintro %s3 %hs3 _ _
    imodintro
    iintro Hl
    have hbr : (if Weak.Prom.Ref.brEval .ne (s2.rd 15) (s2.rd 0) then 1 else s2.pc + 1) = 1 := by
      rw [f15]; rfl
    rw [hbr] at hs3
    obtain ⟨hP3, hc3, hq3⟩ := LPstep_at hs3 hP2 rfl
    have hls : lhS1c s3 := ⟨hP3, hq3, hc3, by rw [LPstep_rd hs3 14 (.inr rfl), f14],
      by rw [LPstep_rd hs3 9 (.inr rfl), f9], by rw [LPstep_rd hs3 11 (.inr rfl), f11],
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
  · -- acquired: `sext.w`, `bnez` falls through to `sd a0,16(s1)`
    iapply (wpKA_addiw (Xs := xs1c) hw (xAg_x xs1c imgL M h s1) hq1 (p1c_at hP1) (by rw [hc1]; rfl) (by decide))
    iframe Hl
    inext
    iintro %s2 %hs2 _ _
    imodintro
    iintro Hl
    obtain ⟨hP2, hc2, hq2⟩ := LPstep_at hs2 hP1 (by rw [hc1])
    have f15 : s2.rd 15 = 0 := by
      rw [LPstep_rd_eq hs2 (by decide) (by omega), e15, hv]; decide
    have f9 : s2.rd 9 = X := by rw [LPstep_rd hs2 9 (.inl (by decide)), e9]
    have f11 : s2.rd 11 = Y := by rw [LPstep_rd hs2 11 (.inl (by decide)), e11]
    iapply (wpKA_brx (Xs := xs1c) hw (xAg_x xs1c imgL M h s2) hq2 (p1c_at hP2) (by rw [hc2]; rfl)
      (by rw [hP2]; decide))
    iframe Hl
    inext
    iintro %s3 %hs3 _ _
    imodintro
    iintro Hl
    have hbr : (if Weak.Prom.Ref.brEval .ne (s2.rd 15) (s2.rd 0) then 1 else s2.pc + 1) = 5 := by
      rw [f15, hc2]; rfl
    rw [hbr] at hs3
    obtain ⟨hP3, hc3, hq3⟩ := LPstep_at hs3 hP2 rfl
    unfold Rs
    icases HR with ⟨⟨%lw, %hlw, Hc⟩, Hpp⟩
    have hvr : lw ≤ (instrR (ctrlP (instrR (regWP (qPosts (amoPost (storeRun (loadRun
        (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) true false
        (srcsView (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) (srcR 9)) Lk tvs) false
        (srcsView (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) (srcR 9)) ts Lk (amoD .swap 4 (s.rd 15) tvs).length ts)
        true ts) (regWL 15 [.DLdRes] ++ [LInstr])) 15 (srcR 15))) (srcR 15 ++ srcR 0))).wVrNew := by
      simp only [regWL, show (15 : Nat) ≠ 0 by decide, if_false, List.singleton_append, qPosts, qPost,
        instrR_vrNew, ctrlP_vrNew, regWP_vrNew, amoPost_vrNew, if_true]
      omega
    have hvw : s0r ≤ (instrR (ctrlP (instrR (regWP (qPosts (amoPost (storeRun (loadRun
        (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) true false
        (srcsView (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) (srcR 9)) Lk tvs) false
        (srcsView (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) (srcR 9)) ts Lk (amoD .swap 4 (s.rd 15) tvs).length ts)
        true ts) (regWL 15 [.DLdRes] ++ [LInstr])) 15 (srcR 15))) (srcR 15 ++ srcR 0))).wVwNew := by
      simp only [regWL, show (15 : Nat) ≠ 0 by decide, if_false, List.singleton_append, qPosts, qPost,
        instrR_vwNew, ctrlP_vwNew, regWP_vwNew, amoPost_vwNew, if_true]
      omega
    iapply (lk_cpu1 g M tk h hh hdd s3 _ _ _ ts lw s0r
      ⟨hP3, hq3, hc3, by rw [LPstep_rd hs3 9 (.inr rfl), f9], by rw [LPstep_rd hs3 11 (.inr rfl), f11]⟩
      hcs hvr hvw (noC_snoc hnoC (rmw_nonC _ _ _ _ _ _ _)))
    iframe Hctx Hc Hpp Hl
    unfold obag bagA bagL
    icases Hbag with ⟨HbA, HbL⟩
    isplitl [HbA]
    · iapply bsl_filter_mono (pend g) _ _ (fun t ht => by
        simp only [Bool.and_eq_true, decide_eq_true_eq] at ht ⊢
        exact ⟨⟨⟨by omega, by omega⟩, ht.1.2⟩, ht.2⟩) (rng M) $$ HbA
    · iapply bsl_filter_mono (fun t => token (tk t)) _ _ (fun t ht => by
        simp only [Bool.and_eq_true, decide_eq_true_eq] at ht ⊢
        exact ⟨⟨⟨by omega, by omega⟩, ht.1.2⟩, ht.2⟩) (rng M) $$ HbL

end loop

/-! ## The hart, the setup -/

section hart

variable {GF : BundledGFunctors} [GhostVarG GF HSt] [GhostVarG GF Bool] [TokenG GF] [InvGS GF]

/-- **A HART** of (1c): `li a4,1`, then the spin loop. -/
theorem lk_hart1c (g : AGN) (M : List PMsg) (tk : Nat → GName) (h : Nat) (hh : h < 2) (hdd : g.dd = ddL M)
    (s0 : LP) {P0 : GSet Nat} (hprog : s0.prog = b1c) (hpc : s0.pc = 0) (hq : s0.q = [])
    (hlen : s0.regs.length = 32) (h9 : s0.rd 9 = X) (h11 : s0.rd 11 = Y) :
    lkCtx (GF := GF) g M tk ∗ obag g M tk h 0 0 ∗ lhA g Proto.triv (wL1c M h) (qsLk M h) psInit P0 [] ⊢
      wpKA g Proto.triv (wL1c M h) (qsLk M) s0 (ΦL g M) := by
  have hw := litW_x xs1c imgL M h
  iintro ⟨#Hctx, Hbag, Hl⟩
  iapply (wpKA_alui hw (litAg_x hq (p1c_at hprog) (by rw [hpc]; rfl) rfl) hq (by rw [hprog, hpc]; rfl)
    (by decide))
  iframe Hl
  inext
  iintro %s1 %hs1 _ _
  imodintro
  iintro Hl
  obtain ⟨hP1, hc1, hq1⟩ := LPstep_at hs1 hprog (by rw [hpc])
  have hls : lhS1c s1 := ⟨hP1, hq1, hc1, li_val hs1 (by decide) (by omega) (by decide),
    by rw [LPstep_rd hs1 9 (.inl (by decide)), h9], by rw [LPstep_rd hs1 11 (.inl (by decide)), h11],
    hs1.2.2.2.1.trans hlen⟩
  ihave Hloop := lk_loop1c (GF := GF) g M tk h hh hdd
  iapply Hloop $$ %s1 %_ %_ %_ %0 %hls %⟨Nat.zero_le _, noC_nil⟩ Hctx Hbag Hl

/-- A release slot. -/
theorem rSlot_alloc (g : AGN) (M : List PMsg) (tk : Nat → GName) (r : Nat) :
    pend (GF := GF) g r ⊢ |={⊤}=> rSlot g M tk r := by
  iintro Hp
  unfold rSlot
  iapply inv_alloc
  inext; ileft; iexact Hp

/-- Hart `h`'s acquire messages. -/
def pA (M : List PMsg) (h t : Nat) : Bool := decide (0 < t) && decide (t ≠ 0) && isA M t && byH M h t
/-- Hart `h`'s lock messages. -/
def pL (M : List PMsg) (h t : Nat) : Bool := decide (0 < t) && decide (t ≠ 0) && (isA M t || isR M t) && byH M h t

theorem pA_10 {M : List PMsg} {t : Nat} (h1 : pA M 1 t = true) : pA M 0 t = false := by
  unfold pA at h1 ⊢
  cases h0 : byH M 0 t
  · simp
  · have := byH_01 h0
    rw [this] at h1; simp at h1

theorem pL_10 {M : List PMsg} {t : Nat} (h1 : pL M 1 t = true) : pL M 0 t = false := by
  unfold pL at h1 ⊢
  cases h0 : byH M 0 t
  · simp
  · have := byH_01 h0
    rw [this] at h1; simp at h1

/-- **THE SETUP** of (1c) (as (1a)'s, the cpu-field messages' `pend`s join the counter's in the image's slot; plan §3 "At adequacy start … for every index t in 1..|M|", R-a5): one token per message; acquire
messages' `pend`s to their authors' bags, release messages' to their slots, counter messages' to the counter's
points-to in the image's slot (the lock is born unlocked), the rest to dead invariants. -/
theorem lk_setup (g : AGN) (M : List PMsg) (hm : g.mn.length = M.length) :
    doomInv (GF := GF) g M ∗ ([∗list] k ↦ _x ∈ g.mn, pend g (k + 1)) ⊢
      |={⊤}=> ∃ tk, lkCtx g M tk ∗ obag g M tk 0 0 0 ∗ obag g M tk 1 0 0 := by
  iintro ⟨#Hdoom, Hp⟩
  have h0 : ([∗list] k ↦ _x ∈ g.mn, pend (GF := GF) g (k + 1)) ⊢ [∗list] t ∈ rng M, pend g t := by
    have := bsl_range (pend (GF := GF) g) g.mn 1; rw [hm] at this; exact this
  ihave Hp := h0 $$ Hp
  imod toks_alloc (GF := GF) (rng M) (nodup_rng M) with ⟨%tk, Ht⟩
  -- pends
  have s1 := bsl_filter_split (pend (GF := GF) g) (pA M 0) (rng M)
  have s2 := bsl_filter_split (pend (GF := GF) g) (pA M 1) ((rng M).filter (fun t => !pA M 0 t))
  rw [filter_filter_of (r := pA M 1) (fun t => by
      cases h1 : pA M 1 t
      · simp
      · rw [pA_10 h1]; rfl)] at s2
  rw [filter_filter_of (r := fun t => !pA M 0 t && !pA M 1 t) (fun t => rfl)] at s2
  have s3 := bsl_filter_split (pend (GF := GF) g) (isR M) ((rng M).filter (fun t => !pA M 0 t && !pA M 1 t))
  rw [filter_filter_of (r := isR M) (fun t => by
      cases hR : isR M t
      · simp
      · have e0 : pA M 0 t = false := by simp [pA, isR_A hR]
        have e1 : pA M 1 t = false := by simp [pA, isR_A hR]
        rw [e0, e1]; rfl)] at s3
  rw [filter_filter_of (r := fun t => !pA M 0 t && !pA M 1 t && !isR M t) (fun t => rfl)] at s3
  have s4 := bsl_filter_split (pend (GF := GF) g) (isC M)
    ((rng M).filter (fun t => !pA M 0 t && !pA M 1 t && !isR M t))
  rw [filter_filter_of (r := isC M) (fun t => by
      cases hC : isC M t
      · simp
      · have e0 : pA M 0 t = false := by simp [pA, (isC_A hC).1]
        have e1 : pA M 1 t = false := by simp [pA, (isC_A hC).1]
        rw [e0, e1, (isC_A hC).2]; rfl)] at s4
  rw [filter_filter_of (r := fun t => !pA M 0 t && !pA M 1 t && !isR M t && !isC M t) (fun t => rfl)] at s4
  have s5 := bsl_filter_split (pend (GF := GF) g) (isP M)
    ((rng M).filter (fun t => !pA M 0 t && !pA M 1 t && !isR M t && !isC M t))
  rw [filter_filter_of (r := isP M) (fun t => by
      cases hP : isP M t
      · simp
      · obtain ⟨hA, hR, hC⟩ := isP_A hP
        have e0 : pA M 0 t = false := by simp [pA, hA]
        have e1 : pA M 1 t = false := by simp [pA, hA]
        rw [e0, e1, hR, hC]; rfl)] at s5
  rw [filter_filter_of (r := fun t => !pA M 0 t && !pA M 1 t && !isR M t && !isC M t && !isP M t)
    (fun t => rfl)] at s5
  ihave ⟨HA0, Hp⟩ := s1 $$ Hp
  ihave ⟨HA1, Hp⟩ := s2 $$ Hp
  ihave ⟨HR, Hp⟩ := s3 $$ Hp
  ihave ⟨HC, Hp⟩ := s4 $$ Hp
  ihave ⟨HP, Hp⟩ := s5 $$ Hp
  ihave HJ := bsl_filter_mono (pend (GF := GF) g) _ (isJ M) (fun t hJ => by
    have hA : isA M t = false := by
      cases h : isA M t
      · rfl
      · unfold isJ isDd at hJ; rw [h, isA_L h] at hJ; simp at hJ
    have hR : isR M t = false := by
      cases h : isR M t
      · rfl
      · unfold isJ isDd at hJ; rw [h, isR_L h] at hJ; simp at hJ
    have hC : isC M t = false := by
      cases h : isC M t
      · rfl
      · unfold isJ isDd at hJ; rw [isC_L h, h] at hJ; simp at hJ
    have hP : isP M t = false := by
      cases h : isP M t
      · rfl
      · unfold isJ isDd at hJ; rw [isP_L h, h] at hJ; simp at hJ
    have e0 : pA M 0 t = false := by simp [pA, hA]
    have e1 : pA M 1 t = false := by simp [pA, hA]
    rw [e0, e1, hR, hC, hP]; rfl) (rng M) $$ Hp
  -- tokens
  have t1 := bsl_filter_split (fun t => token (GF := GF) (tk t)) (pL M 0) (rng M)
  ihave ⟨HL0, Ht⟩ := t1 $$ Ht
  ihave HL1 := bsl_filter_mono (fun t => token (GF := GF) (tk t)) _ (pL M 1) (fun t h1 => by
    rw [pL_10 h1]; rfl) (rng M) $$ Ht
  -- the invariants
  imod bsl_fupd (G := fun r => rSlot (GF := GF) g M tk r) (fun r => rSlot_alloc g M tk r) _ $$ HR with #Hrs
  imod bsl_fupd (G := fun t => deadInv (GF := GF) g t) (fun t => dead_alloc g t) _ $$ HJ with #Hdd
  imod inv_alloc (ndot lkN 0) ⊤ iprop(Rs (GF := GF) g M 0 ∨ nxtTok M tk 0) $$ [HC HP] with #Hi
  · inext; ileft; unfold Rs cPts pPts
    have hp0 : pBag M 0 = (rng M).filter (isP M) := by
      unfold pBag; refine List.filter_congr (fun t ht => ?_); have := rng_ge ht; simp [show 0 < t by omega]
    rw [hp0]
    iframe HP
    iexists 0
    isplitr
    · ipureintro; exact Nat.le_refl _
    isplitr
    · ipureintro; exact .inl rfl
    have hc0 : cBag M 0 = (rng M).filter (isC M) := by
      unfold cBag; refine List.filter_congr (fun t ht => ?_); have := rng_ge ht; simp [show 0 < t by omega]
    rw [hc0]; iexact HC
  imodintro
  iexists tk
  isplitr [HA0 HA1 HL0 HL1]
  · unfold lkCtx iSlot
    iframe Hdoom Hi Hrs Hdd
  have eA : ∀ h, bagA M h 0 0 = (rng M).filter (pA M h) := fun _ => rfl
  have eL : ∀ h, bagL M h 0 0 = (rng M).filter (pL M h) := fun _ => rfl
  isplitl [HA0 HL0]
  · unfold obag; rw [eA, eL]; iframe HA0 HL0
  · unfold obag; rw [eA, eL]; iframe HA1 HL1

end hart

/-! ## The verdict -/

theorem progs_1c : ∃ p0 p1 : LP, progs t1c = [p0, p1] := ⟨_, _, rfl⟩

/-- THE ADEQUACY PREMISE for (1b). -/
theorem lk_premise1c (M : List PMsg) :
    wpPremise .hasLC ownGF (xStep xs1c) litDone imgL M (progs t1c) Proto.triv (fun _ _ => True)
      (fun h => ΨK M (qsLk M h)) (ddL M) := by
  intro Hinv g P0 hn hm hdd hP0
  obtain ⟨p0, p1, hps⟩ := progs_1c
  have hg0 : (progs t1c)[0]? = some p0 := by rw [hps]; rfl
  have hg1 : (progs t1c)[1]? = some p1 := by rw [hps]; rfl
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
  have k0 := lk_hart1c (GF := ownGF) g M tk 0 (by decide) hdd p0 (P0 := P0 0) hpr0 hpc0 hq0 hl0
    (by rw [hrd0 9 (by decide) (by decide)]; rfl) (by rw [hrd0 11 (by decide) (by decide)]; rfl)
  have k1 := lk_hart1c (GF := ownGF) g M tk 1 (by decide) hdd p1 (P0 := P0 1) hpr1 hpc1 hq1 hl1
    (by rw [hrd1 9 (by decide) (by decide)]; rfl) (by rw [hrd1 11 (by decide) (by decide)]; rfl)
  have k0' : lkCtx (GF := ownGF) g M tk ∗ obag g M tk 0 0 0 ∗
      lhA g Proto.triv (wL1c M 0) (qsLk M 0) psInit (P0 0) [] ⊢
      wpA (hlc := .hasLC) g Proto.triv (hw (xStep xs1c) litDone imgL M 0) (fun h => ΨK M (qsLk M h)) p0
        (fun v => iprop(⌜∃ V, grd Proto.triv imgL M V ((fun (_ : Nat) (_ : Unit) => True) 0 v)⌝ ∨ dshot g)) := k0
  have k1' : lkCtx (GF := ownGF) g M tk ∗ obag g M tk 1 0 0 ∗
      lhA g Proto.triv (wL1c M 1) (qsLk M 1) psInit (P0 1) [] ⊢
      wpA (hlc := .hasLC) g Proto.triv (hw (xStep xs1c) litDone imgL M (0 + 1)) (fun h => ΨK M (qsLk M h)) p1
        (fun v => iprop(⌜∃ V, grd Proto.triv imgL M V ((fun (_ : Nat) (_ : Unit) => True) (0 + 1) v)⌝ ∨
          dshot g)) := k1
  rw [hgn]
  icases (BigSepL.bigSepL_cons).1 $$ Hh with ⟨H0, Hh⟩
  icases (BigSepL.bigSepL_cons).1 $$ Hh with ⟨H1, -⟩
  imodintro
  have s0 := lhA_start (GF := ownGF) (g := g) (π := Proto.triv) (w := wL1c M 0) (Qs := qsLk M) (P0 := P0 0)
    (qLk_noC noC_nil)
  have s1 := lhA_start (GF := ownGF) (g := g) (π := Proto.triv) (w := wL1c M 1) (Qs := qsLk M) (P0 := P0 (0 + 1))
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

/-- **G4 TARGET (1c) ON TRACK (a): xv6's EXACT ACQUIRE/RELEASE TEXT WITH A MUTUAL-EXCLUSION CLIENT** (plan §4 G4
(1c)).  Over every final memory `M` and every valid run of machine v2 of two harts running `p1c`
(`li a4,1; again: mv a5,a4; amoswap.w.aq a5,a5,(s1); sext.w a5,a5; bnez a5,again; sd a0,16(s1);
ld t2,(a1); addi t2,t2,1; sd t2,(a1); sd zero,16(s1); fence rw,w; sw zero,0(s1)` — Xv6/KernelImage.lean acquire
and release, `mycpu()`'s result in `a0`), each hart's trace satisfies `qLk`: its critical section's load read, in
every byte, the latest counter message below its store (or the initial memory) — no counter write by anybody lies in
between.  The release is a PLAIN store, release-class through `fence rw,w` (plan §3); the lock resource (the
counter's points-to and the cpu field's message bag) moves through the release slots, claimed by the unique AMO
reading each release.  0 named inputs; finite runs (a hart may stop anywhere in its spin loop; the prefix lemma S3d
is separate, [OWN.P4]). -/
theorem own_lock1c (M : List PMsg) (run : PFRun LP Unit)
    (hrun : PF.validRun (xStep xs1c) imgL () (progs t1c) M run) : ∀ h, qLk M (run.trace h) := by
  obtain ⟨_, hΨ, _⟩ := adequacyA (hlc := .hasLC) (GF := ownGF) Proto.triv (fun _ _ => True)
    (fun h => ΨK M (qsLk M h)) (ddL M) trivial (fun h => ⟨qLk_noC noC_nil, wrOk_nil M⟩) (lk_premise1c M) hrun
  intro h
  have hq := (hΨ h (run.trace h).length).1
  rw [List.take_length] at hq
  exact qLk_of_memEv hq

/-- **MUTUAL EXCLUSION, ordered**: if hart `h`'s critical section loaded `tvs` and stored at `ts`, every counter
message `ts0 < ts` (another critical section's store, or any) is at or below the load's source in every byte — the
critical section that stores later READ the earlier one's write or a later one. -/
theorem own_lock1c_excl (M : List PMsg) (run : PFRun LP Unit)
    (hrun : PF.validRun (xStep xs1c) imgL () (progs t1c) M run) (h : Nat) (tvs : List (Nat × BitVec 8))
    (ts ts0 : Nat) (hl : ∃ e ∈ run.trace h, isCLd e tvs) (hs : ∃ e ∈ run.trace h, isCSt e ts)
    (hc : isC M ts0 = true) (hlt : ts0 < ts) : ∀ p ∈ tvs, ts0 ≤ p.1 := by
  obtain ⟨lw, hall, _, _, hno⟩ := own_lock1c M run hrun h tvs ts hl hs
  intro p hp
  rw [hall p hp]
  apply Classical.byContradiction; intro hne
  have := hno ts0 (by omega) hlt
  rw [hc] at this; cases this

#print axioms own_lock1c
#print axioms own_lock1c_excl

end Weak.Prom.OA.C
