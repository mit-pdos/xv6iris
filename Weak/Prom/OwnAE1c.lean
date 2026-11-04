/-
Weak/Prom: **E-a, G4 (1c) WITH THE DEAD SET EMPTY, PROVED** (stage E-a; G4-review.md §6 condition 1; plan rev 7 §4 G4
(1c), §3 "Acquire", "Atomicity", "The deposit", "Opening", R-a1, R-a5).

`own_lock1cE`: the SAME verdict as `own_lock1c` (OwnALock1c.lean) — in every valid run of two harts running xv6's
exact acquire/release text around the counter client, each hart's trace satisfies `qLk` — proved through
`adequacyA` at `Dd := fun _ => False` (NO free mode, no `deadInv`), with protocol `π1c`.
Setup (`lk_setupE`, plan R-a5, per-byte owners): every message's `pend` goes to the owner of the bytes it touches —
lock-word messages to the lock (acquire AMOs to their authors' bags, release words to their slots, the rest to
`lkJunk`), counter messages (ANY shape and author) to the counter's points-to in the image's slot, cpu-field messages
to the cpu field's bag there; the rest stays with the boot owner, unused.
0 named inputs; finite runs (the prefix lemma S3d is separate, [OWN.P4]).
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.OwnAE1cCS

namespace Weak.Prom.OA.EC

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.PF Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Ref (Instr Test two64)
open Weak.Prom.Ref.Lit (X Y)
open Weak.Prom.OA.C (Pc p1c b1c t1c xs1c xOf_1c p1c_at wL1c msgAt_of wpKA_alu)
open Weak.Prom.OA.E
open PLabel
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode

section loop

variable {GF : BundledGFunctors} [GhostVarG GF HSt] [GhostVarG GF Bool] [TokenG GF] [InvGS GF]

/-- **THE SPIN LOOP** of (1c) (Löb induction at `again:`): `mv a5,a4; amoswap.w.aq a5,a5,(s1); sext.w a5,a5;
bnez a5,again`; the claim at the AMO's step (aq: the frontier covers `ts`, plan §3 "Acquire"). -/
theorem lk_loopE (g : AGN) (M : List PMsg) (tk : Nat → GName) (h : Nat) (hh : h < 2)
    (hdd : g.dd = fun _ => False) (hnoinv : ∀ t a, ¬ cmoAt M isInvalK t a) :
    ⊢ ∀ (s : LP) (ws : PState) (pr : GSet Nat) (ev : Trace) (lo : Nat), ⌜C.lhS1c s⌝ -∗
      ⌜lo ≤ coh ws Lk ∧ noC ev⌝ -∗ lkCtxE (GF := GF) g M tk -∗ C.obag g M tk h lo 0 -∗
      lhA g π1c (wL1c M h) (qsLk M h) ws pr ev -∗ wpKA g π1c (wL1c M h) (qsLk M) s (ΦE g M) := by
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
  obtain ⟨hA, hbyH⟩ := C.isA_of_msg hh hts1 hmsg
  have hmt := msgAt_of hts1 hmsg
  have htsM := msgAt_le hmt
  have hlots : lo < ts := by omega
  -- the acquire message's `pend` and token
  unfold C.obag
  icases Hbag with ⟨HbA, HbL⟩
  unfold C.bagA
  icases bsl_filter_take (pend g) (fun t => decide (lo < t) && decide (t ≠ 0) && C.isA M t && byH M h t)
    (fun t => decide (lo < t) && decide (t ≠ ts) && C.isA M t && byH M h t) ts (by simp [hlots, hA, hbyH]; omega)
    (fun t ht => by
      simp only [Bool.and_eq_true, decide_eq_true_eq] at ht ⊢
      exact ⟨⟨⟨⟨ht.1.1.1, by omega⟩, ht.1.2⟩, ht.2⟩, ht.1.1.2⟩) (rng M) (mem_rng.2 htsM) (nodup_rng M)
    $$ HbA with ⟨Hp, HbA⟩
  unfold C.bagL
  icases bsl_filter_take (fun t => token (tk t))
    (fun t => decide (lo < t) && decide (t ≠ 0) && (C.isA M t || C.isR M t) && byH M h t)
    (fun t => decide (lo < t) && decide (t ≠ ts) && (C.isA M t || C.isR M t) && byH M h t) ts
    (by simp [hlots, hA, hbyH]; omega)
    (fun t ht => by
      simp only [Bool.and_eq_true, decide_eq_true_eq] at ht ⊢
      exact ⟨⟨⟨⟨ht.1.1.1, by omega⟩, ht.1.2⟩, ht.2⟩, ht.1.1.2⟩) (rng M) (mem_rng.2 htsM) (nodup_rng M)
    $$ HbL with ⟨Ht, HbL⟩
  imod shoot $$ Hp with #Hsh
  imodintro
  isplitr
  · ileft; ipureintro
    exact ⟨⟨0, grd_intro (qLk_noC (noC_snoc hnoC (rmw_nonC _ _ _ _ _ _ _)))⟩, grd_intro (ok_lk hlenD)⟩
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
  imod lk_acqE g M tk h hdd (π := π1c) (ws := instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) hlen4 hlo1 hex hsrc
    hcohB hlo hts_f hwts hnoinv $$ [HbA HbL Ht] with (⟨Hbag, %hv⟩ | ⟨Hbag, %hv, %s0r, %hs0r, HR⟩)
  · iframe Hctx Hfr Ht; unfold C.obag C.bagA C.bagL; iframe HbA HbL
  all_goals imodintro
  all_goals iintro Hl
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
    have hls : C.lhS1c s3 := ⟨hP3, hq3, hc3, by rw [LPstep_rd hs3 14 (.inr rfl), f14],
      by rw [LPstep_rd hs3 9 (.inr rfl), f9], by rw [LPstep_rd hs3 11 (.inr rfl), f11],
      hs3.2.2.2.1.trans hlen2⟩
    iapply IH $$ %s3 %_ %_ %_ %ts %hls %⟨hcs, noC_snoc hnoC (rmw_nonC _ _ _ _ _ _ _)⟩ Hctx [Hbag] Hl
    unfold C.obag C.bagA C.bagL
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
    unfold RsE
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
    iapply (lk_cpu1E g M tk h hh s3 _ _ _ ts lw s0r
      ⟨hP3, hq3, hc3, by rw [LPstep_rd hs3 9 (.inr rfl), f9], by rw [LPstep_rd hs3 11 (.inr rfl), f11]⟩
      hcs hvr hvw (noC_snoc hnoC (rmw_nonC _ _ _ _ _ _ _)) hnoinv)
    iframe Hctx Hc Hpp Hl
    unfold C.obag C.bagA C.bagL
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

/-- **A HART**: `li a4,1`, then the spin loop. -/
theorem lk_hartE (g : AGN) (M : List PMsg) (tk : Nat → GName) (h : Nat) (hh : h < 2)
    (hdd : g.dd = fun _ => False) (hnoinv : ∀ t a, ¬ cmoAt M isInvalK t a)
    (s0 : LP) {P0 : GSet Nat} (hprog : s0.prog = b1c) (hpc : s0.pc = 0) (hq : s0.q = [])
    (hlen : s0.regs.length = 32) (h9 : s0.rd 9 = X) (h11 : s0.rd 11 = Y) :
    lkCtxE (GF := GF) g M tk ∗ C.obag g M tk h 0 0 ∗ lhA g π1c (wL1c M h) (qsLk M h) psInit P0 [] ⊢
      wpKA g π1c (wL1c M h) (qsLk M) s0 (ΦE g M) := by
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
  have hls : C.lhS1c s1 := ⟨hP1, hq1, hc1, li_val hs1 (by decide) (by omega) (by decide),
    by rw [LPstep_rd hs1 9 (.inl (by decide)), h9], by rw [LPstep_rd hs1 11 (.inl (by decide)), h11],
    hs1.2.2.2.1.trans hlen⟩
  ihave Hloop := lk_loopE (GF := GF) g M tk h hh hdd hnoinv
  iapply Hloop $$ %s1 %_ %_ %_ %0 %hls %⟨Nat.zero_le _, noC_nil⟩ Hctx Hbag Hl

theorem rSlotE_alloc (g : AGN) (M : List PMsg) (tk : Nat → GName) (r : Nat) :
    pend (GF := GF) g r ⊢ |={⊤}=> rSlotE g M tk r := by
  iintro Hp
  unfold rSlotE
  iapply inv_alloc
  inext; ileft; iexact Hp

theorem pA_A {M : List PMsg} {h t : Nat} (hp : C.pA M h t = true) : C.isA M t = true := by
  unfold C.pA at hp; simp only [Bool.and_eq_true] at hp; exact hp.1.2

/-- **THE SETUP, PER-BYTE OWNERS** (plan R-a5; see the header). -/
theorem lk_setupE (g : AGN) (M : List PMsg) (hm : g.mn.length = M.length) :
    doomInv (GF := GF) g M ∗ ([∗list] k ↦ _x ∈ g.mn, pend g (k + 1)) ⊢
      |={⊤}=> ∃ tk, lkCtxE g M tk ∗ C.obag g M tk 0 0 0 ∗ C.obag g M tk 1 0 0 := by
  iintro ⟨#Hdoom, Hp⟩
  have h0 : ([∗list] k ↦ _x ∈ g.mn, pend (GF := GF) g (k + 1)) ⊢ [∗list] t ∈ rng M, pend g t := by
    have := bsl_range (pend (GF := GF) g) g.mn 1; rw [hm] at this; exact this
  ihave Hp := h0 $$ Hp
  imod toks_alloc (GF := GF) (rng M) (nodup_rng M) with ⟨%tk, Ht⟩
  -- the owners, peeled one by one (each class implies the remainder)
  have hLA : ∀ t, C.isA M t = true → isCT M t = false ∧ isPT M t = false := fun t hA => by
    simp [isCT, isPT, A_LT hA]
  have hLR : ∀ t, C.isR M t = true → isCT M t = false ∧ isPT M t = false := fun t hR => by
    simp [isCT, isPT, R_LT hR]
  ihave ⟨HA0, Hp⟩ := bsl_filter_split (pend (GF := GF) g) (C.pA M 0) (rng M) $$ Hp
  ihave ⟨HA1, Hp⟩ := bsl_peel (pend (GF := GF) g) (C.pA M 1) (fun t => !C.pA M 0 t)
    (fun t h1 => by simp [C.pA_10 h1]) (rng M) $$ Hp
  ihave ⟨HR, Hp⟩ := bsl_peel (pend (GF := GF) g) (C.isR M) (fun t => !C.pA M 0 t && !C.pA M 1 t)
    (fun t hR => by simp [C.pA, C.isR_A hR]) (rng M) $$ Hp
  ihave ⟨HC, Hp⟩ := bsl_peel (pend (GF := GF) g) (isCT M)
    (fun t => !C.pA M 0 t && !C.pA M 1 t && !C.isR M t)
    (fun t hC => by
      have hA : C.isA M t = false := by
        cases h : C.isA M t
        · rfl
        · rw [(hLA t h).1] at hC; cases hC
      have hR : C.isR M t = false := by
        cases h : C.isR M t
        · rfl
        · rw [(hLR t h).1] at hC; cases hC
      simp [C.pA, hA, hR]) (rng M) $$ Hp
  ihave ⟨HP, Hp⟩ := bsl_peel (pend (GF := GF) g) (isPT M)
    (fun t => !C.pA M 0 t && !C.pA M 1 t && !C.isR M t && !isCT M t)
    (fun t hP => by
      have hA : C.isA M t = false := by
        cases h : C.isA M t
        · rfl
        · rw [(hLA t h).2] at hP; cases hP
      have hR : C.isR M t = false := by
        cases h : C.isR M t
        · rfl
        · rw [(hLR t h).2] at hP; cases hP
      have hC : isCT M t = false := by
        unfold isPT at hP; simp only [Bool.and_eq_true, Bool.not_eq_true'] at hP; exact hP.2
      simp [C.pA, hA, hR, hC]) (rng M) $$ Hp
  ihave ⟨HJ, -⟩ := bsl_peel (pend (GF := GF) g) (isJE M)
    (fun t => !C.pA M 0 t && !C.pA M 1 t && !C.isR M t && !isCT M t && !isPT M t)
    (fun t hJ => by
      unfold isJE at hJ; simp only [Bool.and_eq_true, Bool.not_eq_true'] at hJ
      obtain ⟨⟨hL, hA⟩, hR⟩ := hJ
      simp [C.pA, hA, hR, isCT, isPT, hL]) (rng M) $$ Hp
  -- tokens: each hart's lock messages
  ihave ⟨HL0, Ht⟩ := bsl_filter_split (fun t => token (GF := GF) (tk t)) (C.pL M 0) (rng M) $$ Ht
  ihave HL1 := bsl_filter_mono (fun t => token (GF := GF) (tk t)) _ (C.pL M 1) (fun t h1 => by
    rw [C.pL_10 h1]; rfl) (rng M) $$ Ht
  -- the invariants
  imod bsl_fupd (G := fun r => rSlotE (GF := GF) g M tk r) (fun r => rSlotE_alloc g M tk r) _ $$ HR with #Hrs
  imod bsl_fupd (G := fun t => lkJunk (GF := GF) g t) (fun t => junk_alloc g t) _ $$ HJ with #Hjs
  imod inv_alloc (ndot lkNE 0) ⊤ iprop(RsE (GF := GF) g M 0 ∨ nxtTok M tk 0) $$ [HC HP] with #Hi
  · inext; ileft; unfold RsE cPtsE pPtsE
    have hp0 : pBagE M 0 = (rng M).filter (isPT M) := by
      unfold pBagE; refine List.filter_congr (fun t ht => ?_); have := rng_ge ht; simp [show 0 < t by omega]
    rw [hp0]
    iframe HP
    iexists 0
    isplitr
    · ipureintro; exact Nat.le_refl _
    isplitr
    · ipureintro; exact .inl rfl
    have hc0 : cBagE M 0 = (rng M).filter (isCT M) := by
      unfold cBagE; refine List.filter_congr (fun t ht => ?_); have := rng_ge ht; simp [show 0 < t by omega]
    rw [hc0]; iexact HC
  imodintro
  iexists tk
  isplitr [HA0 HA1 HL0 HL1]
  · unfold lkCtxE iSlotE
    iframe Hdoom Hi Hrs Hjs
  have eA : ∀ h, C.bagA M h 0 0 = (rng M).filter (C.pA M h) := fun _ => rfl
  have eL : ∀ h, C.bagL M h 0 0 = (rng M).filter (C.pL M h) := fun _ => rfl
  isplitl [HA0 HL0]
  · unfold C.obag; rw [eA, eL]; iframe HA0 HL0
  · unfold C.obag; rw [eA, eL]; iframe HA1 HL1

end hart

/-! ## The verdict -/

/-- THE ADEQUACY PREMISE at `Dd := fun _ => False` (no dead set). -/
theorem lk_premiseE (M : List PMsg) (hnoinv : ∀ t a, ¬ cmoAt M isInvalK t a) :
    wpPremise .hasLC ownGF (xStep xs1c) litDone imgL M (progs t1c) π1c (fun _ _ => True)
      (fun h => ΨK M (qsLk M h)) (fun _ => False) := by
  intro Hinv g P0 hn hm hdd hP0
  obtain ⟨p0, p1, hps⟩ := C.progs_1c
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
  imod lk_setupE g M hm $$ [Hp] with ⟨%tk, #Hctx, Hb0, Hb1⟩
  · iframe Hdoom Hp
  have k0 := lk_hartE (GF := ownGF) g M tk 0 (by decide) hdd hnoinv p0 (P0 := P0 0) hpr0 hpc0 hq0 hl0
    (by rw [hrd0 9 (by decide) (by decide)]; rfl) (by rw [hrd0 11 (by decide) (by decide)]; rfl)
  have k1 := lk_hartE (GF := ownGF) g M tk 1 (by decide) hdd hnoinv p1 (P0 := P0 1) hpr1 hpc1 hq1 hl1
    (by rw [hrd1 9 (by decide) (by decide)]; rfl) (by rw [hrd1 11 (by decide) (by decide)]; rfl)
  have k0' : lkCtxE (GF := ownGF) g M tk ∗ C.obag g M tk 0 0 0 ∗
      lhA g π1c (wL1c M 0) (qsLk M 0) psInit (P0 0) [] ⊢
      wpA (hlc := .hasLC) g π1c (hw (xStep xs1c) litDone imgL M 0) (fun h => ΨK M (qsLk M h)) p0
        (fun v => iprop(⌜∃ V, grd π1c imgL M V ((fun (_ : Nat) (_ : Unit) => True) 0 v)⌝ ∨ dshot g)) := k0
  have k1' : lkCtxE (GF := ownGF) g M tk ∗ C.obag g M tk 1 0 0 ∗
      lhA g π1c (wL1c M 1) (qsLk M 1) psInit (P0 1) [] ⊢
      wpA (hlc := .hasLC) g π1c (hw (xStep xs1c) litDone imgL M (0 + 1)) (fun h => ΨK M (qsLk M h)) p1
        (fun v => iprop(⌜∃ V, grd π1c imgL M V ((fun (_ : Nat) (_ : Unit) => True) (0 + 1) v)⌝ ∨
          dshot g)) := k1
  rw [hgn]
  icases (BigSepL.bigSepL_cons).1 $$ Hh with ⟨H0, Hh⟩
  icases (BigSepL.bigSepL_cons).1 $$ Hh with ⟨H1, -⟩
  imodintro
  have s0 := lhA_start (GF := ownGF) (g := g) (π := π1c) (w := wL1c M 0) (Qs := qsLk M) (P0 := P0 0)
    (qLk_noC noC_nil)
  have s1 := lhA_start (GF := ownGF) (g := g) (π := π1c) (w := wL1c M 1) (Qs := qsLk M) (P0 := P0 (0 + 1))
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

/-- **E-a: G4 TARGET (1c) WITH THE DEAD SET EMPTY** — the statement of `own_lock1c` (OwnALock1c.lean), proved
through `adequacyA` at `Dd := fun _ => False` (no free mode, no dead invariant), the per-byte owners of
OwnAE1cDefs.lean and the protocol `π1c`.  0 named inputs; finite runs (S3d separate, [OWN.P4]). -/
theorem own_lock1cE (M : List PMsg) (run : PFRun LP Unit)
    (hrun : PF.validRun (xStep xs1c) imgL () (progs t1c) M run) : ∀ h, qLk M (run.trace h) := by
  have hnoinv := x_noInvalT hrun
  obtain ⟨_, hΨ, _⟩ := adequacyA (hlc := .hasLC) (GF := ownGF) π1c (fun _ _ => True)
    (fun h => ΨK M (qsLk M h)) (fun _ => False) trivial (fun h => ⟨qLk_noC noC_nil, wrOk_nil M⟩)
    (lk_premiseE M hnoinv) hrun
  intro h
  have hq := (hΨ h (run.trace h).length).1
  rw [List.take_length] at hq
  exact qLk_of_memEv hq

/-- Mutual exclusion, ordered (as `own_lock1c_excl`). -/
theorem own_lock1cE_excl (M : List PMsg) (run : PFRun LP Unit)
    (hrun : PF.validRun (xStep xs1c) imgL () (progs t1c) M run) (h : Nat) (tvs : List (Nat × BitVec 8))
    (ts ts0 : Nat) (hl : ∃ e ∈ run.trace h, isCLd e tvs) (hs : ∃ e ∈ run.trace h, isCSt e ts)
    (hc : isC M ts0 = true) (hlt : ts0 < ts) : ∀ p ∈ tvs, ts0 ≤ p.1 := by
  obtain ⟨lw, hall, _, _, hno⟩ := own_lock1cE M run hrun h tvs ts hl hs
  intro p hp
  rw [hall p hp]
  apply Classical.byContradiction; intro hne
  have := hno ts0 (by omega) hlt
  rw [hc] at this; cases this

#print axioms own_lock1cE
#print axioms own_lock1cE_excl

end Weak.Prom.OA.EC
