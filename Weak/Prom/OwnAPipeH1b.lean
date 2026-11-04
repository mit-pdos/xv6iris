/-
Weak/Prom: **G4 target (4) on track (a): hart 1 — the L1 spin loop (the publication) and the start** (stage S4a
part 4; plan rev 7 §4 G4 (4); §3 "Acquire": "An aq AMO gives WF ≥ ts > tr immediately … So the acquirer can open
the source's invariant at once, provided the source s is release-class").

`h1_loop1` (Löb at `pc = 1`): at the aq AMO's continuation the word is 1 (spin), or 0 read from hart 0's release
`s` (`l1_acq`): its slot yields `Pub1 s` — the L2 handle with the RUNTIME name `γ`, the birth `b < s`, the field
write `c < s`, and the `pend`s of hart 0's later L2 words; the view after the aq AMO is `≥ ts > s`, which is what
puts the L2 read above `b` (R-a4).  Then the L2 loop (`h1_loop2`).
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.OwnAPipeH1

namespace Weak.Prom.OA.P

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.PF Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Ref (Instr Test two64)
open Weak.Prom.Ref.Lit (X Y Z)
open PLabel
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode

section h1

variable {GF : BundledGFunctors} [GhostVarG GF HSt] [GhostVarG GF Bool] [TokenG GF] [SavedPropG GF] [InvGS GF]

/-- The hart's state at the L1 loop head (`pc = 1`). -/
def lhS1 (s : LP) : Prop :=
  s.prog = b4h ∧ s.q = [] ∧ s.pc = 1 ∧ s.rd 14 = 1 ∧ s.rd 9 = X ∧ s.rd 11 = Y ∧ s.rd 12 = Z ∧ s.regs.length = 32

/-- **THE L1 SPIN LOOP** (Löb induction at `pc = 1`; see the header). -/
theorem h1_loop1 (g : AGN) (M : List PMsg) (sv : SV) (hdd : g.dd = dd4 M)
    (hnoinv : ∀ t a, ¬ cmoAt M isInvalK t a := by assumption) :   -- [rebase-repair] MachFix-R-b5: `vi = 0`
    ⊢ ∀ (s : LP) (ws : PState) (pr : GSet Nat) (ev : Trace) (lo : Nat), ⌜lhS1 s⌝ -∗
      ⌜lo ≤ coh ws L1 ∧ q4 ev⌝ -∗ pCtx (GF := GF) g M sv -∗ ([∗list] t ∈ bagK M 2 lo, pend g t) -∗
      tk1 M sv -∗ ob2 g M sv 0 0 -∗ r2Bag g M -∗
      lhA g Proto.triv (w4 M 1) (qs4 1) ws pr ev -∗ wpKA g Proto.triv (w4 M 1) qs4 s (Φ4 g M) := by
  have hw := litW_x xs4 img4 M 1
  iloeb as IH
  iintro %s0 %ws0 %pr0 %ev %lo %hs %hl0 #Hctx HbA Htk Hob Hr2 Hl
  obtain ⟨hprog0, hq0, hpc0, h14, h9_0, h11_0, h12_0, hlen0⟩ := hs
  obtain ⟨hlo0, hq4⟩ := hl0
  -- `mv a5,a4`
  iapply (C.wpKA_alu hw (litAg_x hq0 (p4h_at hprog0) (by rw [hpc0]; rfl) rfl) hq0 (by rw [hprog0, hpc0]; rfl)
    (by decide))
  iframe Hl
  inext
  iintro %s %hsA _ _
  imodintro
  iintro Hl
  obtain ⟨hprog, hpc, hq⟩ := LPstep_at hsA hprog0 (by rw [hpc0])
  have h9 : s.rd 9 = X := by rw [LPstep_rd hsA 9 (.inl (by decide)), h9_0]
  have h11 : s.rd 11 = Y := by rw [LPstep_rd hsA 11 (.inl (by decide)), h11_0]
  have h12 : s.rd 12 = Z := by rw [LPstep_rd hsA 12 (.inl (by decide)), h12_0]
  have h14' : s.rd 14 = 1 := by rw [LPstep_rd hsA 14 (.inl (by decide)), h14]
  have hlen : s.regs.length = 32 := hsA.2.2.2.1.trans hlen0
  have h15 : s.rd 15 = 1 := mv_15 hsA h14 hlen0
  have hX := p4h_at hprog
  -- `amoswap.w.aq a5,a5,(a2)`
  iapply (wpKA_amo (base := L1) hw (litAg_x hq hX (by rw [hpc]; rfl) rfl) hq (by rw [hprog, hpc]; rfl)
    (alg_L1 h12) (by rw [h12]))
  iframe Hl
  inext
  iintro %tvs %ts %hlen4 %_ %hmsg %hlo1 %hex %hcoh %_ _ _
  have hd1 : amoD .swap 4 (s.rd 15) tvs = toBytes 1 4 := amo_msg1 h15
  have hlenD : (amoD .swap 4 (s.rd 15) tvs).length = 4 := by rw [hd1]; rfl
  rw [hd1] at hmsg
  rw [hlenD] at hcoh
  have hcohB : ∀ j : Nat, j < 4 → coh (loadRun (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) true false
      (srcsView (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) (srcR 12)) L1 tvs) (L1 + j) < ts :=
    fun j hj => cohBelow_at hcoh hj
  have hc0 : coh (loadRun (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) true false
      (srcsView (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) (srcR 12)) L1 tvs) L1 < ts := by
    simpa using hcohB 0 (by decide)
  have hcm := (loadRun_mono (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) true false
    (srcsView (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) (srcR 12)) L1 tvs).2.2.2.2.2.2.2.2.2.2.1 L1
  have hts1 : 1 ≤ ts := by omega
  have hmt := msgAt_of hts1 hmsg
  have hk2 : knd M ts = 2 := by rw [knd_of hmt]; exact kind_a1
  have htsM := msgAt_le hmt
  have hlo : lo ≤ coh (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) L1 := hlo0
  have hlots : lo < ts := by omega
  unfold bagK
  icases bsl_filter_take (pend g) (fun t => decide (lo < t) && isK M 2 t)
    (fun t => decide (ts < t) && isK M 2 t) ts (by simp [hlots, isK, hk2])
    (fun t ht => by
      simp only [Bool.and_eq_true, decide_eq_true_eq] at ht ⊢
      exact ⟨⟨by omega, ht.2⟩, by omega⟩) (rng M) (mem_rng.2 htsM) (nodup_rng M)
    $$ HbA with ⟨Hp, HbA⟩
  imod shoot $$ Hp with #Hsh
  imodintro
  isplitr
  · ileft; ipureintro
    exact ⟨⟨0, grd_intro (q4_snoc hq4 notCLd_rmw)⟩, grd_intro trivial⟩
  isplitr
  · unfold fulT; ileft; iexact Hsh
  iintro %s1 %hs1 #Hfr Hc
  have hts_f := postA_wf (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) 12 L1 tvs ts
    (amoD .swap 4 (s.rd 15) tvs).length
  have hsrc : bytesAll (fun x u _ => u ≤ coh (loadRun (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) true false
      (srcsView (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) (srcR 12)) L1 tvs) x) L1 tvs :=
    bytesAll_mono (fun _ _ _ hh => hh.2) _ _
      (loadBytes_coh true (ldPre (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) true false
        (srcsView (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) (srcR 12))) (instrR (regWP ws0 15 (srcR 0 ++ srcR 14)))
        L1 tvs).2
  have hm : bytesAll (fun a t v => memByte img4 M t a = some v) L1 tvs :=
    bytesAll_mono (fun _ _ _ hh => hh.1) _ _ (loadOk_weak hlo1)
  obtain ⟨hP1, hc1, hq1⟩ := LPstep_at hs1 hprog (by rw [hpc])
  have e9 : s1.rd 9 = X := by rw [LPstep_rd hs1 9 (.inl (by decide)), h9]
  have e11 : s1.rd 11 = Y := by rw [LPstep_rd hs1 11 (.inl (by decide)), h11]
  have e12 : s1.rd 12 = Z := by rw [LPstep_rd hs1 12 (.inl (by decide)), h12]
  have e14 : s1.rd 14 = 1 := by rw [LPstep_rd hs1 14 (.inl (by decide)), h14']
  have hlen1 : s1.regs.length = 32 := hs1.2.2.2.1.trans hlen
  have e15 := LPstep_rd_eq hs1 (by decide) (by omega)
  imod l1_acq g M sv hdd (π := Proto.triv)
    (ws1 := qPosts (amoPost (storeRun (loadRun (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) true false
      (srcsView (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) (srcR 12)) L1 tvs) false
      (srcsView (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) (srcR 12)) ts L1 (amoD .swap 4 (s.rd 15) tvs).length ts)
      true ts) (regWL 15 [.DLdRes] ++ [LInstr]).dropLast)
    hlen4 hm hsrc hcohB hts_f $$ [Htk Hc] with (⟨#Hf, #Hd⟩ | ⟨Htk, %hv⟩ | ⟨%hv, %sr, %hsr, HP⟩)
  · iframe Hctx Hfr Htk Hc
  · -- free mode
    imodintro
    iintro Hl
    ihave Hfree := p4h_free (GF := GF) g M hdd
    have hfr : frS4 s1 := ⟨hP1, hq1, by rw [hc1]; decide, by rw [hc1]; decide, e9, e11, e12, e14, hlen1,
      fun h => by omega⟩
    iapply Hfree $$ %s1 %_ %_ %_ %hfr Hf Hd Hl
  · -- held: `sext.w`, `bnez` back to the loop head
    imodintro
    iintro Hl
    iapply (wpKA_addiw (Xs := xs4) hw (xAg_x xs4 img4 M 1 s1) hq1 (p4h_at hP1) (by rw [hc1]; rfl) (by decide))
    iframe Hl
    inext
    iintro %s2 %hs2 _ _
    imodintro
    iintro Hl
    obtain ⟨hP2, hc2, hq2⟩ := LPstep_at hs2 hP1 (by rw [hc1])
    have f15 : s2.rd 15 = 1 := a5_val (.inr rfl) e15 hv hs2 hlen1
    have hlen2 : s2.regs.length = 32 := hs2.2.2.2.1.trans hlen1
    iapply (wpKA_brx (Xs := xs4) hw (xAg_x xs4 img4 M 1 s2) hq2 (p4h_at hP2) (by rw [hc2]; rfl)
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
    have r9 : s3.rd 9 = X := by
      rw [LPstep_rd hs3 9 (.inr rfl), LPstep_rd hs2 9 (.inl (by decide)), e9]
    have r11 : s3.rd 11 = Y := by
      rw [LPstep_rd hs3 11 (.inr rfl), LPstep_rd hs2 11 (.inl (by decide)), e11]
    have r12 : s3.rd 12 = Z := by
      rw [LPstep_rd hs3 12 (.inr rfl), LPstep_rd hs2 12 (.inl (by decide)), e12]
    have r14 : s3.rd 14 = 1 := by
      rw [LPstep_rd hs3 14 (.inr rfl), LPstep_rd hs2 14 (.inl (by decide)), e14]
    have hls : lhS1 s3 := ⟨hP3, hq3, hc3, r14, r9, r11, r12, hs3.2.2.2.1.trans hlen2⟩
    have hcs := postA_coh (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) 12 L1 tvs ts
      (amoD .swap 4 (s.rd 15) tvs).length (by rw [hlenD]; decide)
    iapply IH $$ %s3 %_ %_ %_ %ts %hls %⟨hcs, q4_snoc hq4 notCLd_rmw⟩ Hctx HbA Htk Hob Hr2 Hl
  · -- acquired: the L2 handle, published by hart 0's L1 release `sr`
    unfold Pub1
    icases HP with ⟨%γ, %b, %c, %hbc, #Hlk, Hz⟩
    obtain ⟨hbs, hcs', hc5⟩ := hbc
    unfold isLockAt
    icases Hlk with ⟨%hb, #Hds, #HsQ, #Hslot⟩
    imodintro
    iintro Hl
    iapply (wpKA_addiw (Xs := xs4) hw (xAg_x xs4 img4 M 1 s1) hq1 (p4h_at hP1) (by rw [hc1]; rfl) (by decide))
    iframe Hl
    inext
    iintro %s2 %hs2 _ _
    imodintro
    iintro Hl
    obtain ⟨hP2, hc2, hq2⟩ := LPstep_at hs2 hP1 (by rw [hc1])
    have f15 : s2.rd 15 = 0 := a5_val (.inl rfl) e15 hv hs2 hlen1
    have hlen2 : s2.regs.length = 32 := hs2.2.2.2.1.trans hlen1
    iapply (wpKA_brx (Xs := xs4) hw (xAg_x xs4 img4 M 1 s2) hq2 (p4h_at hP2) (by rw [hc2]; rfl)
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
    have r9 : s3.rd 9 = X := by
      rw [LPstep_rd hs3 9 (.inr rfl), LPstep_rd hs2 9 (.inl (by decide)), e9]
    have r11 : s3.rd 11 = Y := by
      rw [LPstep_rd hs3 11 (.inr rfl), LPstep_rd hs2 11 (.inl (by decide)), e11]
    have r12 : s3.rd 12 = Z := by
      rw [LPstep_rd hs3 12 (.inr rfl), LPstep_rd hs2 12 (.inl (by decide)), e12]
    have r14 : s3.rd 14 = 1 := by
      rw [LPstep_rd hs3 14 (.inr rfl), LPstep_rd hs2 14 (.inl (by decide)), e14]
    have hls : lhS2 s3 := ⟨hP3, hq3, hc3, r14, r9, r11, r12, hs3.2.2.2.1.trans hlen2⟩
    have hvr := postA_vr (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) 12 L1 tvs ts
      (amoD .swap 4 (s.rd 15) tvs).length
    ihave Hloop := h1_loop2 (GF := GF) g M sv hdd γ b c hb hc5
    iapply Hloop $$ %s3 %(postA (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) 12 L1 tvs ts
        (amoD .swap 4 (s.rd 15) tvs).length) %_ %_ %0 %hls
      %⟨Nat.zero_le _, by omega, by omega, q4_snoc hq4 notCLd_rmw⟩ Hctx
      [] Hob Hr2 Hz Hl
    unfold isLockAt; iframe Hds HsQ Hslot; ipureintro; exact hb

/-- **HART 1**: `li a4,1`, then the L1 spin loop. -/
theorem h1_hart (g : AGN) (M : List PMsg) (sv : SV) (hdd : g.dd = dd4 M)
    (s0 : LP) {P0 : GSet Nat} (hprog : s0.prog = b4h) (hpc : s0.pc = 0) (hq : s0.q = [])
    (hlen : s0.regs.length = 32) (h9 : s0.rd 9 = X) (h11 : s0.rd 11 = Y) (h12 : s0.rd 12 = Z)
    (hnoinv : ∀ t a, ¬ cmoAt M isInvalK t a := by assumption) :   -- [rebase-repair] MachFix-R-b5: `vi = 0`
    pCtx (GF := GF) g M sv ∗ ([∗list] t ∈ bagK M 2 0, pend g t) ∗ tk1 M sv ∗ ob2 g M sv 0 0 ∗ r2Bag g M ∗
      lhA g Proto.triv (w4 M 1) (qs4 1) psInit P0 [] ⊢
      wpKA g Proto.triv (w4 M 1) qs4 s0 (Φ4 g M) := by
  have hw := litW_x xs4 img4 M 1
  iintro ⟨#Hctx, HbA, Htk, Hob, Hr2, Hl⟩
  iapply (wpKA_alui hw (litAg_x hq (p4h_at hprog) (by rw [hpc]; rfl) rfl) hq (by rw [hprog, hpc]; rfl)
    (by decide))
  iframe Hl
  inext
  iintro %s1 %hs1 _ _
  imodintro
  iintro Hl
  obtain ⟨hP1, hc1, hq1⟩ := LPstep_at hs1 hprog (by rw [hpc])
  have hls : lhS1 s1 := ⟨hP1, hq1, hc1, li_val hs1 (by decide) (by omega) (by decide),
    by rw [LPstep_rd hs1 9 (.inl (by decide)), h9], by rw [LPstep_rd hs1 11 (.inl (by decide)), h11],
    by rw [LPstep_rd hs1 12 (.inl (by decide)), h12], hs1.2.2.2.1.trans hlen⟩
  ihave Hloop := h1_loop1 (GF := GF) g M sv hdd
  iapply Hloop $$ %s1 %_ %_ %_ %0 %hls %⟨Nat.zero_le _, q4_nil⟩ Hctx HbA Htk Hob Hr2 Hl

end h1

end Weak.Prom.OA.P
