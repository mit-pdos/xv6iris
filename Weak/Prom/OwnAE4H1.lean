/-
Weak/Prom: **E-a4 — an acquirer's round** (hart 1 or 2, round `k`; stage E-a4): wait for the publication of
round `k`, CLAIM its part of the lock born at the published `b` (`hclaim7`), xv6's acquire (`loopG`), `lk->cpu`
(`cpu1G`), the critical section `ld; addi; sd` (as E-a2's `cs1_5`/`cs2_5`, R-a1 by doom / the guard), xv6's
release (`relG`, the resource deposited), then `fence rw,w; sb a3,0(a6)`: THE DONE BYTE, whose slot receives the
hart's REMAINING PART and its participation one-shot `eP h k` (the death mark needs it); the next round.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.OwnAE4Gen

namespace Weak.Prom.OA.E4

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.PF Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Ref (Instr Test two64)
open Weak.Prom.Ref.Lit (X Y Z)
open Weak.Prom.OA.P (L1 J SV bSlot dshotD dpendD msgAt_of cAt5)
open Weak.Prom.OA.C (Pc st_nonC Lk_ne_Ct)
open Weak.Prom.OA.E
open Weak.Prom.OA.EP (tL1 tL2 isL2O isCO cB cBX cB_X c_cls)
open Weak.Prom.OA.E2
open PLabel
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode

/-- An acquirer's registers in round `k`. -/
def RKa (h k : Nat) (s : LP) : Prop :=
  s.regs.length = 32 ∧ s.rd 9 = X ∧ s.rd 11 = Y ∧ s.rd 12 = Z ∧ s.rd 13 = k ∧ s.rd 16 = Z + h ∧ s.rd 28 = 3

theorem RKa_step {h k : Nat} {s s' : LP} {pc rd v : Nat} (hr : RKa h k s) (hs : LPstep s s' pc rd v)
    (hrd : rd = 0 ∨ rd = 5 ∨ rd = 7 ∨ rd = 14 ∨ rd = 15) : RKa h k s' := by
  obtain ⟨h0, h9, h11, h12, h13, h16, h28⟩ := hr
  have e : ∀ r, (r = 9 ∨ r = 11 ∨ r = 12 ∨ r = 13 ∨ r = 16 ∨ r = 28) → s'.rd r = s.rd r :=
    fun r hr' => LPstep_rd hs r (by omega)
  exact ⟨hs.2.2.2.1.trans h0, by rw [e 9 (by omega), h9], by rw [e 11 (by omega), h11], by rw [e 12 (by omega), h12],
    by rw [e 13 (by omega), h13], by rw [e 16 (by omega), h16], by rw [e 28 (by omega), h28]⟩

theorem pA_at {s : LP} (h : s.prog = bA) : xOf xs7 s.prog = some pA := by rw [h]; exact xOf_pA

theorem fI_fn {ws : PState} (h : fI ws) (pr pw sr sw : Bool) : fI (instrR (fencePost ws pr pw sr sw)) :=
  fI_of h rfl rfl
theorem wsM_fn (ws : PState) (pr pw sr sw : Bool) : wsM ws (instrR (fencePost ws pr pw sr sw)) :=
  wsM_trans (wsM_fence ws pr pw sr sw) (wsM_eq (fun _ => rfl) rfl rfl rfl rfl)
theorem fI_rw {ws : PState} (h : fI ws) (rd : Nat) (srcs : List Dsrc) : fI (instrR (regWP ws rd srcs)) := fI_of h rfl rfl
theorem wsM_rw (ws : PState) (rd : Nat) (srcs : List Dsrc) : wsM ws (instrR (regWP ws rd srcs)) :=
  wsM_eq (fun _ => rfl) rfl rfl rfl rfl

/-- The `ld; addi` post-state (stated over an abstract `L`, so that `rfl` stays cheap). -/
theorem wsM_ldA (L : PState) :
    wsM L (instrR (regWP (qPosts L (regWL 7 [.DLdRes] ++ [LInstr])) 7 (srcR 7))) := wsM_eq (fun _ => rfl) rfl rfl rfl rfl
theorem fI_ldA {L : PState} (h : fI L) : fI (instrR (regWP (qPosts L (regWL 7 [.DLdRes] ++ [LInstr])) 7 (srcR 7))) :=
  fI_of h rfl rfl

section h1

variable {GF : BundledGFunctors} [GhostVarG GF HSt] [GhostVarG GF Bool] [TokenG GF] [SavedPropG GF] [InvGS GF]

/-- The BAD mode after a field read above `lw`: doomed, or the guarded refutation `⟦ex⟧ False`. -/
def bad7 (g : AGN) (M : List PMsg) (ex : Nat) : IProp GF := iprop(dshot g ∨ ⌜grd π7 img7 M ex False⌝)

instance (g : AGN) (M : List PMsg) (ex : Nat) : Persistent (bad7 (GF := GF) g M ex) := by
  unfold bad7; infer_instance

set_option maxHeartbeats 2000000 in
/-- **THE CRITICAL SECTION** `ld t2,(a1); addi t2,t2,1; sd t2,(a1)` (`pc = 9..11`, plan R-a1): the owned read of
the field, per byte (clean, or doomed / guard-refuted), and the store moving the points-to. -/
theorem csA (g : AGN) (M : List PMsg) (sv : SV) (ak ek : Nat → Nat → GName) (h : Nat) (hh : h = 1 ∨ h = 2)
    (hnoinv : ∀ t a, ¬ cmoAt M isInvalK t a) (k : Nat) (R : IProp GF) (ws0 : PState)
    (s : LP) (ws : PState) (pr : GSet Nat) (ev : Trace) (lw : Nat)
    (hs : s.prog = bA ∧ s.q = [] ∧ s.pc = 9 ∧ RKa h k s ∧ fI ws ∧ wsM ws0 ws ∧ lw ≤ ws.wVrNew) :
    ctx7 (GF := GF) g M sv ak ek ∗ cPts5 g M lw ∗ QE7 g M h ev ∗ R ∗
      (∀ (s' : LP) (ws' : PState) (pr' : GSet Nat) (ev' : Trace) (lw' : Nat),
        ⌜s'.prog = bA ∧ s'.q = [] ∧ s'.pc = 12 ∧ RKa h k s' ∧ fI ws' ∧ wsM ws0 ws' ∧ lw' ≤ ws'.wVwOld⌝ -∗
        cPts5 g M lw' -∗ QE7 g M h ev' -∗ R -∗ lhA g π7 (w7 M h) (qs7 M h) ws' pr' ev' -∗
        wpKA g π7 (w7 M h) (qs7 M) s' (Φ7 g M)) ∗
      lhA g π7 (w7 M h) (qs7 M h) ws pr ev ⊢ wpKA g π7 (w7 M h) (qs7 M) s (Φ7 g M) := by
  obtain ⟨hprog, hq, hpc, hrk, hfi, hmo, hvr⟩ := hs
  have hw := litW_x xs7 img7 M h
  have h11 := hrk.2.2.1
  iintro ⟨#Hctx, Hc, #HQ, HR, HK, Hl⟩
  unfold cPts5
  icases Hc with ⟨%hlw, Hb⟩
  rw [cB_X]
  iapply (wpKA_ld (sz := 8) (sgn := true) (rd := 7) (rs1 := 11) (off := 0) (base := Ct) hw
    (litAg_x hq (pA_at hprog) (by rw [hpc]; rfl) rfl) hq (by rw [hprog, hpc]; rfl)
    (alg_of h11 (by decide) (by decide)) (base_of h11 (by decide)))
  iframe Hl
  inext
  iintro %tvs1 %hl1 %hlo1 _ _
  have hvp : lw ≤ ldPre ws false false (srcsView ws (srcR 11)) :=
    Nat.le_trans hvr (PF.ldPre_ge ws false false (srcsView ws (srcR 11))).2.1
  have hcases := cld3 (img := img7) hlw.1 hvp 0 tvs1 (by rw [hl1]; decide)
    (by have := loadOk_weak hlo1; simpa using this)
  have hcohj := (loadBytes_coh false (ldPre ws false false (srcsView ws (srcR 11))) ws Ct tvs1).2
  have hq0 : h ≠ 0 := by omega
  ihave Hmode : |={⊤}=> ∃ ex, ([∗list] t ∈ cBX M lw ex, pend g t) ∗
      QE7 g M h (ev ++ [(LLoad false false Ct tvs1 (srcR 11), none)]) ∗
      (⌜ex = 0 ∧ (∀ p ∈ tvs1, p.1 = lw) ∧ lw ≤ coh (loadRun ws false false (srcsView ws (srcR 11)) Ct tvs1) Ct⌝ ∨
        (bad7 g M ex ∗ ⌜lw < ex ∧ ∃ j : Nat, j < 8 ∧
          ex ≤ coh (loadRun ws false false (srcsView ws (srcR 11)) Ct tvs1) (Ct + j)⌝)) $$ [Hb]
  · rcases hcases with hall | ⟨j, t, v, hj, hlt, hwt⟩ | ⟨ti, hti, j, hj, hc⟩
    · obtain ⟨t0, v0, r0, rfl⟩ := tvs_cons hl1 (by decide)
      have h0 := loadRun_coh0 ws false false (srcsView ws (srcR 11)) Ct t0 v0 r0
      have ht0 : t0 = lw := hall (t0, v0) (List.mem_cons_self ..)
      imodintro; iexists 0; iframe Hb
      isplitr
      · unfold QE7
        icases HQ with (%hQ | #Hd)
        · ileft; ipureintro; obtain ⟨V, hV⟩ := hQ
          exact ⟨V, grd_imp (fun q => by
            simp only [qs7, if_neg hq0] at q ⊢; exact q7_ld q (fun p hp => by rw [hall p hp]; exact hlw)) hV⟩
        · iright; iexact Hd
      ileft; ipureintro
      exact ⟨rfl, hall, by rw [← ht0]; exact h0⟩
    · have hj8 : j < 8 := by rw [← hl1]; exact (List.getElem?_eq_some_iff.1 hj).1
      have htM : 1 ≤ t ∧ t ≤ M.length := by obtain ⟨m, hm, _⟩ := hwt; exact msgAt_le hm
      have hcoh : t ≤ coh (loadRun ws false false (srcsView ws (srcR 11)) Ct tvs1) (Ct + j) :=
        (bytesAll_get hcohj hj).2
      obtain ⟨m, hm, hb⟩ := hwt
      rcases c_cls hm hj8 (by simpa using hb) with hCO | hL
      · unfold cBX
        icases bsl_filter_take (pend g) (fun t => decide (lw < t) && decide (t ≠ 0) && isCO M t)
          (fun x => decide (lw < x) && decide (x ≠ t) && isCO M x) t (by simp [hlt, hCO]; omega)
          (fun x hx => by
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hx ⊢
            exact ⟨⟨⟨hx.1.1, by omega⟩, hx.2⟩, hx.1.2⟩) (rng M) (mem_rng.2 htM) (nodup_rng M)
          $$ Hb with ⟨Hp, Hb⟩
        unfold ctx7
        icases Hctx with ⟨Hdoom, -⟩
        imod doom (E := ⊤) CoPset.subseteq_top g M t htM $$ [Hdoom Hp] with #Hd
        · iframe Hdoom Hp
        imodintro; iexists t; iframe Hb
        isplitr
        · unfold QE7; iright; iexact Hd
        iright; isplitl []
        · unfold bad7; ileft; iexact Hd
        · ipureintro; exact ⟨hlt, j, hj8, hcoh⟩
      · have hgf := straddle7 (img := img7) hm hL hj8 (by simpa using hb)
        imodintro; iexists t; isplitl [Hb]
        · unfold cBX
          iapply bsl_filter_mono (pend g) _ _ (fun x hx => by
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hx ⊢
            exact ⟨⟨hx.1.1, by omega⟩, hx.2⟩) (rng M) $$ Hb
        isplitr
        · unfold QE7; ileft; ipureintro; exact ⟨t, fun hv => (hgf hv).elim⟩
        iright; isplitl []
        · unfold bad7; iright; ipureintro; exact hgf
        · ipureintro; exact ⟨hlt, j, hj8, hcoh⟩
    · exact absurd hc (hnoinv _ _)
  imod Hmode with ⟨%ex, Hb, #HQ1, Hm⟩
  imodintro
  isplitr
  · unfold QE7; iexact HQ1
  iintro %s1 %hs1 _ _
  imodintro
  iintro Hl
  obtain ⟨hP1, hc1, hq1⟩ := LPstep_at hs1 hprog (by rw [hpc])
  have hrk1 := RKa_step hrk hs1 (by omega)
  have hmono := (loadRun_mono ws false false (srcsView ws (srcR 11)) Ct tvs1).2.2.2.2.2.2.2.2.2.2.1
  -- `addi t2,t2,1`
  iapply (wpKA_alui hw (litAg_x hq1 (pA_at hP1) (by rw [hc1]; rfl) rfl) hq1 (by rw [hP1, hc1]; rfl) (by decide))
  iframe Hl
  inext
  iintro %s2 %hs2 _ _
  imodintro
  iintro Hl
  obtain ⟨hP2, hc2, hq2⟩ := LPstep_at hs2 hP1 (by rw [hc1])
  have hrk2 := RKa_step hrk1 hs2 (by omega)
  have e11 : s2.rd 11 = Y := hrk2.2.2.1
  -- `sd t2,(a1)`
  iapply (wpKA_sw (sz := 8) (rs2 := 7) (rs1 := 11) (off := 0) (base := Ct) hw
    (litAg_x hq2 (pA_at hP2) (by rw [hc2]; rfl) rfl) hq2 (by rw [hP2, hc2]; rfl)
    (alg_of e11 (by decide) (by decide)) (base_of e11 (by decide)))
  iframe Hl
  inext
  iintro %ts %_ %hmsg %hcoh %_ _ _
  rw [toBytes_length] at hcoh
  have hcj : ∀ j : Nat, j < 8 → coh (instrR (regWP (qPosts (loadRun ws false false (srcsView ws (srcR 11)) Ct tvs1)
      (regWL 7 [.DLdRes] ++ [LInstr])) 7 (srcR 7))) (Ct + j) < ts := fun j hj => cohBelow_at hcoh hj
  have hmt := msgAt_of (by have := hcj 0 (by decide); omega) hmsg
  have hC := C3_of (by omega : h < 3) (toBytes_length _ _) hmt
  have hCO := C3_CO hC
  have htsM := msgAt_le hmt
  have hnc : (∀ tvs, ¬ isCLd (LStore false false Ct (toBytes (s2.rd 7) 8) (srcR 11) (srcR 7), some ts) tvs) :=
    fun _ ⟨_, h⟩ => by cases h
  ihave HQs : |={⊤}=> QE7 g M h (ev ++ [(LLoad false false Ct tvs1 (srcR 11), none)] ++
      [(LStore false false Ct (toBytes (s2.rd 7) 8) (srcR 11) (srcR 7), some ts)]) ∗ shot g ts ∗
      ([∗list] t ∈ cB M ts, pend g t) $$ [Hb Hm]
  · icases Hm with (%hcl | ⟨#Hbad, %hra⟩)
    · obtain ⟨rfl, hall, hlc⟩ := hcl
      have hlts : lw < ts := by
        have h0 := hcj 0 (by decide); rw [show Ct + ((0 : Nat) : Int) = Ct from by simp] at h0
        exact Nat.lt_of_le_of_lt hlc h0
      unfold cBX
      icases bsl_filter_take (pend g) (fun t => decide (lw < t) && decide (t ≠ 0) && isCO M t)
        (fun t => decide (lw < t) && decide (t ≠ ts) && isCO M t) ts (by simp [hlts, hCO]; omega)
        (fun t ht => by simp at ht; exact ⟨by simp [ht.1.1, ht.2]; omega, ht.1.2⟩) (rng M)
        (mem_rng.2 htsM) (nodup_rng M) $$ Hb with ⟨Hp, Hb⟩
      imod shoot $$ Hp with #Hsh
      by_cases hg : ∃ u, lw < u ∧ u < ts ∧ isC3 M u = true
      · obtain ⟨u, hu1, hu2, hu3⟩ := hg
        have huM : 1 ≤ u ∧ u ≤ M.length := by obtain ⟨m, hm, _⟩ := clsB_iff.1 hu3; exact msgAt_le hm
        icases bsl_filter_take (pend g) (fun t => decide (lw < t) && decide (t ≠ ts) && isCO M t)
          (fun t => decide (lw < t) && decide (t ≠ ts) && decide (t ≠ u) && isCO M t) u
          (by simp [hu1, C3_CO hu3]; omega)
          (fun t ht => by simp at ht; exact ⟨by simp [ht.1.1.1, ht.1.1.2, ht.2], ht.1.2⟩) (rng M)
          (mem_rng.2 huM) (nodup_rng M) $$ Hb with ⟨Hu, Hb⟩
        unfold ctx7
        icases Hctx with ⟨Hdoom, -⟩
        imod doom (E := ⊤) CoPset.subseteq_top g M u huM $$ [Hdoom Hu] with #Hd
        · iframe Hdoom Hu
        imodintro
        isplitr
        · unfold QE7; iright; iexact Hd
        iframe Hsh
        unfold cB
        iapply bsl_filter_mono (pend g) _ _ (fun t ht => by
          simp only [Bool.and_eq_true, decide_eq_true_eq] at ht ⊢
          exact ⟨⟨⟨by omega, by omega⟩, by omega⟩, ht.2⟩) (rng M) $$ Hb
      · have hl : latestC3 M lw ts := ⟨hlw.1, hlts, fun u h1 h2 => by
          cases h3 : isC3 M u
          · rfl
          · exact absurd ⟨u, h1, h2, h3⟩ hg⟩
        imodintro
        isplitr
        · unfold QE7
          icases HQ1 with (%hQ | #Hd)
          · ileft; ipureintro; obtain ⟨V, hV⟩ := hQ
            exact ⟨V, grd_imp (fun q => by simp only [qs7, if_neg hq0] at q ⊢; exact q7_pair q ⟨lw, hall, hl⟩) hV⟩
          · iright; iexact Hd
        iframe Hsh
        unfold cB
        iapply bsl_filter_mono (pend g) _ _ (fun t ht => by
          simp only [Bool.and_eq_true, decide_eq_true_eq] at ht ⊢
          exact ⟨⟨by omega, by omega⟩, ht.2⟩) (rng M) $$ Hb
    · obtain ⟨hlex, j, hj, hexc⟩ := hra
      have hext : ex < ts := Nat.lt_of_le_of_lt hexc (hcj j hj)
      unfold cBX
      icases bsl_filter_take (pend g) (fun t => decide (lw < t) && decide (t ≠ ex) && isCO M t)
        (fun t => decide (lw < t) && decide (t ≠ ex) && decide (t ≠ ts) && isCO M t) ts
        (by simp [hCO]; omega)
        (fun t ht => by simp at ht; exact ⟨by simp [ht.1.1.1, ht.1.1.2, ht.2], ht.1.2⟩) (rng M)
        (mem_rng.2 htsM) (nodup_rng M) $$ Hb with ⟨Hp, Hb⟩
      imod shoot $$ Hp with #Hsh
      imodintro
      isplitr
      · unfold QE7 bad7
        icases Hbad with (#Hd | %hgf)
        · iright; iexact Hd
        · ileft; ipureintro; exact ⟨ex, fun hv => (hgf hv).elim⟩
      iframe Hsh
      unfold cB
      iapply bsl_filter_mono (pend g) _ _ (fun t ht => by
        simp only [Bool.and_eq_true, decide_eq_true_eq] at ht ⊢
        exact ⟨⟨⟨by omega, by omega⟩, by omega⟩, ht.2⟩) (rng M) $$ Hb
  imod HQs with ⟨#HQ2, #Hsh, Hb⟩
  imodintro
  isplitl []
  · unfold QE7
    icases HQ2 with (%hQ | #Hd)
    · ileft; ipureintro; exact ⟨hQ, grd_intro (ok7_far (toBytes_length _ _) (.inl rfl))⟩
    · iright; iexact Hd
  isplitr
  · unfold fulT; ileft; iexact Hsh
  iintro %s3 %hs3 _ _
  imodintro
  iintro Hl
  obtain ⟨hP3, hc3, hq3⟩ := LPstep_at hs3 hP2 (by rw [hc2])
  obtain ⟨f3, m3, e3, -, -⟩ := wsSt_props (instrR (regWP (qPosts (loadRun ws false false (srcsView ws (srcR 11)) Ct
    tvs1) (regWL 7 [.DLdRes] ++ [LInstr])) 7 (srcR 7))) 11 7 Ct (toBytes (s2.rd 7) 8).length ts
    (fI_ldA (fI_ld hfi false false (srcsView ws (srcR 11)) Ct tvs1))
  have hq7 := wsM_ldA (loadRun ws false false (srcsView ws (srcR 11)) Ct tvs1)
  have hm3 : wsM ws0 (wsSt (instrR (regWP (qPosts (loadRun ws false false (srcsView ws (srcR 11)) Ct tvs1)
      (regWL 7 [.DLdRes] ++ [LInstr])) 7 (srcR 7))) 11 7 Ct (toBytes (s2.rd 7) 8).length ts) :=
    wsM_trans (wsM_trans (wsM_trans hmo (wsM_ld ws false false (srcsView ws (srcR 11)) Ct tvs1)) hq7) m3
  iapply HK $$ %s3 %(wsSt (instrR (regWP (qPosts (loadRun ws false false (srcsView ws (srcR 11)) Ct tvs1)
      (regWL 7 [.DLdRes] ++ [LInstr])) 7 (srcR 7))) 11 7 Ct (toBytes (s2.rd 7) 8).length ts) %_ %_ %ts
    %⟨hP3, hq3, by rw [hc3], RKa_step hrk2 hs3 (by omega), f3, hm3, by rw [e3]; omega⟩
    [Hb] HQ2 HR Hl
  iframe Hb; ipureintro
  exact ⟨hC, .inr (by simp [tidAt, hmt]; omega)⟩

theorem tk_take (ek ak : Nat → Nat → GName) (h k : Nat) (hk : k < 3) :
    ([∗list] k' ∈ (List.range 3).filter (fun k' => decide (k ≤ k')), eP (GF := GF) ek h k' ∗ token (ak h k')) ⊢
      (eP ek h k ∗ token (ak h k)) ∗
        [∗list] k' ∈ (List.range 3).filter (fun k' => decide (k + 1 ≤ k')), eP ek h k' ∗ token (ak h k') :=
  bsl_filter_take (fun k' => iprop(eP (GF := GF) ek h k' ∗ token (ak h k'))) _ _ k (by simp)
    (fun t ht => by simp at ht ⊢; omega) (List.range 3) (List.mem_range.2 hk) List.nodup_range

set_option maxHeartbeats 4000000 in
/-- **AN ACQUIRER'S ROUNDS** (induction on the rounds left; see the header). -/
theorem acqR (g : AGN) (M : List PMsg) (sv : SV) (ak ek : Nat → Nat → GName) (h : Nat) (hh : h = 1 ∨ h = 2)
    (hdd : g.dd = fun _ => False) (hnoinv : ∀ t a, ¬ cmoAt M isInvalK t a) :
    ∀ n k, k + n = 3 → 1 ≤ k → 0 < n → ⊢ ∀ (s : LP) (ws : PState) (pr : GSet Nat) (ev : Trace),
      ⌜s.prog = bA ∧ s.q = [] ∧ s.pc = 0 ∧ RKa h k s ∧ fI ws⌝ -∗ ctx7 (GF := GF) g M sv ak ek -∗
      ([∗list] k' ∈ (List.range 3).filter (fun k' => decide (k ≤ k')), eP ek h k' ∗ token (ak h k')) -∗
      QE7 g M h ev -∗ lhA g π7 (w7 M h) (qs7 M h) ws pr ev -∗ wpKA g π7 (w7 M h) (qs7 M) s (Φ7 g M) := by
  intro n
  induction n with
  | zero => intro k hk h1 h0; omega
  | succ n IH =>
  intro k hkn hk1 _
  have hk3 : k < 3 := by omega
  have hh3 : h < 3 := by omega
  have hw := litW_x xs7 img7 M h
  iintro %s %ws %pr %ev %hs #Hctx Htk #HQ Hl
  obtain ⟨hprog, hq, hpc, hrk, hfi⟩ := hs
  -- the publication wait
  ihave Hwait := waitG (GF := GF) g M h pA xOf_pA 0 0 k (by decide) ⟨by omega, by omega⟩ rfl rfl (by decide)
    (RKa h k) (fun s hs => ⟨hs.2.2.2.1, hs.2.2.2.2.1, hs.1⟩) (fun s s' pc rd v hr hs hrd => RKa_step hr hs (by omega))
    hnoinv iprop([∗list] k' ∈ (List.range 3).filter (fun k' => decide (k ≤ k')), eP ek h k' ∗ token (ak h k')) ws
  iapply Hwait $$ %s %ws %pr %ev %⟨hprog, hq, hpc, hrk, hfi, wsM_refl ws⟩ HQ Htk [] Hl
  iintro %s1 %ws1 %pr1 %ev1 %t %⟨hP1, hq1, hc1, hrk1, hfi1, -, ht1, htM', htv, hcls⟩ #HQ1 Htk Hl
  have htM : 1 ≤ t ∧ t ≤ M.length := ⟨ht1, htM'⟩
  -- `fence rw,rw`: the publication is below the frontier
  iapply (wpKA_fence hw (litAg_x hq1 (pA_at hP1) (by rw [hc1]; rfl) rfl) hq1 (by rw [hP1, hc1]; rfl))
  iframe Hl
  inext
  iintro %s2 %hs2 #Hfr Hc
  obtain ⟨hP2, hc2, hq2⟩ := LPstep_at hs2 hP1 (by rw [hc1])
  have hrk2 := RKa_step hrk1 hs2 (by omega)
  have hfl : t ≤ wfr (fencePost ws1 true true true true) := by
    refine Nat.le_trans ?_ (wfr_ge_vwNew _); simp only [fence_vwNew, ite_true]; omega
  unfold ctx7
  icases Hctx with ⟨Hdoom, Hps, Hn1, Hn2, Hfj, Hbs⟩
  imod frontS g M hdd (π := π7) (img := img7) t ⟨htM.1, htM.2, hfl⟩ $$ [] with #Hsh
  · iframe Hdoom Hfr
  rcases hcls with ⟨hfB, hval⟩ | hJ
  rotate_left
  · ihave #Hj := bsl_mem (F := fun t => lkJunk g t) (List.mem_filter.2 ⟨mem_rng.2 htM, hJ⟩) $$ Hfj
    imod junk_shot g t $$ [] with %hf
    · iframe Hj Hsh
    exact hf.elim
  ihave #Hpsl := bsl_mem (F := fun t => pSl g M sv ak ek t) (List.mem_filter.2 ⟨mem_rng.2 htM, hfB⟩) $$ Hps
  imod pclaim7 g M sv ak ek t $$ [Hc] with HP
  · iframe Hpsl Hsh Hc
  unfold Pub7
  icases HP with ⟨%b, %c, %sp, %hbc, #Hl7, #Hlk⟩
  obtain ⟨hbt, hct, hst, -⟩ := hbc
  rw [hval]
  icases tk_take ek ak h k hk3 $$ Htk with ⟨⟨Hek, Hak⟩, Htk⟩
  imod hclaim7 g M sv.tk ak ek hh $$ [Hak] with Hprt
  · iframe Hlk Hak
  unfold hdl
  icases Hl7 with ⟨%hb, #Hds, #HsQ, #Hbsl⟩
  unfold prt
  icases Hprt with ⟨Hob, HrB⟩
  imodintro
  iintro Hl
  -- `li a4,1`
  iapply (wpKA_alui hw (litAg_x hq2 (pA_at hP2) (by rw [hc2]; rfl) rfl) hq2 (by rw [hP2, hc2]; rfl) (by decide))
  iframe Hl
  inext
  iintro %s3 %hs3 _ _
  imodintro
  iintro Hl
  obtain ⟨hP3, hc3, hq3⟩ := LPstep_at hs3 hP2 (by rw [hc2])
  have hrk3 := RKa_step hrk2 hs3 (by omega)
  have h14 : s3.rd 14 = 1 := li_val hs3 (by decide) (by rw [hrk2.1]; decide) (by decide)
  have hvr3 : t ≤ (instrR (regWP (instrR (fencePost ws1 true true true true)) 14 (srcR 0))).wVrNew ∧
      t ≤ (instrR (regWP (instrR (fencePost ws1 true true true true)) 14 (srcR 0))).wVwNew := by
    simp only [instrR_vrNew, regWP_vrNew, instrR_vwNew, regWP_vwNew, fence_vrNew, fence_vwNew, ite_true]; omega
  -- THE ACQUIRE of the lock born at `b`
  ihave Hloop := loopG (GF := GF) g M sv ak ek h hh3 hdd hnoinv pA xOf_pA 4 rfl rfl rfl rfl (by decide)
    (fun s => RKa h k s ∧ s.rd 14 = 1) (fun s hs => ⟨hs.1.2.1, hs.2, hs.1.1⟩)
    (fun s s' pc rd v hr hs hrd => ⟨RKa_step hr.1 hs (by omega), by rw [LPstep_rd hs 14 (by omega), hr.2]⟩)
    b k c sp t hb hct hst
    iprop([∗list] k' ∈ (List.range 3).filter (fun k' => decide (k + 1 ≤ k')), eP ek h k' ∗ token (ak h k'))
    (instrR (regWP (instrR (fencePost ws1 true true true true)) 14 (srcR 0)))
  iapply Hloop $$ %s3 %(instrR (regWP (instrR (fencePost ws1 true true true true)) 14 (srcR 0))) %_ %_ %b
    %⟨hP3, hq3, hc3, ⟨hrk3, h14⟩, fI_rw (fI_fn hfi1 _ _ _ _) _ _, wsM_refl _, hvr3.1, hvr3.2,
      fun j _ => by have := hvr3.1; omega, Nat.le_refl _, by have := hvr3.1; omega⟩ [] [] [] Hob HrB Hek HQ1 Htk [] Hl
  · unfold ctx7; iframe Hdoom Hps Hn1 Hn2 Hfj Hbs
  · iexact Hlk
  · unfold hdl; iframe Hds HsQ Hbsl; ipureintro; exact hb
  iintro %s4 %ws4 %pr4 %ev4 %ts %lw %sq %⟨hP4, hq4, hc4, ⟨hrk4, -⟩, hfi4, hmo4, hbts, hcts, -, -, hlwr, -, hsqw⟩
    Hob HrB Hek HC HP #HQ4 Htk Hl
  -- `sd a0,16(s1)`
  iapply (cpu1G g M h pA xOf_pA 8 rfl (RKa h k) (fun s hs => hs.2.1) (fun s s' pc v hr hs => RKa_step hr hs (by omega))
    iprop(obg g M sv.tk h ts 0 ∗ ([∗list] t ∈ rB M h b ts, pend g t) ∗ eP ek h k ∗ cPts5 g M lw ∗
      [∗list] k' ∈ (List.range 3).filter (fun k' => decide (k + 1 ≤ k')), eP ek h k' ∗ token (ak h k'))
    ws4 s4 ws4 pr4 ev4 sq ⟨hP4, hq4, hc4, hrk4, hfi4, wsM_refl _, hsqw⟩)
  iframe HP HQ4 Hl
  isplitl [Hob HrB Hek HC Htk]
  · iframe Hob HrB Hek HC Htk
  iintro %s5 %ws5 %pr5 %ev5 %ts1 %⟨hP5, hq5, hc5, hrk5, hfi5, hmo5, hts1P, -⟩ HPp #HQ5 ⟨Hob, HrB, Hek, HC, Htk⟩ Hl
  -- THE CRITICAL SECTION
  iapply (csA g M sv ak ek h hh hnoinv k
    iprop(obg g M sv.tk h ts 0 ∗ ([∗list] t ∈ rB M h b ts, pend g t) ∗ eP ek h k ∗ pPts5 g M ts1 ∗
      [∗list] k' ∈ (List.range 3).filter (fun k' => decide (k + 1 ≤ k')), eP ek h k' ∗ token (ak h k'))
    ws5 s5 ws5 pr5 ev5 lw ⟨hP5, hq5, hc5, hrk5, hfi5, wsM_refl _, Nat.le_trans hlwr hmo5.2.2.2.1⟩)
  iframe HC HQ5 Hl
  isplitr
  · unfold ctx7; iframe Hdoom Hps Hn1 Hn2 Hfj Hbs
  isplitl [Hob HrB Hek HPp Htk]
  · iframe Hob HrB Hek HPp Htk
  iintro %s6 %ws6 %pr6 %ev6 %lw' %⟨hP6, hq6, hc6, hrk6, hfi6, hmo6, hlw'⟩ HC #HQ6 ⟨Hob, HrB, Hek, HPp, Htk⟩ Hl
  -- THE RELEASE (the resource deposited)
  have hts6 : ts ≤ coh ws6 Lk := by
    have := hcts 0 (by decide); rw [show Lk + ((0 : Nat) : Int) = Lk from by simp] at this
    exact Nat.le_trans this (Nat.le_trans (hmo5.1 Lk) (hmo6.1 Lk))
  iapply (relG g M sv ak ek h hh3 pA xOf_pA 12 rfl rfl rfl (RKa h k) (fun s hs => hs.2.1)
    (fun s s' pc v hr hs => RKa_step hr hs (by omega))
    iprop(eP ek h k ∗ [∗list] k' ∈ (List.range 3).filter (fun k' => decide (k + 1 ≤ k')), eP ek h k' ∗ token (ak h k'))
    ws6 false b k s6 ws6 pr6 ev6 ts lw' ts1
    ⟨hP6, hq6, hc6, hrk6, hfi6, wsM_refl _, hbts, hts6, fun _ => hlw', Nat.le_trans hts1P (hmo6.1 Pc)⟩)
  iframe Hob HrB HC HPp HQ6 Hl
  isplitr
  · unfold ctx7; iframe Hdoom Hps Hn1 Hn2 Hfj Hbs
  isplitr
  · iexact Hlk
  isplitr
  · ileft; ipureintro; rfl
  isplitl [Hek Htk]
  · iframe Hek Htk
  iintro %s7 %ws7 %pr7 %ev7 %r %tc %⟨hP7, hq7, hc7, hrk7, hfi7, hmo7, hbr, hrL, hrw, -, -⟩ Hob HrB - #HQ7
    ⟨Hek, Htk⟩ Hl
  -- `fence rw,w`
  iapply (wpKA_fence hw (litAg_x hq7 (pA_at hP7) (by rw [hc7]; rfl) rfl) hq7 (by rw [hP7, hc7]; rfl))
  iframe Hl
  inext
  iintro %s8 %hs8 _ _
  imodintro
  iintro Hl
  obtain ⟨hP8, hc8, hq8⟩ := LPstep_at hs8 hP7 (by rw [hc7])
  have hrk8 := RKa_step hrk7 hs8 (by omega)
  have h16 := hrk8.2.2.2.2.2.1
  have hZh : (Z + h + 0) % two64 = Z + h := Nat.mod_eq_of_lt (by simp [Z, two64]; omega)
  -- `sb a3,0(a6)`: THE DONE BYTE, returning the part and the participation
  iapply (wpKA_sw (sz := 1) (rs2 := 13) (rs1 := 16) (off := 0) (base := (Z : Int) + h) hw
    (litAg_x hq8 (pA_at hP8) (by rw [hc8]; rfl) rfl) hq8 (by rw [hP8, hc8]; rfl)
    (by rw [h16]; simp [aligned, Nat.mod_one]) (by rw [h16, hZh]; omega))
  iframe Hl
  inext
  iintro %f %_ %hmsg %_ %hext _ _
  have hvf : ws7.wVwOld ≤ (instrR (fencePost ws7 true true false true)).wVwNew := by
    simp only [instrR_vwNew, fence_vwNew, ite_true]; omega
  have hpf : (instrR (fencePost ws7 true true false true)).wVwNew < f :=
    Nat.lt_of_le_of_lt (PF.stPreA_ge _ false false _ _).2.2.2.1 hext
  have hmf := msgAt_of (by omega) hmsg
  have hfM := msgAt_le hmf
  have hfB := fB_of (o := h) (toBytes_length _ _) hmf
  have hval : val7 M f = k := by
    have h13 : s8.rd 13 = k := hrk8.2.2.2.2.1
    simp [val7, hmf, toBytes, Weak.Prom.Ref.byteList, bv8, h13]; omega
  ihave #Hns : nSl g M sv.tk ek h f $$ []
  · rcases hh with rfl | rfl
    · iapply bsl_mem (F := fun t => nSl g M sv.tk ek 1 t) (List.mem_filter.2 ⟨mem_rng.2 hfM, hfB⟩) $$ Hn1
    · iapply bsl_mem (F := fun t => nSl g M sv.tk ek 2 t) (List.mem_filter.2 ⟨mem_rng.2 hfM, hfB⟩) $$ Hn2
  imod ndep7 g M sv.tk ek h f $$ [Hob HrB Hek] with #Hsh
  · iframe Hns; unfold Dn7; iexists b; iexists r; rw [hval]; iframe Hek; unfold prt; iframe Hob HrB
    ipureintro; exact ⟨by omega, by omega⟩
  have hnc := st_nonC (b := (Z : Int) + h) (by simp [Z, Ct, Y]; omega) (toBytes (s8.rd 13) 1) (srcR 16) (srcR 13) f
  ihave #HQ8 := QE7_snoc g M hnc.1 hnc.2 $$ HQ7
  imodintro
  isplitr
  · iapply QE7_st g M hnc.1 hnc.2 (ok7_z (o := h) hh3 (toBytes_length _ 1)) $$ HQ7
  isplitr
  · unfold fulT; ileft; iexact Hsh
  iintro %s9 %hs9 _ _
  imodintro
  iintro Hl
  obtain ⟨hP9, hc9, hq9⟩ := LPstep_at hs9 hP8 (by rw [hc8])
  have hrk9 := RKa_step hrk8 hs9 (by omega)
  obtain ⟨f9, -, -, -, -⟩ := wsSt_props (instrR (fencePost ws7 true true false true)) 16 13 ((Z : Int) + h)
    (toBytes (s8.rd 13) 1).length f (fI_fn hfi7 _ _ _ _)
  -- the round step
  iapply (roundG g M h pA xOf_pA 17 rfl rfl rfl
    iprop([∗list] k' ∈ (List.range 3).filter (fun k' => decide (k + 1 ≤ k')), eP ek h k' ∗ token (ak h k'))
    s9 _ _ _ k ⟨hP9, hq9, hc9, hrk9.2.2.2.2.1, hrk9.2.2.2.2.2.2, hrk9.1, hk3, f9⟩)
  iframe Htk Hl
  iintro %s10 %ws10 %⟨hk1', hP10, hq10, hc10, h13, hreg, hl10, hfi10, -⟩ Htk Hl
  ihave Hn := IH (k + 1) (by omega) (by omega) (by omega)
  iapply Hn $$ %s10 %ws10 %_ %_ %⟨hP10, hq10, hc10, ⟨hl10, by rw [hreg 9 (by decide)]; exact hrk9.2.1,
    by rw [hreg 11 (by decide)]; exact hrk9.2.2.1, by rw [hreg 12 (by decide)]; exact hrk9.2.2.2.1, h13,
    by rw [hreg 16 (by decide)]; exact hrk9.2.2.2.2.2.1, by rw [hreg 28 (by decide)]; exact hrk9.2.2.2.2.2.2⟩,
    hfi10⟩ [] Htk HQ8 Hl
  unfold ctx7; iframe Hdoom Hps Hn1 Hn2 Hfj Hbs

end h1

end Weak.Prom.OA.E4
