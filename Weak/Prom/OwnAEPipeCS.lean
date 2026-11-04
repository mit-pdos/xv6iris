/-
Weak/Prom: **E-a, G4 (4) with the dead set empty — hart 1's critical section and its release of L2** (stage E-a;
the steps of OwnAPipeCS.lean over `π4` and the per-byte owners of OwnAEPipeDefs.lean).

* `h1_cldE` — THE OWNED READ OF THE FIELD (plan R-a1), per byte: the latest write `c` (value 5: the verdict), or a
  later message touching the field — the points-to holds its `pend` (ANY such message: ordinary doom, every other
  resource kept), or it also touches a lock word (`π4` refutes it under the guard, `⟦t⟧ False`, `straddle4_grd`);
* `h1_relE` — xv6's release of L2 (`sw zero`): its `pend` is in the L2 word's bag hart 1 received through L1's
  publication (the bag above its acquiring AMO, which lies below the release by coherence).
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.OwnAEPipeH0

namespace Weak.Prom.OA.EP

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.PF Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Ref (Instr Test two64)
open Weak.Prom.Ref.Lit (X Y Z)
open Weak.Prom.OA.P (L1 p4h b4h xs4 p4h_at img4 w4 SV cAt5 q4 qs4 q4_snoc notCLd_st msgAt_of vals_of_src)
open Weak.Prom.OA.E
open PLabel
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode

section cs

variable {GF : BundledGFunctors} [GhostVarG GF HSt] [GhostVarG GF Bool] [TokenG GF] [SavedPropG GF] [InvGS GF]

/-- The guarded trace invariant, or doom. -/
def QP (g : AGN) (M : List PMsg) (ev : Trace) : IProp GF := iprop(⌜∃ V, grd π4 img4 M V (q4 ev)⌝ ∨ dshot g)

instance (g : AGN) (M : List PMsg) (ev : Trace) : Persistent (QP (GF := GF) g M ev) := by unfold QP; infer_instance

/-- The bad mode of a field read above `c`: doomed, or `⟦ex⟧ False`. -/
def badP (g : AGN) (M : List PMsg) (ex : Nat) : IProp GF := iprop(dshot g ∨ ⌜grd π4 img4 M ex False⌝)

instance (g : AGN) (M : List PMsg) (ex : Nat) : Persistent (badP (GF := GF) g M ex) := by
  unfold badP; infer_instance

theorem gq4_st {M : List PMsg} {ev : Trace} {e : PEv} (he : ∀ tvs, isCLd e tvs → tvs.map Prod.snd = toBytes 5 8)
    (h : ∃ V, grd π4 img4 M V (q4 ev)) : ∃ V, grd π4 img4 M V (q4 (ev ++ [e])) :=
  let ⟨V, hV⟩ := h; ⟨V, grd_imp (fun q => q4_snoc q he) hV⟩

/-- `pc = 13`: **xv6's release of L2** `sw zero,0(s1)`, its `pend` from the L2 word's bag; then the end. -/
theorem h1_relE (g : AGN) (M : List PMsg) (sv : SV) (s : LP) (ws : PState) (pr : GSet Nat) (ev : Trace) (lo : Nat)
    (hs : s.prog = b4h ∧ s.q = [] ∧ s.pc = 13 ∧ s.rd 9 = X) (hlo : lo ≤ coh ws Lk) :
    pCtxE (GF := GF) g M sv ∗ zBagE g M sv lo 0 ∗ QP g M ev ∗ lhA g π4 (w4 M 1) (qs4 1) ws pr ev ⊢
      wpKA g π4 (w4 M 1) qs4 s (Φ4E g M) := by
  obtain ⟨hprog, hq, hpc, h9⟩ := hs
  have hw := litW_x xs4 img4 M 1
  have hX := p4h_at hprog
  iintro ⟨#Hctx, Hz, #HQ, Hl⟩
  iapply (wpKA_sw (sz := 4) (rs2 := 0) (rs1 := 9) (off := 0) (base := Lk) hw
    (litAg_x hq hX (by rw [hpc]; rfl) rfl) hq (by rw [hprog, hpc]; rfl) (alg_of h9 (by decide) (by decide))
    (base_of h9 (by decide)))
  iframe Hl
  inext
  iintro %r %_ %hmsg %hcoh %_ _ _
  have hd0 : toBytes (s.rd 0) 4 = toBytes 0 4 := rfl
  rw [hd0] at hmsg hcoh
  have hc0 : coh ws Lk < r := by
    have := cohBelow_at (j := 0) hcoh (by decide)
    simpa using this
  have hr1 : 1 ≤ r := by omega
  have hmr := msgAt_of hr1 hmsg
  icases zBag_take0 (GF := GF) g M sv (by omega : lo < r) (lk_L2O (toBytes_length 0 4) hmr) (msgAt_le hmr) $$ Hz
    with ⟨Hp, -⟩
  imod shoot $$ Hp with #Hsh
  imodintro
  isplitl []
  · unfold QP
    icases HQ with (%hQ | #Hd)
    · ileft; ipureintro; exact ⟨gq4_st notCLd_st hQ, grd_intro (ok4_lk (toBytes_length _ _))⟩
    · iright; iexact Hd
  isplitr
  · unfold fulT; ileft; iexact Hsh
  iintro %s' %hs' _ _
  imodintro
  iintro Hl
  obtain ⟨hP', hc', hq'⟩ := LPstep_at hs' hprog (by rw [hpc])
  have hend : s'.prog.length ≤ s'.pc := by rw [hP', hc']; decide
  iapply (wpKA_end (v := ()) (litAg_xn hq' (fun x hx => by rw [p4h_at hP', hc'] at hx; cases hx)) hq' hend
    (by show litDone s' = some (); unfold litDone; rw [if_pos ⟨hq', hend⟩]))
  iframe Hl
  imodintro
  ileft; ipureintro; exact ⟨0, grd_intro trivial⟩

/-- `pc = 12`: `fence rw,w`. -/
theorem h1_fenceE (g : AGN) (M : List PMsg) (sv : SV) (s : LP) (ws : PState) (pr : GSet Nat) (ev : Trace)
    (lo : Nat) (hs : s.prog = b4h ∧ s.q = [] ∧ s.pc = 12 ∧ s.rd 9 = X) (hlo : lo ≤ coh ws Lk) :
    pCtxE (GF := GF) g M sv ∗ zBagE g M sv lo 0 ∗ QP g M ev ∗ lhA g π4 (w4 M 1) (qs4 1) ws pr ev ⊢
      wpKA g π4 (w4 M 1) qs4 s (Φ4E g M) := by
  obtain ⟨hprog, hq, hpc, h9⟩ := hs
  have hw := litW_x xs4 img4 M 1
  have hX := p4h_at hprog
  iintro ⟨#Hctx, Hz, HQ, Hl⟩
  iapply (wpKA_fence hw (litAg_x hq hX (by rw [hpc]; rfl) rfl) hq (by rw [hprog, hpc]; rfl))
  iframe Hl
  inext
  iintro %s1 %hs1 _ _
  imodintro
  iintro Hl
  obtain ⟨hP1, hc1, hq1⟩ := LPstep_at hs1 hprog (by rw [hpc])
  iapply (h1_relE g M sv s1 (instrR (fencePost ws true true false true)) _ ev lo
    ⟨hP1, hq1, hc1, by rw [LPstep_rd hs1 9 (.inr rfl), h9]⟩ hlo)
  iframe Hctx Hz HQ Hl

/-- `pc = 11`: `sd t2,(a1)`: its `pend` is in the field's bag (above `c`, not the bad read's `ex`). -/
theorem h1_cstE (g : AGN) (M : List PMsg) (sv : SV) (s : LP) (ws : PState) (pr : GSet Nat) (ev : Trace)
    (lo lw ex : Nat) (hs : s.prog = b4h ∧ s.q = [] ∧ s.pc = 11 ∧ s.rd 9 = X ∧ s.rd 11 = Y) (hlo : lo ≤ coh ws Lk)
    (hmd : (ex = 0 ∧ lw ≤ coh ws Ct) ∨ (lw < ex ∧ ∃ j : Nat, j < 8 ∧ ex ≤ coh ws (Ct + j))) :
    pCtxE (GF := GF) g M sv ∗ zBagE g M sv lo 0 ∗ ([∗list] t ∈ cBX M lw ex, pend g t) ∗ QP g M ev ∗
      lhA g π4 (w4 M 1) (qs4 1) ws pr ev ⊢ wpKA g π4 (w4 M 1) qs4 s (Φ4E g M) := by
  obtain ⟨hprog, hq, hpc, h9, h11⟩ := hs
  have hw := litW_x xs4 img4 M 1
  have hX := p4h_at hprog
  iintro ⟨#Hctx, Hz, Hb, #HQ, Hl⟩
  iapply (wpKA_sw (sz := 8) (rs2 := 7) (rs1 := 11) (off := 0) (base := Ct) hw
    (litAg_x hq hX (by rw [hpc]; rfl) rfl) hq (by rw [hprog, hpc]; rfl) (alg_of h11 (by decide) (by decide))
    (base_of h11 (by decide)))
  iframe Hl
  inext
  iintro %ts %_ %hmsg %hcoh %_ _ _
  rw [toBytes_length] at hcoh
  have hcj : ∀ j : Nat, j < 8 → coh ws (Ct + j) < ts := fun j hj => cohBelow_at hcoh hj
  have hts1 : 1 ≤ ts := by have := hcj 0 (by decide); omega
  have hC := isC_of_msg (by decide : 1 < 2) (toBytes_length _ _) hts1 hmsg
  have htsM := msgAt_le (msgAt_of hts1 hmsg)
  have hlts : lw < ts := by
    rcases hmd with ⟨_, hle⟩ | ⟨hlt, j, hj, hle⟩
    · have := hcj 0 (by decide); simp at this; omega
    · have := hcj j hj; omega
  have hexts : ts ≠ ex := by
    rcases hmd with ⟨rfl, _⟩ | ⟨_, j, hj, hle⟩
    · omega
    · have := hcj j hj; omega
  unfold cBX
  icases bsl_filter_take (pend g) (fun t => decide (lw < t) && decide (t ≠ ex) && isCO M t) (fun _ => false) ts
    (by simp [hlts, C_CO hC, hexts]) (fun _ h => by cases h) (rng M) (mem_rng.2 htsM) (nodup_rng M) $$ Hb
    with ⟨Hp, -⟩
  imod shoot $$ Hp with #Hsh
  imodintro
  isplitl []
  · unfold QP
    icases HQ with (%hQ | #Hd)
    · ileft; ipureintro; exact ⟨gq4_st notCLd_st hQ, grd_intro (ok4_ct (toBytes_length _ _))⟩
    · iright; iexact Hd
  isplitr
  · unfold fulT; ileft; iexact Hsh
  iintro %s1 %hs1 _ _
  imodintro
  iintro Hl
  obtain ⟨hP1, hc1, hq1⟩ := LPstep_at hs1 hprog (by rw [hpc])
  iapply (h1_fenceE g M sv s1 _ _ _ lo ⟨hP1, hq1, hc1, by rw [LPstep_rd hs1 9 (.inr rfl), h9]⟩
    (Nat.le_trans hlo (C.st_coh _ _ _ _ _ _ Lk)))
  iframe Hctx Hz Hl
  unfold QP
  icases HQ with (%hQ | #Hd)
  · ileft; ipureintro; exact gq4_st notCLd_st hQ
  · iright; iexact Hd

/-- `pc = 10`: `addi t2,t2,1`. -/
theorem h1_addiE (g : AGN) (M : List PMsg) (sv : SV) (s : LP) (ws : PState) (pr : GSet Nat) (ev : Trace)
    (lo lw ex : Nat) (hs : s.prog = b4h ∧ s.q = [] ∧ s.pc = 10 ∧ s.rd 9 = X ∧ s.rd 11 = Y) (hlo : lo ≤ coh ws Lk)
    (hmd : (ex = 0 ∧ lw ≤ coh ws Ct) ∨ (lw < ex ∧ ∃ j : Nat, j < 8 ∧ ex ≤ coh ws (Ct + j))) :
    pCtxE (GF := GF) g M sv ∗ zBagE g M sv lo 0 ∗ ([∗list] t ∈ cBX M lw ex, pend g t) ∗ QP g M ev ∗
      lhA g π4 (w4 M 1) (qs4 1) ws pr ev ⊢ wpKA g π4 (w4 M 1) qs4 s (Φ4E g M) := by
  obtain ⟨hprog, hq, hpc, h9, h11⟩ := hs
  have hw := litW_x xs4 img4 M 1
  iintro ⟨#Hctx, Hz, Hb, HQ, Hl⟩
  iapply (wpKA_alui hw (litAg_x hq (p4h_at hprog) (by rw [hpc]; rfl) rfl) hq (by rw [hprog, hpc]; rfl) (by decide))
  iframe Hl
  inext
  iintro %s1 %hs1 _ _
  imodintro
  iintro Hl
  obtain ⟨hP1, hc1, hq1⟩ := LPstep_at hs1 hprog (by rw [hpc])
  iapply (h1_cstE g M sv s1 (instrR (regWP ws 7 (srcR 7))) _ ev lo lw ex
    ⟨hP1, hq1, hc1, by rw [LPstep_rd hs1 9 (.inl (by decide)), h9], by rw [LPstep_rd hs1 11 (.inl (by decide)), h11]⟩
    hlo hmd)
  iframe Hctx Hz Hb HQ Hl

/-- **THE CRITICAL SECTION** (`pc = 9`, `ld t2,(a1)`; `addi t2,t2,1`; then the store): the owned read of the field
(plan R-a1, per byte); the verdict's obligation (the value is 5) is discharged here, or by doom / the guard. -/
theorem h1_cldE (g : AGN) (M : List PMsg) (sv : SV) (s : LP) (ws : PState) (pr : GSet Nat) (ev : Trace)
    (lo c : Nat) (hs : s.prog = b4h ∧ s.q = [] ∧ s.pc = 9 ∧ s.rd 9 = X ∧ s.rd 11 = Y) (hlo : lo ≤ coh ws Lk)
    (hc5 : cAt5 M c) (hvr : c ≤ ws.wVrNew) (hq4 : q4 ev) (hnoinv : ∀ t a, ¬ cmoAt M isInvalK t a) :
    pCtxE (GF := GF) g M sv ∗ zBagE g M sv lo 0 ∗ cPtsP g M c ∗ lhA g π4 (w4 M 1) (qs4 1) ws pr ev ⊢
      wpKA g π4 (w4 M 1) qs4 s (Φ4E g M) := by
  obtain ⟨hprog, hq, hpc, h9, h11⟩ := hs
  have hw := litW_x xs4 img4 M 1
  have hX := p4h_at hprog
  iintro ⟨#Hctx, Hz, Hc, Hl⟩
  unfold cPtsP
  icases Hc with ⟨%hlw, Hb⟩
  rw [cB_X]
  iapply (wpKA_ld (sz := 8) (sgn := true) (rd := 7) (rs1 := 11) (off := 0) (base := Ct) hw
    (litAg_x hq hX (by rw [hpc]; rfl) rfl) hq (by rw [hprog, hpc]; rfl) (alg_of h11 (by decide) (by decide))
    (base_of h11 (by decide)))
  iframe Hl
  inext
  iintro %tvs1 %hl1 %hlo1 _ _
  have hvp : c ≤ ldPre ws false false (srcsView ws (srcR 11)) :=
    Nat.le_trans hvr (PF.ldPre_ge ws false false (srcsView ws (srcR 11))).2.1
  have hwk := loadOk_weak hlo1
  have hcases := cld_cases (img := img4) hlw hvp 0 tvs1 (by rw [hl1]; decide) (by simpa using hwk)
  have hcohj := (loadBytes_coh false (ldPre ws false false (srcsView ws (srcR 11))) ws Ct tvs1).2
  -- THE MODE after the read: clean (value 5), or bad (doomed / guarded-false)
  ihave Hmode : |={⊤}=> ∃ ex, ([∗list] t ∈ cBX M c ex, pend g t) ∗
      ((⌜ex = 0 ∧ tvs1.map Prod.snd = toBytes 5 8 ∧
          c ≤ coh (loadRun ws false false (srcsView ws (srcR 11)) Ct tvs1) Ct⌝) ∨
        (badP g M ex ∗ ⌜c < ex ∧ ∃ j : Nat, j < 8 ∧
          ex ≤ coh (loadRun ws false false (srcsView ws (srcR 11)) Ct tvs1) (Ct + j)⌝)) $$ [Hb]
  · rcases hcases with hall | ⟨j, t, v, hj, hlt, hwt⟩ | ⟨ti, hti, j, hj, hc⟩
    · obtain ⟨t0, v0, r0, rfl⟩ := tvs_cons hl1 (by decide)
      have h0 := loadRun_coh0 ws false false (srcsView ws (srcR 11)) Ct t0 v0 r0
      have ht0 : t0 = c := hall (t0, v0) (List.mem_cons_self ..)
      have hval := vals_of_src (img := img4) hc5 rfl 0 ((t0, v0) :: r0)
        (by rw [hl1, toBytes_length]; decide) (by
          have := bytesAll_mono (fun _ _ _ hh => hh.1) _ _ hwk
          simpa using this) hall
      have hv5 : ((t0, v0) :: r0).map Prod.snd = toBytes 5 8 := by
        rw [hval, hl1]; rfl
      imodintro; iexists 0; iframe Hb; ileft; ipureintro
      exact ⟨rfl, hv5, by rw [← ht0]; exact h0⟩
    · have hj8 : j < 8 := by rw [← hl1]; exact (List.getElem?_eq_some_iff.1 hj).1
      have htM : 1 ≤ t ∧ t ≤ M.length := by obtain ⟨m, hm, _⟩ := hwt; exact msgAt_le hm
      have hcoh : t ≤ coh (loadRun ws false false (srcsView ws (srcR 11)) Ct tvs1) (Ct + j) :=
        (bytesAll_get hcohj hj).2
      have hwt' : wrB M (Ct + j) t := by simpa using hwt
      obtain ⟨m, hm, hb⟩ := hwt'
      rcases c_cls hm hj8 hb with hCO | hL
      · -- the points-to holds its `pend`: doom (plan R-a1), every other resource kept
        unfold cBX
        icases bsl_filter_take (pend g) (fun t => decide (c < t) && decide (t ≠ 0) && isCO M t)
          (fun x => decide (c < x) && decide (x ≠ t) && isCO M x) t (by simp [hlt, hCO]; omega)
          (fun x hx => by
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hx ⊢
            exact ⟨⟨⟨hx.1.1, by omega⟩, hx.2⟩, hx.1.2⟩) (rng M) (mem_rng.2 htM) (nodup_rng M)
          $$ Hb with ⟨Hp, Hb⟩
        unfold pCtxE
        icases Hctx with ⟨Hdoom, -⟩
        imod doom (E := ⊤) CoPset.subseteq_top g M t htM $$ [Hdoom Hp] with #Hd
        · iframe Hdoom Hp
        imodintro; iexists t; iframe Hb; iright; isplitl []
        · unfold badP; ileft; iexact Hd
        · ipureintro; exact ⟨hlt, j, hj8, hcoh⟩
      · -- a lock word owns it: THE GUARD refutes it, every resource kept
        imodintro; iexists t; isplitl [Hb]
        · unfold cBX
          iapply bsl_filter_mono (pend g) _ _ (fun x hx => by
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hx ⊢
            exact ⟨⟨hx.1.1, by omega⟩, hx.2⟩) (rng M) $$ Hb
        iright; isplitl []
        · unfold badP; iright; ipureintro; exact straddle4_grd hm hL hj8 hb
        · ipureintro; exact ⟨hlt, j, hj8, hcoh⟩
    · exact absurd hc (hnoinv _ _)
  imod Hmode with ⟨%ex, Hb, Hm⟩
  have hlo' : lo ≤ coh (qPosts (loadRun ws false false (srcsView ws (srcR 11)) Ct tvs1)
      (regWL 7 [.DLdRes] ++ [LInstr])) Lk := by
    have := (loadRun_mono ws false false (srcsView ws (srcR 11)) Ct tvs1).2.2.2.2.2.2.2.2.2.2.1 Lk
    exact Nat.le_trans hlo this
  icases Hm with (%hcl | ⟨#Hbad, %hra⟩)
  · obtain ⟨rfl, hv5, hcc⟩ := hcl
    imodintro
    isplitr
    · ileft; ipureintro
      exact ⟨0, grd_intro (q4_snoc hq4 (fun tvs ⟨_, h⟩ => by cases h; exact hv5))⟩
    iintro %s1 %hs1 _ _
    imodintro
    iintro Hl
    obtain ⟨hP1, hc1, hq1⟩ := LPstep_at hs1 hprog (by rw [hpc])
    iapply (h1_addiE g M sv s1 _ _ _ lo c 0 ⟨hP1, hq1, hc1, by rw [LPstep_rd hs1 9 (.inl (by decide)), h9],
      by rw [LPstep_rd hs1 11 (.inl (by decide)), h11]⟩ hlo' (.inl ⟨rfl, hcc⟩))
    iframe Hctx Hz Hb Hl
    unfold QP; ileft; ipureintro
    exact ⟨0, grd_intro (q4_snoc hq4 (fun tvs ⟨_, h⟩ => by cases h; exact hv5))⟩
  · imodintro
    isplitr
    · unfold badP
      icases Hbad with (#Hd | %hgf)
      · iright; iexact Hd
      · ileft; ipureintro; exact ⟨ex, fun hv => (hgf hv).elim⟩
    iintro %s1 %hs1 _ _
    imodintro
    iintro Hl
    obtain ⟨hP1, hc1, hq1⟩ := LPstep_at hs1 hprog (by rw [hpc])
    iapply (h1_addiE g M sv s1 _ _ _ lo c ex ⟨hP1, hq1, hc1, by rw [LPstep_rd hs1 9 (.inl (by decide)), h9],
      by rw [LPstep_rd hs1 11 (.inl (by decide)), h11]⟩ hlo' (.inr hra))
    iframe Hctx Hz Hb Hl
    unfold QP badP
    icases Hbad with (#Hd | %hgf)
    · iright; iexact Hd
    · ileft; ipureintro; exact ⟨ex, fun hv => (hgf hv).elim⟩

end cs

end Weak.Prom.OA.EP
