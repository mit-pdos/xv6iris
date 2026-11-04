/-
Weak/Prom: **G4 target (4) on track (a): hart 1 — xv6's acquire of L1 (publication), xv6's acquire of the
runtime-born L2** (stage S4a part 4; plan rev 7 §4 G4 (4); §3 "Acquire", "Atomicity", "Opening", R-a4).

* `h1_loop1` (Löb at `pc = 1`): the L1 spin loop; at the aq AMO's continuation (frontier `≥ ts`) the word is 1
  (spin) or 0 read from hart 0's release `s`, whose slot yields `Pub1 s`: the L2 HANDLE `isLockAt … γ Lk (cPts c) b`
  with RUNTIME `γ`, `b, c < s`, and the `pend`s of hart 0's later L2 words.  After the aq AMO the view is `≥ ts > s`,
  so `b` and `c` lie below it.
* `h1_loop2` (Löb at `pc = 5`): the L2 spin loop.  Its read's pre-view is `≥ b`, so (R-a4) no byte comes from the
  junk `j < b` or the image; the word is 1 (spin) or 0 read from the birth `b` (`l2_acq`, `l2_src0`); then the AMO is
  the first L2 write after `b` (`l2_chain`) and its token opens the saved-proposition slot of `b` (`bslot_claim`):
  `cPts c ∗ token γ`, the resource hart 0 deposited at its L1 release.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.OwnAPipeCS

namespace Weak.Prom.OA.P

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.PF Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Ref (Instr Test two64)
open Weak.Prom.Ref.Lit (X Y Z)
open PLabel
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode

/-- The state after `amoswap.w.aq a5,a5,(r)`, `sext.w a5,a5`, `bnez a5`. -/
abbrev postA (ws : PState) (r : Nat) (base : Int) (tvs : List (Nat × BitVec 8)) (ts n : Nat) : PState :=
  instrR (ctrlP (instrR (regWP (qPosts (amoPost (storeRun (loadRun ws true false (srcsView ws (srcR r)) base tvs)
    false (srcsView ws (srcR r)) ts base n ts) true ts) (regWL 15 [.DLdRes] ++ [LInstr])) 15 (srcR 15)))
    (srcR 15 ++ srcR 0))

theorem postA_vr (ws : PState) (r : Nat) (base : Int) (tvs : List (Nat × BitVec 8)) (ts n : Nat) :
    ws.wVrNew ≤ (postA ws r base tvs ts n).wVrNew ∧ ts ≤ (postA ws r base tvs ts n).wVrNew := by
  have := (loadRun_mono ws true false (srcsView ws (srcR r)) base tvs).2.2.2.2.2.2.2.1
  simp only [postA, regWL, show (15 : Nat) ≠ 0 by decide, if_false, List.singleton_append, qPosts, qPost,
    instrR_vrNew, ctrlP_vrNew, regWP_vrNew, amoPost_vrNew, if_true, storeRun_vrNew]
  omega

theorem postA_wf (ws : PState) (r : Nat) (base : Int) (tvs : List (Nat × BitVec 8)) (ts n : Nat) :
    ts ≤ wfr (qPosts (amoPost (storeRun (loadRun ws true false (srcsView ws (srcR r)) base tvs)
      false (srcsView ws (srcR r)) ts base n ts) true ts) (regWL 15 [.DLdRes] ++ [LInstr]).dropLast) := by
  show ts ≤ stFloor _
  unfold stFloor
  simp only [regWL, show (15 : Nat) ≠ 0 by decide, if_false, List.singleton_append, List.dropLast, qPosts, qPost,
    regWP_vwNew, amoPost_vwNew, if_true]
  omega

theorem postA_coh (ws : PState) (r : Nat) (base : Int) (tvs : List (Nat × BitVec 8)) (ts n : Nat) (hn : 0 < n) :
    ts ≤ coh (postA ws r base tvs ts n) base :=
  storeRun_coh0 (loadRun ws true false (srcsView ws (srcR r)) base tvs) false (srcsView ws (srcR r)) ts base n ts hn

/-- `sext.w; bnez` on the AMO's 4-byte result `toBytes k 4` (`k ∈ {0, 1}`): `a5 = k`. -/
theorem a5_val {s1 s2 : LP} {tvs : List (Nat × BitVec 8)} {k : Nat} (hk : k = 0 ∨ k = 1)
    (e15 : s1.rd 15 = Weak.Prom.Ref.sext 4 (ofBytes (tvs.map Prod.snd)) % two64) (hv : tvs.map Prod.snd = toBytes k 4)
    (hs2 : LPstep s1 s2 (s1.pc + 1) 15 (addiwV (s1.rd 15) 0)) (hlen : s1.regs.length = 32) : s2.rd 15 = k := by
  rw [LPstep_rd_eq hs2 (by decide) (by omega), e15, hv]
  rcases hk with rfl | rfl <;> decide

section h1

variable {GF : BundledGFunctors} [GhostVarG GF HSt] [GhostVarG GF Bool] [TokenG GF] [SavedPropG GF] [InvGS GF]

/-- The hart's state at the L2 loop head (`pc = 5`). -/
def lhS2 (s : LP) : Prop :=
  s.prog = b4h ∧ s.q = [] ∧ s.pc = 5 ∧ s.rd 14 = 1 ∧ s.rd 9 = X ∧ s.rd 11 = Y ∧ s.rd 12 = Z ∧ s.regs.length = 32

/-- **THE L2 SPIN LOOP** (Löb induction at `pc = 5`; see the header). -/
theorem h1_loop2 (g : AGN) (M : List PMsg) (sv : SV) (hdd : g.dd = dd4 M) (γ : GName) (b c : Nat)
    (hb : bthAt M Lk b) (hc5 : cAt5 M c)
    (hnoinv : ∀ t a, ¬ cmoAt M isInvalK t a := by assumption) :   -- [rebase-repair] MachFix-R-b5: `vi = 0`
    ⊢ ∀ (s : LP) (ws : PState) (pr : GSet Nat) (ev : Trace) (lo : Nat), ⌜lhS2 s⌝ -∗
      ⌜lo ≤ coh ws Lk ∧ b ≤ ws.wVrNew ∧ c ≤ ws.wVrNew ∧ q4 ev⌝ -∗ pCtx (GF := GF) g M sv -∗
      isLockAt M sv γ Lk (cPts g M c) b -∗ ob2 g M sv lo 0 -∗ r2Bag g M -∗ zBag g M b -∗
      lhA g Proto.triv (w4 M 1) (qs4 1) ws pr ev -∗ wpKA g Proto.triv (w4 M 1) qs4 s (Φ4 g M) := by
  have hw := litW_x xs4 img4 M 1
  iloeb as IH
  iintro %s0 %ws0 %pr0 %ev %lo %hs %hl0 #Hctx #Hlk Hbag Hr2 Hz Hl
  obtain ⟨hprog0, hq0, hpc0, h14, h9_0, h11_0, h12_0, hlen0⟩ := hs
  obtain ⟨hlo0, hb0, hcv0, hq4⟩ := hl0
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
  -- `amoswap.w.aq a5,a5,(s1)`
  iapply (wpKA_amo (base := Lk) hw (litAg_x hq hX (by rw [hpc]; rfl) rfl) hq (by rw [hprog, hpc]; rfl)
    (alg_L2 h9) (by rw [h9]))
  iframe Hl
  inext
  iintro %tvs %ts %hlen4 %_ %hmsg %hlo1 %hex %hcoh %_ _ _
  have hd1 : amoD .swap 4 (s.rd 15) tvs = toBytes 1 4 := amo_msg1 h15
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
  have hmt := msgAt_of hts1 hmsg
  have hk4 : knd M ts = 4 := by rw [knd_of hmt]; exact kind_a2
  have htsM := msgAt_le hmt
  have hlo : lo ≤ coh (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) Lk := hlo0
  have hlots : lo < ts := by omega
  -- the AMO's own message: its `pend` and token from the bag
  unfold ob2
  icases Hbag with ⟨HbA, HbL⟩
  unfold bagKX
  icases bsl_filter_take (pend g) (fun t => decide (lo < t) && decide (t ≠ 0) && isK M 4 t)
    (fun t => decide (lo < t) && decide (t ≠ ts) && isK M 4 t) ts (by simp [hlots, isK, hk4]; omega)
    (fun t ht => by
      simp only [Bool.and_eq_true, decide_eq_true_eq] at ht ⊢
      exact ⟨⟨⟨ht.1.1, by omega⟩, ht.2⟩, ht.1.2⟩) (rng M) (mem_rng.2 htsM) (nodup_rng M)
    $$ HbA with ⟨Hp, HbA⟩
  icases bsl_filter_take (fun t => token (sv.tk t)) (fun t => decide (lo < t) && decide (t ≠ 0) && isK M 4 t)
    (fun t => decide (lo < t) && decide (t ≠ ts) && isK M 4 t) ts (by simp [hlots, isK, hk4]; omega)
    (fun t ht => by
      simp only [Bool.and_eq_true, decide_eq_true_eq] at ht ⊢
      exact ⟨⟨⟨ht.1.1, by omega⟩, ht.2⟩, ht.1.2⟩) (rng M) (mem_rng.2 htsM) (nodup_rng M)
    $$ HbL with ⟨Ht, HbL⟩
  imod shoot $$ Hp with #Hsh
  imodintro
  isplitr
  · ileft; ipureintro
    exact ⟨⟨0, grd_intro (q4_snoc hq4 notCLd_rmw)⟩, grd_intro trivial⟩
  isplitr
  · unfold fulT; ileft; iexact Hsh
  iintro %s1 %hs1 #Hfr Hc
  have hts_f := postA_wf (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) 9 Lk tvs ts
    (amoD .swap 4 (s.rd 15) tvs).length
  have hsrc : bytesAll (fun x u _ => u ≤ coh (loadRun (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) true false
      (srcsView (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) (srcR 9)) Lk tvs) x) Lk tvs :=
    bytesAll_mono (fun _ _ _ hh => hh.2) _ _
      (loadBytes_coh true (ldPre (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) true false
        (srcsView (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) (srcR 9))) (instrR (regWP ws0 15 (srcR 0 ++ srcR 14)))
        Lk tvs).2
  have hwts : wrB M Lk ts := by
    refine ⟨_, hmt, ?_⟩
    have := byteAt_off (m := ⟨Lk, toBytes 1 4, some 1, .excl⟩) (p := Lk) (k := 0) rfl
    rw [show Lk + ((0 : Nat) : Int) = Lk by simp] at this
    rw [this]; rfl
  have hbv : b ≤ ldPre (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) true false
      (srcsView (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) (srcR 9)) :=
    Nat.le_trans hb0 (PF.ldPre_ge (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) true false _).2.1
  obtain ⟨hP1, hc1, hq1⟩ := LPstep_at hs1 hprog (by rw [hpc])
  have e9 : s1.rd 9 = X := by rw [LPstep_rd hs1 9 (.inl (by decide)), h9]
  have e11 : s1.rd 11 = Y := by rw [LPstep_rd hs1 11 (.inl (by decide)), h11]
  have e12 : s1.rd 12 = Z := by rw [LPstep_rd hs1 12 (.inl (by decide)), h12]
  have e14 : s1.rd 14 = 1 := by rw [LPstep_rd hs1 14 (.inl (by decide)), h14']
  have hlen1 : s1.regs.length = 32 := hs1.2.2.2.1.trans hlen
  have e15 := LPstep_rd_eq hs1 (by decide) (by omega)
  have hb := hb
  unfold isLockAt
  icases Hlk with ⟨_, #Hds, #HsQ, #Hslot⟩
  imod l2_acq g M sv hdd (π := Proto.triv) (ws := instrR (regWP ws0 15 (srcR 0 ++ srcR 14)))
    (ws1 := qPosts (amoPost (storeRun (loadRun (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) true false
      (srcsView (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) (srcR 9)) Lk tvs) false
      (srcsView (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) (srcR 9)) ts Lk (amoD .swap 4 (s.rd 15) tvs).length ts)
      true ts) (regWL 15 [.DLdRes] ++ [LInstr]).dropLast)
    hlen4 hlo1 hb hbv hsrc hcohB hts_f $$ [Hr2 Hz] with (⟨#Hf, #Hd⟩ | ⟨Hr2, Hz, %hv⟩)
  · iframe Hctx Hfr Hr2 Hz
  · -- free mode
    imodintro
    iintro Hl
    ihave Hfree := p4h_free (GF := GF) g M hdd
    have hfr : frS4 s1 := ⟨hP1, hq1, by rw [hc1]; decide, by rw [hc1]; decide, e9, e11, e12, e14, hlen1,
      fun h => by omega⟩
    iapply Hfree $$ %s1 %_ %_ %_ %hfr Hf Hd Hl
  rcases hv with hv | hv
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
    have hbr : (if Weak.Prom.Ref.brEval .ne (s2.rd 15) (s2.rd 0) then 5 else s2.pc + 1) = 5 := by
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
    have hls : lhS2 s3 := ⟨hP3, hq3, hc3, r14, r9, r11, r12, hs3.2.2.2.1.trans hlen2⟩
    have hvr := postA_vr (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) 9 Lk tvs ts (amoD .swap 4 (s.rd 15) tvs).length
    have hcs := postA_coh (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) 9 Lk tvs ts (amoD .swap 4 (s.rd 15) tvs).length
      (by rw [hlenD]; decide)
    have hb0' : b ≤ (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))).wVrNew := hb0
    have hcv0' : c ≤ (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))).wVrNew := hcv0
    iapply IH $$ %s3 %_ %_ %_ %ts %hls %⟨hcs, by omega, by omega, q4_snoc hq4 notCLd_rmw⟩ Hctx [Hds HsQ Hslot]
      [HbA HbL] Hr2 Hz Hl
    · iframe Hds HsQ Hslot; ipureintro; exact hb
    isplitl [HbA]
    · iapply bsl_filter_mono (pend g) _ _ (fun t ht => by
        simp only [Bool.and_eq_true, decide_eq_true_eq] at ht ⊢
        exact ⟨⟨by omega, by omega⟩, ht.2⟩) (rng M) $$ HbA
    · iapply bsl_filter_mono (fun t => token (sv.tk t)) _ _ (fun t ht => by
        simp only [Bool.and_eq_true, decide_eq_true_eq] at ht ⊢
        exact ⟨⟨by omega, by omega⟩, ht.2⟩) (rng M) $$ HbL
  · -- the word is 0: byte 0 came from the birth `b`
    imod l2_src0 g M sv hdd (π := Proto.triv) (ws := instrR (regWP ws0 15 (srcR 0 ++ srcR 14)))
      (ws1 := qPosts (amoPost (storeRun (loadRun (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) true false
        (srcsView (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) (srcR 9)) Lk tvs) false
        (srcsView (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) (srcR 9)) ts Lk (amoD .swap 4 (s.rd 15) tvs).length ts)
        true ts) (regWL 15 [.DLdRes] ++ [LInstr]).dropLast)
      hlen4 hlo1 hb hbv hsrc hcohB hts_f hv $$ [Hr2 Hz] with (⟨#Hf, #Hd⟩ | ⟨Hr2, Hz, %hsb⟩)
    · iframe Hctx Hfr Hr2 Hz
    · imodintro
      iintro Hl
      ihave Hfree := p4h_free (GF := GF) g M hdd
      have hfr : frS4 s1 := ⟨hP1, hq1, by rw [hc1]; decide, by rw [hc1]; decide, e9, e11, e12, e14, hlen1,
        fun h => by omega⟩
      iapply Hfree $$ %s1 %_ %_ %_ %hfr Hf Hd Hl
    obtain ⟨v0, r0, rfl⟩ := hsb
    have hbts : b < ts := by
      have h1 := bytesAll_get (j := 0) hsrc rfl
      have h2 := hcohB 0 (by decide)
      simp at h1 h2; omega
    obtain ⟨_, hr0⟩ := loadOk_b0 hlo1
    rcases hr0 with hr0 | ⟨ti, hci, hti, _⟩
    rotate_left
    · -- an invalidate on the path: dead
      obtain ⟨hk, hle⟩ := cmo_knd (by omega) hci
      imod pCtx_read_dead g M sv hdd ⟨by omega, hle⟩ hk $$ Hctx with ⟨#Hf, #Hd⟩
      imodintro
      iintro Hl
      ihave Hfree := p4h_free (GF := GF) g M hdd
      have hfr : frS4 s1 := ⟨hP1, hq1, by rw [hc1]; decide, by rw [hc1]; decide, e9, e11, e12, e14, hlen1,
        fun h => by omega⟩
      iapply Hfree $$ %s1 %_ %_ %_ %hfr Hf Hd Hl
    have hx0 : ¬ writesInBy M (fun tid => tid ≠ some 1) Lk b (ts - 1) := hex.1
    imod l2_chain g M sv hdd (π := Proto.triv) (ws := instrR (regWP ws0 15 (srcR 0 ++ srcR 14)))
      (ws1 := qPosts (amoPost (storeRun (loadRun (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) true false
        (srcsView (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) (srcR 9)) Lk ((b, v0) :: r0)) false
        (srcsView (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) (srcR 9)) ts Lk
        (amoD .swap 4 (s.rd 15) ((b, v0) :: r0)).length ts) true ts) (regWL 15 [.DLdRes] ++ [LInstr]).dropLast)
      (lo := lo) (vpre := ldPre (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) true false
        (srcsView (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) (srcR 9)))
      hbts hts_f hwts hlo hr0 hx0 $$ [HbA HbL Hr2] with (⟨Hbag, Hr2, %hn⟩ | ⟨#Hf, #Hd⟩)
    · iframe Hctx Hfr Hr2; unfold ob2 bagKX; iframe HbA HbL
    rotate_left
    · imodintro
      iintro Hl
      ihave Hfree := p4h_free (GF := GF) g M hdd
      have hfr : frS4 s1 := ⟨hP1, hq1, by rw [hc1]; decide, by rw [hc1]; decide, e9, e11, e12, e14, hlen1,
        fun h => by omega⟩
      iapply Hfree $$ %s1 %_ %_ %_ %hfr Hf Hd Hl
    -- THE CLAIM: the token of the AMO reading `b` opens `b`'s saved-proposition slot
    imod bslot_claim M sv b ts hn iprop(cPts g M c ∗ token γ) $$ [Ht Hc] with HR
    · iframe Hslot Hds HsQ Ht Hc
    icases HR with >⟨HC, -⟩
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
    have hbr : (if Weak.Prom.Ref.brEval .ne (s2.rd 15) (s2.rd 0) then 5 else s2.pc + 1) = 9 := by
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
    have hvr := postA_vr (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) 9 Lk ((b, v0) :: r0) ts
      (amoD .swap 4 (s.rd 15) ((b, v0) :: r0)).length
    have hcv0' : c ≤ (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))).wVrNew := hcv0
    iapply (h1_cld g M sv hdd s3 _ _ _ c ⟨hP3, hq3, hc3, r9, r11, r12, r14, hs3.2.2.2.1.trans hlen2⟩ hc5
      (Nat.le_trans hcv0' hvr.1) (q4_snoc hq4 notCLd_rmw))
    iframe Hctx Hr2 HC Hl

end h1

end Weak.Prom.OA.P
