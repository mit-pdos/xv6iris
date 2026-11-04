/-
Weak/Prom: **E-a2 — an acquirer (hart 1 or 2): the publication wait, the claim of its part, the contended L2 loop**
(stage E-a2; OwnAE1c.lean's loop and OwnAEPipeH1.lean's loops over the owners of OwnAE2Defs.lean).

* `floop5` — `lw t0,0(a2); bnez t0,0; fence rw,rw`: the word at `Z` read 0 in byte 0 comes from a message (the
  image holds 1); after the fence it is below the frontier, so it is the publication (`fSlot5`, persistent content:
  the L2 handle and `lkB5 b`) or the flag's junk (absurd).  The hart then CLAIMS ITS OWN PART of the lock born at
  `b` (`hclaim5`, its boot token `ak h b`): its own-message bag above `b`.
* `loop5` — (1c)'s spin loop on the RUNTIME-BORN lock: the read floor covers the birth (the publication's view),
  the acquire `acq5` (contended: other harts' releases and acquires are in the protocol `lkB5 b`).
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.OwnAE2CS

namespace Weak.Prom.OA.E2

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.PF Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Ref (Instr Test two64)
open Weak.Prom.Ref.Lit (X Y Z)
open Weak.Prom.OA.P (L1 SV bthAt isLockAt cAt5 msgAt_of postA postA_vr postA_wf postA_coh a5_val alg_L2 amo_msg1
  mv_15)
open Weak.Prom.OA.E
open Weak.Prom.OA.EP (π4 ok4_lk tL1_of lk_wr)
open PLabel
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode

theorem postA_vw (ws : PState) (r : Nat) (base : Int) (tvs : List (Nat × BitVec 8)) (ts n : Nat) :
    ts ≤ (postA ws r base tvs ts n).wVwNew := by
  simp only [postA, regWL, show (15 : Nat) ≠ 0 by decide, if_false, List.singleton_append, qPosts, qPost,
    instrR_vwNew, ctrlP_vwNew, regWP_vwNew, amoPost_vwNew, if_true]
  omega

/-- `lw` read 0 (sign-extended, mod 2⁶⁴): byte 0 is 0. -/
theorem lw0 {t : Nat} {v : BitVec 8} {r : List (Nat × BitVec 8)} (hl : r.length = 3)
    (h : ldVal true 4 ((t, v) :: r) % two64 = 0) : v = 0 := by
  match r, hl with
  | [(_, v1), (_, v2), (_, v3)], _ =>
    have h0 : v.toNat < 256 := v.isLt
    have h1 : v1.toNat < 256 := v1.isLt
    have h2 : v2.toNat < 256 := v2.isLt
    have h3 : v3.toNat < 256 := v3.isLt
    simp only [ldVal, if_true, Weak.Prom.Ref.sext, ofBytes, Weak.Prom.Ref.bytesVal, List.map, List.foldr, two64] at h
    simp only [show (2:Nat) ^ (8 * 4 - 1) = 2147483648 from rfl, show (2:Nat) ^ (8 * 4) = 4294967296 from rfl] at h
    apply BitVec.eq_of_toNat_eq
    show v.toNat = 0
    split at h <;> omega

theorem ld_nonC {a : Int} (ha : a ≠ Ct) (tvs0 : List (Nat × BitVec 8)) (s : List Dsrc) :
    (∀ tvs, ¬ isCLd (LLoad false false a tvs0 s, none) tvs) ∧
      (∀ ts, ¬ isCSt (LLoad false false a tvs0 s, none) ts) := by
  refine ⟨fun _ ⟨_, h⟩ => ?_, fun _ ⟨_, _, _, h⟩ => ?_⟩
  · injection h with h1; injection h1 with _ _ h3; exact ha h3
  · cases h

/-- The hart's state at the L2 loop head (`pc = 4`, `mv a5,a4`). -/
def lhS5 (s : LP) : Prop :=
  s.prog = b5h ∧ s.q = [] ∧ s.pc = 4 ∧ s.rd 14 = 1 ∧ s.rd 9 = X ∧ s.rd 11 = Y ∧ s.regs.length = 32

/-- The hart's state at the publication wait (`pc = 0`). -/
def fS5 (s : LP) : Prop :=
  s.prog = b5h ∧ s.q = [] ∧ s.pc = 0 ∧ s.rd 9 = X ∧ s.rd 11 = Y ∧ s.rd 12 = Z ∧ s.regs.length = 32

section h1

variable {GF : BundledGFunctors} [GhostVarG GF HSt] [GhostVarG GF Bool] [TokenG GF] [SavedPropG GF] [InvGS GF]

/-- **THE L2 SPIN LOOP** on the runtime-born lock (Löb at `pc = 4`; see the header). -/
theorem loop5 (g : AGN) (M : List PMsg) (sv : SV) (ak : Nat → Nat → GName) (h : Nat) (hh : h < 3) (hh0 : h ≠ 0)
    (hdd : g.dd = fun _ => False) (hnoinv : ∀ t a, ¬ cmoAt M isInvalK t a) (γ : GName) (b c : Nat)
    (hb : bthAt M Lk b) :
    ⊢ ∀ (s : LP) (ws : PState) (pr : GSet Nat) (ev : Trace) (lo : Nat), ⌜lhS5 s⌝ -∗
      ⌜b ≤ ws.wVrNew ∧ c ≤ ws.wVrNew ∧ b ≤ lo ∧ lo ≤ max ws.wVrNew (coh ws Lk) ∧ noC ev⌝ -∗
      ctx5 (GF := GF) g M sv ak -∗ lkB5 g M sv ak b -∗ isLockAt M sv γ Lk (Rb5 g M c) b -∗
      obg g M sv.tk h lo 0 -∗ lhA g π4 (w5 M h) (qs5 M h) ws pr ev -∗ wpKA g π4 (w5 M h) (qs5 M) s (Φ5 g M) := by
  have hw := litW_x xs5 img5 M h
  iloeb as IH
  iintro %s0 %ws0 %pr0 %ev %lo %hs %hl0 #Hctx #Hlk #HL Hbag Hl
  obtain ⟨hprog0, hq0, hpc0, h14, h9_0, h11_0, hlen0⟩ := hs
  obtain ⟨hbv0, hcv0, hbl, hlo0, hnoC⟩ := hl0
  -- `mv a5,a4`
  iapply (C.wpKA_alu hw (litAg_x hq0 (p5h_at hprog0) (by rw [hpc0]; rfl) rfl) hq0 (by rw [hprog0, hpc0]; rfl)
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
  have h15 : s.rd 15 = 1 := mv_15 hsA h14 hlen0
  -- `amoswap.w.aq a5,a5,(s1)`
  iapply (wpKA_amo (base := Lk) hw (litAg_x hq (p5h_at hprog) (by rw [hpc]; rfl) rfl) hq (by rw [hprog, hpc]; rfl)
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
  have hpre : max (ldPre (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) true false
      (srcsView (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) (srcR 9))) (coh ws0 Lk) ≤
      coh (loadRun (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) true false
        (srcsView (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) (srcR 9)) Lk tvs) Lk := by
    obtain ⟨t0, v0, r0, rfl⟩ := tvs_cons hlen4 (by decide)
    have := (loadRun_b0 (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) true false
      (srcsView (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) (srcR 9)) Lk t0 v0 r0).2.2.1
    have := (loadRun_mono (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) true false
      (srcsView (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) (srcR 9)) Lk ((t0, v0) :: r0)).2.2.2.2.2.2.2.2.2.2.1 Lk
    have e : coh (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) Lk = coh ws0 Lk := rfl
    omega
  have hvp := (PF.ldPre_ge (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) true false
    (srcsView (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) (srcR 9))).2.1
  have ev0 : (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))).wVrNew = ws0.wVrNew := rfl
  have ec0 : coh (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) Lk = coh ws0 Lk := rfl
  have hc0 : coh (loadRun (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) true false
      (srcsView (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) (srcR 9)) Lk tvs) Lk < ts := by
    simpa using hcohB 0 (by decide)
  have hmt := msgAt_of (by omega) hmsg
  have htsM := msgAt_le hmt
  obtain ⟨hA, hbyH⟩ := A2_of hh hmt
  -- the AMO's own message: its `pend` and token from the own-message bag
  icases obg_take g M sv.tk (by omega : lo < ts) hA hbyH htsM $$ Hbag with ⟨⟨Hp, Ht⟩, Hbag⟩
  imod shoot $$ Hp with #Hsh
  imodintro
  isplitr
  · ileft; ipureintro
    exact ⟨⟨0, grd_intro (q5_noLd (noC_noLd (noC_snoc hnoC (rmw_nonC _ _ _ _ _ _ _))))⟩, grd_intro (ok4_lk hlenD)⟩
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
  have hwts : wrB M Lk ts := by simpa using lk_wr (toBytes_length 1 4) (j := 0) (by decide) hmt
  obtain ⟨hP1, hc1, hq1⟩ := LPstep_at hs1 hprog (by rw [hpc])
  have e9 : s1.rd 9 = X := by rw [LPstep_rd hs1 9 (.inl (by decide)), h9]
  have e11 : s1.rd 11 = Y := by rw [LPstep_rd hs1 11 (.inl (by decide)), h11]
  have e14 : s1.rd 14 = 1 := by rw [LPstep_rd hs1 14 (.inl (by decide)), h14']
  have hlen1 : s1.regs.length = 32 := hs1.2.2.2.1.trans hlen
  have e15 := LPstep_rd_eq hs1 (by decide) (by omega)
  have hvr := postA_vr (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) 9 Lk tvs ts (amoD .swap 4 (s.rd 15) tvs).length
  have hcs := postA_coh (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) 9 Lk tvs ts (amoD .swap 4 (s.rd 15) tvs).length
    (by rw [hlenD]; decide)
  have hnoC' := noC_snoc hnoC (rmw_nonC true false tvs (amoD .swap 4 (s.rd 15) tvs) (srcR 9) (srcR 15) ts)
  have hbv' : b ≤ ldPre (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) true false
      (srcsView (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) (srcR 9)) := by omega
  have hlo' : lo ≤ max (ldPre (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) true false
      (srcsView (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) (srcR 9))) (coh (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) Lk) := by
    omega
  imod acq5 g M sv ak h hdd (π := π4) (ws := instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) (γ := γ) (c := c) hb hlen4
    hlo1 hex hsrc hcohB hbv' hlo' hts_f hwts hnoinv $$ [Hbag Ht Hc]
    with (⟨Hbag, %hv⟩ | ⟨Hbag, %hv, %lw, %sp, %hls, HC, HP⟩)
  · iframe Hctx Hlk HL Hfr Hbag Ht Hc
  all_goals imodintro
  all_goals iintro Hl
  · -- held: `sext.w`, `bnez` back to the loop head
    iapply (wpKA_addiw (Xs := xs5) hw (xAg_x xs5 img5 M h s1) hq1 (p5h_at hP1) (by rw [hc1]; rfl) (by decide))
    iframe Hl
    inext
    iintro %s2 %hs2 _ _
    imodintro
    iintro Hl
    obtain ⟨hP2, hc2, hq2⟩ := LPstep_at hs2 hP1 (by rw [hc1])
    have f15 : s2.rd 15 = 1 := a5_val (.inr rfl) e15 hv hs2 hlen1
    have hlen2 : s2.regs.length = 32 := hs2.2.2.2.1.trans hlen1
    iapply (wpKA_brx (Xs := xs5) hw (xAg_x xs5 img5 M h s2) hq2 (p5h_at hP2) (by rw [hc2]; rfl)
      (by rw [hP2]; decide))
    iframe Hl
    inext
    iintro %s3 %hs3 _ _
    imodintro
    iintro Hl
    have hbr : (if Weak.Prom.Ref.brEval .ne (s2.rd 15) (s2.rd 0) then 4 else s2.pc + 1) = 4 := by rw [f15]; rfl
    rw [hbr] at hs3
    obtain ⟨hP3, hc3, hq3⟩ := LPstep_at hs3 hP2 rfl
    have hls : lhS5 s3 := ⟨hP3, hq3, hc3,
      by rw [LPstep_rd hs3 14 (.inr rfl), LPstep_rd hs2 14 (.inl (by decide)), e14],
      by rw [LPstep_rd hs3 9 (.inr rfl), LPstep_rd hs2 9 (.inl (by decide)), e9],
      by rw [LPstep_rd hs3 11 (.inr rfl), LPstep_rd hs2 11 (.inl (by decide)), e11], hs3.2.2.2.1.trans hlen2⟩
    iapply IH $$ %s3 %_ %_ %_ %ts %hls %⟨by omega, by omega, by omega, Nat.le_trans hcs (Nat.le_max_right _ _), hnoC'⟩
      Hctx Hlk HL [Hbag] Hl
    iapply obg_up g M sv.tk (Nat.le_of_lt (by omega : lo < ts)) (Nat.le_refl _) $$ Hbag
  · -- acquired: `sext.w`, `bnez` falls through to `sd a0,16(s1)`
    iapply (wpKA_addiw (Xs := xs5) hw (xAg_x xs5 img5 M h s1) hq1 (p5h_at hP1) (by rw [hc1]; rfl) (by decide))
    iframe Hl
    inext
    iintro %s2 %hs2 _ _
    imodintro
    iintro Hl
    obtain ⟨hP2, hc2, hq2⟩ := LPstep_at hs2 hP1 (by rw [hc1])
    have f15 : s2.rd 15 = 0 := a5_val (.inl rfl) e15 hv hs2 hlen1
    iapply (wpKA_brx (Xs := xs5) hw (xAg_x xs5 img5 M h s2) hq2 (p5h_at hP2) (by rw [hc2]; rfl)
      (by rw [hP2]; decide))
    iframe Hl
    inext
    iintro %s3 %hs3 _ _
    imodintro
    iintro Hl
    have hbr : (if Weak.Prom.Ref.brEval .ne (s2.rd 15) (s2.rd 0) then 4 else s2.pc + 1) = 8 := by
      rw [f15, hc2]; rfl
    rw [hbr] at hs3
    obtain ⟨hP3, hc3, hq3⟩ := LPstep_at hs3 hP2 rfl
    have hvw5 := postA_vw (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) 9 Lk tvs ts (amoD .swap 4 (s.rd 15) tvs).length
    iapply (cpu1_5 g M sv ak h hh hh0 b s3 _ _ _ ts lw sp ⟨hP3, hq3, hc3,
      by rw [LPstep_rd hs3 9 (.inr rfl), LPstep_rd hs2 9 (.inl (by decide)), e9],
      by rw [LPstep_rd hs3 11 (.inr rfl), LPstep_rd hs2 11 (.inl (by decide)), e11]⟩ (by omega) hcs
      (by rcases hls.1 with h1 | h1 <;> omega) (by omega) hnoC' hnoinv)
    iframe Hctx Hlk HC HP Hl
    iapply obg_up g M sv.tk (Nat.le_of_lt (by omega : lo < ts)) (Nat.le_refl _) $$ Hbag

/-- **THE PUBLICATION WAIT** (Löb at `pc = 0`; see the header), then `li a4,1` and the L2 loop. -/
theorem floop5 (g : AGN) (M : List PMsg) (sv : SV) (ak : Nat → Nat → GName) (h : Nat) (hh : h < 3) (hh0 : h ≠ 0)
    (hdd : g.dd = fun _ => False) (hnoinv : ∀ t a, ¬ cmoAt M isInvalK t a) :
    ⊢ ∀ (s : LP) (ws : PState) (pr : GSet Nat) (ev : Trace), ⌜fS5 s⌝ -∗ ⌜ws.wFwd = ∅ ∧ noC ev⌝ -∗
      ctx5 (GF := GF) g M sv ak -∗ ([∗list] t ∈ rng M, token (ak h t)) -∗
      lhA g π4 (w5 M h) (qs5 M h) ws pr ev -∗ wpKA g π4 (w5 M h) (qs5 M) s (Φ5 g M) := by
  have hw := litW_x xs5 img5 M h
  iloeb as IH
  iintro %s0 %ws0 %pr0 %ev %hs %hl0 #Hctx Hak Hl
  obtain ⟨hprog, hq, hpc, h9, h11, h12, hlen⟩ := hs
  obtain ⟨hfw, hnoC⟩ := hl0
  -- `lw t0,0(a2)`
  iapply (wpKA_ld (sz := 4) (sgn := true) (rd := 5) (rs1 := 12) (off := 0) (base := L1) hw
    (litAg_x hq (p5h_at hprog) (by rw [hpc]; rfl) rfl) hq (by rw [hprog, hpc]; rfl) (alg_of h12 (by decide) (by decide))
    (base_of h12 (by decide)))
  iframe Hl
  inext
  iintro %tvs0 %hl0 %hlo0 _ _
  have hnoC1 := noC_snoc hnoC (ld_nonC (a := L1) (by simp [L1, Z, Ct, Y]) tvs0 (srcR 12))
  imodintro
  isplitr
  · ileft; ipureintro; exact ⟨0, grd_intro (q5_noLd (noC_noLd hnoC1))⟩
  iintro %s1 %hs1 _ _
  imodintro
  iintro Hl
  obtain ⟨hP1, hc1, hq1⟩ := LPstep_at hs1 hprog (by rw [hpc])
  have e5 : s1.rd 5 = ldVal true 4 tvs0 % two64 := LPstep_rd_eq hs1 (by decide) (by omega)
  have e9 : s1.rd 9 = X := by rw [LPstep_rd hs1 9 (.inl (by decide)), h9]
  have e11 : s1.rd 11 = Y := by rw [LPstep_rd hs1 11 (.inl (by decide)), h11]
  have e12 : s1.rd 12 = Z := by rw [LPstep_rd hs1 12 (.inl (by decide)), h12]
  have hlen1 : s1.regs.length = 32 := hs1.2.2.2.1.trans hlen
  -- `bnez t0,0`
  iapply (wpKA_brx (Xs := xs5) hw (xAg_x xs5 img5 M h s1) hq1 (p5h_at hP1) (by rw [hc1]; rfl) (by rw [hP1]; decide))
  iframe Hl
  inext
  iintro %s2 %hs2 _ _
  imodintro
  iintro Hl
  by_cases hz : s1.rd 5 = 0
  rotate_left
  · -- not yet published: back to the wait
    have hbr : (if Weak.Prom.Ref.brEval .ne (s1.rd 5) (s1.rd 0) then 0 else s1.pc + 1) = 0 := by
      have h0 : s1.rd 0 = 0 := rfl
      simp [Weak.Prom.Ref.brEval, hz, h0]
    rw [hbr] at hs2
    obtain ⟨hP2, hc2, hq2⟩ := LPstep_at hs2 hP1 rfl
    have hls : fS5 s2 := ⟨hP2, hq2, hc2, by rw [LPstep_rd hs2 9 (.inr rfl), e9],
      by rw [LPstep_rd hs2 11 (.inr rfl), e11], by rw [LPstep_rd hs2 12 (.inr rfl), e12], hs2.2.2.2.1.trans hlen1⟩
    iapply IH $$ %s2 %_ %_ %_ %hls %⟨by simp [regWL, qPosts, qPost, hfw], hnoC1⟩ Hctx Hak Hl
  -- published: fall through to the fence
  have hbr : (if Weak.Prom.Ref.brEval .ne (s1.rd 5) (s1.rd 0) then 0 else s1.pc + 1) = 2 := by
    rw [hz, hc1]; rfl
  rw [hbr] at hs2
  obtain ⟨hP2, hc2, hq2⟩ := LPstep_at hs2 hP1 rfl
  obtain ⟨t0, v0, r0, rfl⟩ := tvs_cons hl0 (by decide)
  have hv0 : v0 = 0 := lw0 (by simpa using hl0) (by rw [← e5]; exact hz)
  subst hv0
  obtain ⟨k, m, ht0, hmk, hby⟩ := src_of_val (loadOk_b0 hlo0).1 img5_L1 (by decide)
  have hmt : msgAt M t0 = some m := by rw [ht0]; exact hmk
  have htM := msgAt_le hmt
  have hro : t0 ≤ (qPosts (loadRun ws0 false false (srcsView ws0 (srcR 12)) L1 ((t0, 0) :: r0))
      (regWL 5 [.DLdRes] ++ [LInstr])).wVrOld := by
    have := (loadRun_b0 ws0 false false (srcsView ws0 (srcR 12)) L1 t0 0 r0).2.1
    rw [fwdView_empty hfw] at this
    simp only [regWL, qPosts, qPost, regWP_vrOld, instrR_vrOld, show (5 : Nat) ≠ 0 by decide, if_false,
      List.singleton_append]
    omega
  -- `fence rw,rw`: at the next step, the frontier covers the publication read
  iapply (wpKA_fence hw (litAg_x hq2 (p5h_at hP2) (by rw [hc2]; rfl) rfl) hq2 (by rw [hP2, hc2]; rfl))
  iframe Hl
  inext
  iintro %s3 %hs3 #Hfr Hc
  obtain ⟨hP3, hc3, hq3⟩ := LPstep_at hs3 hP2 (by rw [hc2])
  have hfl : t0 ≤ wfr (fencePost (instrR (ctrlP (qPosts (loadRun ws0 false false (srcsView ws0 (srcR 12)) L1
      ((t0, 0) :: r0)) (regWL 5 [.DLdRes] ++ [LInstr])) (srcR 5 ++ srcR 0))) true true true true) := by
    refine Nat.le_trans ?_ (wfr_ge_vwNew _)
    simp only [fence_vwNew, ite_true, instrR_vrOld, ctrlP_vrOld]
    omega
  unfold ctx5
  icases Hctx with ⟨Hdoom, Hfs, Hfj, Hbs⟩
  imod frontS g M hdd (π := π4) (img := img5) t0 ⟨htM.1, htM.2, hfl⟩ $$ [] with #Hsh
  · iframe Hdoom Hfr
  have hT := tL1_of hmt (j := 0) (by decide) (by simp [hby])
  cases hf : fPub M t0
  · -- the flag's junk: fulfilled, absurd
    ihave #Hj := bsl_mem (F := fun t => lkJunk g t) (List.mem_filter.2 ⟨mem_rng.2 htM, by simp [fJ, hT, hf]⟩) $$ Hfj
    imod junk_shot g t0 $$ [] with %hfalse
    · iframe Hj Hsh
    exact hfalse.elim
  -- THE PUBLICATION: the handle and the lock's protocol (persistent)
  ihave #Hfsl := bsl_mem (F := fun t => fSlot5 g M sv ak t) (List.mem_filter.2 ⟨mem_rng.2 htM, hf⟩) $$ Hfs
  imod fclaim5 g M sv ak t0 $$ [Hc] with HP
  · iframe Hfsl Hsh Hc
  unfold Pub5
  icases HP with ⟨%γ, %b, %c, %hbc, #HL, #Hlk⟩
  obtain ⟨hbt, hct, _⟩ := hbc
  unfold isLockAt
  icases HL with ⟨%hb, #Hds, #HsQ, #Hbsl⟩
  -- THE HART TAKES ITS OWN PART of the lock born at `b`
  have hbM := msgAt_le (show msgAt M b = _ from hb.choose_spec.1)
  imod hclaim5 g M sv ak hh $$ [Hak] with Hbag
  · iframe Hlk
    iapply (BigSepL.bigSepL_mem (Φ := fun t => token (GF := GF) (ak h t)) (mem_rng.2 hbM)) $$ Hak
  imodintro
  iintro Hl
  have hvr : t0 ≤ (instrR (fencePost (instrR (ctrlP (qPosts (loadRun ws0 false false (srcsView ws0 (srcR 12)) L1
      ((t0, 0) :: r0)) (regWL 5 [.DLdRes] ++ [LInstr])) (srcR 5 ++ srcR 0))) true true true true)).wVrNew := by
    simp only [instrR_vrNew, fence_vrNew, ite_true, instrR_vrOld, ctrlP_vrOld]
    omega
  -- `li a4,1`
  iapply (wpKA_alui hw (litAg_x hq3 (p5h_at hP3) (by rw [hc3]; rfl) rfl) hq3 (by rw [hP3, hc3]; rfl) (by decide))
  iframe Hl
  inext
  iintro %s4 %hs4 _ _
  imodintro
  iintro Hl
  obtain ⟨hP4, hc4, hq4⟩ := LPstep_at hs4 hP3 (by rw [hc3])
  have hlen3 : s3.regs.length = 32 := hs3.2.2.2.1.trans (hs2.2.2.2.1.trans hlen1)
  have hls : lhS5 s4 := ⟨hP4, hq4, hc4, li_val hs4 (by decide) (by omega) (by decide),
    by rw [LPstep_rd hs4 9 (.inl (by decide)), LPstep_rd hs3 9 (.inr rfl), LPstep_rd hs2 9 (.inr rfl), e9],
    by rw [LPstep_rd hs4 11 (.inl (by decide)), LPstep_rd hs3 11 (.inr rfl), LPstep_rd hs2 11 (.inr rfl), e11],
    hs4.2.2.2.1.trans hlen3⟩
  have hvr4 : t0 ≤ (instrR (regWP (instrR (fencePost (instrR (ctrlP (qPosts (loadRun ws0 false false
      (srcsView ws0 (srcR 12)) L1 ((t0, 0) :: r0)) (regWL 5 [.DLdRes] ++ [LInstr])) (srcR 5 ++ srcR 0))) true true true
      true)) 14 (srcR 0))).wVrNew := by simpa only [instrR_vrNew, regWP_vrNew] using hvr
  ihave Hloop := loop5 (GF := GF) g M sv ak h hh hh0 hdd hnoinv γ b c hb
  iapply Hloop $$ %s4 %(instrR (regWP (instrR (fencePost (instrR (ctrlP (qPosts (loadRun ws0 false false
      (srcsView ws0 (srcR 12)) L1 ((t0, 0) :: r0)) (regWL 5 [.DLdRes] ++ [LInstr])) (srcR 5 ++ srcR 0))) true true true
      true)) 14 (srcR 0))) %_ %_ %b %hls %⟨by omega, by omega, Nat.le_refl _,
    Nat.le_trans (by omega) (Nat.le_max_left _ _), hnoC1⟩ [] Hlk [] Hbag Hl
  · unfold ctx5; iframe Hdoom Hfs Hfj Hbs
  · unfold isLockAt; iframe Hds HsQ Hbsl; ipureintro; exact hb

end h1

end Weak.Prom.OA.E2
