/-
Weak/Prom: **E-a, G4 (4) with the dead set empty — hart 1: the L1 loop (publication), the L2 loop (the runtime
lock)** (stage E-a; OwnAPipeH1.lean / OwnAPipeH1b.lean over `π4` and the per-byte owners of OwnAEPipeDefs.lean).

* `h1_loop1E` — xv6's acquire of the boot lock L1: the word is 1 (spin) or 0 read from hart 0's release `s`, whose
  slot yields `Pub1E s`: the L2 handle (runtime `γ`) and THE L2 WORD'S BAG above the birth `b`.
* `h1_loop2E` — xv6's acquire of L2, R-a4 BY OWNERSHIP: hart 1's read floor `lo` (the birth, or its own last AMO
  write; `lo ≤` its view) lies below every byte's source, and every L2 message above `lo` is hart 1's to fulfil
  (`pend` in its bag) or L1's junk, so every byte comes from `lo` (`l2_byteE`): value 0 at the birth, 1 at its own
  write.  At the birth, the AMO is the first L2 write after it (`l2_nxtE`, the same ownership fact) and its token
  opens `b`'s saved-proposition slot: the field's points-to and `token γ`.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.OwnAEPipeCS

namespace Weak.Prom.OA.EP

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.PF Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Ref (Instr Test two64)
open Weak.Prom.Ref.Lit (X Y Z)
open Weak.Prom.OA.P (L1 p4h b4h xs4 p4h_at img4 w4 SV cAt5 q4 qs4 q4_nil q4_snoc notCLd_rmw msgAt_of vals_of_src
  knd knd_of kind_a1 isK bagK tk1 bthAt bth_wr isLockAt bslot_claim postA postA_vr postA_wf postA_coh a5_val lhS1 lhS2
  alg_L1 alg_L2 amo_msg1 mv_15)
open Weak.Prom.OA.E
open PLabel
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode

/-- A byte's floor: no write between the source `t` and a floor `fl ≥ lo`, `lo` writing the byte: `lo ≤ t`. -/
theorem src_floor {M : List PMsg} {a : Int} {lo t fl : Nat} (hlw : wrB M a lo) (hfl : lo ≤ fl)
    (hr : ¬ writesIn M a t fl) : lo ≤ t := by
  apply Classical.byContradiction; intro hlt
  obtain ⟨m, hm', hba⟩ := hlw
  obtain ⟨k, hk⟩ : ∃ k, lo = k + 1 := by
    cases lo with
    | zero => cases hm'
    | succ k => exact ⟨k, rfl⟩
  exact hr ⟨lo, by omega, hfl, m, by rw [hk] at hm' ⊢; simpa [msgAt] using hm', hba⟩

/-- A 4-byte message at `Lk` writes each of its bytes. -/
theorem lk_wr {M : List PMsg} {t j : Nat} {d : List (BitVec 8)} {tid : Option Nat} {c : PClass} (hd : d.length = 4)
    (hj : j < 4) (hm : msgAt M t = some ⟨Lk, d, tid, c⟩) : wrB M (Lk + j) t :=
  ⟨_, hm, by rw [byteAt_off rfl, List.getElem?_eq_getElem (by rw [hd]; exact hj)]; rfl⟩

/-- The floor message of the L2 loop: the birth, or hart 1's own last AMO write. -/
def lo2 (M : List PMsg) (b lo : Nat) : Prop := lo = b ∨ msgAt M lo = some ⟨Lk, toBytes 1 4, some 1, .excl⟩

theorem lo2_wr {M : List PMsg} {b lo j : Nat} (hb : bthAt M Lk b) (h : lo2 M b lo) (hj : j < 4) :
    wrB M (Lk + j) lo := by
  rcases h with rfl | h
  · exact bth_wr hj hb
  · exact lk_wr (toBytes_length 1 4) hj h

section h1

variable {GF : BundledGFunctors} [GhostVarG GF HSt] [GhostVarG GF Bool] [TokenG GF] [SavedPropG GF] [InvGS GF]

/-- **THE L2 SPIN LOOP** (Löb at `pc = 5`; see the header). -/
theorem h1_loop2E (g : AGN) (M : List PMsg) (sv : SV) (hdd : g.dd = fun _ => False)
    (hnoinv : ∀ t a, ¬ cmoAt M isInvalK t a) (γ : GName) (b c : Nat) (hb : bthAt M Lk b) (hc5 : cAt5 M c) :
    ⊢ ∀ (s : LP) (ws : PState) (pr : GSet Nat) (ev : Trace) (lo : Nat), ⌜lhS2 s⌝ -∗
      ⌜lo2 M b lo ∧ lo ≤ ws.wVrNew ∧ c ≤ ws.wVrNew ∧ q4 ev⌝ -∗ pCtxE (GF := GF) g M sv -∗
      isLockAt M sv γ Lk (cPtsP g M c) b -∗ zBagE g M sv lo 0 -∗
      lhA g π4 (w4 M 1) (qs4 1) ws pr ev -∗ wpKA g π4 (w4 M 1) qs4 s (Φ4E g M) := by
  have hw := litW_x xs4 img4 M 1
  iloeb as IH
  iintro %s0 %ws0 %pr0 %ev %lo %hs %hl0 #Hctx #Hlk Hz Hl
  obtain ⟨hprog0, hq0, hpc0, h14, h9_0, h11_0, h12_0, hlen0⟩ := hs
  obtain ⟨hlo2, hlov0, hcv0, hq4⟩ := hl0
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
  obtain ⟨t0, v0, t1, v1, t2, v2, t3, v3, rfl⟩ : ∃ t0 v0 t1 v1 t2 v2 t3 v3,
      tvs = [(t0, v0), (t1, v1), (t2, v2), (t3, v3)] := by
    match tvs, hlen4 with
    | [(a, b), (c, d), (e, f), (i, j)], _ => exact ⟨a, b, c, d, e, f, i, j, rfl⟩
  have hd1 : amoD .swap 4 (s.rd 15) [(t0, v0), (t1, v1), (t2, v2), (t3, v3)] = toBytes 1 4 := amo_msg1 h15
  have hlenD : (amoD .swap 4 (s.rd 15) [(t0, v0), (t1, v1), (t2, v2), (t3, v3)]).length = 4 := by rw [hd1]; rfl
  rw [hd1] at hmsg
  rw [hlenD] at hcoh
  have hcohB : ∀ j : Nat, j < 4 → coh (loadRun (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) true false
      (srcsView (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) (srcR 9)) Lk [(t0, v0), (t1, v1), (t2, v2), (t3, v3)])
      (Lk + j) < ts :=
    fun j hj => cohBelow_at hcoh hj
  have hsrc : bytesAll (fun x u _ => u ≤ coh (loadRun (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) true false
      (srcsView (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) (srcR 9)) Lk [(t0, v0), (t1, v1), (t2, v2), (t3, v3)]) x) Lk [(t0, v0), (t1, v1), (t2, v2), (t3, v3)] :=
    bytesAll_mono (fun _ _ _ hh => hh.2) _ _
      (loadBytes_coh true (ldPre (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) true false
        (srcsView (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) (srcR 9))) (instrR (regWP ws0 15 (srcR 0 ++ srcR 14)))
        Lk [(t0, v0), (t1, v1), (t2, v2), (t3, v3)]).2
  have hlv : lo ≤ ldPre (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) true false
      (srcsView (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) (srcR 9)) :=
    Nat.le_trans hlov0 (PF.ldPre_ge (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) true false _).2.1
  -- each byte: below `ts`, no write between it and a floor above `lo`
  have hbyte : ∀ (j t : Nat) (v : BitVec 8), j < 4 → [(t0, v0), (t1, v1), (t2, v2), (t3, v3)][j]? = some (t, v) →
      memByte img4 M t (Lk + j) = some v ∧ t < ts ∧ ∃ fl, lo ≤ fl ∧ ¬ writesIn M (Lk + j) t fl :=
    fun j t v hj hg => by
      have h1 := bytesAll_get (loadOk_weak hlo1) hg
      refine ⟨h1.1, Nat.lt_of_le_of_lt (bytesAll_get hsrc hg) (hcohB j hj), ?_⟩
      rcases h1.2 with ⟨fl, hfl, h⟩ | ⟨fl, hfl, ti, hc, _⟩
      · exact ⟨fl, by omega, h⟩
      · exact absurd hc (hnoinv _ _)
  have hlots : lo < ts := by
    obtain ⟨_, hlt, fl, hfl, hr⟩ := hbyte 0 t0 v0 (by decide) rfl
    have := src_floor (lo2_wr hb hlo2 (j := 0) (by decide)) hfl hr
    omega
  have hts1 : 1 ≤ ts := by omega
  have hmt := msgAt_of hts1 hmsg
  have htsM := msgAt_le hmt
  -- the AMO's own message: its `pend` and token from the L2 word's bag
  icases zBag_takeE g M sv hlots (lk_L2O (toBytes_length 1 4) hmt) htsM $$ Hz with ⟨⟨Hp, Ht⟩, Hz⟩
  imod shoot $$ Hp with #Hsh
  imodintro
  isplitr
  · ileft; ipureintro
    exact ⟨⟨0, grd_intro (q4_snoc hq4 notCLd_rmw)⟩, grd_intro (ok4_lk hlenD)⟩
  isplitr
  · unfold fulT; ileft; iexact Hsh
  iintro %s1 %hs1 #Hfr Hc
  have hts_f := postA_wf (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) 9 Lk [(t0, v0), (t1, v1), (t2, v2), (t3, v3)] ts
    (amoD .swap 4 (s.rd 15) [(t0, v0), (t1, v1), (t2, v2), (t3, v3)]).length
  -- R-a4 BY OWNERSHIP: every byte came from `lo`
  have step : ∀ (j t : Nat) (v : BitVec 8), j < 4 → [(t0, v0), (t1, v1), (t2, v2), (t3, v3)][j]? = some (t, v) →
      pCtxE (GF := GF) g M sv ∗ frontA g π4 img4 M (qPosts (amoPost (storeRun (loadRun
        (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) true false
        (srcsView (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) (srcR 9)) Lk [(t0, v0), (t1, v1), (t2, v2), (t3, v3)]) false
        (srcsView (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) (srcR 9)) ts Lk
        (amoD .swap 4 (s.rd 15) [(t0, v0), (t1, v1), (t2, v2), (t3, v3)]).length ts) true ts) (regWL 15 [.DLdRes] ++ [LInstr]).dropLast) ∗
        zBagE g M sv lo ts ⊢ |={⊤}=> zBagE g M sv lo ts ∗ ⌜t = lo⌝ := fun j t v hj hg => by
    obtain ⟨hm, hlt, fl, hfl, hr⟩ := hbyte j t v hj hg
    exact l2_byteE g M sv hdd hj (lo2_wr hb hlo2 hj) hfl hm hr (by omega) (by omega)
  imod step 0 t0 v0 (by decide) rfl $$ [Hz] with ⟨Hz, %e0⟩
  · iframe Hctx Hfr Hz
  imod step 1 t1 v1 (by decide) rfl $$ [Hz] with ⟨Hz, %e1⟩
  · iframe Hctx Hfr Hz
  imod step 2 t2 v2 (by decide) rfl $$ [Hz] with ⟨Hz, %e2⟩
  · iframe Hctx Hfr Hz
  imod step 3 t3 v3 (by decide) rfl $$ [Hz] with ⟨Hz, %e3⟩
  · iframe Hctx Hfr Hz
  have hall : ∀ p ∈ [(t0, v0), (t1, v1), (t2, v2), (t3, v3)], p.1 = lo := by
    intro p hp; simp only [List.mem_cons, List.mem_nil_iff, _root_.or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> assumption
  have hmb : bytesAll (fun a t v => memByte img4 M t a = some v) Lk [(t0, v0), (t1, v1), (t2, v2), (t3, v3)] := by
    exact bytesAll_mono (fun _ _ _ hh => hh.1) _ _ (loadOk_weak hlo1)
  obtain ⟨hP1, hc1, hq1⟩ := LPstep_at hs1 hprog (by rw [hpc])
  have e9 : s1.rd 9 = X := by rw [LPstep_rd hs1 9 (.inl (by decide)), h9]
  have e11 : s1.rd 11 = Y := by rw [LPstep_rd hs1 11 (.inl (by decide)), h11]
  have e12 : s1.rd 12 = Z := by rw [LPstep_rd hs1 12 (.inl (by decide)), h12]
  have e14 : s1.rd 14 = 1 := by rw [LPstep_rd hs1 14 (.inl (by decide)), h14']
  have hlen1 : s1.regs.length = 32 := hs1.2.2.2.1.trans hlen
  have e15 := LPstep_rd_eq hs1 (by decide) (by omega)
  have hvr := postA_vr (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) 9 Lk [(t0, v0), (t1, v1), (t2, v2), (t3, v3)] ts (amoD .swap 4 (s.rd 15) [(t0, v0), (t1, v1), (t2, v2), (t3, v3)]).length
  have hcs := postA_coh (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) 9 Lk [(t0, v0), (t1, v1), (t2, v2), (t3, v3)] ts (amoD .swap 4 (s.rd 15) [(t0, v0), (t1, v1), (t2, v2), (t3, v3)]).length
    (by rw [hlenD]; decide)
  have hcv0' : c ≤ (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))).wVrNew := hcv0
  by_cases hlb : lo = b
  · -- THE BIRTH: the word is 0; the AMO is the first L2 write after `b`; its token opens `b`'s slot
    subst hlb
    obtain ⟨mb, hmbt, hpb, hdb, _⟩ := hb
    have hv : [(t0, v0), (t1, v1), (t2, v2), (t3, v3)].map Prod.snd = toBytes 0 4 := by
      rw [vals_of_src (img := img4) hmbt hpb 0 _ (by rw [hdb, toBytes_length]; simp) (by simpa using hmb) hall,
        hdb]; rfl
    have hwts : wrB M Lk ts := by simpa using lk_wr (toBytes_length 1 4) (j := 0) (by decide) hmt
    imod l2_nxtE g M sv hdd (π := π4) hlots hts_f hwts $$ [Hz] with ⟨Hz, %hn⟩
    · iframe Hctx Hfr Hz
    unfold isLockAt
    icases Hlk with ⟨_, #Hds, #HsQ, #Hslot⟩
    imod bslot_claim M sv lo ts hn iprop(cPtsP g M c ∗ token γ) $$ [Ht Hc] with HR
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
    iapply (h1_cldE g M sv s3 _ _ _ ts c ⟨hP3, hq3, hc3, r9, r11⟩ hcs hc5 (Nat.le_trans hcv0' hvr.1)
      (q4_snoc hq4 notCLd_rmw) hnoinv)
    iframe Hctx HC Hl
    iapply zBag_up g M sv (Nat.le_of_lt hlots) (Nat.le_refl _) $$ Hz
  · -- its own last write: the word is 1, spin
    have hown : msgAt M lo = some ⟨Lk, toBytes 1 4, some 1, .excl⟩ := hlo2.resolve_left hlb
    have hv : [(t0, v0), (t1, v1), (t2, v2), (t3, v3)].map Prod.snd = toBytes 1 4 := by
      rw [vals_of_src (img := img4) hown rfl 0 _ (by rw [toBytes_length]; simp) (by simpa using hmb) hall]
      rfl
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
    iapply IH $$ %s3 %_ %_ %_ %ts %hls %⟨.inr hmt, hvr.2, Nat.le_trans hcv0' hvr.1, q4_snoc hq4 notCLd_rmw⟩
      Hctx Hlk [Hz] Hl
    iapply zBag_up g M sv (Nat.le_of_lt hlots) (Nat.le_refl _) $$ Hz

/-- **THE L1 SPIN LOOP** (Löb induction at `pc = 1`; see the header). -/
theorem h1_loop1E (g : AGN) (M : List PMsg) (sv : SV) (hdd : g.dd = fun _ => False)
    (hnoinv : ∀ t a, ¬ cmoAt M isInvalK t a) :
    ⊢ ∀ (s : LP) (ws : PState) (pr : GSet Nat) (ev : Trace) (lo : Nat), ⌜lhS1 s⌝ -∗
      ⌜lo ≤ coh ws L1 ∧ q4 ev⌝ -∗ pCtxE (GF := GF) g M sv -∗ ([∗list] t ∈ bagK M 2 lo, pend g t) -∗
      tk1 M sv -∗
      lhA g π4 (w4 M 1) (qs4 1) ws pr ev -∗ wpKA g π4 (w4 M 1) qs4 s (Φ4E g M) := by
  have hw := litW_x xs4 img4 M 1
  iloeb as IH
  iintro %s0 %ws0 %pr0 %ev %lo %hs %hl0 #Hctx HbA Htk Hl
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
    exact ⟨⟨0, grd_intro (q4_snoc hq4 notCLd_rmw)⟩, grd_intro (ok4_l1 hlenD)⟩
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
  imod l1_acqE g M sv hdd (π := π4)
    (ws1 := qPosts (amoPost (storeRun (loadRun (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) true false
      (srcsView (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) (srcR 12)) L1 tvs) false
      (srcsView (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) (srcR 12)) ts L1 (amoD .swap 4 (s.rd 15) tvs).length ts)
      true ts) (regWL 15 [.DLdRes] ++ [LInstr]).dropLast)
    hlen4 hm hsrc hcohB hts_f $$ [Htk Hc] with (⟨Htk, %hv⟩ | ⟨%hv, %sr, %hsr, HP⟩)
  · iframe Hctx Hfr Htk Hc
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
    iapply IH $$ %s3 %_ %_ %_ %ts %hls %⟨hcs, q4_snoc hq4 notCLd_rmw⟩ Hctx HbA Htk Hl
  · -- acquired: the L2 handle, published by hart 0's L1 release `sr`
    unfold Pub1E
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
    ihave Hloop := h1_loop2E (GF := GF) g M sv hdd hnoinv γ b c hb hc5
    iapply Hloop $$ %s3 %(postA (instrR (regWP ws0 15 (srcR 0 ++ srcR 14))) 12 L1 tvs ts
        (amoD .swap 4 (s.rd 15) tvs).length) %_ %_ %b %hls
      %⟨.inl rfl, by omega, by omega, q4_snoc hq4 notCLd_rmw⟩ Hctx [] Hz Hl
    unfold isLockAt; iframe Hds HsQ Hslot; ipureintro; exact hb

/-- **HART 1**: `li a4,1`, then the L1 spin loop. -/
theorem h1_hartE (g : AGN) (M : List PMsg) (sv : SV) (hdd : g.dd = fun _ => False)
    (s0 : LP) {P0 : GSet Nat} (hprog : s0.prog = b4h) (hpc : s0.pc = 0) (hq : s0.q = [])
    (hlen : s0.regs.length = 32) (h9 : s0.rd 9 = X) (h11 : s0.rd 11 = Y) (h12 : s0.rd 12 = Z)
    (hnoinv : ∀ t a, ¬ cmoAt M isInvalK t a) :
    pCtxE (GF := GF) g M sv ∗ ([∗list] t ∈ bagK M 2 0, pend g t) ∗ tk1 M sv ∗
      lhA g π4 (w4 M 1) (qs4 1) psInit P0 [] ⊢
      wpKA g π4 (w4 M 1) qs4 s0 (Φ4E g M) := by
  have hw := litW_x xs4 img4 M 1
  iintro ⟨#Hctx, HbA, Htk, Hl⟩
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
  ihave Hloop := h1_loop1E (GF := GF) g M sv hdd hnoinv
  iapply Hloop $$ %s1 %_ %_ %_ %0 %hls %⟨Nat.zero_le _, q4_nil⟩ Hctx HbA Htk Hl

end h1

end Weak.Prom.OA.EP
