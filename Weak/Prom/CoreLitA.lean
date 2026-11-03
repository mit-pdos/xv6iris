/-
Weak/Prom: **rows 10, 11, 11b, 28, 28c (AMOs), proved IN THE LOGIC** (stage S2; plan rev 7 §5 rows 10, 11, 11b,
28, 28c; §1 M0 "an aligned AMO gives rise to a single memory operation that is both a load operation and a store
operation simultaneously"; §2 "The AMO rule gives both the read source and the write ts … (M0(v)) regv rd ≥ ts").

The AMO is machine v2's fused `LRmw` (one label, `wpK_amo`); its view facts, each from one leaf of the AMO arm:
* COH of the write half above the read half's coherence floor: the read's byte-0 source is below the AMO's
  timestamp (`src0 < ts`);
* M0 (i), (iv): `amoPost` raises `vrOld` to `ts` (a later `fence r,·` covers the AMO as a load, §expl Example 2);
* M0 (v): the result register's view is `ts` (`wLdv ⊔= ts`, then `LRegW rd [DLdRes]`), so a data (row 28) or
  control (row 28c, `LCtrl`, rule 11) dependency from `rd` puts `ts` below a later store's pre-view;
* rule 5 / 6: an acquire AMO raises the load floor to `ts` (row 10's reader); a release AMO's pre-view contains
  `vwOld` (row 10's writer).
Rows (RefTests.lean): 10 `Lit.mpAmoRlAq`, 11 `Lit.mpFAmo`, 11b `Lit.amoStorePart`, 28 `Lit.mpAmoData`, 28c
`Lit.mpAmoCtrl`.  Contradictions from A0's exports (ii), (iii), (v) only.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.CoreLitCo

namespace Weak.Prom.PF

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Ref (Instr Test two64 aluOp brEval amoOp sext byteList bytesVal FenceSet AmoOp)
open Weak.Prom.Ref.Lit (X Y Z)
open PLabel
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode

/-! ## 1. Trace invariants -/

/-- A store, then a swap AMO above it (rows 10, 11, H0). -/
def qSA (a b : Int) (v : Nat) (rl : Bool) (pa r pb : Nat) : Trace → Prop :=
  q2 (isSt a (toBytes v 4) [.DReg pa] [.DReg r])
    (fun e0 e1 => isRmw false rl b 4 (amoD .swap 4 v) [.DReg pb] [.DReg r] e1 ∧ tsOf e0 < tsOf e1)

/-- An AMO reading below its own timestamp, then a load with no write to its byte in `(s, ts]` (rows 10, 11, H1). -/
def qAR (M : List PMsg) (a b : Int) (aq : Bool) (dat : List (Nat × BitVec 8) → List (BitVec 8)) (pa : Nat)
    (vs : List Dsrc) (pb : Nat) : Trace → Prop :=
  q2 (fun e0 => isRmw aq false a 4 dat [.DReg pa] vs e0 ∧ src0 e0 < tsOf e0)
    (fun e0 e1 => isLd b 4 [.DReg pb] e1 ∧ (noCmo M → ¬ writesIn M b (src0 e1) (tsOf e0)))

/-- A swap AMO, then a store (any data) above it (rows 11b, 28, 28c, H0). -/
def qAW (a b : Int) (v : Nat) (pa ra pb rb : Nat) : Trace → Prop :=
  q2 (isRmw false false a 4 (amoD .swap 4 v) [.DReg pa] [.DReg ra])
    (fun e0 e1 => (∃ d, d.length = 4 ∧ isSt b d [.DReg pb] [.DReg rb] e1) ∧ tsOf e0 < tsOf e1)

/-! ## 2. The harts -/

section harts

variable {hlc : HasLC} {GF : BundledGFunctors} [GhostVarG GF HSt] [InvGS_gen hlc GF]

/-- **Row 10's writer**: `li r,v; sw r,(pa); amoswap.w.rl x0,r,(pb)` proves `qSA` (rule 6: the release AMO's
pre-view contains `vwOld ≥ tx`). -/
theorem hSAmoRl_hart (img : Image) (M : List PMsg) (h : Nat) (s0 : LP) (a b v r pa pb : Nat)
    (hprog : s0.prog = [.alui .add r 0 v, .store 4 r pa 0, .amo .swap 4 false true 0 r pb])
    (hpc : s0.pc = 0) (hq : s0.q = []) (hnz : r ≠ 0 ∧ pa ≠ 0 ∧ pb ≠ 0 ∧ pa ≠ r ∧ pb ≠ r) (hlen : r < s0.regs.length)
    (hv : v < two64) (ha : s0.rd pa = a) (hb : s0.rd pb = b) (hal : a < two64) (hbl : b < two64)
    (hA : aligned a 4 = true) (hB : aligned b 4 = true) :
    ⊢@{IProp GF} wpPF Proto.triv ⟨litStep, litDone, img, M, h⟩ (ΨK M (qSA a b v true pa r pb)) s0
      (fun _ => iprop(⌜∃ V, grd Proto.triv img M V True⌝)) := by
  have hw := litW_lit img M h
  have hag := litAg_lit (V := Unit) litDone img M h
  iapply (wpK_start (by trivial))
  iintro %γ %P0 Hl
  iapply (wpK_alui hw (hag s0) hq (by rw [hprog, hpc]; rfl) hnz.1)
  iframe Hl
  inext
  iintro %s1 %hs1 Hl
  obtain ⟨hP1, hc1, hq1⟩ := LPstep_at hs1 hprog (by rw [hpc])
  have e1 : s1.rd r = v := li_val hs1 hnz.1 hlen hv
  have e1a : s1.rd pa = a := by rw [LPstep_rd hs1 pa (.inl hnz.2.2.2.1), ha]
  have e1b : s1.rd pb = b := by rw [LPstep_rd hs1 pb (.inl hnz.2.2.2.2), hb]
  iapply (wpK_sw (sz := 4) (rs2 := r) (rs1 := pa) (off := 0) (base := (a : Int)) hw (hag s1) hq1
    (by rw [hP1, hc1]; rfl) (alg_of e1a hal hA) (base_of e1a hal))
  iframe Hl
  inext
  iintro %tx %_ %_ %_ %hx
  imodintro
  isplitr
  · ipureintro; exact ⟨0, grd_intro ⟨tx, by omega, by simp only [e1, srcR_pos hnz.2.1, srcR_pos hnz.1]⟩⟩
  isplitr
  · ipureintro; exact grd_intro trivial
  iintro %s2 %hs2 Hl
  obtain ⟨hP2, hc2, hq2⟩ := LPstep_at hs2 hP1 (by rw [hc1])
  have e2 : s2.rd r = v := by rw [LPstep_rd hs2 r (.inr rfl), e1]
  have e2b : s2.rd pb = b := by rw [LPstep_rd hs2 pb (.inr rfl), e1b]
  iapply (wpK_amo (base := (b : Int)) hw (hag s2) hq2 (by rw [hP2, hc2]; rfl)
    (by rw [e2b]; exact hB) (by rw [e2b]))
  iframe Hl
  inext
  iintro %tvs %ty %hl %_ %_ %_ %_ %_ %hy
  have hlt : tx < ty := by
    simp [stPre] at hy
    omega
  imodintro
  isplitr
  · ipureintro
    exact ⟨0, grd_intro ⟨⟨tx, by omega, by simp only [e1, srcR_pos hnz.2.1, srcR_pos hnz.1]⟩,
      ⟨tvs, ty, by omega, by simp only [e2, srcR_pos hnz.2.2.1, srcR_pos hnz.1], hl⟩, hlt⟩⟩
  isplitr
  · ipureintro; exact grd_intro trivial
  iintro %s3 %hs3 Hl
  obtain ⟨hP3, hc3, hq3⟩ := LPstep_at hs3 hP2 (by rw [hc2])
  iapply (wpK_fin hq3 (by rw [hP3, hc3]; simp))
  iexact Hl

/-- **Row 11's writer**: `li r,v; sw r,(pa); fence rw,w; amoswap.w x0,r,(pb)` proves `qSA` (rule 4: the fence
raises the store floor to `vwOld ≥ tx`, below the AMO's write pre-view). -/
theorem hSFAmo_hart (img : Image) (M : List PMsg) (h : Nat) (s0 : LP) (a b v r pa pb : Nat)
    (hprog : s0.prog = [.alui .add r 0 v, .store 4 r pa 0, .fence ⟨true, true, false, false, false, true, false, false⟩,
      .amo .swap 4 false false 0 r pb])
    (hpc : s0.pc = 0) (hq : s0.q = []) (hnz : r ≠ 0 ∧ pa ≠ 0 ∧ pb ≠ 0 ∧ pa ≠ r ∧ pb ≠ r) (hlen : r < s0.regs.length)
    (hv : v < two64) (ha : s0.rd pa = a) (hb : s0.rd pb = b) (hal : a < two64) (hbl : b < two64)
    (hA : aligned a 4 = true) (hB : aligned b 4 = true) :
    ⊢@{IProp GF} wpPF Proto.triv ⟨litStep, litDone, img, M, h⟩ (ΨK M (qSA a b v false pa r pb)) s0
      (fun _ => iprop(⌜∃ V, grd Proto.triv img M V True⌝)) := by
  have hw := litW_lit img M h
  have hag := litAg_lit (V := Unit) litDone img M h
  iapply (wpK_start (by trivial))
  iintro %γ %P0 Hl
  iapply (wpK_alui hw (hag s0) hq (by rw [hprog, hpc]; rfl) hnz.1)
  iframe Hl
  inext
  iintro %s1 %hs1 Hl
  obtain ⟨hP1, hc1, hq1⟩ := LPstep_at hs1 hprog (by rw [hpc])
  have e1 : s1.rd r = v := li_val hs1 hnz.1 hlen hv
  have e1a : s1.rd pa = a := by rw [LPstep_rd hs1 pa (.inl hnz.2.2.2.1), ha]
  have e1b : s1.rd pb = b := by rw [LPstep_rd hs1 pb (.inl hnz.2.2.2.2), hb]
  iapply (wpK_sw (sz := 4) (rs2 := r) (rs1 := pa) (off := 0) (base := (a : Int)) hw (hag s1) hq1
    (by rw [hP1, hc1]; rfl) (alg_of e1a hal hA) (base_of e1a hal))
  iframe Hl
  inext
  iintro %tx %_ %_ %_ %hx
  imodintro
  isplitr
  · ipureintro; exact ⟨0, grd_intro ⟨tx, by omega, by simp only [e1, srcR_pos hnz.2.1, srcR_pos hnz.1]⟩⟩
  isplitr
  · ipureintro; exact grd_intro trivial
  iintro %s2 %hs2 Hl
  obtain ⟨hP2, hc2, hq2⟩ := LPstep_at hs2 hP1 (by rw [hc1])
  iapply (wpK_fence (f := ⟨true, true, false, false, false, true, false, false⟩) hw (hag s2) hq2
    (by rw [hP2, hc2]; rfl))
  iframe Hl
  inext
  iintro %s3 %hs3 Hl
  obtain ⟨hP3, hc3, hq3⟩ := LPstep_at hs3 hP2 (by rw [hc2])
  have e3 : s3.rd r = v := by rw [LPstep_rd hs3 r (.inr rfl), LPstep_rd hs2 r (.inr rfl), e1]
  have e3b : s3.rd pb = b := by rw [LPstep_rd hs3 pb (.inr rfl), LPstep_rd hs2 pb (.inr rfl), e1b]
  iapply (wpK_amo (base := (b : Int)) hw (hag s3) hq3 (by rw [hP3, hc3]; rfl)
    (by rw [e3b]; exact hB) (by rw [e3b]))
  iframe Hl
  inext
  iintro %tvs %ty %hl %_ %_ %_ %_ %_ %hy
  have hlt : tx < ty := by
    simp [stPre] at hy
    omega
  imodintro
  isplitr
  · ipureintro
    exact ⟨0, grd_intro ⟨⟨tx, by omega, by simp only [e1, srcR_pos hnz.2.1, srcR_pos hnz.1]⟩,
      ⟨tvs, ty, by omega, by simp only [e3, srcR_pos hnz.2.2.1, srcR_pos hnz.1], hl⟩, hlt⟩⟩
  isplitr
  · ipureintro; exact grd_intro trivial
  iintro %s4 %hs4 Hl
  obtain ⟨hP4, hc4, hq4⟩ := LPstep_at hs4 hP3 (by rw [hc3])
  iapply (wpK_fin hq4 (by rw [hP4, hc4]; simp))
  iexact Hl

/-- **Row 10's reader**: `amoswap.w.aq rd,x0,(pa); lw d,(pb)` proves `qAR` (COH: the AMO reads below its write;
rule 5: the acquire raises the load floor to the AMO's timestamp). -/
theorem hAqR_hart (img : Image) (M : List PMsg) (h : Nat) (s0 : LP) (a b rd pa pb d : Nat)
    (hprog : s0.prog = [.amo .swap 4 true false rd 0 pa, .load 4 true d pb 0])
    (hpc : s0.pc = 0) (hq : s0.q = []) (hnz : rd ≠ 0 ∧ pa ≠ 0 ∧ pb ≠ 0 ∧ pb ≠ rd)
    (ha : s0.rd pa = a) (hb : s0.rd pb = b) (hal : a < two64) (hbl : b < two64)
    (hA : aligned a 4 = true) (hB : aligned b 4 = true) :
    ⊢@{IProp GF} wpPF Proto.triv ⟨litStep, litDone, img, M, h⟩
      (ΨK M (qAR M a b true (amoD .swap 4 0) pa [] pb)) s0
      (fun _ => iprop(⌜∃ V, grd Proto.triv img M V True⌝)) := by
  have hw := litW_lit img M h
  have hag := litAg_lit (V := Unit) litDone img M h
  iapply (wpK_start (by trivial))
  iintro %γ %P0 Hl
  iapply (wpK_amo (base := (a : Int)) hw (hag s0) hq (by rw [hprog, hpc]; rfl) (by rw [ha]; exact hA) (by rw [ha]))
  iframe Hl
  inext
  iintro %tvs %t1 %hl %_ %_ %_ %_ %hcoh %hext
  have hsrc : src0 (LRmw true false (a : Int) tvs (amoD .swap 4 (s0.rd 0) tvs) (srcR pa) (srcR 0), some t1) < t1 := by
    obtain ⟨t0, v0, r0, rfl⟩ := tvs_cons hl (by decide)
    have hb0 := loadRun_coh0 psInit true false (srcsView psInit (srcR pa)) (a : Int) t0 v0 r0
    have h1 := cohBelow_b0 hcoh (by rw [amoD, toBytes_length]; decide)
    show t0 < t1
    omega
  imodintro
  isplitr
  · ipureintro
    exact ⟨0, grd_intro ⟨⟨tvs, t1, by omega, by simp only [srcR_pos hnz.2.1, srcR_zero, LP.rd]; rfl, hl⟩, hsrc⟩⟩
  isplitr
  · ipureintro; exact grd_intro trivial
  iintro %s1 %hs1 Hl
  obtain ⟨hP1, hc1, hq1⟩ := LPstep_at hs1 hprog (by rw [hpc])
  have e1 : s1.rd pb = b := by rw [LPstep_rd hs1 pb (.inl hnz.2.2.2), hb]
  iapply (wpK_ld (sz := 4) (sgn := true) (rd := d) (rs1 := pb) (off := 0) (base := (b : Int)) hw (hag s1) hq1
    (by rw [hP1, hc1]; rfl) (alg_of e1 hbl hB) (base_of e1 hbl))
  iframe Hl
  inext
  iintro %tvs1 %hl1 %hlo1
  have hord : noCmo M → ¬ writesIn M b (src0 (LLoad false false (b : Int) tvs1 (srcR pb), none))
      (tsOf (LRmw true false (a : Int) tvs (amoD .swap 4 (s0.rd 0) tvs) (srcR pa) (srcR 0), some t1)) := by
    intro hnc
    obtain ⟨u1, w1, q1, rfl⟩ := tvs_cons hl1 (by decide)
    have hw1 := (loadOk_b0nc hnc hlo1).2
    intro hc
    apply hw1
    refine writesIn_mono hc ?_
    show t1 ≤ _
    simp [ldPre, regWL, hnz.1, hnz.2.1, hnz.2.2.1]
    omega
  imodintro
  isplitr
  · ipureintro
    exact ⟨0, grd_intro ⟨⟨⟨tvs, t1, by omega, by simp only [srcR_pos hnz.2.1, srcR_zero, LP.rd]; rfl, hl⟩, hsrc⟩,
      ⟨tvs1, by rw [srcR_pos hnz.2.2.1], hl1⟩, hord⟩⟩
  iintro %s2 %hs2 Hl
  obtain ⟨hP2, hc2, hq2⟩ := LPstep_at hs2 hP1 (by rw [hc1])
  iapply (wpK_fin hq2 (by rw [hP2, hc2]; simp))
  iexact Hl

/-- **Row 11's reader**: `li r,v; amoswap.w rd,r,(pa); fence r,rw; lw d,(pb)` proves `qAR` (M0 (iv): the AMO is a
load for the fence, `vrOld ⊔= ts`; rule 4 raises the load floor). -/
theorem hLAFR_hart (img : Image) (M : List PMsg) (h : Nat) (s0 : LP) (a b v r rd pa pb d : Nat)
    (hprog : s0.prog = [.alui .add r 0 v, .amo .swap 4 false false rd r pa,
      .fence ⟨true, false, false, false, true, true, false, false⟩, .load 4 true d pb 0])
    (hpc : s0.pc = 0) (hq : s0.q = []) (hnz : r ≠ 0 ∧ rd ≠ 0 ∧ pa ≠ 0 ∧ pb ≠ 0 ∧ pa ≠ r ∧ pb ≠ r ∧ pb ≠ rd)
    (hlen : r < s0.regs.length) (hv : v < two64)
    (ha : s0.rd pa = a) (hb : s0.rd pb = b) (hal : a < two64) (hbl : b < two64)
    (hA : aligned a 4 = true) (hB : aligned b 4 = true) :
    ⊢@{IProp GF} wpPF Proto.triv ⟨litStep, litDone, img, M, h⟩
      (ΨK M (qAR M a b false (amoD .swap 4 v) pa [.DReg r] pb)) s0
      (fun _ => iprop(⌜∃ V, grd Proto.triv img M V True⌝)) := by
  have hw := litW_lit img M h
  have hag := litAg_lit (V := Unit) litDone img M h
  iapply (wpK_start (by trivial))
  iintro %γ %P0 Hl
  iapply (wpK_alui hw (hag s0) hq (by rw [hprog, hpc]; rfl) hnz.1)
  iframe Hl
  inext
  iintro %s1 %hs1 Hl
  obtain ⟨hP1, hc1, hq1⟩ := LPstep_at hs1 hprog (by rw [hpc])
  have e1 : s1.rd r = v := li_val hs1 hnz.1 hlen hv
  have e1a : s1.rd pa = a := by rw [LPstep_rd hs1 pa (.inl hnz.2.2.2.2.1), ha]
  have e1b : s1.rd pb = b := by rw [LPstep_rd hs1 pb (.inl hnz.2.2.2.2.2.1), hb]
  iapply (wpK_amo (base := (a : Int)) hw (hag s1) hq1 (by rw [hP1, hc1]; rfl) (by rw [e1a]; exact hA) (by rw [e1a]))
  iframe Hl
  inext
  iintro %tvs %t1 %hl %_ %_ %_ %_ %hcoh %hext
  have hsrc : src0 (LRmw false false (a : Int) tvs (amoD .swap 4 (s1.rd r) tvs) (srcR pa) (srcR r), some t1) < t1 := by
    obtain ⟨t0, v0, r0, rfl⟩ := tvs_cons hl (by decide)
    have hb0 := loadRun_coh0 (instrR (regWP psInit r (srcR 0))) false false
      (srcsView (instrR (regWP psInit r (srcR 0))) (srcR pa)) (a : Int) t0 v0 r0
    have h1 := cohBelow_b0 hcoh (by rw [amoD, toBytes_length]; decide)
    show t0 < t1
    omega
  imodintro
  isplitr
  · ipureintro
    exact ⟨0, grd_intro ⟨⟨tvs, t1, by omega, by simp only [e1, srcR_pos hnz.2.2.1, srcR_pos hnz.1], hl⟩, hsrc⟩⟩
  isplitr
  · ipureintro; exact grd_intro trivial
  iintro %s2 %hs2 Hl
  obtain ⟨hP2, hc2, hq2⟩ := LPstep_at hs2 hP1 (by rw [hc1])
  iapply (wpK_fence (f := ⟨true, false, false, false, true, true, false, false⟩) hw (hag s2) hq2
    (by rw [hP2, hc2]; rfl))
  iframe Hl
  inext
  iintro %s3 %hs3 Hl
  obtain ⟨hP3, hc3, hq3⟩ := LPstep_at hs3 hP2 (by rw [hc2])
  have e3 : s3.rd pb = b := by rw [LPstep_rd hs3 pb (.inr rfl), LPstep_rd hs2 pb (.inl hnz.2.2.2.2.2.2), e1b]
  iapply (wpK_ld (sz := 4) (sgn := true) (rd := d) (rs1 := pb) (off := 0) (base := (b : Int)) hw (hag s3) hq3
    (by rw [hP3, hc3]; rfl) (alg_of e3 hbl hB) (base_of e3 hbl))
  iframe Hl
  inext
  iintro %tvs1 %hl1 %hlo1
  have hord : noCmo M → ¬ writesIn M b (src0 (LLoad false false (b : Int) tvs1 (srcR pb), none))
      (tsOf (LRmw false false (a : Int) tvs (amoD .swap 4 (s1.rd r) tvs) (srcR pa) (srcR r), some t1)) := by
    intro hnc
    obtain ⟨u1, w1, q1, rfl⟩ := tvs_cons hl1 (by decide)
    have hw1 := (loadOk_b0nc hnc hlo1).2
    intro hc
    apply hw1
    refine writesIn_mono hc ?_
    show t1 ≤ _
    simp [ldPre, regWL, hnz.1, hnz.2.1, hnz.2.2.1, hnz.2.2.2.1]
    omega
  imodintro
  isplitr
  · ipureintro
    exact ⟨0, grd_intro ⟨⟨⟨tvs, t1, by omega, by simp only [e1, srcR_pos hnz.2.2.1, srcR_pos hnz.1], hl⟩, hsrc⟩,
      ⟨tvs1, by rw [srcR_pos hnz.2.2.2.1], hl1⟩, hord⟩⟩
  iintro %s4 %hs4 Hl
  obtain ⟨hP4, hc4, hq4⟩ := LPstep_at hs4 hP3 (by rw [hc3])
  iapply (wpK_fin hq4 (by rw [hP4, hc4]; simp))
  iexact Hl

/-- **Row 11b's writer**: `li r,v; amoswap.w rd,r,(pa); fence r,rw; li r',v'; sw r',(pb)` proves `qAW` (M0 (iv):
the AMO is a load for `fence r,rw`, whose store floor is then above it). -/
theorem hLAFW_hart (img : Image) (M : List PMsg) (h : Nat) (s0 : LP) (a b v v' r rd pa r' pb : Nat)
    (hprog : s0.prog = [.alui .add r 0 v, .amo .swap 4 false false rd r pa,
      .fence ⟨true, false, false, false, true, true, false, false⟩, .alui .add r' 0 v', .store 4 r' pb 0])
    (hpc : s0.pc = 0) (hq : s0.q = [])
    (hnz : r ≠ 0 ∧ rd ≠ 0 ∧ pa ≠ 0 ∧ pb ≠ 0 ∧ r' ≠ 0 ∧ pa ≠ r ∧ pb ≠ r ∧ pb ≠ rd ∧ pb ≠ r')
    (hlen : r < s0.regs.length ∧ r' < s0.regs.length) (hv : v < two64)
    (ha : s0.rd pa = a) (hb : s0.rd pb = b) (hal : a < two64) (hbl : b < two64)
    (hA : aligned a 4 = true) (hB : aligned b 4 = true) :
    ⊢@{IProp GF} wpPF Proto.triv ⟨litStep, litDone, img, M, h⟩ (ΨK M (qAW a b v pa r pb r')) s0
      (fun _ => iprop(⌜∃ V, grd Proto.triv img M V True⌝)) := by
  have hw := litW_lit img M h
  have hag := litAg_lit (V := Unit) litDone img M h
  iapply (wpK_start (by trivial))
  iintro %γ %P0 Hl
  iapply (wpK_alui hw (hag s0) hq (by rw [hprog, hpc]; rfl) hnz.1)
  iframe Hl
  inext
  iintro %s1 %hs1 Hl
  obtain ⟨hP1, hc1, hq1⟩ := LPstep_at hs1 hprog (by rw [hpc])
  have e1 : s1.rd r = v := li_val hs1 hnz.1 hlen.1 hv
  have e1a : s1.rd pa = a := by rw [LPstep_rd hs1 pa (.inl hnz.2.2.2.2.2.1), ha]
  have e1b : s1.rd pb = b := by rw [LPstep_rd hs1 pb (.inl hnz.2.2.2.2.2.2.1), hb]
  iapply (wpK_amo (base := (a : Int)) hw (hag s1) hq1 (by rw [hP1, hc1]; rfl) (by rw [e1a]; exact hA) (by rw [e1a]))
  iframe Hl
  inext
  iintro %tvs %t0 %hl %_ %_ %_ %_ %_ %hext
  imodintro
  isplitr
  · ipureintro
    exact ⟨0, grd_intro ⟨tvs, t0, by omega, by simp only [e1, srcR_pos hnz.2.2.1, srcR_pos hnz.1], hl⟩⟩
  isplitr
  · ipureintro; exact grd_intro trivial
  iintro %s2 %hs2 Hl
  obtain ⟨hP2, hc2, hq2⟩ := LPstep_at hs2 hP1 (by rw [hc1])
  iapply (wpK_fence (f := ⟨true, false, false, false, true, true, false, false⟩) hw (hag s2) hq2
    (by rw [hP2, hc2]; rfl))
  iframe Hl
  inext
  iintro %s3 %hs3 Hl
  obtain ⟨hP3, hc3, hq3⟩ := LPstep_at hs3 hP2 (by rw [hc2])
  iapply (wpK_alui hw (hag s3) hq3 (by rw [hP3, hc3]; rfl) hnz.2.2.2.2.1)
  iframe Hl
  inext
  iintro %s4 %hs4 Hl
  obtain ⟨hP4, hc4, hq4⟩ := LPstep_at hs4 hP3 (by rw [hc3])
  have e4b : s4.rd pb = b := by
    rw [LPstep_rd hs4 pb (.inl hnz.2.2.2.2.2.2.2.2), LPstep_rd hs3 pb (.inr rfl),
      LPstep_rd hs2 pb (.inl hnz.2.2.2.2.2.2.2.1), e1b]
  iapply (wpK_sw (sz := 4) (rs2 := r') (rs1 := pb) (off := 0) (base := (b : Int)) hw (hag s4) hq4
    (by rw [hP4, hc4]; rfl) (alg_of e4b hbl hB) (base_of e4b hbl))
  iframe Hl
  inext
  iintro %tz %_ %_ %_ %hz
  have hlt : t0 < tz := by
    simp [stPreA, stPre, regWL, hnz.1, hnz.2.1, hnz.2.2.1, hnz.2.2.2.1, hnz.2.2.2.2.1] at hz
    omega
  imodintro
  isplitr
  · ipureintro
    exact ⟨0, grd_intro ⟨⟨tvs, t0, by omega, by simp only [e1, srcR_pos hnz.2.2.1, srcR_pos hnz.1], hl⟩,
      ⟨_, toBytes_length _ _, tz, by omega, by simp only [srcR_pos hnz.2.2.2.1, srcR_pos hnz.2.2.2.2.1]; rfl⟩, hlt⟩⟩
  isplitr
  · ipureintro; exact grd_intro trivial
  iintro %s5 %hs5 Hl
  obtain ⟨hP5, hc5, hq5⟩ := LPstep_at hs5 hP4 (by rw [hc4])
  iapply (wpK_fin hq5 (by rw [hP5, hc5]; simp))
  iexact Hl

/-- **Row 28's writer**: `li r,v; amoswap.w rd,r,(pa); addi r',rd,k; sw r',(pb)` proves `qAW` (M0 (v): the result
register's view is the AMO's timestamp; rule 10: the store's data view contains it). -/
theorem hLADW_hart (img : Image) (M : List PMsg) (h : Nat) (s0 : LP) (a b v k r rd pa r' pb : Nat)
    (hprog : s0.prog = [.alui .add r 0 v, .amo .swap 4 false false rd r pa, .alui .add r' rd k, .store 4 r' pb 0])
    (hpc : s0.pc = 0) (hq : s0.q = [])
    (hnz : r ≠ 0 ∧ rd ≠ 0 ∧ pa ≠ 0 ∧ pb ≠ 0 ∧ r' ≠ 0 ∧ pa ≠ r ∧ pb ≠ r ∧ pb ≠ rd ∧ pb ≠ r')
    (hlen : r < s0.regs.length) (hv : v < two64)
    (ha : s0.rd pa = a) (hb : s0.rd pb = b) (hal : a < two64) (hbl : b < two64)
    (hA : aligned a 4 = true) (hB : aligned b 4 = true) :
    ⊢@{IProp GF} wpPF Proto.triv ⟨litStep, litDone, img, M, h⟩ (ΨK M (qAW a b v pa r pb r')) s0
      (fun _ => iprop(⌜∃ V, grd Proto.triv img M V True⌝)) := by
  have hw := litW_lit img M h
  have hag := litAg_lit (V := Unit) litDone img M h
  iapply (wpK_start (by trivial))
  iintro %γ %P0 Hl
  iapply (wpK_alui hw (hag s0) hq (by rw [hprog, hpc]; rfl) hnz.1)
  iframe Hl
  inext
  iintro %s1 %hs1 Hl
  obtain ⟨hP1, hc1, hq1⟩ := LPstep_at hs1 hprog (by rw [hpc])
  have e1 : s1.rd r = v := li_val hs1 hnz.1 hlen hv
  have e1a : s1.rd pa = a := by rw [LPstep_rd hs1 pa (.inl hnz.2.2.2.2.2.1), ha]
  have e1b : s1.rd pb = b := by rw [LPstep_rd hs1 pb (.inl hnz.2.2.2.2.2.2.1), hb]
  iapply (wpK_amo (base := (a : Int)) hw (hag s1) hq1 (by rw [hP1, hc1]; rfl) (by rw [e1a]; exact hA) (by rw [e1a]))
  iframe Hl
  inext
  iintro %tvs %t0 %hl %_ %_ %_ %_ %_ %hext
  imodintro
  isplitr
  · ipureintro
    exact ⟨0, grd_intro ⟨tvs, t0, by omega, by simp only [e1, srcR_pos hnz.2.2.1, srcR_pos hnz.1], hl⟩⟩
  isplitr
  · ipureintro; exact grd_intro trivial
  iintro %s2 %hs2 Hl
  obtain ⟨hP2, hc2, hq2⟩ := LPstep_at hs2 hP1 (by rw [hc1])
  iapply (wpK_alui hw (hag s2) hq2 (by rw [hP2, hc2]; rfl) hnz.2.2.2.2.1)
  iframe Hl
  inext
  iintro %s3 %hs3 Hl
  obtain ⟨hP3, hc3, hq3⟩ := LPstep_at hs3 hP2 (by rw [hc2])
  have e3b : s3.rd pb = b := by
    rw [LPstep_rd hs3 pb (.inl hnz.2.2.2.2.2.2.2.2), LPstep_rd hs2 pb (.inl hnz.2.2.2.2.2.2.2.1), e1b]
  iapply (wpK_sw (sz := 4) (rs2 := r') (rs1 := pb) (off := 0) (base := (b : Int)) hw (hag s3) hq3
    (by rw [hP3, hc3]; rfl) (alg_of e3b hbl hB) (base_of e3b hbl))
  iframe Hl
  inext
  iintro %ty %_ %_ %_ %hy
  have hlt : t0 < ty := by
    simp [stPreA, stPre, regWL, hnz.1, hnz.2.1, hnz.2.2.1, hnz.2.2.2.1, hnz.2.2.2.2.1] at hy
    omega
  imodintro
  isplitr
  · ipureintro
    exact ⟨0, grd_intro ⟨⟨tvs, t0, by omega, by simp only [e1, srcR_pos hnz.2.2.1, srcR_pos hnz.1], hl⟩,
      ⟨_, toBytes_length _ _, ty, by omega, by simp only [srcR_pos hnz.2.2.2.1, srcR_pos hnz.2.2.2.2.1]; rfl⟩, hlt⟩⟩
  isplitr
  · ipureintro; exact grd_intro trivial
  iintro %s4 %hs4 Hl
  obtain ⟨hP4, hc4, hq4⟩ := LPstep_at hs4 hP3 (by rw [hc3])
  iapply (wpK_fin hq4 (by rw [hP4, hc4]; simp))
  iexact Hl

/-- **Row 28c's writer**: `li r,v; amoswap.w rd,r,(pa); bne rd,x0,L; L: li r',v'; sw r',(pb)` proves `qAW` (M0 (v)
and rule 11: `LCtrl [rd]` raises the capture view to the AMO's timestamp, below every later store's pre-view). -/
theorem hLACW_hart (img : Image) (M : List PMsg) (h : Nat) (s0 : LP) (a b v v' r rd pa r' pb : Nat)
    (hprog : s0.prog = [.alui .add r 0 v, .amo .swap 4 false false rd r pa, .br .ne rd 0 3, .alui .add r' 0 v',
      .store 4 r' pb 0])
    (hpc : s0.pc = 0) (hq : s0.q = [])
    (hnz : r ≠ 0 ∧ rd ≠ 0 ∧ pa ≠ 0 ∧ pb ≠ 0 ∧ r' ≠ 0 ∧ pa ≠ r ∧ pb ≠ r ∧ pb ≠ rd ∧ pb ≠ r')
    (hlen : r < s0.regs.length) (hv : v < two64)
    (ha : s0.rd pa = a) (hb : s0.rd pb = b) (hal : a < two64) (hbl : b < two64)
    (hA : aligned a 4 = true) (hB : aligned b 4 = true) :
    ⊢@{IProp GF} wpPF Proto.triv ⟨litStep, litDone, img, M, h⟩ (ΨK M (qAW a b v pa r pb r')) s0
      (fun _ => iprop(⌜∃ V, grd Proto.triv img M V True⌝)) := by
  have hw := litW_lit img M h
  have hag := litAg_lit (V := Unit) litDone img M h
  iapply (wpK_start (by trivial))
  iintro %γ %P0 Hl
  iapply (wpK_alui hw (hag s0) hq (by rw [hprog, hpc]; rfl) hnz.1)
  iframe Hl
  inext
  iintro %s1 %hs1 Hl
  obtain ⟨hP1, hc1, hq1⟩ := LPstep_at hs1 hprog (by rw [hpc])
  have e1 : s1.rd r = v := li_val hs1 hnz.1 hlen hv
  have e1a : s1.rd pa = a := by rw [LPstep_rd hs1 pa (.inl hnz.2.2.2.2.2.1), ha]
  have e1b : s1.rd pb = b := by rw [LPstep_rd hs1 pb (.inl hnz.2.2.2.2.2.2.1), hb]
  iapply (wpK_amo (base := (a : Int)) hw (hag s1) hq1 (by rw [hP1, hc1]; rfl) (by rw [e1a]; exact hA) (by rw [e1a]))
  iframe Hl
  inext
  iintro %tvs %t0 %hl %_ %_ %_ %_ %_ %hext
  imodintro
  isplitr
  · ipureintro
    exact ⟨0, grd_intro ⟨tvs, t0, by omega, by simp only [e1, srcR_pos hnz.2.2.1, srcR_pos hnz.1], hl⟩⟩
  isplitr
  · ipureintro; exact grd_intro trivial
  iintro %s2 %hs2 Hl
  obtain ⟨hP2, hc2, hq2⟩ := LPstep_at hs2 hP1 (by rw [hc1])
  -- `bne rd,x0,3`: both outcomes go to instruction 3
  iapply (wpK_br hw (hag s2) hq2 (by rw [hP2, hc2]; rfl) (by rw [hP2, hc2]; simp))
  iframe Hl
  inext
  iintro %s3 %hs3 Hl
  obtain ⟨hP3, hc3, hq3⟩ := LPstep_at (k := 3) hs3 hP2 (by rw [hc2]; split <;> rfl)
  iapply (wpK_alui hw (hag s3) hq3 (by rw [hP3, hc3]; rfl) hnz.2.2.2.2.1)
  iframe Hl
  inext
  iintro %s4 %hs4 Hl
  obtain ⟨hP4, hc4, hq4⟩ := LPstep_at hs4 hP3 (by rw [hc3])
  have e4b : s4.rd pb = b := by
    rw [LPstep_rd hs4 pb (.inl hnz.2.2.2.2.2.2.2.2), LPstep_rd hs3 pb (.inr rfl),
      LPstep_rd hs2 pb (.inl hnz.2.2.2.2.2.2.2.1), e1b]
  iapply (wpK_sw (sz := 4) (rs2 := r') (rs1 := pb) (off := 0) (base := (b : Int)) hw (hag s4) hq4
    (by rw [hP4, hc4]; rfl) (alg_of e4b hbl hB) (base_of e4b hbl))
  iframe Hl
  inext
  iintro %ty %_ %_ %_ %hy
  have hlt : t0 < ty := by
    simp [stPreA, stPre, regWL, hnz.1, hnz.2.1, hnz.2.2.1, hnz.2.2.2.1, hnz.2.2.2.2.1] at hy
    omega
  imodintro
  isplitr
  · ipureintro
    exact ⟨0, grd_intro ⟨⟨tvs, t0, by omega, by simp only [e1, srcR_pos hnz.2.2.1, srcR_pos hnz.1], hl⟩,
      ⟨_, toBytes_length _ _, ty, by omega, by simp only [srcR_pos hnz.2.2.2.1, srcR_pos hnz.2.2.2.2.1]; rfl⟩, hlt⟩⟩
  isplitr
  · ipureintro; exact grd_intro trivial
  iintro %s5 %hs5 Hl
  obtain ⟨hP5, hc5, hq5⟩ := LPstep_at hs5 hP4 (by rw [hc4])
  iapply (wpK_fin hq5 (by rw [hP5, hc5]; simp))
  iexact Hl

end harts

/-! ## 3. Writers and outcomes -/

theorem lw_rmw {aq rl : Bool} {a : Int} {tvs : List (Nat × BitVec 8)} {d : List (BitVec 8)} {as0 vs0 : List Dsrc}
    {pa : Int} {data : List (BitVec 8)} (h : labelWrite (LRmw aq rl a tvs d as0 vs0) = some (pa, data)) :
    pa = a ∧ data = d := by
  simp only [labelWrite, Option.some.injEq, Prod.mk.injEq] at h; exact ⟨h.1.symm, h.2.symm⟩

theorem qSA_writer {a b : Int} {v : Nat} {rl : Bool} {pa r pb : Nat} {ev : Trace} {e : PEv} {t : Nat}
    (hQ : qSA a b v rl pa r pb ev) (he : e ∈ ev) (ht : e.2 = some t) :
    e = (LStore false false a (toBytes v 4) [.DReg pa] [.DReg r], some t) ∨
      ((∃ tvs, e = (LRmw false rl b tvs (amoD .swap 4 v tvs) [.DReg pb] [.DReg r], some t)) ∧
        ∃ t0, 0 < t0 ∧ (LStore false false a (toBytes v 4) [.DReg pa] [.DReg r], some t0) ∈ ev ∧ t0 < t) := by
  rcases q2_cases hQ with rfl | ⟨e0, rfl, ⟨t0, _, rfl⟩⟩ | ⟨e0, e1, rfl, ⟨t0, h0, rfl⟩, ⟨tvs, t1, _, rfl, _⟩, hlt⟩
  · cases he
  · rw [List.mem_singleton] at he; subst he; cases ht; exact .inl rfl
  · rcases List.mem_cons.1 he with rfl | he
    · cases ht; exact .inl rfl
    · rw [List.mem_singleton] at he; subst he; cases ht
      exact .inr ⟨⟨tvs, rfl⟩, t0, h0, by simp, hlt⟩

theorem qAR_writer {M : List PMsg} {a b : Int} {aq : Bool} {dat : List (Nat × BitVec 8) → List (BitVec 8)}
    {pa : Nat} {vs : List Dsrc} {pb : Nat} {ev : Trace} {e : PEv} {t : Nat}
    (hQ : qAR M a b aq dat pa vs pb ev) (he : e ∈ ev) (ht : e.2 = some t) :
    ∃ tvs, e = (LRmw aq false a tvs (dat tvs) [.DReg pa] vs, some t) := by
  rcases q2_cases hQ with rfl | ⟨e0, rfl, ⟨⟨tvs, t0, _, rfl, _⟩, _⟩⟩ |
      ⟨e0, e1, rfl, ⟨⟨tvs, t0, _, rfl, _⟩, _⟩, ⟨_, rfl, _⟩, _⟩
  · cases he
  · rw [List.mem_singleton] at he; subst he; cases ht; exact ⟨tvs, rfl⟩
  · rcases List.mem_cons.1 he with rfl | he
    · cases ht; exact ⟨tvs, rfl⟩
    · rw [List.mem_singleton] at he; subst he; cases ht

theorem qAR_out {P D : Type} {run : PFRun P D} {M : List PMsg} {h : Nat} {a b : Int} {aq : Bool}
    {dat : List (Nat × BitVec 8) → List (BitVec 8)} {pa : Nat} {vs : List Dsrc} {pb : Nat} {v0 v1 : Nat}
    (hwf : run.traceWf M) (hQ : qAR M a b aq dat pa vs pb (memEv (run.trace h)))
    (ho0 : run.obsLoad h 0 = some v0) (ho1 : run.obsLoad h 1 = some v1) :
    ∃ s0 b0 t1 s1 b1, memByte run.cfg.pcImg M s0 a = some b0 ∧ b0.toNat = v0 % 256 ∧ s0 < t1 ∧
      memByte run.cfg.pcImg M s1 b = some b1 ∧ b1.toNat = v1 % 256 ∧ (noCmo M → ¬ writesIn M b s1 t1) := by
  rw [obsLoad_memEv] at ho0 ho1
  rcases q2_cases hQ with hev | ⟨e0, hev, ⟨⟨tvs, t0, _, rfl, _⟩, _⟩⟩ |
      ⟨e0, e1, hev, ⟨⟨tvs, t0, _, rfl, hl0⟩, hsrc⟩, hP1, hord⟩
  · rw [hev] at ho0; simp [loadsOf] at ho0
  · rw [hev] at ho1; simp [loadsOf, loadLikeTvs] at ho1
  · obtain ⟨u0, w0, r0, rfl⟩ := tvs_cons hl0 (by decide)
    obtain ⟨u1, w1, r1, rfl, _⟩ := isLd_cons hP1 (by decide)
    have hm0 : (LRmw aq false a ((u0, w0) :: r0) (dat ((u0, w0) :: r0)) [.DReg pa] vs, some t0) ∈
        memEv (run.trace h) := by rw [hev]; simp
    have hm1 : (LLoad false false b ((u1, w1) :: r1) [.DReg pb], (none : Option Nat)) ∈ memEv (run.trace h) := by
      rw [hev]; simp
    rw [hev] at ho0 ho1
    simp only [loadsOf, List.filterMap_cons, loadLikeTvs, List.filterMap_nil, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.map_some, Option.some.injEq] at ho0 ho1
    exact ⟨u0, w0, t0, u1, w1, (kit_read hwf hm0 rfl).1, obsOf_b0 ho0, hsrc, kit_read0 hwf hm1 rfl, obsOf_b0 ho1, hord⟩

theorem qAW_writer {a b : Int} {v : Nat} {pa ra pb rb : Nat} {ev : Trace} {e : PEv} {t : Nat}
    (hQ : qAW a b v pa ra pb rb ev) (he : e ∈ ev) (ht : e.2 = some t) :
    (∃ tvs, e = (LRmw false false a tvs (amoD .swap 4 v tvs) [.DReg pa] [.DReg ra], some t)) ∨
      ((∃ d, d.length = 4 ∧ e = (LStore false false b d [.DReg pb] [.DReg rb], some t)) ∧
        ∃ t0 tvs, 0 < t0 ∧ (LRmw false false a tvs (amoD .swap 4 v tvs) [.DReg pa] [.DReg ra], some t0) ∈ ev ∧
          t0 < t) := by
  rcases q2_cases hQ with rfl | ⟨e0, rfl, ⟨tvs, t0, _, rfl, _⟩⟩ |
      ⟨e0, e1, rfl, ⟨tvs, t0, h0, rfl, _⟩, ⟨d, hdl, t1, _, rfl⟩, hlt⟩
  · cases he
  · rw [List.mem_singleton] at he; subst he; cases ht; exact .inl ⟨tvs, rfl⟩
  · rcases List.mem_cons.1 he with rfl | he
    · cases ht; exact .inl ⟨tvs, rfl⟩
    · rw [List.mem_singleton] at he; subst he; cases ht
      exact .inr ⟨⟨d, hdl, rfl⟩, t0, tvs, h0, by simp, hlt⟩

/-! ## 4. The contradictions -/

/-- **Rows 10, 11**: the reader's AMO read H0's AMO (the only write of 1 to y), which is above H0's `st x`; the
reader's load is above its own AMO, so it cannot read the image at x. -/
theorem amoRel_glue {run : PFRun LP Unit} {M : List PMsg} {img : Image} {rl aq : Bool} {r : Nat}
    {dat : List (Nat × BitVec 8) → List (BitVec 8)} {vs : List Dsrc} (himg : run.cfg.pcImg = img)
    (hx : img (X : Int) = some 0) (hy : img (Y : Int) = some 0)
    (hQ0 : qSA (X : Int) (Y : Int) 1 rl 8 r 9 (memEv (run.trace 0)))
    (hQ1 : qAR M (Y : Int) (X : Int) aq dat 9 vs 8 (memEv (run.trace 1)))
    (hout : ∀ h, 2 ≤ h → memEv (run.trace h) = [])
    (hdat : ∀ tvs (m : PMsg), m.pa = (Y : Int) → m.data = dat tvs → m.byteAt (Y : Int) ≠ some 1 ∧
      m.byteAt (X : Int) = none)
    (hnc : noCmo M) (hpart : ∀ t, 1 ≤ t → t ≤ M.length → exU (fun h => t ∈ run.fulfils h ∧ tidAt M t = some h))
    (hwf : run.traceWf M) : ¬ (run.obsLoad 1 0 = some 1 ∧ run.obsLoad 1 1 = some 0) := by
  rintro ⟨ho0, ho1⟩
  obtain ⟨s0, b0, t1, s1, b1, hr0, hv0, hlt, hr1, hv1, hord⟩ := qAR_out hwf hQ1 ho0 ho1
  rw [himg] at hr0 hr1
  obtain ⟨k, m, rfl, hm, hb⟩ := src_of_val hr0 hy (by rw [bv_of_toNat hv0 (by decide)]; decide)
  obtain ⟨h, hh, e, he, het, hlw⟩ := writer_cases hpart hwf 2 hout hm
  obtain ⟨tx, htx, hinx, hxy⟩ : ∃ tx, 0 < tx ∧
      (LStore false false (X : Int) (toBytes 1 4) [.DReg 8] [.DReg r], some tx) ∈ memEv (run.trace 0) ∧
      tx < k + 1 := by
    match h, hh with
    | 0, _ =>
      rcases qSA_writer hQ0 he het with rfl | ⟨⟨tvs, rfl⟩, t0, h0, hin, hlt'⟩
      · obtain ⟨hpa, hd⟩ := lw_st hlw; rw [byteAt_none_of hpa hd (by decide)] at hb; cases hb
      · exact ⟨t0, h0, hin, hlt'⟩
    | 1, _ =>
      obtain ⟨tvs, rfl⟩ := qAR_writer hQ1 he het
      obtain ⟨hpa, hd⟩ := lw_rmw hlw
      exact absurd (by rw [hb, bv_of_toNat hv0 (by decide)]; rfl) (hdat tvs m hpa hd).1
  have hs1 : s1 = 0 := src_img0 hr1 (bv_of_toNat hv1 (by decide)) (fun k' m' hm' hb' => by
    obtain ⟨h', hh', e', he', het', hlw'⟩ := writer_cases hpart hwf 2 hout hm'
    match h', hh' with
    | 0, _ =>
      rcases qSA_writer hQ0 he' het' with rfl | ⟨⟨tvs, rfl⟩, _⟩
      · obtain ⟨hpa, hd⟩ := lw_st hlw'; rw [byteAt_some_of hpa hd (v := 1) (by decide)] at hb'; cases hb'
      · obtain ⟨hpa, hd⟩ := lw_rmw hlw'
        rw [amoD_swap] at hd
        rw [byteAt_none_of hpa hd (by decide)] at hb'; cases hb'
    | 1, _ =>
      obtain ⟨tvs, rfl⟩ := qAR_writer hQ1 he' het'
      obtain ⟨hpa, hd⟩ := lw_rmw hlw'
      rw [(hdat tvs m' hpa hd).2] at hb'; cases hb')
  subst hs1
  exact hord hnc (st_writes hwf hinx htx (by decide) htx (by omega))

/-- **Rows 11b, 28, 28c**: the reader's first load read H0's store (the only write to `b`), which is above H0's AMO;
the reader's second load is above its first (fence), so it cannot read the image at `a`. -/
theorem amoW_glue {run : PFRun LP Unit} {M : List PMsg} {img : Image} {a b : Int} {v w : Nat} {pa ra pb rb p0 p1 : Nat}
    (himg : run.cfg.pcImg = img) (ha : img a = some 0) (hb0 : img b = some 0) (hw0 : w % 256 ≠ 0) (hw : w < 256)
    (hQ0 : qAW a b v pa ra pb rb (memEv (run.trace 0))) (hQ1 : qRR M b a 4 [.DReg p0] [.DReg p1] (memEv (run.trace 1)))
    (hout : ∀ h, 2 ≤ h → memEv (run.trace h) = [])
    (hab : ∀ (m : PMsg) d, m.pa = b → m.data = d → d.length = 4 → m.byteAt a = none)
    (hba : ∀ (m : PMsg) tvs, m.pa = a → m.data = amoD .swap 4 v tvs → m.byteAt b = none ∧ m.byteAt a ≠ some 0 ∧
      (m.byteAt a).isSome = true)
    (hnc : noCmo M) (hpart : ∀ t, 1 ≤ t → t ≤ M.length → exU (fun h => t ∈ run.fulfils h ∧ tidAt M t = some h))
    (hwf : run.traceWf M) : ¬ (run.obsLoad 1 0 = some w ∧ run.obsLoad 1 1 = some 0) := by
  rintro ⟨ho0, ho1⟩
  obtain ⟨s0, s1, b0, b1, hr0, hv0, hr1, hv1, hord⟩ := qRR_out hwf (by decide) hQ1 ho0 ho1
  rw [himg] at hr0 hr1
  obtain ⟨k, m, rfl, hm, hb⟩ := src_of_val hr0 hb0 (by
    intro he; rw [he] at hv0; simp at hv0; omega)
  obtain ⟨h, hh, e, he, het, hlw⟩ := writer_cases hpart hwf 2 hout hm
  obtain ⟨t0, tvs, ht0, hin0, h0k⟩ : ∃ t0 tvs, 0 < t0 ∧
      (LRmw false false a tvs (amoD .swap 4 v tvs) [.DReg pa] [.DReg ra], some t0) ∈ memEv (run.trace 0) ∧
      t0 < k + 1 := by
    match h, hh with
    | 0, _ =>
      rcases qAW_writer hQ0 he het with ⟨tvs, rfl⟩ | ⟨⟨d, _, rfl⟩, t0, tvs, h0, hin, hlt⟩
      · obtain ⟨hpa, hd⟩ := lw_rmw hlw; rw [(hba m tvs hpa hd).1] at hb; cases hb
      · exact ⟨t0, tvs, h0, hin, hlt⟩
    | 1, _ => rw [qRR_nots hQ1 he] at het; cases het
  have hs1 : s1 = 0 := src_img0 hr1 (bv_of_toNat hv1 (by decide)) (fun k' m' hm' hb' => by
    obtain ⟨h', hh', e', he', het', hlw'⟩ := writer_cases hpart hwf 2 hout hm'
    match h', hh' with
    | 0, _ =>
      rcases qAW_writer hQ0 he' het' with ⟨tvs', rfl⟩ | ⟨⟨d, hdl, rfl⟩, _⟩
      · obtain ⟨hpa, hd⟩ := lw_rmw hlw'; exact (hba m' tvs' hpa hd).2.1 hb'
      · obtain ⟨hpa, hd⟩ := lw_st hlw'
        rw [hab m' d hpa hd hdl] at hb'; cases hb'
    | 1, _ => rw [qRR_nots hQ1 he'] at het'; cases het')
  subst hs1
  obtain ⟨m0, hm0, hpa0, hd0⟩ := kit_msg hwf hin0 rfl rfl
  exact hord hnc (writesIn_of hm0 (hba m0 tvs hpa0 hd0).2.2 (by omega) (by omega))

/-! ## 5. The verdicts -/

theorem amo_hdat (c : Nat) (hc : c % 256 ≠ 1) (hc' : c < 256) : ∀ tvs (m : PMsg), m.pa = (Y : Int) →
    m.data = amoD .swap 4 c tvs → m.byteAt (Y : Int) ≠ some 1 ∧ m.byteAt (X : Int) = none := by
  intro tvs m hpa hd
  rw [amoD_swap] at hd
  refine ⟨fun h => ?_, byteAt_lt (by rw [hpa]; decide)⟩
  rw [byteAt_pd hpa hd] at h
  simp only [show ((Y : Nat) : Int) ≤ ((Y : Nat) : Int) from Int.le_refl _, if_true, Int.sub_self,
    Int.toNat_zero] at h
  simp only [toBytes, byteList, List.range, List.range.loop, List.map, List.getElem?_cons_zero,
    Option.some.injEq] at h
  have := congrArg BitVec.toNat h
  simp [bv8, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hc' (by decide : 256 ≤ 2 ^ 32))] at this
  omega

/-- **ROW 10, MP+amo.rl+amo.aq: FORBIDDEN, in the logic** (plan §5 row 10, rules 5, 6; M0). -/
theorem lit_mpAmoRlAq : ∀ (M : List PMsg) (run : PFRun LP Unit),
    validRun litStep (testImg Weak.Prom.Ref.Lit.mpAmoRlAq) () (progs Weak.Prom.Ref.Lit.mpAmoRlAq) M run →
    ¬ (run.obsLoad 1 0 = some 1 ∧ run.obsLoad 1 1 = some 0) := by
  intro M run hrun
  obtain ⟨_, hQ, hnc, hpart, hwf, himg, _⟩ := kitAdeq (π := Proto.triv)
    (fun h => match h with
      | 0 => qSA (X : Int) (Y : Int) 1 true 8 6 9
      | 1 => qAR M (Y : Int) (X : Int) true (amoD .swap 4 0) 9 [] 8
      | _ => q0) (fun _ _ => True) trivial
    (fun h => match h with | 0 => trivial | 1 => trivial | _ + 2 => rfl)
    (fun h p hp _ => by
      obtain ⟨hpr, hpc, hq, hlen, hrd⟩ := progs_get hp
      match h with
      | 0 =>
        exact hSAmoRl_hart _ M 0 p X Y 1 6 8 9 (by rw [hpr]; rfl) hpc hq (by decide) (by rw [hlen]; decide)
          (by decide) (by rw [hrd 8 (by decide) (by decide)]; rfl) (by rw [hrd 9 (by decide) (by decide)]; rfl)
          (by decide) (by decide) (by decide) (by decide)
      | 1 =>
        exact hAqR_hart _ M 1 p Y X 10 9 8 11 (by rw [hpr]; rfl) hpc hq (by decide)
          (by rw [hrd 9 (by decide) (by decide)]; rfl) (by rw [hrd 8 (by decide) (by decide)]; rfl)
          (by decide) (by decide) (by decide) (by decide)
      | n + 2 =>
        have hl : (progs Weak.Prom.Ref.Lit.mpAmoRlAq).length = 2 := rfl
        rw [List.getElem?_eq_none (by omega)] at hp; cases hp) hrun
  exact amoRel_glue himg rfl rfl (hQ 0) (hQ 1) (fun h hh => by
      obtain ⟨k, rfl⟩ : ∃ k, h = k + 2 := ⟨h - 2, by omega⟩; exact hQ (k + 2))
    (amo_hdat 0 (by decide) (by decide)) hnc hpart hwf

/-- **ROW 11, MP+fence.rw.w-amo+amo-fence.r.rw: FORBIDDEN, in the logic** (plan §5 row 11, rule 4 both sides, M0's
read half: the AMO is a load for `fence r,rw`). -/
theorem lit_mpFAmo : ∀ (M : List PMsg) (run : PFRun LP Unit),
    validRun litStep (testImg Weak.Prom.Ref.Lit.mpFAmo) () (progs Weak.Prom.Ref.Lit.mpFAmo) M run →
    ¬ (run.obsLoad 1 0 = some 1 ∧ run.obsLoad 1 1 = some 0) := by
  intro M run hrun
  obtain ⟨_, hQ, hnc, hpart, hwf, himg, _⟩ := kitAdeq (π := Proto.triv)
    (fun h => match h with
      | 0 => qSA (X : Int) (Y : Int) 1 false 8 5 9
      | 1 => qAR M (Y : Int) (X : Int) false (amoD .swap 4 2) 9 [.DReg 7] 8
      | _ => q0) (fun _ _ => True) trivial
    (fun h => match h with | 0 => trivial | 1 => trivial | _ + 2 => rfl)
    (fun h p hp _ => by
      obtain ⟨hpr, hpc, hq, hlen, hrd⟩ := progs_get hp
      match h with
      | 0 =>
        exact hSFAmo_hart _ M 0 p X Y 1 5 8 9 (by rw [hpr]; rfl) hpc hq (by decide) (by rw [hlen]; decide)
          (by decide) (by rw [hrd 8 (by decide) (by decide)]; rfl) (by rw [hrd 9 (by decide) (by decide)]; rfl)
          (by decide) (by decide) (by decide) (by decide)
      | 1 =>
        exact hLAFR_hart _ M 1 p Y X 2 7 10 9 8 11 (by rw [hpr]; rfl) hpc hq (by decide) (by rw [hlen]; decide)
          (by decide) (by rw [hrd 9 (by decide) (by decide)]; rfl) (by rw [hrd 8 (by decide) (by decide)]; rfl)
          (by decide) (by decide) (by decide) (by decide)
      | n + 2 =>
        have hl : (progs Weak.Prom.Ref.Lit.mpFAmo).length = 2 := rfl
        rw [List.getElem?_eq_none (by omega)] at hp; cases hp) hrun
  exact amoRel_glue himg rfl rfl (hQ 0) (hQ 1) (fun h hh => by
      obtain ⟨k, rfl⟩ : ∃ k, h = k + 2 := ⟨h - 2, by omega⟩; exact hQ (k + 2))
    (amo_hdat 2 (by decide) (by decide)) hnc hpart hwf

theorem amo_hba {a b : Int} (v : Nat) (hab : a + 4 ≤ b) (hv : v % 256 ≠ 0) (hv' : v < 256) :
    ∀ (m : PMsg) tvs, m.pa = a → m.data = amoD .swap 4 v tvs → m.byteAt b = none ∧ m.byteAt a ≠ some 0 ∧
      (m.byteAt a).isSome = true := by
  intro m tvs hpa hd
  rw [amoD_swap] at hd
  have hlen : m.data.length = 4 := by rw [hd, toBytes_length]
  have e0 : m.byteAt a = m.data[0]? := by rw [← hpa]; exact byteAt_base m
  refine ⟨?_, ?_, ?_⟩
  · unfold PMsg.byteAt; rw [hpa, if_pos (by omega)]
    apply List.getElem?_eq_none; rw [hlen]; omega
  · rw [e0, hd]
    simp only [toBytes, byteList, List.range, List.range.loop, List.map, List.getElem?_cons_zero, ne_eq,
      Option.some.injEq]
    intro h
    have := congrArg BitVec.toNat h
    simp [bv8, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hv' (by decide : 256 ≤ 2 ^ 32))] at this
    omega
  · rw [e0, hd]; rfl

/-- **ROW 11b, AMO-store-part+fence.r.rw: FORBIDDEN, in the logic** (plan §5 row 11b, M0 (iv): the AMO is a load,
so `fence r,rw` orders the single op before `sd z`). -/
theorem lit_amoStorePart : ∀ (M : List PMsg) (run : PFRun LP Unit),
    validRun litStep (testImg Weak.Prom.Ref.Lit.amoStorePart) () (progs Weak.Prom.Ref.Lit.amoStorePart) M run →
    ¬ (run.obsLoad 1 0 = some 2 ∧ run.obsLoad 1 1 = some 0) := by
  intro M run hrun
  obtain ⟨_, hQ, hnc, hpart, hwf, himg, _⟩ := kitAdeq (π := Proto.triv)
    (fun h => match h with
      | 0 => qAW (Y : Int) (Z : Int) 1 9 5 18 28
      | 1 => qRR M (Z : Int) (Y : Int) 4 [.DReg 18] [.DReg 9]
      | _ => q0) (fun _ _ => True) trivial
    (fun h => match h with | 0 => trivial | 1 => trivial | _ + 2 => rfl)
    (fun h p hp _ => by
      obtain ⟨hpr, hpc, hq, hlen, hrd⟩ := progs_get hp
      match h with
      | 0 =>
        exact hLAFW_hart _ M 0 p Y Z 1 2 5 10 9 28 18 (by rw [hpr]; rfl) hpc hq (by decide)
          ⟨by rw [hlen]; decide, by rw [hlen]; decide⟩ (by decide)
          (by rw [hrd 9 (by decide) (by decide)]; rfl) (by rw [hrd 18 (by decide) (by decide)]; rfl)
          (by decide) (by decide) (by decide) (by decide)
      | 1 =>
        exact hRR_hart _ M 1 p 4 Z Y 18 9 10 11 true false false (by rw [hpr]; rfl) hpc hq (by decide) (by decide)
          (by decide) (by rw [hrd 18 (by decide) (by decide)]; rfl) (by rw [hrd 9 (by decide) (by decide)]; rfl)
          (by decide) (by decide) (by decide) (by decide)
      | n + 2 =>
        have hl : (progs Weak.Prom.Ref.Lit.amoStorePart).length = 2 := rfl
        rw [List.getElem?_eq_none (by omega)] at hp; cases hp) hrun
  exact amoW_glue himg rfl rfl (by decide) (by decide) (hQ 0) (hQ 1) (fun h hh => by
      obtain ⟨k, rfl⟩ : ∃ k, h = k + 2 := ⟨h - 2, by omega⟩; exact hQ (k + 2))
    (fun m d hpa _ _ => byteAt_lt (by rw [hpa]; decide)) (amo_hba 1 (by decide) (by decide) (by decide))
    hnc hpart hwf

/-- **ROW 28, MP+amo-data+fence.r.r: FORBIDDEN, in the logic** (plan §5 row 28, rule 10 from the AMO's single op,
M0 (v)). -/
theorem lit_mpAmoData : ∀ (M : List PMsg) (run : PFRun LP Unit),
    validRun litStep (testImg Weak.Prom.Ref.Lit.mpAmoData) () (progs Weak.Prom.Ref.Lit.mpAmoData) M run →
    ¬ (run.obsLoad 1 0 = some 5 ∧ run.obsLoad 1 1 = some 0) := by
  intro M run hrun
  obtain ⟨_, hQ, hnc, hpart, hwf, himg, _⟩ := kitAdeq (π := Proto.triv)
    (fun h => match h with
      | 0 => qAW (X : Int) (Y : Int) 2 8 7 9 5
      | 1 => qRR M (Y : Int) (X : Int) 4 [.DReg 9] [.DReg 8]
      | _ => q0) (fun _ _ => True) trivial
    (fun h => match h with | 0 => trivial | 1 => trivial | _ + 2 => rfl)
    (fun h p hp _ => by
      obtain ⟨hpr, hpc, hq, hlen, hrd⟩ := progs_get hp
      match h with
      | 0 =>
        exact hLADW_hart _ M 0 p X Y 2 5 7 10 8 5 9 (by rw [hpr]; rfl) hpc hq (by decide) (by rw [hlen]; decide)
          (by decide) (by rw [hrd 8 (by decide) (by decide)]; rfl) (by rw [hrd 9 (by decide) (by decide)]; rfl)
          (by decide) (by decide) (by decide) (by decide)
      | 1 =>
        exact hRR_hart _ M 1 p 4 Y X 9 8 11 12 true false false (by rw [hpr]; rfl) hpc hq (by decide) (by decide)
          (by decide) (by rw [hrd 9 (by decide) (by decide)]; rfl) (by rw [hrd 8 (by decide) (by decide)]; rfl)
          (by decide) (by decide) (by decide) (by decide)
      | n + 2 =>
        have hl : (progs Weak.Prom.Ref.Lit.mpAmoData).length = 2 := rfl
        rw [List.getElem?_eq_none (by omega)] at hp; cases hp) hrun
  exact amoW_glue himg rfl rfl (by decide) (by decide) (hQ 0) (hQ 1) (fun h hh => by
      obtain ⟨k, rfl⟩ : ∃ k, h = k + 2 := ⟨h - 2, by omega⟩; exact hQ (k + 2))
    (fun m d hpa _ _ => byteAt_lt (by rw [hpa]; decide)) (amo_hba 2 (by decide) (by decide) (by decide))
    hnc hpart hwf

/-- **ROW 28c, MP+amo-ctrl+fence.r.r: FORBIDDEN, in the logic** (plan §5 row 28c, rule 11 from the AMO through
`LCtrl`, M0 (v)). -/
theorem lit_mpAmoCtrl : ∀ (M : List PMsg) (run : PFRun LP Unit),
    validRun litStep (testImg Weak.Prom.Ref.Lit.mpAmoCtrl) () (progs Weak.Prom.Ref.Lit.mpAmoCtrl) M run →
    ¬ (run.obsLoad 1 0 = some 1 ∧ run.obsLoad 1 1 = some 0) := by
  intro M run hrun
  obtain ⟨_, hQ, hnc, hpart, hwf, himg, _⟩ := kitAdeq (π := Proto.triv)
    (fun h => match h with
      | 0 => qAW (X : Int) (Y : Int) 2 8 5 9 6
      | 1 => qRR M (Y : Int) (X : Int) 4 [.DReg 9] [.DReg 8]
      | _ => q0) (fun _ _ => True) trivial
    (fun h => match h with | 0 => trivial | 1 => trivial | _ + 2 => rfl)
    (fun h p hp _ => by
      obtain ⟨hpr, hpc, hq, hlen, hrd⟩ := progs_get hp
      match h with
      | 0 =>
        exact hLACW_hart _ M 0 p X Y 2 1 5 10 8 6 9 (by rw [hpr]; rfl) hpc hq (by decide) (by rw [hlen]; decide)
          (by decide) (by rw [hrd 8 (by decide) (by decide)]; rfl) (by rw [hrd 9 (by decide) (by decide)]; rfl)
          (by decide) (by decide) (by decide) (by decide)
      | 1 =>
        exact hRR_hart _ M 1 p 4 Y X 9 8 11 12 true false false (by rw [hpr]; rfl) hpc hq (by decide) (by decide)
          (by decide) (by rw [hrd 9 (by decide) (by decide)]; rfl) (by rw [hrd 8 (by decide) (by decide)]; rfl)
          (by decide) (by decide) (by decide) (by decide)
      | n + 2 =>
        have hl : (progs Weak.Prom.Ref.Lit.mpAmoCtrl).length = 2 := rfl
        rw [List.getElem?_eq_none (by omega)] at hp; cases hp) hrun
  exact amoW_glue himg rfl rfl (by decide) (by decide) (hQ 0) (hQ 1) (fun h hh => by
      obtain ⟨k, rfl⟩ : ∃ k, h = k + 2 := ⟨h - 2, by omega⟩; exact hQ (k + 2))
    (fun m d hpa _ _ => byteAt_lt (by rw [hpa]; decide)) (amo_hba 2 (by decide) (by decide) (by decide))
    hnc hpart hwf

end Weak.Prom.PF

#print axioms Weak.Prom.PF.lit_mpAmoRlAq
#print axioms Weak.Prom.PF.lit_mpFAmo
#print axioms Weak.Prom.PF.lit_amoStorePart
#print axioms Weak.Prom.PF.lit_mpAmoData
#print axioms Weak.Prom.PF.lit_mpAmoCtrl
