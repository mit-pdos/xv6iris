/-
Weak/Prom: **the litmus harts of the forbidden rows, proved IN THE LOGIC** (stage S2; plan rev 7 §2 "Leaf rules",
§5 rows 8, 13, 21, 22, 24, 25, §8 S2).

Each theorem is ONE HART'S wp proof (`wpPF … (ΨK M Q) s0 …`, V = 0), by the kit's instruction rules (CoreKit.lean)
over the hart's exact state; Q (the trace invariant over the memory entries, plan §2 "Ψ chosen by the proof") records
the hart's ORDER FACT, which comes from a view fact of one leaf rule:
* `hWW_hart`  `st; fence ·w,·w; st` → `qWW` (ts₀ < ts₁): FULFIL `vwOld ≥ ts₀`, FENCE (rule 4) `vwNew ≥ vwOld`, EXT;
* `hWWc_hart` `st a; st a`          → `qWW` (ts₀ < ts₁): COH (rule 1) — `coh a ≥ ts₀` after the first, `< ts₁` at the second;
* `hRR_hart`  `ld; fence r·,r·; ld` → `qRR` (no write to a₁ in `(s₁, s₀]`): LOAD (X4) `vrOld ≥ s₀`, FENCE `vrNew ≥ vrOld`,
  `loadOk` at the pre-view;
* `hRRc_hart` `ld a; ld a`          → `qRR`: coherence floor `coh a ≥ s₀` (rule 2 / load value axiom);
* `hRW_hart`  `ld; fence r·,·w; st` → `qLW` (s₀ < ts): (X4), FENCE `vwNew ≥ vrOld`, EXT;
* `hRWc_hart` `ld a; st a`          → `qLW`: COH;
* `hWR_hart`  `st; fence ·w,r·; ld` → `qWR` (no write to a₁ in `(s₁, ts]`): FULFIL, FENCE `vrNew ≥ vwOld`, `loadOk`;
* `hWRc_hart` `st a; ld a`          → `qWR`: COH floor;
* `hW_hart` / `hLW_hart`  one store (after `li`) → `qS`.
Next to each Q: its WRITER lemma (which entry fulfilled a timestamp) and its OUTCOME lemma (the answers of its
loads), used by the contradictions after A0.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.CoreKitQ

namespace Weak.Prom.PF

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Ref (Instr Test two64 aluOp brEval amoOp sext byteList bytesVal FenceSet)
open PLabel
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode

/-! ## 1. The trace invariants -/

/-- Two plain stores, the first's timestamp below the second's. -/
def qWW (a0 a1 : Int) (d0 d1 : List (BitVec 8)) (as0 vs0 as1 vs1 : List Dsrc) : Trace → Prop :=
  q2 (isSt a0 d0 as0 vs0) (fun e0 e1 => isSt a1 d1 as1 vs1 e1 ∧ tsOf e0 < tsOf e1)

/-- Two plain loads; no write to the second's byte between its byte-0 source and the first's. -/
def qRR (M : List PMsg) (a0 a1 : Int) (n : Nat) (as0 as1 : List Dsrc) : Trace → Prop :=
  q2 (isLd a0 n as0) (fun e0 e1 => isLd a1 n as1 e1 ∧ (noCmo M → ¬ writesIn M a1 (src0 e1) (src0 e0)))

/-- A load, then a store above the load's byte-0 source. -/
def qLW (a0 a1 : Int) (n : Nat) (d1 : List (BitVec 8)) (as0 as1 vs1 : List Dsrc) : Trace → Prop :=
  q2 (isLd a0 n as0) (fun e0 e1 => isSt a1 d1 as1 vs1 e1 ∧ src0 e0 < tsOf e1)

/-- A store, then a load with no write to its byte between its byte-0 source and the store. -/
def qWR (M : List PMsg) (a0 a1 : Int) (n : Nat) (d0 : List (BitVec 8)) (as0 vs0 as1 : List Dsrc) : Trace → Prop :=
  q2 (isSt a0 d0 as0 vs0) (fun e0 e1 => isLd a1 n as1 e1 ∧ (noCmo M → ¬ writesIn M a1 (src0 e1) (tsOf e0)))

/-- A two-store hart's postcondition: both its stores are in `M`, in order. -/
def wwDone (M : List PMsg) (h : Nat) (a0 a1 : Int) (d0 d1 : List (BitVec 8)) : Prop :=
  ∃ t0 t1, 0 < t0 ∧ t0 < t1 ∧ M[t0 - 1]? = some ⟨a0, d0, some h, .plain⟩ ∧ M[t1 - 1]? = some ⟨a1, d1, some h, .plain⟩

/-- A hart's postcondition: its store is in `M`. -/
def wDone (M : List PMsg) (h : Nat) (a : Int) (d : List (BitVec 8)) : Prop :=
  ∃ t, 0 < t ∧ M[t - 1]? = some ⟨a, d, some h, .plain⟩

/-- One plain store. -/
def qS (a0 : Int) (d0 : List (BitVec 8)) (as0 vs0 : List Dsrc) : Trace → Prop := q1 (isSt a0 d0 as0 vs0)

/-! ## 2. Small helpers -/

theorem alg_of {s : LP} {p a n : Nat} (hp : s.rd p = a) (hal : a < two64) (hA : aligned a n = true) :
    aligned ((s.rd p + 0) % two64) n = true := by rw [hp, Nat.add_zero, Nat.mod_eq_of_lt hal]; exact hA

theorem base_of {s : LP} {p a : Nat} (hp : s.rd p = a) (hal : a < two64) :
    (((s.rd p + 0) % two64 : Nat) : Int) = (a : Int) := by rw [hp, Nat.add_zero, Nat.mod_eq_of_lt hal]

theorem tvs_cons {tvs : List (Nat × BitVec 8)} {n : Nat} (hl : tvs.length = n) (hn : 0 < n) :
    ∃ t v r, tvs = (t, v) :: r := by
  cases tvs with
  | nil => simp at hl; omega
  | cons tv r => exact ⟨tv.1, tv.2, r, rfl⟩

section harts

variable {hlc : HasLC} {GF : BundledGFunctors} [GhostVarG GF HSt] [InvGS_gen hlc GF]

/-- The end of a litmus hart, with a pure postcondition the hart knows. -/
theorem wpK_finP {img : Image} {M : List PMsg} {h : Nat} {γ : GName} {π : Proto} {Q : Trace → Prop} {s : LP}
    {ws : PState} {pr : GSet Nat} {ev : Trace} {R : Prop} (hq : s.q = []) (hpc : s.prog.length ≤ s.pc) (hR : R) :
    lh (GF := GF) γ π ⟨litStep, litDone, img, M, h⟩ Q ws pr ev ⊢
      wpK γ π ⟨litStep, litDone, img, M, h⟩ Q s (fun _ => iprop(⌜∃ V, grd π img M V R⌝)) := by
  iintro Hl
  iapply (wpK_end (v := ()) (litAg_lit _ _ _ _ s) hq hpc (by show litDone s = some (); unfold litDone; rw [if_pos ⟨hq, hpc⟩]))
  iframe Hl
  imodintro
  ipureintro
  exact ⟨0, grd_intro hR⟩

/-- The end of a litmus hart (postcondition `True`). -/
theorem wpK_fin {img : Image} {M : List PMsg} {h : Nat} {γ : GName} {π : Proto} {Q : Trace → Prop} {s : LP}
    {ws : PState} {pr : GSet Nat} {ev : Trace} (hq : s.q = []) (hpc : s.prog.length ≤ s.pc) :
    lh (GF := GF) γ π ⟨litStep, litDone, img, M, h⟩ Q ws pr ev ⊢
      wpK γ π ⟨litStep, litDone, img, M, h⟩ Q s (fun _ => iprop(⌜∃ V, grd π img M V True⌝)) :=
  wpK_finP hq hpc trivial

/-- **`st; fence ·w,·w; st`** proves `qWW` (rule 4: the fence orders the stores). -/
theorem hWW_hart (img : Image) (M : List PMsg) (h : Nat) (s0 : LP) (n a0 a1 v0 v1 p0 p1 r0 r1 : Nat) (pr sr : Bool)
    (hprog : s0.prog = [.store n r0 p0 0, .fence ⟨pr, true, false, false, sr, true, false, false⟩, .store n r1 p1 0])
    (hpc : s0.pc = 0) (hq : s0.q = []) (hnz : p0 ≠ 0 ∧ p1 ≠ 0 ∧ r0 ≠ 0 ∧ r1 ≠ 0)
    (hv0 : s0.rd r0 = v0) (hv1 : s0.rd r1 = v1) (ha0 : s0.rd p0 = a0) (ha1 : s0.rd p1 = a1)
    (hal0 : a0 < two64) (hal1 : a1 < two64) (hA0 : aligned a0 n = true) (hA1 : aligned a1 n = true) :
    ⊢@{IProp GF} wpPF Proto.triv ⟨litStep, litDone, img, M, h⟩
      (ΨK M (qWW a0 a1 (toBytes v0 n) (toBytes v1 n) [.DReg p0] [.DReg r0] [.DReg p1] [.DReg r1])) s0
      (fun _ => iprop(⌜∃ V, grd Proto.triv img M V (wwDone M h a0 a1 (toBytes v0 n) (toBytes v1 n))⌝)) := by
  have hw := litW_lit img M h
  have hag := litAg_lit (V := Unit) litDone img M h
  iapply (wpK_start (by trivial))
  iintro %γ %P0 Hl
  iapply (wpK_sw (sz := n) (rs2 := r0) (rs1 := p0) (off := 0) (base := (a0 : Int)) hw (hag s0) hq
    (by rw [hprog, hpc]; rfl) (alg_of ha0 hal0 hA0) (base_of ha0 hal0))
  iframe Hl
  inext
  iintro %tx %_ %hmx %_ %hx
  imodintro
  isplitr
  · ipureintro; exact ⟨0, grd_intro ⟨tx, by omega, by simp only [hv0, srcR_pos hnz.1, srcR_pos hnz.2.2.1]⟩⟩
  isplitr
  · ipureintro; exact grd_intro trivial
  iintro %s1 %hs1 Hl
  obtain ⟨hP1, hc1, hq1⟩ := LPstep_at hs1 hprog (by rw [hpc])
  iapply (wpK_fence (f := ⟨pr, true, false, false, sr, true, false, false⟩) hw (hag s1) hq1 (by rw [hP1, hc1]; rfl))
  iframe Hl
  inext
  iintro %s2 %hs2 Hl
  obtain ⟨hP2, hc2, hq2⟩ := LPstep_at hs2 hP1 (by rw [hc1])
  have e1 : s2.rd r1 = v1 := by rw [LPstep_rd hs2 r1 (.inr rfl), LPstep_rd hs1 r1 (.inr rfl), hv1]
  have e2 : s2.rd p1 = a1 := by rw [LPstep_rd hs2 p1 (.inr rfl), LPstep_rd hs1 p1 (.inr rfl), ha1]
  iapply (wpK_sw (sz := n) (rs2 := r1) (rs1 := p1) (off := 0) (base := (a1 : Int)) hw (hag s2) hq2
    (by rw [hP2, hc2]; rfl) (alg_of e2 hal1 hA1) (base_of e2 hal1))
  iframe Hl
  inext
  iintro %ty %_ %hmy %_ %hy
  have hlt : tx < ty := by
    cases pr <;> cases sr <;> simp [stPreA, stPre] at hy <;> omega
  imodintro
  isplitr
  · ipureintro
    exact ⟨0, grd_intro ⟨⟨tx, by omega, by simp only [hv0, srcR_pos hnz.1, srcR_pos hnz.2.2.1]⟩,
      ⟨ty, by omega, by simp only [e1, srcR_pos hnz.2.1, srcR_pos hnz.2.2.2]⟩, hlt⟩⟩
  isplitr
  · ipureintro; exact grd_intro trivial
  iintro %s3 %hs3 Hl
  obtain ⟨hP3, hc3, hq3⟩ := LPstep_at hs3 hP2 (by rw [hc2])
  iapply (wpK_finP hq3 (by rw [hP3, hc3]; simp) ⟨tx, ty, by omega, hlt, by rw [← hv0]; exact hmx,
    by rw [← e1]; exact hmy⟩)
  iexact Hl

/-- **`st a; st a`** proves `qWW` (rule 1 / COH: same-address stores are ordered). -/
theorem hWWc_hart (img : Image) (M : List PMsg) (h : Nat) (s0 : LP) (n a v0 v1 p r0 r1 : Nat)
    (hprog : s0.prog = [.store n r0 p 0, .store n r1 p 0])
    (hpc : s0.pc = 0) (hq : s0.q = []) (hnz : p ≠ 0 ∧ r0 ≠ 0 ∧ r1 ≠ 0) (hn : 0 < n)
    (hv0 : s0.rd r0 = v0) (hv1 : s0.rd r1 = v1) (ha : s0.rd p = a) (hal : a < two64) (hA : aligned a n = true) :
    ⊢@{IProp GF} wpPF Proto.triv ⟨litStep, litDone, img, M, h⟩
      (ΨK M (qWW a a (toBytes v0 n) (toBytes v1 n) [.DReg p] [.DReg r0] [.DReg p] [.DReg r1])) s0
      (fun _ => iprop(⌜∃ V, grd Proto.triv img M V (wwDone M h a a (toBytes v0 n) (toBytes v1 n))⌝)) := by
  have hw := litW_lit img M h
  have hag := litAg_lit (V := Unit) litDone img M h
  iapply (wpK_start (by trivial))
  iintro %γ %P0 Hl
  iapply (wpK_sw (sz := n) (rs2 := r0) (rs1 := p) (off := 0) (base := (a : Int)) hw (hag s0) hq
    (by rw [hprog, hpc]; rfl) (alg_of ha hal hA) (base_of ha hal))
  iframe Hl
  inext
  iintro %tx %_ %hmx %_ %hx
  imodintro
  isplitr
  · ipureintro; exact ⟨0, grd_intro ⟨tx, by omega, by simp only [hv0, srcR_pos hnz.1, srcR_pos hnz.2.1]⟩⟩
  isplitr
  · ipureintro; exact grd_intro trivial
  iintro %s1 %hs1 Hl
  obtain ⟨hP1, hc1, hq1⟩ := LPstep_at hs1 hprog (by rw [hpc])
  have e1 : s1.rd r1 = v1 := by rw [LPstep_rd hs1 r1 (.inr rfl), hv1]
  have e2 : s1.rd p = a := by rw [LPstep_rd hs1 p (.inr rfl), ha]
  iapply (wpK_sw (sz := n) (rs2 := r1) (rs1 := p) (off := 0) (base := (a : Int)) hw (hag s1) hq1
    (by rw [hP1, hc1]; rfl) (alg_of e2 hal hA) (base_of e2 hal))
  iframe Hl
  inext
  iintro %ty %_ %hmy %hcoh %hy
  have hlt : tx < ty := by
    have h1 := cohBelow_b0 hcoh (by rw [toBytes_length]; exact hn)
    simp only [instrR_coh, acqPost_false'] at h1
    exact Nat.lt_of_le_of_lt (storeRun_coh0 _ _ _ _ _ _ _ (by rw [toBytes_length]; exact hn)) h1
  imodintro
  isplitr
  · ipureintro
    exact ⟨0, grd_intro ⟨⟨tx, by omega, by simp only [hv0, srcR_pos hnz.1, srcR_pos hnz.2.1]⟩,
      ⟨ty, by omega, by simp only [e1, srcR_pos hnz.1, srcR_pos hnz.2.2]⟩, hlt⟩⟩
  isplitr
  · ipureintro; exact grd_intro trivial
  iintro %s2 %hs2 Hl
  obtain ⟨hP2, hc2, hq2⟩ := LPstep_at hs2 hP1 (by rw [hc1])
  iapply (wpK_finP hq2 (by rw [hP2, hc2]; simp) ⟨tx, ty, by omega, hlt, by rw [← hv0]; exact hmx,
    by rw [← e1]; exact hmy⟩)
  iexact Hl

/-- **`ld; fence r·,r·; ld`** proves `qRR` (rule 4: the fence orders the loads). -/
theorem hRR_hart (img : Image) (M : List PMsg) (h : Nat) (s0 : LP) (n a0 a1 p0 p1 d0 d1 : Nat) (sg pw sw : Bool)
    (hprog : s0.prog = [.load n sg d0 p0 0, .fence ⟨true, pw, false, false, true, sw, false, false⟩,
      .load n sg d1 p1 0])
    (hpc : s0.pc = 0) (hq : s0.q = []) (hnz : p0 ≠ 0 ∧ p1 ≠ 0 ∧ p1 ≠ d0) (hd0 : d0 ≠ 0) (hn : 0 < n)
    (ha0 : s0.rd p0 = a0) (ha1 : s0.rd p1 = a1) (hal0 : a0 < two64) (hal1 : a1 < two64)
    (hA0 : aligned a0 n = true) (hA1 : aligned a1 n = true) :
    ⊢@{IProp GF} wpPF Proto.triv ⟨litStep, litDone, img, M, h⟩ (ΨK M (qRR M a0 a1 n [.DReg p0] [.DReg p1])) s0
      (fun _ => iprop(⌜∃ V, grd Proto.triv img M V True⌝)) := by
  have hw := litW_lit img M h
  have hag := litAg_lit (V := Unit) litDone img M h
  iapply (wpK_start (by trivial))
  iintro %γ %P0 Hl
  iapply (wpK_ld (sz := n) (sgn := sg) (rd := d0) (rs1 := p0) (off := 0) (base := (a0 : Int)) hw (hag s0) hq
    (by rw [hprog, hpc]; rfl) (alg_of ha0 hal0 hA0) (base_of ha0 hal0))
  iframe Hl
  inext
  iintro %tvs0 %hl0 %_
  imodintro
  isplitr
  · ipureintro; exact ⟨0, grd_intro ⟨tvs0, by rw [srcR_pos hnz.1], hl0⟩⟩
  iintro %s1 %hs1 Hl
  obtain ⟨hP1, hc1, hq1⟩ := LPstep_at hs1 hprog (by rw [hpc])
  iapply (wpK_fence (f := ⟨true, pw, false, false, true, sw, false, false⟩) hw (hag s1) hq1 (by rw [hP1, hc1]; rfl))
  iframe Hl
  inext
  iintro %s2 %hs2 Hl
  obtain ⟨hP2, hc2, hq2⟩ := LPstep_at hs2 hP1 (by rw [hc1])
  have e2 : s2.rd p1 = a1 := by rw [LPstep_rd hs2 p1 (.inr rfl), LPstep_rd hs1 p1 (.inl hnz.2.2), ha1]
  iapply (wpK_ld (sz := n) (sgn := sg) (rd := d1) (rs1 := p1) (off := 0) (base := (a1 : Int)) hw (hag s2) hq2
    (by rw [hP2, hc2]; rfl) (alg_of e2 hal1 hA1) (base_of e2 hal1))
  iframe Hl
  inext
  iintro %tvs1 %hl1 %hlo1
  have hord : noCmo M → ¬ writesIn M a1 (src0 (LLoad false false (a1 : Int) tvs1 (srcR p1), none))
      (src0 (LLoad false false (a0 : Int) tvs0 (srcR p0), none)) := by
    intro hnc
    obtain ⟨t0, v0, r0, rfl⟩ := tvs_cons hl0 hn
    obtain ⟨t1, v1, r1, rfl⟩ := tvs_cons hl1 hn
    have hw1 := (loadOk_b0nc hnc hlo1).2
    have hb0 := (loadRun_b0 psInit false false (srcsView psInit (srcR p0)) (a0 : Int) t0 v0 r0).2.1
    rw [fwdView_empty rfl] at hb0
    intro hc
    apply hw1
    refine writesIn_mono hc ?_
    show t0 ≤ _
    simp [ldPre, regWL, hnz.1, hnz.2.1, hd0] at hb0 ⊢
    cases pw <;> cases sw <;> (try simp) <;> omega
  imodintro
  isplitr
  · ipureintro
    exact ⟨0, grd_intro ⟨⟨tvs0, by rw [srcR_pos hnz.1], hl0⟩, ⟨tvs1, by rw [srcR_pos hnz.2.1], hl1⟩, hord⟩⟩
  iintro %s3 %hs3 Hl
  obtain ⟨hP3, hc3, hq3⟩ := LPstep_at hs3 hP2 (by rw [hc2])
  iapply (wpK_fin hq3 (by rw [hP3, hc3]; simp))
  iexact Hl

/-- **`ld a; ld a`** proves `qRR` (the coherence floor: rule 2 / the load value axiom). -/
theorem hRRc_hart (img : Image) (M : List PMsg) (h : Nat) (s0 : LP) (n a p d0 d1 : Nat) (sg : Bool)
    (hprog : s0.prog = [.load n sg d0 p 0, .load n sg d1 p 0])
    (hpc : s0.pc = 0) (hq : s0.q = []) (hnz : p ≠ 0 ∧ p ≠ d0) (hd0 : d0 ≠ 0) (hn : 0 < n)
    (ha : s0.rd p = a) (hal : a < two64) (hA : aligned a n = true) :
    ⊢@{IProp GF} wpPF Proto.triv ⟨litStep, litDone, img, M, h⟩ (ΨK M (qRR M a a n [.DReg p] [.DReg p])) s0
      (fun _ => iprop(⌜∃ V, grd Proto.triv img M V True⌝)) := by
  have hw := litW_lit img M h
  have hag := litAg_lit (V := Unit) litDone img M h
  iapply (wpK_start (by trivial))
  iintro %γ %P0 Hl
  iapply (wpK_ld (sz := n) (sgn := sg) (rd := d0) (rs1 := p) (off := 0) (base := (a : Int)) hw (hag s0) hq
    (by rw [hprog, hpc]; rfl) (alg_of ha hal hA) (base_of ha hal))
  iframe Hl
  inext
  iintro %tvs0 %hl0 %_
  imodintro
  isplitr
  · ipureintro; exact ⟨0, grd_intro ⟨tvs0, by rw [srcR_pos hnz.1], hl0⟩⟩
  iintro %s1 %hs1 Hl
  obtain ⟨hP1, hc1, hq1⟩ := LPstep_at hs1 hprog (by rw [hpc])
  have e1 : s1.rd p = a := by rw [LPstep_rd hs1 p (.inl hnz.2), ha]
  iapply (wpK_ld (sz := n) (sgn := sg) (rd := d1) (rs1 := p) (off := 0) (base := (a : Int)) hw (hag s1) hq1
    (by rw [hP1, hc1]; rfl) (alg_of e1 hal hA) (base_of e1 hal))
  iframe Hl
  inext
  iintro %tvs1 %hl1 %hlo1
  have hord : noCmo M → ¬ writesIn M a (src0 (LLoad false false (a : Int) tvs1 (srcR p), none))
      (src0 (LLoad false false (a : Int) tvs0 (srcR p), none)) := by
    intro hnc
    obtain ⟨t0, v0, r0, rfl⟩ := tvs_cons hl0 hn
    obtain ⟨t1, v1, r1, rfl⟩ := tvs_cons hl1 hn
    have hw1 := (loadOk_b0nc hnc hlo1).2
    have hb0 := loadRun_coh0 psInit false false (srcsView psInit (srcR p)) (a : Int) t0 v0 r0
    intro hc
    apply hw1
    refine writesIn_mono hc ?_
    show t0 ≤ _
    simp [regWL, hd0] at hb0 ⊢
    omega
  imodintro
  isplitr
  · ipureintro
    exact ⟨0, grd_intro ⟨⟨tvs0, by rw [srcR_pos hnz.1], hl0⟩, ⟨tvs1, by rw [srcR_pos hnz.1], hl1⟩, hord⟩⟩
  iintro %s2 %hs2 Hl
  obtain ⟨hP2, hc2, hq2⟩ := LPstep_at hs2 hP1 (by rw [hc1])
  iapply (wpK_fin hq2 (by rw [hP2, hc2]; simp))
  iexact Hl

/-- **`ld; fence r·,·w; st`** proves `qLW` (rule 4: the fence orders the load before the store). -/
theorem hRW_hart (img : Image) (M : List PMsg) (h : Nat) (s0 : LP) (n a0 a1 v p0 p1 d r : Nat) (sg pw sr : Bool)
    (hprog : s0.prog = [.load n sg d p0 0, .fence ⟨true, pw, false, false, sr, true, false, false⟩, .store n r p1 0])
    (hpc : s0.pc = 0) (hq : s0.q = []) (hnz : p0 ≠ 0 ∧ p1 ≠ 0 ∧ r ≠ 0 ∧ p1 ≠ d ∧ r ≠ d) (hd0 : d ≠ 0) (hn : 0 < n)
    (ha0 : s0.rd p0 = a0) (ha1 : s0.rd p1 = a1) (hv : s0.rd r = v) (hal0 : a0 < two64) (hal1 : a1 < two64)
    (hA0 : aligned a0 n = true) (hA1 : aligned a1 n = true) :
    ⊢@{IProp GF} wpPF Proto.triv ⟨litStep, litDone, img, M, h⟩
      (ΨK M (qLW a0 a1 n (toBytes v n) [.DReg p0] [.DReg p1] [.DReg r])) s0
      (fun _ => iprop(⌜∃ V, grd Proto.triv img M V True⌝)) := by
  have hw := litW_lit img M h
  have hag := litAg_lit (V := Unit) litDone img M h
  iapply (wpK_start (by trivial))
  iintro %γ %P0 Hl
  iapply (wpK_ld (sz := n) (sgn := sg) (rd := d) (rs1 := p0) (off := 0) (base := (a0 : Int)) hw (hag s0) hq
    (by rw [hprog, hpc]; rfl) (alg_of ha0 hal0 hA0) (base_of ha0 hal0))
  iframe Hl
  inext
  iintro %tvs0 %hl0 %_
  imodintro
  isplitr
  · ipureintro; exact ⟨0, grd_intro ⟨tvs0, by rw [srcR_pos hnz.1], hl0⟩⟩
  iintro %s1 %hs1 Hl
  obtain ⟨hP1, hc1, hq1⟩ := LPstep_at hs1 hprog (by rw [hpc])
  iapply (wpK_fence (f := ⟨true, pw, false, false, sr, true, false, false⟩) hw (hag s1) hq1 (by rw [hP1, hc1]; rfl))
  iframe Hl
  inext
  iintro %s2 %hs2 Hl
  obtain ⟨hP2, hc2, hq2⟩ := LPstep_at hs2 hP1 (by rw [hc1])
  have e1 : s2.rd p1 = a1 := by rw [LPstep_rd hs2 p1 (.inr rfl), LPstep_rd hs1 p1 (.inl hnz.2.2.2.1), ha1]
  have e2 : s2.rd r = v := by rw [LPstep_rd hs2 r (.inr rfl), LPstep_rd hs1 r (.inl hnz.2.2.2.2), hv]
  iapply (wpK_sw (sz := n) (rs2 := r) (rs1 := p1) (off := 0) (base := (a1 : Int)) hw (hag s2) hq2
    (by rw [hP2, hc2]; rfl) (alg_of e1 hal1 hA1) (base_of e1 hal1))
  iframe Hl
  inext
  iintro %ts %_ %_ %_ %hext
  have hlt : src0 (LLoad false false (a0 : Int) tvs0 (srcR p0), none) < ts := by
    obtain ⟨t0, v0, r0, rfl⟩ := tvs_cons hl0 hn
    have hb0 := (loadRun_b0 psInit false false (srcsView psInit (srcR p0)) (a0 : Int) t0 v0 r0).2.1
    rw [fwdView_empty rfl] at hb0
    show t0 < ts
    simp [ldPre, stPreA, stPre, regWL, hnz.1, hnz.2.1, hnz.2.2.1, hd0] at hb0 hext
    cases pw <;> cases sr <;> (try simp at hext) <;> omega
  imodintro
  isplitr
  · ipureintro
    exact ⟨0, grd_intro ⟨⟨tvs0, by rw [srcR_pos hnz.1], hl0⟩,
      ⟨ts, by omega, by simp only [e2, srcR_pos hnz.2.1, srcR_pos hnz.2.2.1]⟩, hlt⟩⟩
  isplitr
  · ipureintro; exact grd_intro trivial
  iintro %s3 %hs3 Hl
  obtain ⟨hP3, hc3, hq3⟩ := LPstep_at hs3 hP2 (by rw [hc2])
  iapply (wpK_fin hq3 (by rw [hP3, hc3]; simp))
  iexact Hl

/-- **`ld a; st a`** proves `qLW` (COH: the store is above every source the load read at its byte). -/
theorem hRWc_hart (img : Image) (M : List PMsg) (h : Nat) (s0 : LP) (n a v p d r : Nat) (sg : Bool)
    (hprog : s0.prog = [.load n sg d p 0, .store n r p 0])
    (hpc : s0.pc = 0) (hq : s0.q = []) (hnz : p ≠ 0 ∧ r ≠ 0 ∧ p ≠ d ∧ r ≠ d) (hd0 : d ≠ 0) (hn : 0 < n)
    (ha : s0.rd p = a) (hv : s0.rd r = v) (hal : a < two64) (hA : aligned a n = true) :
    ⊢@{IProp GF} wpPF Proto.triv ⟨litStep, litDone, img, M, h⟩
      (ΨK M (qLW a a n (toBytes v n) [.DReg p] [.DReg p] [.DReg r])) s0
      (fun _ => iprop(⌜∃ V, grd Proto.triv img M V (wDone M h a (toBytes v n))⌝)) := by
  have hw := litW_lit img M h
  have hag := litAg_lit (V := Unit) litDone img M h
  iapply (wpK_start (by trivial))
  iintro %γ %P0 Hl
  iapply (wpK_ld (sz := n) (sgn := sg) (rd := d) (rs1 := p) (off := 0) (base := (a : Int)) hw (hag s0) hq
    (by rw [hprog, hpc]; rfl) (alg_of ha hal hA) (base_of ha hal))
  iframe Hl
  inext
  iintro %tvs0 %hl0 %_
  imodintro
  isplitr
  · ipureintro; exact ⟨0, grd_intro ⟨tvs0, by rw [srcR_pos hnz.1], hl0⟩⟩
  iintro %s1 %hs1 Hl
  obtain ⟨hP1, hc1, hq1⟩ := LPstep_at hs1 hprog (by rw [hpc])
  have e1 : s1.rd p = a := by rw [LPstep_rd hs1 p (.inl hnz.2.2.1), ha]
  have e2 : s1.rd r = v := by rw [LPstep_rd hs1 r (.inl hnz.2.2.2), hv]
  iapply (wpK_sw (sz := n) (rs2 := r) (rs1 := p) (off := 0) (base := (a : Int)) hw (hag s1) hq1
    (by rw [hP1, hc1]; rfl) (alg_of e1 hal hA) (base_of e1 hal))
  iframe Hl
  inext
  iintro %ts %_ %hmt %hcoh %hext
  have hlt : src0 (LLoad false false (a : Int) tvs0 (srcR p), none) < ts := by
    obtain ⟨t0, v0, r0, rfl⟩ := tvs_cons hl0 hn
    have hb0 := loadRun_coh0 psInit false false (srcsView psInit (srcR p)) (a : Int) t0 v0 r0
    have h1 := cohBelow_b0 hcoh (by rw [toBytes_length]; exact hn)
    show t0 < ts
    simp [regWL, hd0] at hb0 h1
    omega
  imodintro
  isplitr
  · ipureintro
    exact ⟨0, grd_intro ⟨⟨tvs0, by rw [srcR_pos hnz.1], hl0⟩,
      ⟨ts, by omega, by simp only [e2, srcR_pos hnz.1, srcR_pos hnz.2.1]⟩, hlt⟩⟩
  isplitr
  · ipureintro; exact grd_intro trivial
  iintro %s2 %hs2 Hl
  obtain ⟨hP2, hc2, hq2⟩ := LPstep_at hs2 hP1 (by rw [hc1])
  iapply (wpK_finP hq2 (by rw [hP2, hc2]; simp) ⟨ts, by omega, by rw [← e2]; exact hmt⟩)
  iexact Hl

/-- **`st; fence ·w,r·; ld`** proves `qWR` (rule 4: the fence orders the store before the load). -/
theorem hWR_hart (img : Image) (M : List PMsg) (h : Nat) (s0 : LP) (n a0 a1 v p0 p1 d r : Nat) (sg pr sw : Bool)
    (hprog : s0.prog = [.store n r p0 0, .fence ⟨pr, true, false, false, true, sw, false, false⟩, .load n sg d p1 0])
    (hpc : s0.pc = 0) (hq : s0.q = []) (hnz : p0 ≠ 0 ∧ p1 ≠ 0 ∧ r ≠ 0) (hn : 0 < n)
    (ha0 : s0.rd p0 = a0) (ha1 : s0.rd p1 = a1) (hv : s0.rd r = v) (hal0 : a0 < two64) (hal1 : a1 < two64)
    (hA0 : aligned a0 n = true) (hA1 : aligned a1 n = true) :
    ⊢@{IProp GF} wpPF Proto.triv ⟨litStep, litDone, img, M, h⟩
      (ΨK M (qWR M a0 a1 n (toBytes v n) [.DReg p0] [.DReg r] [.DReg p1])) s0
      (fun _ => iprop(⌜∃ V, grd Proto.triv img M V True⌝)) := by
  have hw := litW_lit img M h
  have hag := litAg_lit (V := Unit) litDone img M h
  iapply (wpK_start (by trivial))
  iintro %γ %P0 Hl
  iapply (wpK_sw (sz := n) (rs2 := r) (rs1 := p0) (off := 0) (base := (a0 : Int)) hw (hag s0) hq
    (by rw [hprog, hpc]; rfl) (alg_of ha0 hal0 hA0) (base_of ha0 hal0))
  iframe Hl
  inext
  iintro %tx %_ %_ %_ %hx
  imodintro
  isplitr
  · ipureintro; exact ⟨0, grd_intro ⟨tx, by omega, by simp only [hv, srcR_pos hnz.1, srcR_pos hnz.2.2]⟩⟩
  isplitr
  · ipureintro; exact grd_intro trivial
  iintro %s1 %hs1 Hl
  obtain ⟨hP1, hc1, hq1⟩ := LPstep_at hs1 hprog (by rw [hpc])
  iapply (wpK_fence (f := ⟨pr, true, false, false, true, sw, false, false⟩) hw (hag s1) hq1 (by rw [hP1, hc1]; rfl))
  iframe Hl
  inext
  iintro %s2 %hs2 Hl
  obtain ⟨hP2, hc2, hq2⟩ := LPstep_at hs2 hP1 (by rw [hc1])
  have e1 : s2.rd p1 = a1 := by rw [LPstep_rd hs2 p1 (.inr rfl), LPstep_rd hs1 p1 (.inr rfl), ha1]
  iapply (wpK_ld (sz := n) (sgn := sg) (rd := d) (rs1 := p1) (off := 0) (base := (a1 : Int)) hw (hag s2) hq2
    (by rw [hP2, hc2]; rfl) (alg_of e1 hal1 hA1) (base_of e1 hal1))
  iframe Hl
  inext
  iintro %tvs1 %hl1 %hlo1
  have hord : noCmo M → ¬ writesIn M a1 (src0 (LLoad false false (a1 : Int) tvs1 (srcR p1), none))
      (tsOf (LStore false false (a0 : Int) (toBytes (s0.rd r) n) (srcR p0) (srcR r), some tx)) := by
    intro hnc
    obtain ⟨t1, v1, r1, rfl⟩ := tvs_cons hl1 hn
    have hw1 := (loadOk_b0nc hnc hlo1).2
    intro hc
    apply hw1
    refine writesIn_mono hc ?_
    show tx ≤ _
    simp [ldPre]
    cases pr <;> cases sw <;> (try simp) <;> omega
  imodintro
  isplitr
  · ipureintro
    exact ⟨0, grd_intro ⟨⟨tx, by omega, by simp only [hv, srcR_pos hnz.1, srcR_pos hnz.2.2]⟩,
      ⟨tvs1, by rw [srcR_pos hnz.2.1], hl1⟩, hord⟩⟩
  iintro %s3 %hs3 Hl
  obtain ⟨hP3, hc3, hq3⟩ := LPstep_at hs3 hP2 (by rw [hc2])
  iapply (wpK_fin hq3 (by rw [hP3, hc3]; simp))
  iexact Hl

/-- **`st a; ld a`** proves `qWR` (the coherence floor after the store). -/
theorem hWRc_hart (img : Image) (M : List PMsg) (h : Nat) (s0 : LP) (n a v p d r : Nat) (sg : Bool)
    (hprog : s0.prog = [.store n r p 0, .load n sg d p 0])
    (hpc : s0.pc = 0) (hq : s0.q = []) (hnz : p ≠ 0 ∧ r ≠ 0) (hn : 0 < n)
    (ha : s0.rd p = a) (hv : s0.rd r = v) (hal : a < two64) (hA : aligned a n = true) :
    ⊢@{IProp GF} wpPF Proto.triv ⟨litStep, litDone, img, M, h⟩
      (ΨK M (qWR M a a n (toBytes v n) [.DReg p] [.DReg r] [.DReg p])) s0
      (fun _ => iprop(⌜∃ V, grd Proto.triv img M V True⌝)) := by
  have hw := litW_lit img M h
  have hag := litAg_lit (V := Unit) litDone img M h
  iapply (wpK_start (by trivial))
  iintro %γ %P0 Hl
  iapply (wpK_sw (sz := n) (rs2 := r) (rs1 := p) (off := 0) (base := (a : Int)) hw (hag s0) hq
    (by rw [hprog, hpc]; rfl) (alg_of ha hal hA) (base_of ha hal))
  iframe Hl
  inext
  iintro %tx %_ %_ %_ %hx
  imodintro
  isplitr
  · ipureintro; exact ⟨0, grd_intro ⟨tx, by omega, by simp only [hv, srcR_pos hnz.1, srcR_pos hnz.2]⟩⟩
  isplitr
  · ipureintro; exact grd_intro trivial
  iintro %s1 %hs1 Hl
  obtain ⟨hP1, hc1, hq1⟩ := LPstep_at hs1 hprog (by rw [hpc])
  have e1 : s1.rd p = a := by rw [LPstep_rd hs1 p (.inr rfl), ha]
  iapply (wpK_ld (sz := n) (sgn := sg) (rd := d) (rs1 := p) (off := 0) (base := (a : Int)) hw (hag s1) hq1
    (by rw [hP1, hc1]; rfl) (alg_of e1 hal hA) (base_of e1 hal))
  iframe Hl
  inext
  iintro %tvs1 %hl1 %hlo1
  have hord : noCmo M → ¬ writesIn M a (src0 (LLoad false false (a : Int) tvs1 (srcR p), none))
      (tsOf (LStore false false (a : Int) (toBytes (s0.rd r) n) (srcR p) (srcR r), some tx)) := by
    intro hnc
    obtain ⟨t1, v1, r1, rfl⟩ := tvs_cons hl1 hn
    have hw1 := (loadOk_b0nc hnc hlo1).2
    have hc0 := storeRun_coh0 psInit false (srcsView psInit (srcR p)) (max (srcsView psInit (srcR p))
      (srcsView psInit (srcR r))) (a : Int) (toBytes (s0.rd r) n).length tx (by rw [toBytes_length]; exact hn)
    intro hc
    apply hw1
    refine writesIn_mono hc ?_
    show tx ≤ _
    simp at hc0 ⊢
    omega
  imodintro
  isplitr
  · ipureintro
    exact ⟨0, grd_intro ⟨⟨tx, by omega, by simp only [hv, srcR_pos hnz.1, srcR_pos hnz.2]⟩,
      ⟨tvs1, by rw [srcR_pos hnz.1], hl1⟩, hord⟩⟩
  iintro %s2 %hs2 Hl
  obtain ⟨hP2, hc2, hq2⟩ := LPstep_at hs2 hP1 (by rw [hc1])
  iapply (wpK_fin hq2 (by rw [hP2, hc2]; simp))
  iexact Hl

/-- **One store** `st r,(p)` proves `qS`. -/
theorem hW_hart (img : Image) (M : List PMsg) (h : Nat) (s0 : LP) (n a v p r : Nat)
    (hprog : s0.prog = [.store n r p 0]) (hpc : s0.pc = 0) (hq : s0.q = []) (hnz : p ≠ 0 ∧ r ≠ 0)
    (ha : s0.rd p = a) (hv : s0.rd r = v) (hal : a < two64) (hA : aligned a n = true) :
    ⊢@{IProp GF} wpPF Proto.triv ⟨litStep, litDone, img, M, h⟩ (ΨK M (qS a (toBytes v n) [.DReg p] [.DReg r])) s0
      (fun _ => iprop(⌜∃ V, grd Proto.triv img M V True⌝)) := by
  have hw := litW_lit img M h
  have hag := litAg_lit (V := Unit) litDone img M h
  iapply (wpK_start (by trivial))
  iintro %γ %P0 Hl
  iapply (wpK_sw (sz := n) (rs2 := r) (rs1 := p) (off := 0) (base := (a : Int)) hw (hag s0) hq
    (by rw [hprog, hpc]; rfl) (alg_of ha hal hA) (base_of ha hal))
  iframe Hl
  inext
  iintro %tx %_ %_ %_ %hx
  imodintro
  isplitr
  · ipureintro; exact ⟨0, grd_intro ⟨tx, by omega, by simp only [hv, srcR_pos hnz.1, srcR_pos hnz.2]⟩⟩
  isplitr
  · ipureintro; exact grd_intro trivial
  iintro %s1 %hs1 Hl
  obtain ⟨hP1, hc1, hq1⟩ := LPstep_at hs1 hprog (by rw [hpc])
  iapply (wpK_fin hq1 (by rw [hP1, hc1]; simp))
  iexact Hl

/-- **`li r,v; st r,(p)`** proves `qS`. -/
theorem hLW_hart (img : Image) (M : List PMsg) (h : Nat) (s0 : LP) (n a v p r : Nat)
    (hprog : s0.prog = [.alui .add r 0 v, .store n r p 0]) (hpc : s0.pc = 0) (hq : s0.q = [])
    (hnz : p ≠ 0 ∧ r ≠ 0 ∧ p ≠ r) (hlen : r < s0.regs.length) (hvl : v < two64)
    (ha : s0.rd p = a) (hal : a < two64) (hA : aligned a n = true) :
    ⊢@{IProp GF} wpPF Proto.triv ⟨litStep, litDone, img, M, h⟩ (ΨK M (qS a (toBytes v n) [.DReg p] [.DReg r])) s0
      (fun _ => iprop(⌜∃ V, grd Proto.triv img M V True⌝)) := by
  have hw := litW_lit img M h
  have hag := litAg_lit (V := Unit) litDone img M h
  iapply (wpK_start (by trivial))
  iintro %γ %P0 Hl
  iapply (wpK_alui hw (hag s0) hq (by rw [hprog, hpc]; rfl) hnz.2.1)
  iframe Hl
  inext
  iintro %s1 %hs1 Hl
  obtain ⟨hP1, hc1, hq1⟩ := LPstep_at hs1 hprog (by rw [hpc])
  have e1 : s1.rd p = a := by rw [LPstep_rd hs1 p (.inl hnz.2.2), ha]
  have e2 : s1.rd r = v := by
    rw [LPstep_rd_eq hs1 hnz.2.1 hlen]
    simp [LP.rd, aluOp, Nat.mod_eq_of_lt hvl]
  iapply (wpK_sw (sz := n) (rs2 := r) (rs1 := p) (off := 0) (base := (a : Int)) hw (hag s1) hq1
    (by rw [hP1, hc1]; rfl) (alg_of e1 hal hA) (base_of e1 hal))
  iframe Hl
  inext
  iintro %tx %_ %_ %_ %hx
  imodintro
  isplitr
  · ipureintro; exact ⟨0, grd_intro ⟨tx, by omega, by simp only [e2, srcR_pos hnz.1, srcR_pos hnz.2.1]⟩⟩
  isplitr
  · ipureintro; exact grd_intro trivial
  iintro %s2 %hs2 Hl
  obtain ⟨hP2, hc2, hq2⟩ := LPstep_at hs2 hP1 (by rw [hc1])
  iapply (wpK_fin hq2 (by rw [hP2, hc2]; simp))
  iexact Hl

end harts

/-! ## 3. Writers and outcomes of the trace invariants -/

section contra

/-- Two plain stores: a timestamped entry is the first store, or the second with the first below it. -/
theorem qWW_writer {a0 a1 : Int} {d0 d1 : List (BitVec 8)} {as0 vs0 as1 vs1 : List Dsrc} {ev : Trace} {e : PEv}
    {t : Nat} (hQ : qWW a0 a1 d0 d1 as0 vs0 as1 vs1 ev) (he : e ∈ ev) (ht : e.2 = some t) :
    e = (LStore false false a0 d0 as0 vs0, some t) ∨
      (e = (LStore false false a1 d1 as1 vs1, some t) ∧
        ∃ t0, 0 < t0 ∧ (LStore false false a0 d0 as0 vs0, some t0) ∈ ev ∧ t0 < t) := by
  rcases q2_cases hQ with rfl | ⟨e0, rfl, ⟨t0, _, rfl⟩⟩ | ⟨e0, e1, rfl, ⟨t0, h0, rfl⟩, ⟨t1, _, rfl⟩, hlt⟩
  · cases he
  · rw [List.mem_singleton] at he; subst he; cases ht; exact .inl rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · cases ht; exact .inl rfl
    · cases ht; exact .inr ⟨rfl, t0, h0, by simp, hlt⟩

/-- A reader's memory entries carry no timestamp. -/
theorem qRR_nots {M : List PMsg} {a0 a1 : Int} {n : Nat} {as0 as1 : List Dsrc} {ev : Trace} {e : PEv}
    (hQ : qRR M a0 a1 n as0 as1 ev) (he : e ∈ ev) : e.2 = none := by
  rcases q2_cases hQ with rfl | ⟨e0, rfl, ⟨_, rfl, _⟩⟩ | ⟨e0, e1, rfl, ⟨_, rfl, _⟩, ⟨_, rfl, _⟩, _⟩
  · cases he
  · rw [List.mem_singleton] at he; subst he; rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl <;> rfl

/-- The reader's two answers (byte 0), from its trace invariant and the outcome. -/
theorem qRR_out {P D : Type} {run : PFRun P D} {M : List PMsg} {h : Nat} {a0 a1 : Int} {n : Nat} {as0 as1 : List Dsrc}
    {v0 v1 : Nat} (hwf : run.traceWf M) (hn : 0 < n) (hQ : qRR M a0 a1 n as0 as1 (memEv (run.trace h)))
    (ho0 : run.obsLoad h 0 = some v0) (ho1 : run.obsLoad h 1 = some v1) :
    ∃ s0 s1 b0 b1, memByte run.cfg.pcImg M s0 a0 = some b0 ∧ b0.toNat = v0 % 256 ∧
      memByte run.cfg.pcImg M s1 a1 = some b1 ∧ b1.toNat = v1 % 256 ∧ (noCmo M → ¬ writesIn M a1 s1 s0) := by
  rw [obsLoad_memEv] at ho0 ho1
  rcases q2_cases hQ with hev | ⟨e0, hev, hP0⟩ | ⟨e0, e1, hev, hP0, hP1, hord⟩
  · rw [hev] at ho0; simp [loadsOf] at ho0
  · obtain ⟨tvs0, rfl, _⟩ := hP0
    rw [hev] at ho1; simp [loadsOf, loadLikeTvs] at ho1
  · obtain ⟨t0, b0, r0, rfl, _⟩ := isLd_cons hP0 hn
    obtain ⟨t1, b1, r1, rfl, _⟩ := isLd_cons hP1 hn
    have hm0 : (LLoad false false a0 ((t0, b0) :: r0) as0, (none : Option Nat)) ∈ memEv (run.trace h) := by
      rw [hev]; simp
    have hm1 : (LLoad false false a1 ((t1, b1) :: r1) as1, (none : Option Nat)) ∈ memEv (run.trace h) := by
      rw [hev]; simp
    rw [hev] at ho0 ho1
    simp only [loadsOf, List.filterMap_cons, loadLikeTvs, List.filterMap_nil, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.map_some, Option.some.injEq] at ho0 ho1
    exact ⟨t0, t1, b0, b1, kit_read0 hwf hm0 rfl, obsOf_b0 ho0, kit_read0 hwf hm1 rfl, obsOf_b0 ho1, hord⟩


/-- A load-then-store hart's timestamped entry is its store, above the load's byte-0 source. -/
theorem qLW_writer {a0 a1 : Int} {n : Nat} {d1 : List (BitVec 8)} {as0 as1 vs1 : List Dsrc} {ev : Trace} {e : PEv}
    {t : Nat} (hQ : qLW a0 a1 n d1 as0 as1 vs1 ev) (he : e ∈ ev) (ht : e.2 = some t) :
    e = (LStore false false a1 d1 as1 vs1, some t) ∧ ∃ e0 ∈ ev, isLd a0 n as0 e0 ∧ src0 e0 < t := by
  rcases q2_cases hQ with rfl | ⟨e0, rfl, ⟨_, rfl, _⟩⟩ | ⟨e0, e1, rfl, hP0, ⟨t1, _, rfl⟩, hlt⟩
  · cases he
  · rw [List.mem_singleton] at he; subst he; cases ht
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · obtain ⟨_, rfl, _⟩ := hP0; cases ht
    · cases ht; exact ⟨rfl, e0, by simp, hP0, hlt⟩

/-- A load-then-store hart's load answer (byte 0), and the store above its source. -/
theorem qLW_out {P D : Type} {run : PFRun P D} {M : List PMsg} {h : Nat} {a0 a1 : Int} {n : Nat}
    {d1 : List (BitVec 8)} {as0 as1 vs1 : List Dsrc} {v0 : Nat} (hwf : run.traceWf M) (hn : 0 < n)
    (hQ : qLW a0 a1 n d1 as0 as1 vs1 (memEv (run.trace h))) (ho0 : run.obsLoad h 0 = some v0) :
    ∃ s0 b0, memByte run.cfg.pcImg M s0 a0 = some b0 ∧ b0.toNat = v0 % 256 ∧
      ∀ t, (LStore false false a1 d1 as1 vs1, some t) ∈ memEv (run.trace h) → s0 < t := by
  rw [obsLoad_memEv] at ho0
  have hQ' := hQ
  rcases q2_cases hQ with hev | ⟨e0, hev, hP0⟩ | ⟨e0, e1, hev, hP0, hP1, hord⟩
  · rw [hev] at ho0; simp [loadsOf] at ho0
  · obtain ⟨t0, b0, r0, rfl, _⟩ := isLd_cons hP0 hn
    have hm0 : (LLoad false false a0 ((t0, b0) :: r0) as0, (none : Option Nat)) ∈ memEv (run.trace h) := by
      rw [hev]; simp
    rw [hev] at ho0
    simp only [loadsOf, List.filterMap_cons, loadLikeTvs, List.filterMap_nil, List.getElem?_cons_zero,
      Option.map_some, Option.some.injEq] at ho0
    refine ⟨t0, b0, kit_read0 hwf hm0 rfl, obsOf_b0 ho0, fun t ht => ?_⟩
    rw [hev, List.mem_singleton] at ht; cases ht
  · obtain ⟨t0, b0, r0, rfl, _⟩ := isLd_cons hP0 hn
    obtain ⟨t1, _, rfl⟩ := hP1
    have hm0 : (LLoad false false a0 ((t0, b0) :: r0) as0, (none : Option Nat)) ∈ memEv (run.trace h) := by
      rw [hev]; simp
    rw [hev] at ho0
    simp only [loadsOf, List.filterMap_cons, loadLikeTvs, List.filterMap_nil, List.getElem?_cons_zero,
      Option.map_some, Option.some.injEq] at ho0
    refine ⟨t0, b0, kit_read0 hwf hm0 rfl, obsOf_b0 ho0, fun t ht => ?_⟩
    rw [hev] at ht
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at ht
    rcases ht with ⟨h1, _⟩ | ⟨_, h2⟩
    · cases h1
    · cases h2; exact hord

/-- A store-then-load hart's timestamped entry is its store. -/
theorem qWR_writer {M : List PMsg} {a0 a1 : Int} {n : Nat} {d0 : List (BitVec 8)} {as0 vs0 as1 : List Dsrc}
    {ev : Trace} {e : PEv} {t : Nat} (hQ : qWR M a0 a1 n d0 as0 vs0 as1 ev) (he : e ∈ ev) (ht : e.2 = some t) :
    e = (LStore false false a0 d0 as0 vs0, some t) := by
  rcases q2_cases hQ with rfl | ⟨e0, rfl, ⟨t0, _, rfl⟩⟩ | ⟨e0, e1, rfl, ⟨t0, _, rfl⟩, ⟨_, rfl, _⟩, _⟩
  · cases he
  · rw [List.mem_singleton] at he; subst he; cases ht; rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · cases ht; rfl
    · cases ht

/-- A store-then-load hart's load answer (byte 0), with its store and the coherence/fence fact. -/
theorem qWR_out {P D : Type} {run : PFRun P D} {M : List PMsg} {h : Nat} {a0 a1 : Int} {n : Nat}
    {d0 : List (BitVec 8)} {as0 vs0 as1 : List Dsrc} {v1 : Nat} (hwf : run.traceWf M) (hn : 0 < n)
    (hQ : qWR M a0 a1 n d0 as0 vs0 as1 (memEv (run.trace h))) (ho : run.obsLoad h 0 = some v1) :
    ∃ s1 b1 t0, memByte run.cfg.pcImg M s1 a1 = some b1 ∧ b1.toNat = v1 % 256 ∧ 0 < t0 ∧
      (LStore false false a0 d0 as0 vs0, some t0) ∈ memEv (run.trace h) ∧ (noCmo M → ¬ writesIn M a1 s1 t0) := by
  rw [obsLoad_memEv] at ho
  rcases q2_cases hQ with hev | ⟨e0, hev, ⟨t0, _, rfl⟩⟩ | ⟨e0, e1, hev, ⟨t0, ht0, rfl⟩, hP1, hord⟩
  · rw [hev] at ho; simp [loadsOf] at ho
  · rw [hev] at ho; simp [loadsOf, loadLikeTvs] at ho
  · obtain ⟨t1, b1, r1, rfl, _⟩ := isLd_cons hP1 hn
    have hm1 : (LLoad false false a1 ((t1, b1) :: r1) as1, (none : Option Nat)) ∈ memEv (run.trace h) := by
      rw [hev]; simp
    rw [hev] at ho
    simp only [loadsOf, List.filterMap_cons, loadLikeTvs, List.filterMap_nil, List.getElem?_cons_zero,
      Option.map_some, Option.some.injEq] at ho
    exact ⟨t1, b1, t0, kit_read0 hwf hm1 rfl, obsOf_b0 ho, ht0, by rw [hev]; simp, hord⟩

/-- A one-store hart's timestamped entry is its store. -/
theorem qS_writer {a0 : Int} {d0 : List (BitVec 8)} {as0 vs0 : List Dsrc} {ev : Trace} {e : PEv} {t : Nat}
    (hQ : qS a0 d0 as0 vs0 ev) (he : e ∈ ev) (ht : e.2 = some t) : e = (LStore false false a0 d0 as0 vs0, some t) := by
  rcases q1_cases hQ with rfl | ⟨e0, rfl, ⟨t0, _, rfl⟩⟩
  · cases he
  · rw [List.mem_singleton] at he; subst he; cases ht; rfl

/-- A hart with the empty memory trace fulfils nothing. -/
theorem q0_writer {ev : Trace} {e : PEv} (hQ : q0 ev) (he : e ∈ ev) : False := by
  rw [show ev = [] from hQ] at he; cases he

/-- The message a store entry wrote (A0 (v)), with byte facts by `decide`. -/
theorem st_msg {P D : Type} {run : PFRun P D} {M : List PMsg} (hwf : run.traceWf M) {h : Nat} {a : Int}
    {d : List (BitVec 8)} {as0 vs0 : List Dsrc} {t : Nat}
    (he : (LStore false false a d as0 vs0, some t) ∈ memEv (run.trace h)) :
    ∃ m, M[t - 1]? = some m ∧ m.pa = a ∧ m.data = d := kit_msg hwf he rfl rfl

/-- THE WRITER OF A MESSAGE among the harts `< n` (the others have no memory entry). -/
theorem writer_cases {P D : Type} {run : PFRun P D} {M : List PMsg}
    (hpart : ∀ t, 1 ≤ t → t ≤ M.length → exU (fun h => t ∈ run.fulfils h ∧ tidAt M t = some h))
    (hwf : run.traceWf M) (n : Nat) (hout : ∀ h, n ≤ h → memEv (run.trace h) = []) {k : Nat} {m : PMsg}
    (hm : M[k]? = some m) :
    ∃ h, h < n ∧ ∃ e ∈ memEv (run.trace h), e.2 = some (k + 1) ∧ labelWrite e.1 = some (m.pa, m.data) := by
  obtain ⟨h, e, he, het, hlw⟩ := kit_writer hpart hwf hm
  by_cases hh : h < n
  · exact ⟨h, hh, e, he, het, hlw⟩
  · rw [hout h (by omega)] at he; cases he

/-- A store label's write. -/
theorem lw_st {aq rl : Bool} {a : Int} {d : List (BitVec 8)} {as0 vs0 : List Dsrc} {pa : Int} {data : List (BitVec 8)}
    (h : labelWrite (LStore aq rl a d as0 vs0) = some (pa, data)) : pa = a ∧ data = d := by
  simp only [labelWrite, Option.some.injEq, Prod.mk.injEq] at h; exact ⟨h.1.symm, h.2.symm⟩

/-- Two stores with different labels: the first store's entry is unique. -/
theorem qWW_first {a0 a1 : Int} {d0 d1 : List (BitVec 8)} {as0 vs0 as1 vs1 : List Dsrc} {ev : Trace} {t t' : Nat}
    (hQ : qWW a0 a1 d0 d1 as0 vs0 as1 vs1 ev) (hne : a0 ≠ a1)
    (h1 : (LStore false false a0 d0 as0 vs0, some t) ∈ ev) (h2 : (LStore false false a0 d0 as0 vs0, some t') ∈ ev) :
    t = t' := by
  have hlab : ∀ t1 t2 : Nat, (LStore false false a0 d0 as0 vs0, some t1) ≠ (LStore false false a1 d1 as1 vs1, some t2) := by
    intro t1 t2 he
    have := congrArg (fun e : PEv => labelWrite e.1) he
    simp only [labelWrite, Option.some.injEq, Prod.mk.injEq] at this
    exact hne this.1
  rcases q2_cases hQ with rfl | ⟨e0, rfl, ⟨t0, _, rfl⟩⟩ | ⟨e0, e1, rfl, ⟨t0, _, rfl⟩, ⟨t1, _, rfl⟩, _⟩
  · cases h1
  · rw [List.mem_singleton] at h1 h2; cases h1; cases h2; rfl
  · rcases List.mem_cons.1 h1 with h1 | h1
    · rcases List.mem_cons.1 h2 with h2 | h2
      · cases h1; cases h2; rfl
      · rw [List.mem_singleton] at h2; exact absurd h2 (hlab _ _)
    · rw [List.mem_singleton] at h1; exact absurd h1 (hlab _ _)

/-- Two stores with different labels: every timestamped entry is at or below the second store's. -/
theorem qWW_ts_le {a0 a1 : Int} {d0 d1 : List (BitVec 8)} {as0 vs0 as1 vs1 : List Dsrc} {ev : Trace} {t1 t : Nat}
    {e : PEv} (hQ : qWW a0 a1 d0 d1 as0 vs0 as1 vs1 ev)
    (hne : LStore false false a0 d0 as0 vs0 ≠ LStore false false a1 d1 as1 vs1)
    (h1 : (LStore false false a1 d1 as1 vs1, some t1) ∈ ev) (he : e ∈ ev) (ht : e.2 = some t) : t ≤ t1 := by
  rcases q2_cases hQ with rfl | ⟨e0, rfl, ⟨t0, _, rfl⟩⟩ | ⟨e0, e1, rfl, ⟨t0, _, rfl⟩, ⟨t2, _, rfl⟩, hlt⟩
  · cases h1
  · rw [List.mem_singleton] at h1; cases h1; exact absurd rfl hne
  · rcases List.mem_cons.1 h1 with h1 | h1
    · cases h1; exact absurd rfl hne
    · rw [List.mem_singleton] at h1; cases h1
      simp only [tsOf_some] at hlt
      rcases List.mem_cons.1 he with rfl | he
      · cases ht; omega
      · rw [List.mem_singleton] at he; subst he; cases ht; omega

/-- A store-then-load hart has one store: its timestamp is unique. -/
theorem qWR_st_uniq {M : List PMsg} {a0 a1 : Int} {n : Nat} {d0 : List (BitVec 8)} {as0 vs0 as1 : List Dsrc}
    {ev : Trace} {e e' : PEv} {t t' : Nat} (hQ : qWR M a0 a1 n d0 as0 vs0 as1 ev) (he : e ∈ ev) (ht : e.2 = some t)
    (he' : e' ∈ ev) (ht' : e'.2 = some t') : t = t' := by
  rw [qWR_writer hQ he ht] at he
  rw [qWR_writer hQ he' ht'] at he'
  rcases q2_cases hQ with rfl | ⟨e0, rfl, _⟩ | ⟨e0, e1, rfl, _, ⟨_, rfl, _⟩, _⟩
  · cases he
  · rw [List.mem_singleton] at he he'; rw [← he] at he'; cases he'; rfl
  · rcases List.mem_cons.1 he with he | he
    · rcases List.mem_cons.1 he' with he' | he'
      · rw [← he] at he'; cases he'; rfl
      · rw [List.mem_singleton] at he'; cases he'
    · rw [List.mem_singleton] at he; cases he

/-- A one-store hart: its timestamp is unique. -/
theorem qS_uniq {a0 : Int} {d0 : List (BitVec 8)} {as0 vs0 : List Dsrc} {ev : Trace} {e e' : PEv} {t t' : Nat}
    (hQ : qS a0 d0 as0 vs0 ev) (he : e ∈ ev) (ht : e.2 = some t) (he' : e' ∈ ev) (ht' : e'.2 = some t') : t = t' := by
  rcases q1_cases hQ with rfl | ⟨e0, rfl, _⟩
  · cases he
  · rw [List.mem_singleton] at he he'; subst he he'; rw [ht] at ht'; cases ht'; rfl

end contra

end Weak.Prom.PF
