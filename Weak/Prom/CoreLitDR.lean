/-
Weak/Prom: **row 16, datarfi (manual `litmus_datarfi`), proved IN THE LOGIC** (stage S2; plan rev 7 §5 row 16
"FORBIDDEN (manual: 'Because of PPO rule 12 …') — M2", §8 S2).

`Lit.datarfi` (RefTests.lean, mm-explanatory.adoc:993–1009): H0 `li t1,1; sw t1,0(s0); fence w,w; sw t1,0(s1)` ‖
H1 `lw a0,0(s1); sw a0,0(s2); lw a1,0(s2); xor a2,a1,a1; add s0,s0,a2; lw a3,0(s0)` (s0 = x, s1 = y, s2 = z);
outcome `a0 = 1 ∧ a3 = 0` FORBIDDEN.
* H0 (`hLWW_hart`): `tx < ty` (rule 4).
* H1 (`datarfi1_hart`): RULE 12 — `lw a1,(z)` reads H1's own `sw a0,(z)`: either it forwards (machine v2's M2: the
  byte's view is the store's forward view `va ⊔ vd`, and `vd = regv a0 ≥ s0`) or it reads at or above the store's
  timestamp (coherence floor; `tz > pv ≥ s0` by EXT) — `fwdView_ge_of`.  The syntactic `xor`/`add` dependency
  carries that view into the address of `lw a3,(x)`, so its pre-view is at least `s0`: no write to x in `(s3, s0]`.
* Contradiction: `mp_core` (CoreLitMP.lean), as for row 8.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.CoreLitPI
import Weak.Prom.CoreLitMP

namespace Weak.Prom.PF

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Ref (Instr Test two64 aluOp brEval amoOp sext byteList bytesVal FenceSet AmoOp)
open Weak.Prom.Ref.Lit (X Y Z)
open PLabel
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode

/-- H1's Ψ: `ld y`, `st z` (its data from `a0`), `ld z`, `ld x` with no write to x in `(s3, s0]`. -/
def qDR1 (M : List PMsg) : Trace → Prop :=
  q4 (isLd (Y : Int) 4 [.DReg 9]) (fun _ e1 => ∃ d, d.length = 4 ∧ isSt (Z : Int) d [.DReg 18] [.DReg 10] e1)
    (fun _ _ e2 => isLd (Z : Int) 4 [.DReg 18] e2)
    (fun e0 _ _ e3 => isLd (X : Int) 4 [.DReg 8] e3 ∧ (noCmo M → ¬ writesIn M (X : Int) (src0 e3) (src0 e0)))

section harts

variable {hlc : HasLC} {GF : BundledGFunctors} [GhostVarG GF HSt] [InvGS_gen hlc GF]

/-- **`li r,v; st r,(p0); fence w,w; st r,(p1)`** proves `qWW` (rule 4). -/
theorem hLWW_hart (img : Image) (M : List PMsg) (h : Nat) (s0 : LP) (a0 a1 v r p0 p1 : Nat)
    (hprog : s0.prog = [.alui .add r 0 v, .store 4 r p0 0, .fence ⟨false, true, false, false, false, true, false, false⟩,
      .store 4 r p1 0])
    (hpc : s0.pc = 0) (hq : s0.q = []) (hnz : r ≠ 0 ∧ p0 ≠ 0 ∧ p1 ≠ 0 ∧ p0 ≠ r ∧ p1 ≠ r)
    (hlen : r < s0.regs.length) (hv : v < two64) (ha0 : s0.rd p0 = a0) (ha1 : s0.rd p1 = a1)
    (hal0 : a0 < two64) (hal1 : a1 < two64) (hA0 : aligned a0 4 = true) (hA1 : aligned a1 4 = true) :
    ⊢@{IProp GF} wpPF Proto.triv ⟨litStep, litDone, img, M, h⟩
      (ΨK M (qWW a0 a1 (toBytes v 4) (toBytes v 4) [.DReg p0] [.DReg r] [.DReg p1] [.DReg r])) s0
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
  have e1a : s1.rd p0 = a0 := by rw [LPstep_rd hs1 p0 (.inl hnz.2.2.2.1), ha0]
  have e1b : s1.rd p1 = a1 := by rw [LPstep_rd hs1 p1 (.inl hnz.2.2.2.2), ha1]
  iapply (wpK_sw (sz := 4) (rs2 := r) (rs1 := p0) (off := 0) (base := (a0 : Int)) hw (hag s1) hq1
    (by rw [hP1, hc1]; rfl) (alg_of e1a hal0 hA0) (base_of e1a hal0))
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
  iapply (wpK_fence (f := ⟨false, true, false, false, false, true, false, false⟩) hw (hag s2) hq2
    (by rw [hP2, hc2]; rfl))
  iframe Hl
  inext
  iintro %s3 %hs3 Hl
  obtain ⟨hP3, hc3, hq3⟩ := LPstep_at hs3 hP2 (by rw [hc2])
  have e3 : s3.rd r = v := by rw [LPstep_rd hs3 r (.inr rfl), LPstep_rd hs2 r (.inr rfl), e1]
  have e3b : s3.rd p1 = a1 := by rw [LPstep_rd hs3 p1 (.inr rfl), LPstep_rd hs2 p1 (.inr rfl), e1b]
  iapply (wpK_sw (sz := 4) (rs2 := r) (rs1 := p1) (off := 0) (base := (a1 : Int)) hw (hag s3) hq3
    (by rw [hP3, hc3]; rfl) (alg_of e3b hal1 hA1) (base_of e3b hal1))
  iframe Hl
  inext
  iintro %ty %_ %_ %_ %hy
  have hlt : tx < ty := by
    simp [stPreA, stPre, hnz.1, hnz.2.1, hnz.2.2.1] at hy
    omega
  imodintro
  isplitr
  · ipureintro
    exact ⟨0, grd_intro ⟨⟨tx, by omega, by simp only [e1, srcR_pos hnz.2.1, srcR_pos hnz.1]⟩,
      ⟨ty, by omega, by simp only [e3, srcR_pos hnz.2.2.1, srcR_pos hnz.1]⟩, hlt⟩⟩
  isplitr
  · ipureintro; exact grd_intro trivial
  iintro %s4 %hs4 Hl
  obtain ⟨hP4, hc4, hq4⟩ := LPstep_at hs4 hP3 (by rw [hc3])
  iapply (wpK_fin hq4 (by rw [hP4, hc4]; simp))
  iexact Hl

/-- **Row 16's H1 in the logic** (rule 12 through the forward bank, M2). -/
theorem datarfi1_hart (img : Image) (M : List PMsg) (h : Nat) (s0 : LP)
    (hprog : s0.prog = [.load 4 true 10 9 0, .store 4 10 18 0, .load 4 true 11 18 0, .alu .xor 12 11 11,
      .alu .add 8 8 12, .load 4 true 13 8 0])
    (hpc : s0.pc = 0) (hq : s0.q = []) (hlen : s0.regs.length = 32) (h8 : s0.rd 8 = X) (h9 : s0.rd 9 = Y)
    (h18 : s0.rd 18 = Z) :
    ⊢@{IProp GF} wpPF Proto.triv ⟨litStep, litDone, img, M, h⟩ (ΨK M (qDR1 M)) s0
      (fun _ => iprop(⌜∃ V, grd Proto.triv img M V True⌝)) := by
  have hw := litW_lit img M h
  have hag := litAg_lit (V := Unit) litDone img M h
  iapply (wpK_start (by trivial))
  iintro %γ %P0 Hl
  -- `lw a0,(y)`
  iapply (wpK_ld (sz := 4) (sgn := true) (rd := 10) (rs1 := 9) (off := 0) (base := (Y : Int)) hw (hag s0) hq
    (by rw [hprog, hpc]; rfl) (alg_of h9 (by decide) (by decide)) (base_of h9 (by decide)))
  iframe Hl
  inext
  iintro %tvs0 %hl0 %_
  imodintro
  isplitr
  · ipureintro; exact ⟨0, grd_intro ⟨tvs0, rfl, hl0⟩⟩
  iintro %s1 %hs1 Hl
  obtain ⟨hP1, hc1, hq1⟩ := LPstep_at hs1 hprog (by rw [hpc])
  have e18 : s1.rd 18 = Z := by rw [LPstep_rd hs1 18 (.inl (by decide)), h18]
  -- `sw a0,(z)`
  iapply (wpK_sw (sz := 4) (rs2 := 10) (rs1 := 18) (off := 0) (base := (Z : Int)) hw (hag s1) hq1
    (by rw [hP1, hc1]; rfl) (alg_of e18 (by decide) (by decide)) (base_of e18 (by decide)))
  iframe Hl
  inext
  iintro %tz %_ %hmz %_ %hextz
  imodintro
  isplitr
  · ipureintro
    exact ⟨0, grd_intro ⟨⟨tvs0, rfl, hl0⟩, _, toBytes_length _ _, tz, by omega, rfl⟩⟩
  isplitr
  · ipureintro; exact grd_intro trivial
  iintro %s2 %hs2 Hl
  obtain ⟨hP2, hc2, hq2⟩ := LPstep_at hs2 hP1 (by rw [hc1])
  have e2 : s2.rd 18 = Z := by rw [LPstep_rd hs2 18 (.inr rfl), e18]
  -- `lw a1,(z)`: forwards from the own store, or reads at or above it
  iapply (wpK_ld (sz := 4) (sgn := true) (rd := 11) (rs1 := 18) (off := 0) (base := (Z : Int)) hw (hag s2) hq2
    (by rw [hP2, hc2]; rfl) (alg_of e2 (by decide) (by decide)) (base_of e2 (by decide)))
  iframe Hl
  inext
  iintro %tvs2 %hl2 %hlo2
  imodintro
  isplitr
  · ipureintro; exact ⟨0, grd_intro ⟨⟨tvs0, rfl, hl0⟩, ⟨_, toBytes_length _ _, tz, by omega, rfl⟩, tvs2, rfl, hl2⟩⟩
  iintro %s3 %hs3 Hl
  obtain ⟨hP3, hc3, hq3⟩ := LPstep_at hs3 hP2 (by rw [hc2])
  -- `xor a2,a1,a1`
  iapply (wpK_alu hw (hag s3) hq3 (by rw [hP3, hc3]; rfl) (by decide))
  iframe Hl
  inext
  iintro %s4 %hs4 Hl
  obtain ⟨hP4, hc4, hq4⟩ := LPstep_at hs4 hP3 (by rw [hc3])
  -- `add s0,s0,a2`
  iapply (wpK_alu hw (hag s4) hq4 (by rw [hP4, hc4]; rfl) (by decide))
  iframe Hl
  inext
  iintro %s5 %hs5 Hl
  obtain ⟨hP5, hc5, hq5⟩ := LPstep_at hs5 hP4 (by rw [hc4])
  have e4 : s4.rd 12 = 0 := by
    rw [LPstep_rd_eq hs4 (by decide) (by rw [LPstep_len hs3, LPstep_len hs2, LPstep_len hs1, hlen]; decide)]
    simp [aluOp]
  have e48 : s4.rd 8 = X := by
    rw [LPstep_rd hs4 8 (.inl (by decide)), LPstep_rd hs3 8 (.inl (by decide)), LPstep_rd hs2 8 (.inr rfl),
      LPstep_rd hs1 8 (.inl (by decide)), h8]
  have hl5 : 8 < s4.regs.length := by
    rw [LPstep_len hs4, LPstep_len hs3, LPstep_len hs2, LPstep_len hs1, hlen]; decide
  have e5 : s5.rd 8 = X := by
    rw [LPstep_rd_eq hs5 (by decide) hl5, e48, e4]
    simp [aluOp]; decide
  -- `lw a3,(x)`: its address view carries the view of `lw a1,(z)`
  iapply (wpK_ld (sz := 4) (sgn := true) (rd := 13) (rs1 := 8) (off := 0) (base := (X : Int)) hw (hag s5) hq5
    (by rw [hP5, hc5]; rfl) (alg_of e5 (by decide) (by decide)) (base_of e5 (by decide)))
  iframe Hl
  inext
  iintro %tvs3 %hl3 %hlo3
  have hord : noCmo M → ¬ writesIn M (X : Int) (src0 (LLoad false false (X : Int) tvs3 (srcR 8), none))
      (src0 (LLoad false false (Y : Int) tvs0 (srcR 9), none)) := by
    intro hnc
    obtain ⟨t0, v0, r0, rfl⟩ := tvs_cons hl0 (by decide)
    obtain ⟨t2, v2, r2, rfl⟩ := tvs_cons hl2 (by decide)
    obtain ⟨t3, v3, r3, rfl⟩ := tvs_cons hl3 (by decide)
    have hw3 := (loadOk_b0nc hnc hlo3).2
    -- the view of `lw a0` (X4)
    have k0 := (loadRun_b0 psInit false false (srcsView psInit (srcR 9)) (Y : Int) t0 v0 r0).1
    rw [fwdView_empty rfl] at k0
    -- the view of `lw a1,(z)` is at least the own store's forward view or timestamp
    have k2 := loadRun_ldv_of hlo2
    have hmz' : M[tz - 1]? = some (⟨(Z : Int), toBytes (s1.rd 10) 4, some h, .plain⟩ : PMsg) := hmz
    have kf := fwdView_ge_of hnc hlo2 (by simp; rfl)
      (by simp only [instrR_coh, acqPost_false']; exact storeRun_coh0 _ _ _ _ _ _ _ (by simp [toBytes_length]))
      hmz' (byteAt_base_isSome ⟨(Z : Int), toBytes (s1.rd 10) 4, some h, .plain⟩ (by simp [toBytes_length]))
      (by omega)
    intro hc
    apply hw3
    refine writesIn_mono hc ?_
    show t0 ≤ _
    simp [stPreA, stPre, ldPre, regWL] at hextz k0 k2 kf ⊢
    omega
  imodintro
  isplitr
  · ipureintro
    exact ⟨0, grd_intro ⟨⟨tvs0, rfl, hl0⟩, ⟨_, toBytes_length _ _, tz, by omega, rfl⟩, ⟨tvs2, rfl, hl2⟩,
      ⟨tvs3, rfl, hl3⟩, hord⟩⟩
  iintro %s6 %hs6 Hl
  obtain ⟨hP6, hc6, hq6⟩ := LPstep_at hs6 hP5 (by rw [hc5])
  iapply (wpK_fin hq6 (by rw [hP6, hc6]; simp))
  iexact Hl

end harts

def QsDR (M : List PMsg) : Nat → Trace → Prop
  | 0 => qWW (X : Int) (Y : Int) (toBytes 1 4) (toBytes 1 4) [.DReg 8] [.DReg 6] [.DReg 9] [.DReg 6]
  | 1 => qDR1 M
  | _ => q0

/-- **ROW 16, datarfi (manual `litmus_datarfi`): FORBIDDEN, in the logic** (plan §5 row 16, rule 12 / M2). -/
theorem lit_datarfi : ∀ (M : List PMsg) (run : PFRun LP Unit),
    validRun litStep (testImg Weak.Prom.Ref.Lit.datarfi) () (progs Weak.Prom.Ref.Lit.datarfi) M run →
    ¬ (run.obsLoad 1 0 = some 1 ∧ run.obsLoad 1 2 = some 0) := by
  intro M run hrun
  obtain ⟨_, hQ, hnc, hpart, hwf, himg, _⟩ := kitAdeq (π := Proto.triv) (QsDR M) (fun _ _ => True) trivial
    (fun h => match h with | 0 => trivial | 1 => trivial | _ + 2 => rfl)
    (fun h p hp _ => by
      obtain ⟨hpr, hpc, hq, hlen, hrd⟩ := progs_get hp
      match h with
      | 0 =>
        exact hLWW_hart _ M 0 p X Y 1 6 8 9 (by rw [hpr]; rfl) hpc hq (by decide) (by rw [hlen]; decide) (by decide)
          (by rw [hrd 8 (by decide) (by decide)]; rfl) (by rw [hrd 9 (by decide) (by decide)]; rfl)
          (by decide) (by decide) (by decide) (by decide)
      | 1 =>
        exact datarfi1_hart _ M 1 p (by rw [hpr]; rfl) hpc hq hlen (by rw [hrd 8 (by decide) (by decide)]; rfl)
          (by rw [hrd 9 (by decide) (by decide)]; rfl) (by rw [hrd 18 (by decide) (by decide)]; rfl)
      | n + 2 =>
        have hl : (progs Weak.Prom.Ref.Lit.datarfi).length = 2 := rfl
        rw [List.getElem?_eq_none (by omega)] at hp; cases hp) hrun
  rintro ⟨ho0, ho2⟩
  have hout : ∀ h, 2 ≤ h → memEv (run.trace h) = [] := fun h hh => by
    obtain ⟨k, rfl⟩ : ∃ k, h = k + 2 := ⟨h - 2, by omega⟩; exact hQ (k + 2)
  -- H1's answers: `ld y` (entry 0) and `ld x` (entry 3)
  rw [obsLoad_memEv] at ho0 ho2
  rcases q4_cases (hQ 1) with hev | ⟨e0, hev, hP0⟩ | ⟨e0, e1, hev, hP0, hP1⟩ | ⟨e0, e1, e2, hev, hP0, hP1, hP2⟩ |
      ⟨e0, e1, e2, e3, hev, hP0, hP1, hP2, hP3, hord⟩
  · rw [hev] at ho0; simp [loadsOf] at ho0
  · obtain ⟨_, rfl, _⟩ := hP0; rw [hev] at ho2; simp [loadsOf, loadLikeTvs] at ho2
  · obtain ⟨_, rfl, _⟩ := hP0; obtain ⟨_, _, _, _, rfl⟩ := hP1; rw [hev] at ho2; simp [loadsOf, loadLikeTvs] at ho2
  · obtain ⟨_, rfl, _⟩ := hP0; obtain ⟨_, _, _, _, rfl⟩ := hP1; obtain ⟨_, rfl, _⟩ := hP2
    rw [hev] at ho2; simp [loadsOf, loadLikeTvs] at ho2
  obtain ⟨t0, b0, r0, rfl, _⟩ := isLd_cons hP0 (by decide)
  obtain ⟨d, hdl, tz, _, rfl⟩ := hP1
  obtain ⟨tvs2, rfl, _⟩ := hP2
  obtain ⟨t3, b3, r3, rfl, _⟩ := isLd_cons hP3 (by decide)
  have hm0 : (LLoad false false (Y : Int) ((t0, b0) :: r0) [.DReg 9], (none : Option Nat)) ∈ memEv (run.trace 1) := by
    rw [hev]; simp
  have hm3 : (LLoad false false (X : Int) ((t3, b3) :: r3) [.DReg 8], (none : Option Nat)) ∈ memEv (run.trace 1) := by
    rw [hev]; simp
  rw [hev] at ho0 ho2
  simp only [loadsOf, List.filterMap_cons, loadLikeTvs, List.filterMap_nil, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.map_some, Option.some.injEq] at ho0 ho2
  have hr0 := kit_read0 hwf hm0 rfl
  have hr3 := kit_read0 hwf hm3 rfl
  rw [himg] at hr0 hr3
  have hv0 := obsOf_b0 ho0
  have hv3 := obsOf_b0 ho2
  -- writers: H0's two stores, H1's store at z
  have hW : ∀ (k : Nat) (m : PMsg), M[k]? = some m →
      (∃ e ∈ memEv (run.trace 0), e.2 = some (k + 1) ∧ labelWrite e.1 = some (m.pa, m.data)) ∨
      (m.pa = (Z : Int) ∧ m.data.length = 4) := by
    intro k m hm
    obtain ⟨h, hh, e, he, het, hlw⟩ := writer_cases hpart hwf 2 hout hm
    match h, hh with
    | 0, _ => exact .inl ⟨e, he, het, hlw⟩
    | 1, _ =>
      right
      rw [hev] at he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl
      · cases het
      · obtain ⟨hpa, hd⟩ := lw_st hlw; exact ⟨hpa, by rw [hd, hdl]⟩
      · cases het
      · cases het
  refine mp_core hnc rfl rfl hr0 ?_ hr3 ?_ hord ?_ ?_
  · intro h; rw [h] at hv0; cases hv0
  · apply BitVec.eq_of_toNat_eq; rw [hv3]; rfl
  · intro k m hm hb
    rcases hW k m hm with ⟨e, he, het, hlw⟩ | ⟨hpa, hl⟩
    · rcases qWW_writer (hQ 0) he het with rfl | ⟨rfl, t0', ht0, hin, hlt⟩
      · obtain ⟨hpa, hd⟩ := lw_st hlw; rw [byteAt_none_of hpa hd (by decide)] at hb; cases hb
      · obtain ⟨m', hm', hpa', hd'⟩ := kit_msg hwf hin rfl rfl
        exact ⟨t0' - 1, m', hm', by rw [byteAt_some_of hpa' hd' (v := 1) (by decide)]; rfl, by omega⟩
    · rw [byteAt_lt (by rw [hpa]; decide)] at hb; cases hb
  · intro k m hm hb
    rcases hW k m hm with ⟨e, he, het, hlw⟩ | ⟨hpa, hl⟩
    · rcases qWW_writer (hQ 0) he het with rfl | ⟨rfl, _⟩ <;> obtain ⟨hpa, hd⟩ := lw_st hlw
      · rw [byteAt_some_of hpa hd (v := 1) (by decide)] at hb; cases hb
      · rw [byteAt_none_of hpa hd (by decide)] at hb; cases hb
    · rw [byteAt_lt (by rw [hpa]; decide)] at hb; cases hb

end Weak.Prom.PF

#print axioms Weak.Prom.PF.lit_datarfi
