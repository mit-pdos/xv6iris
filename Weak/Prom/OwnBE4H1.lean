/-
Weak/Prom: **E-b4 — the acquirers' text `pA`** (stage E-b4; E-a4's test `t7`, OwnAE4Defs.lean, read-only).

`acqRound`: one round `k ∈ {1, 2}` of acquirer `i ∈ {1, 2}` from `pc = 0`: wait for the publication of round `k`
(`waitB` + `inv_pubRd`), `fence rw,rw`, xv6's acquire (`amoB`), `sd a0,16(s1)` (`pcB`), the critical section
`ld; addi; sd` (`inv_csld`, `inv_csst`), xv6's release `sd zero,16(s1); fence rw,w; sw zero,0(s1)` (`pcB`,
`inv_rel`, in place), `fence rw,w; sb a3,0(a6)` (`inv_done`, in place), `addi a3,a3,1; bne a3,t3,0`.
`acqWp`: both rounds, from the initial state.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.OwnBE4Gen

namespace Weak.Prom.OB.E4

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Own (OSt upd upd_eq upd_ne fulO rmwOk)
open Weak.Prom.Own.X (xOW XP xp_of)
open Weak.Prom.OA (XI xOf xStep Lk Ct addiwV isCLd isCSt)
open Weak.Prom.OA.P (L1 postA postA_vr)
open Weak.Prom.OA.C (Pc)
open Weak.Prom.OA.E4 (q7 img7 xs7 atI fI wsM wsM_refl wsM_trans fI_ld fI_st wsM_ld wsM_st wsM_fence fI_of wsM_eq
  pA bA xOf_pA)
open Weak.Prom.PF (LPstep LPstep_at LPstep_rd LPstep_rd_eq LPstep_len ldVal instrR qPosts qPost amoD regWP ctrlP
  memEv Trace PEv msgAt li_val)
open Weak.Prom.Ref (Instr two64 aluOp brEval sext)
open Weak.Prom.Ref.Lit (X Y Z)
open PLabel
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode

/-- Fixed registers. -/
def RV (s : LP) (l : List (Nat × Nat)) : Prop := s.regs.length = 32 ∧ ∀ p ∈ l, s.rd p.1 = p.2

theorem rv_step {s s' : LP} {pc rd v : Nat} {l : List (Nat × Nat)} (h : RV s l) (hs : LPstep s s' pc rd v)
    (hn : ∀ p ∈ l, p.1 ≠ rd ∨ rd = 0) : RV s' l :=
  ⟨by rw [LPstep_len hs]; exact h.1, fun p hp => by rw [LPstep_rd hs p.1 (hn p hp)]; exact h.2 p hp⟩

theorem rv_get {s : LP} {l : List (Nat × Nat)} (h : RV s l) {r v : Nat} (hp : (r, v) ∈ l) : s.rd r = v :=
  h.2 _ hp

/-- An acquirer's fixed registers in round `k`. -/
def rA (i k : Nat) : List (Nat × Nat) := [(9, X), (11, Y), (12, Z), (13, k), (16, Z + i), (28, 3)]

theorem rA_reg {i k : Nat} {p : Nat × Nat} (hp : p ∈ rA i k) :
    p.1 = 9 ∨ p.1 = 11 ∨ p.1 = 12 ∨ p.1 = 13 ∨ p.1 = 16 ∨ p.1 = 28 := by
  simp only [rA, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

/-- An LPstep writing none of the fixed registers keeps them. -/
theorem rA_step {s s' : LP} {pc rd v i k : Nat} (h : RV s (rA i k)) (hs : LPstep s s' pc rd v)
    (hrd : rd = 0 ∨ rd = 5 ∨ rd = 7 ∨ rd = 14 ∨ rd = 15) : RV s' (rA i k) :=
  rv_step h hs (fun p hp => by have := rA_reg hp; omega)

theorem rA_succ {s s' : LP} {pc v i k : Nat} (h : RV s (rA i k)) (hs : LPstep s s' pc 13 v) (h13 : s'.rd 13 = k + 1) :
    RV s' (rA i (k + 1)) := by
  refine ⟨by rw [LPstep_len hs]; exact h.1, fun p hp => ?_⟩
  have hk : ∀ r w, (r, w) ∈ rA i k → r ≠ 13 → s'.rd r = w := fun r w hm hr => by
    rw [LPstep_rd hs r (.inl hr)]; exact rv_get h hm
  simp only [rA, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with e | e | e | e | e | e <;> rw [e]
  · exact hk 9 X (by simp [rA]) (by decide)
  · exact hk 11 Y (by simp [rA]) (by decide)
  · exact hk 12 Z (by simp [rA]) (by decide)
  · exact h13
  · exact hk 16 (Z + i) (by simp [rA]) (by decide)
  · exact hk 28 3 (by simp [rA]) (by decide)

section h1

variable {hlc : HasLC} {GF : BundledGFunctors} [GhostVarG GF Loc] [InvGS_gen hlc GF]

theorem pA_at {s : LP} {k : Nat} {ins : Instr} (hprog : s.prog = bA) (hpc : s.pc = k)
    (hx : pA[k]? = some (.i ins)) (hpl : (XI.i ins).plain = true) : s.prog[s.pc]? = some ins ∧ XP xs7 s :=
  ⟨atI hprog (by rw [hpc]; exact hx), xp_of (by rw [hprog]; exact xOf_pA) (by rw [hpc]; exact hx) hpl⟩

set_option maxHeartbeats 4000000 in
/-- **ONE ROUND OF AN ACQUIRER**. -/
theorem acqRound (M : List PMsg) (γ : Nat → GName) (i : Nat) (hi : i = 1 ∨ i = 2)
    (hnoinv : ∀ t a, ¬ cmoAt M isInvalK t a) (k : Nat) (hk : k = 1 ∨ k = 2) :
    ⊢ ∀ (s : LP) (ws : PState) (l : Loc), ⌜s.prog = bA ∧ s.q = [] ∧ s.pc = 0 ∧ RV s (rA i k) ∧ fI ws ∧
        l.st = .W ∧ l.k = k ∧ l.ld = none⌝ -∗ gl (γ i) l -∗
      (∀ (s' : LP) (ws' : PState) (l' : Loc), ⌜k + 1 ≠ 3 ∧ s'.prog = bA ∧ s'.q = [] ∧ s'.pc = 0 ∧
          RV s' (rA i (k + 1)) ∧ fI ws' ∧ l'.st = .W ∧ l'.k = k + 1 ∧ l'.ld = none⌝ -∗ gl (γ i) l' -∗
        wpH (hlc := hlc) (GF := GF) M γ i s' ws') -∗
      wpH (hlc := hlc) M γ i s ws := by
  have hi3 : i < 3 := by omega
  have hi0 : i ≠ 0 := by omega
  iintro %s %ws %l %hs Hl HK
  obtain ⟨hprog, hq, hpc, hrv, hfi, hlW, hlk, hld⟩ := hs
  have hT : xOf xs7 (pA.map XI.base) = some pA := xOf_pA
  have e0 : (L1 : Int) + ((0 : Nat) : Int) = L1 := by simp
  -- 0–1: wait for the publication of round k
  ihave Hw := waitB (hlc := hlc) M γ i hi3 pA hT 0 0 k (by decide) (by omega) rfl rfl (by decide)
    (fun s => RV s (rA i k)) (fun s h => ⟨rv_get h (by simp [rA]), rv_get h (by simp [rA]), h.1⟩)
    (fun s s' pc rd v h hs hrd => rA_step h hs (by omega))
    hnoinv l hld (fun t => { l with st := .A, p := t })
    (fun σ t v a hmb hv S ls hI hl => ⟨S, by
      rw [e0] at hmb ⊢
      have := inv_pubRd (a := a) hI hi (by rw [hl]; exact hlW) hmb (by rw [hl, hlk]; exact hv)
      rw [hl] at this; exact this⟩) ws
  iapply Hw $$ %s %ws %⟨hprog, hq, hpc, hrv, hfi, wsM_refl _⟩ Hl
  iintro %s2 %ws2 %t %⟨hP2, hq2, hc2, hrv2, hfi2, -, hle⟩ Hl
  -- 2: fence rw,rw
  obtain ⟨hp2, hpl2⟩ := pA_at hP2 hc2 (rfl : pA[2]? = some (.i Weak.Prom.Ref.Lit.fRWRW)) rfl
  iapply (wpX_fence hq2 hpl2 hp2)
  iintro %s3 %hs3
  obtain ⟨hP3, hc3, hq3⟩ := LPstep_at hs3 hP2 (by rw [hc2])
  have hrv3 := rv_step hrv2 hs3 (fun _ _ => .inr rfl)
  have hvw3 : t ≤ (instrR (fencePost ws2 true true true true)).wVwNew := by
    simp only [PF.instrR_vwNew, PF.fence_vwNew, if_true]; omega
  -- 3: li a4,1
  obtain ⟨hp3, hpl3⟩ := pA_at hP3 hc3 (rfl : pA[3]? = some (.i (Weak.Prom.Ref.Lit.li 14 1))) rfl
  iapply (wpX_alui hq3 hpl3 hp3 (by decide))
  iintro %s4 %hs4
  obtain ⟨hP4, hc4, hq4⟩ := LPstep_at hs4 hP3 (by rw [hc3])
  have hrv4 := rA_step hrv3 hs4 (by omega)
  have h14 : s4.rd 14 = 1 := li_val hs4 (by decide) (by rw [hrv3.1]; decide) (by decide)
  -- 4–7: xv6's acquire
  ihave Ha := amoB (hlc := hlc) M γ i pA hT 4 rfl rfl rfl rfl (by decide)
    (fun s => RV s (rA i k) ∧ s.rd 14 = 1) (fun s h => ⟨rv_get h.1 (by simp [rA]), h.2, h.1.1⟩)
    (fun s s' pc rd v h hs hrd => ⟨rA_step h.1 hs (by omega), by rw [LPstep_rd hs 14 (by omega)]; exact h.2⟩)
    hnoinv { l with st := .A, p := t } (.inr ⟨hi, rfl⟩) (instrR (regWP (instrR (fencePost ws2 true true true true)) 14
      (srcR 0))) hvw3
  iapply Ha $$ %s4 %(instrR (regWP (instrR (fencePost ws2 true true true true)) 14 (srcR 0)))
    %⟨hP4, hq4, hc4, ⟨hrv4, h14⟩, fI_of hfi2 rfl rfl, wsM_refl _⟩ Hl
  iintro %s8 %ws8 %u %⟨hP8, hq8, hc8, ⟨hrv8, _⟩, hfi8, hmo8, hu8r, hu8w⟩ Hl
  rw [show hS i = .H1 by simp [hS, hi0]]
  -- 8: sd a0,16(s1)
  ihave Hp := pcB (hlc := hlc) M γ i hi3 pA hT 8 10 rfl (fun s => RV s (rA i k))
    (fun s h => ⟨rv_get h (by simp [rA]), h.1⟩) (fun s s' pc v h hs => rv_step h hs (fun _ _ => .inr rfl))
    { { l with st := .A, p := t } with st := .H1, u := u } hld
  iapply Hp $$ %s8 %ws8 %⟨hP8, hq8, hc8, hrv8, hfi8⟩ Hl
  iintro %s9 %ws9 %⟨hP9, hq9, hc9, hrv9, hfi9, hmo9⟩ Hl
  have hu9 : u ≤ ws9.wVrNew := Nat.le_trans hu8r hmo9.2.2.2.1
  have hu9w : u ≤ ws9.wVwNew := Nat.le_trans hu8w hmo9.2.2.2.2
  -- 9: ld t2,(a1) — the critical section's load
  obtain ⟨hp9, hpl9⟩ := pA_at hP9 hc9 (rfl : pA[9]? = some (.i (Weak.Prom.Ref.Lit.ld 7 11))) rfl
  have h11 : s9.rd 11 = Y := rv_get hrv9 (by simp [rA])
  have hadr : (((s9.rd 11 + 0) % two64 : Nat) : Int) = Ct := by rw [h11]; simp [Ct, Y, two64]
  iapply (wpX_ld (sz := 8) (sgn := true) (rd := 7) (rs1 := 11) (off := 0) hq9 hpl9 hp9
    (by rw [h11]; simp [aligned, Y, two64]))
  inext
  iintro %σ %tvs %hl8 %hlo HX _
  rw [hadr] at hlo ⊢
  have hby : ∀ (j : Nat) t b, tvs[j]? = some (t, b) → j < 8 ∧ memByte img7 M t (Ct + j) = some b ∧ t ≤ σ.o.n ∧
      ¬ writesIn (M.take σ.o.n) (Ct + j) t u := by
    intro j t b hj
    obtain ⟨c1, c2, c3⟩ := Weak.Prom.Own.MPL.loadOk_byte hnoinv hlo hj
    refine ⟨by have := (List.getElem?_eq_some_iff.1 hj).1; omega, c1, c2, fun hw => c3 (PF.writesIn_mono hw ?_)⟩
    have := (PF.ldPre_ge ws9 false false (srcsView ws9 (srcR 11))).2.1; omega
  imod xstep (hlc := hlc) (σ' := nxT σ i σ.o (LLoad false false Ct tvs (srcR 11), none))
    (Q := fun l' => l' = { { { l with st := .A, p := t } with st := .H1, u := u } with ld := some tvs }) hi3
    (fun S ls hI hl => by
      obtain ⟨S', hS⟩ := inv_csld (a := srcR 11) hI hi (by rw [hl]) (by rw [hl]; exact hld)
        (fun j t b hj => by rw [hl]; exact hby j t b hj)
      exact ⟨S', _, rfl, by rw [hl] at hS; exact hS⟩) $$ HX Hl with ⟨%l', %e, HX, Hl⟩
  subst e
  imodintro
  iframe HX
  iintro %s10 %hs10
  obtain ⟨hP10, hc10, hq10⟩ := LPstep_at hs10 hP9 (by rw [hc9])
  have hrv10 := rA_step hrv9 hs10 (by omega)
  -- the CS load's sources are below the coherence floor
  have hcoh : ∀ (j : Nat) t b, tvs[j]? = some (t, b) → t ≤ coh (instrR (regWP (qPosts (loadRun ws9 false false
      (srcsView ws9 (srcR 11)) Ct tvs) (regWL 7 [.DLdRes] ++ [LInstr])) 7 (srcR 7))) (Ct + j) := by
    intro j t b hj
    have := Weak.Prom.Own.Lk.loadRun_coh_j (ws := ws9) (aq := false) (rl := false) (va := srcsView ws9 (srcR 11))
      (base := Ct) hj
    simpa [regWL, qPosts, qPost] using this
  have hvwS : u ≤ (instrR (regWP (qPosts (loadRun ws9 false false (srcsView ws9 (srcR 11)) Ct tvs)
      (regWL 7 [.DLdRes] ++ [LInstr])) 7 (srcR 7))).wVwNew := by
    have := (PF.loadRun_mono ws9 false false (srcsView ws9 (srcR 11)) Ct tvs).2.2.2.2.2.2.2.2.1
    simp only [regWL, qPosts, qPost, PF.instrR_vwNew, PF.regWP_vwNew, show (7 : Nat) ≠ 0 by decide, if_false,
      List.singleton_append]; omega
  -- 10: addi t2,t2,1
  obtain ⟨hp10, hpl10⟩ := pA_at hP10 hc10 (rfl : pA[10]? = some (.i (Weak.Prom.Ref.Lit.addi 7 7 1))) rfl
  iapply (wpX_alui hq10 hpl10 hp10 (by decide))
  iintro %s11 %hs11
  obtain ⟨hP11, hc11, hq11⟩ := LPstep_at hs11 hP10 (by rw [hc10])
  have hrv11 := rA_step hrv10 hs11 (by omega)
  -- 11: sd t2,(a1) — the critical section's store
  obtain ⟨hp11, hpl11⟩ := pA_at hP11 hc11 (rfl : pA[11]? = some (.i (Weak.Prom.Ref.Lit.sd 7 11))) rfl
  have h11' : s11.rd 11 = Y := rv_get hrv11 (by simp [rA])
  have hadr' : (((s11.rd 11 + 0) % two64 : Nat) : Int) = Ct := by rw [h11']; simp [Ct, Y, two64]
  iapply (wpX_sd (sz := 8) (rs2 := 7) (rs1 := 11) (off := 0) hq11 hpl11 hp11 (by rw [h11']; simp [aligned, Y, two64]))
  inext
  iintro %σ1 %ts %o' %hful %hmsg %hcb %hpre HX _
  rw [hadr'] at hmsg hcb ⊢
  have hts1 : 1 ≤ ts := by
    rcases hful with ⟨_, h1, _⟩ | ⟨_, _, _, h1, _⟩
    · have := (List.getElem?_eq_some_iff.1 (Weak.Prom.Own.MP.take_get hmsg)); omega
    · omega
  obtain ⟨hm, _⟩ := msgAt_take hmsg hts1
  have hlt : ∀ p ∈ tvs, p.1 < ts := by
    intro p hp
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hp
    have hj8 : j < 8 := by have := (List.getElem?_eq_some_iff.1 hj).1; omega
    have c1 := hcoh j p.1 p.2 (by rw [hj])
    have c2 := Weak.Prom.Own.Lk.cohBelow_get hcb j (by simp [toBytes_len]; omega)
    omega
  have hut : u < ts := by
    have := (PF.stPreA_ge (instrR (regWP (qPosts (loadRun ws9 false false (srcsView ws9 (srcR 11)) Ct tvs)
      (regWL 7 [.DLdRes] ++ [LInstr])) 7 (srcR 7))) false false
      (srcsView (instrR (regWP (qPosts (loadRun ws9 false false (srcsView ws9 (srcR 11)) Ct tvs)
        (regWL 7 [.DLdRes] ++ [LInstr])) 7 (srcR 7))) (srcR 11))
      (srcsView (instrR (regWP (qPosts (loadRun ws9 false false (srcsView ws9 (srcR 11)) Ct tvs)
        (regWL 7 [.DLdRes] ++ [LInstr])) 7 (srcR 7))) (srcR 7))).2.2.2.1
    omega
  imod xstep (hlc := hlc) (σ' := nxT σ1 i o' (LStore false false Ct (toBytes (s11.rd 7) 8) (srcR 11) (srcR 7), some ts))
    (Q := fun l' => l' = { { { { l with st := .A, p := t } with st := .H1, u := u } with ld := some tvs } with
      st := .H2, ld := none }) hi3
    (fun S ls hI hl => by
      obtain ⟨S', hS⟩ := inv_csst hI hi (by rw [hl]) (by rw [hl]) hful hm (by rw [hl]; exact hut) hlt
      exact ⟨S', _, rfl, by rw [hl] at hS; exact hS⟩) $$ HX Hl with ⟨%l', %e, HX, Hl⟩
  subst e
  imodintro
  iframe HX
  iintro %s12 %hs12
  obtain ⟨hP12, hc12, hq12⟩ := LPstep_at hs12 hP11 (by rw [hc11])
  have hrv12 := rA_step hrv11 hs12 (.inl rfl)
  -- 12: sd zero,16(s1)
  ihave Hp2 := pcB (hlc := hlc) M γ i hi3 pA hT 12 0 rfl (fun s => RV s (rA i k))
    (fun s h => ⟨rv_get h (by simp [rA]), h.1⟩) (fun s s' pc v h hs => rv_step h hs (fun _ _ => .inr rfl))
    { { { { l with st := .A, p := t } with st := .H1, u := u } with ld := some tvs } with st := .H2, ld := none } rfl
  iapply Hp2 $$ %s12 %_ %⟨hP12, hq12, hc12, hrv12,
    fI_instrR (fI_stR (fI_instrR (fI_regWP (fI_qreg (fI_ldR hfi9)))))⟩ Hl
  iintro %s13 %ws13 %⟨hP13, hq13, hc13, hrv13, hfi13, -⟩ Hl
  -- 13: fence rw,w
  obtain ⟨hp13, hpl13⟩ := pA_at hP13 hc13 (rfl : pA[13]? = some (.i Weak.Prom.Ref.Lit.fRWW)) rfl
  iapply (wpX_fence hq13 hpl13 hp13)
  iintro %s14 %hs14
  obtain ⟨hP14, hc14, hq14⟩ := LPstep_at hs14 hP13 (by rw [hc13])
  have hrv14 := rv_step hrv13 hs14 (fun _ _ => .inr rfl)
  -- 14: sw zero,0(s1) — xv6's release, in place
  obtain ⟨hp14, hpl14⟩ := pA_at hP14 hc14 (rfl : pA[14]? = some (.i (Weak.Prom.Ref.Lit.sw 0 9))) rfl
  have h9 : s14.rd 9 = X := rv_get hrv14 (by simp [rA])
  have hadr9 : (((s14.rd 9 + 0) % two64 : Nat) : Int) = Lk := by rw [h9]; simp [Lk, X, two64]
  have h0 : s14.rd 0 = 0 := by simp [LP.rd]
  iapply (wpX_sd (sz := 4) (rs2 := 0) (rs1 := 9) (off := 0) hq14 hpl14 hp14 (by rw [h9]; simp [aligned, X, two64]))
  inext
  iintro %σ2 %ts2 %o2 %hful2 %hmsg2 %_ %_ HX _
  rw [hadr9, h0] at hmsg2 ⊢
  have hful2' := hful2
  rcases hful2' with ⟨hn, _, _⟩ | ⟨hrc, _, _, hts2, _⟩
  · exact (hn (Weak.Prom.Own.MPL.relClass_fW _ _ _ _ _ rfl rfl rfl _ _ _ _)).elim
  obtain ⟨hm2, _⟩ := msgAt_take hmsg2 (by omega)
  imod xstep (hlc := hlc) (σ' := nxT σ2 i o2 (LStore false false Lk (toBytes 0 4) (srcR 9) (srcR 0), some ts2))
    (Q := fun l' => l' = { { { { { l with st := .A, p := t } with st := .H1, u := u } with ld := some tvs } with
      st := .H2, ld := none } with st := .R }) hi3
    (fun S ls hI hl => by
      obtain ⟨S', hS⟩ := inv_rel hI hi (by rw [hl]) hful2 hrc hm2
      exact ⟨S', _, rfl, by rw [hl] at hS; exact hS⟩) $$ HX Hl with ⟨%l', %e, HX, Hl⟩
  subst e
  imodintro
  iframe HX
  iintro %s15 %hs15
  obtain ⟨hP15, hc15, hq15⟩ := LPstep_at hs15 hP14 (by rw [hc14])
  have hrv15 := rv_step hrv14 hs15 (fun _ _ => .inr rfl)
  -- 15: fence rw,w
  obtain ⟨hp15, hpl15⟩ := pA_at hP15 hc15 (rfl : pA[15]? = some (.i Weak.Prom.Ref.Lit.fRWW)) rfl
  iapply (wpX_fence hq15 hpl15 hp15)
  iintro %s16 %hs16
  obtain ⟨hP16, hc16, hq16⟩ := LPstep_at hs16 hP15 (by rw [hc15])
  have hrv16 := rv_step hrv15 hs16 (fun _ _ => .inr rfl)
  -- 16: sb a3,0(a6) — the done byte, in place
  obtain ⟨hp16, hpl16⟩ := pA_at hP16 hc16 (rfl : pA[16]? = some (.i (Weak.Prom.Ref.Lit.sb 13 16))) rfl
  have h16 : s16.rd 16 = Z + i := rv_get hrv16 (by simp [rA])
  have h13 : s16.rd 13 = k := rv_get hrv16 (by simp [rA])
  have hadr16 : (((s16.rd 16 + 0) % two64 : Nat) : Int) = L1 + i := by
    rw [h16]; simp [L1, Z, two64]; omega
  iapply (wpX_sd (sz := 1) (rs2 := 13) (rs1 := 16) (off := 0) hq16 hpl16 hp16 (by simp [aligned, Nat.mod_one]))
  inext
  iintro %σ3 %ts3 %o3 %hful3 %hmsg3 %_ %_ HX _
  rw [hadr16, h13] at hmsg3 ⊢
  have hful3' := hful3
  rcases hful3' with ⟨hn, _, _⟩ | ⟨hrc3, _, _, hts3, _⟩
  · exact (hn (Weak.Prom.Own.MPL.relClass_fW _ _ _ _ _ rfl rfl rfl _ _ _ _)).elim
  obtain ⟨hm3, _⟩ := msgAt_take hmsg3 (by omega)
  imod xstep (hlc := hlc) (σ' := nxT σ3 i o3 (LStore false false (L1 + i) (toBytes k 1) (srcR 16) (srcR 13), some ts3))
    (Q := fun l' => l'.st = .W ∧ l'.k = k + 1 ∧ l'.ld = none) hi3
    (fun S ls hI hl => by
      have hk' : (ls i).k = k := by rw [hl]; exact hlk
      obtain ⟨S', hS⟩ := inv_done (a := srcR 16) (c := srcR 13) hI hi (by rw [hl]) hful3 hrc3
        (by rw [hk']; exact hm3)
      rw [hk'] at hS
      exact ⟨S', _, ⟨rfl, rfl, by rw [hl]⟩, hS⟩) $$ HX Hl with ⟨%l', %hl', HX, Hl⟩
  imodintro
  iframe HX
  iintro %s17 %hs17
  obtain ⟨hP17, hc17, hq17⟩ := LPstep_at hs17 hP16 (by rw [hc16])
  have hrv17 := rv_step hrv16 hs17 (fun _ _ => .inr rfl)
  -- 17: addi a3,a3,1
  obtain ⟨hp17, hpl17⟩ := pA_at hP17 hc17 (rfl : pA[17]? = some (.i (Weak.Prom.Ref.Lit.addi 13 13 1))) rfl
  iapply (wpX_alui hq17 hpl17 hp17 (by decide))
  iintro %s18 %hs18
  obtain ⟨hP18, hc18, hq18⟩ := LPstep_at hs18 hP17 (by rw [hc17])
  have h13' : s18.rd 13 = k + 1 := by
    rw [LPstep_rd_eq hs18 (by decide) (by rw [hrv17.1]; decide),
      rv_get hrv17 (show (13, k) ∈ rA i k by simp [rA])]
    simp [aluOp, two64]; omega
  have hrv18 : RV s18 (rA i (k + 1)) := rA_succ hrv17 hs18 h13'
  -- 18: bne a3,t3,0
  have h28 : s18.rd 28 = 3 := rv_get hrv18 (by simp [rA])
  iapply (wpX_brx hq18 (by rw [hP18]; exact hT) (by rw [hc18]; rfl) (by rw [hP18]; decide))
  iintro %s19 %hs19
  by_cases hk3 : k + 1 = 3
  · have hbr : (if brEval .ne (s18.rd 13) (s18.rd 28) then 0 else s18.pc + 1) = 19 := by
      simp [brEval, h13', h28, hk3, hc18]
    rw [hbr] at hs19
    obtain ⟨hP19, hc19, hq19⟩ := LPstep_at hs19 hP18 rfl
    iapply (wpX_end hq19 (by rw [hP19, hc19]; decide))
  · have hbr : (if brEval .ne (s18.rd 13) (s18.rd 28) then 0 else s18.pc + 1) = 0 := by
      simp [brEval, h13', h28]; omega
    rw [hbr] at hs19
    obtain ⟨hP19, hc19, hq19⟩ := LPstep_at hs19 hP18 rfl
    iapply HK $$ %s19 %_ %l' %⟨hk3, hP19, hq19, hc19, rv_step hrv18 hs19 (fun _ _ => .inr rfl),
      fI_instrR (fI_ctrlP (fI_instrR (fI_regWP (fI_instrR (fI_stR (fI_instrR (fI_fence (fI_instrR (fI_stR
        (fI_instrR (fI_fence hfi13))))))))))), hl'.1, hl'.2.1, hl'.2.2⟩ Hl

end h1

end Weak.Prom.OB.E4
