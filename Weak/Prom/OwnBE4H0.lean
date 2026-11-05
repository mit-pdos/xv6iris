/-
Weak/Prom: **E-b4 — hart 0's text `p0`** (stage E-b4; E-a4's test `t7`, OwnAE4Defs.lean, read-only).

`h0Round`: one round `k ∈ {1, 2}` of hart 0 from `pc = 0` in the DEAD phase: kfree junk in the lock word and the
field (`inv_ful`, `inv_h0fld`), INITLOCK `sw zero` (`inv_ful`: a lock-word store of the dead phase — nothing tells
it from a release), the field's initialisation 5 (`inv_h0fld`), `fence rw,w; sb a3,0(a2)` — THE PUBLICATION
(`inv_pub`, in place), the two done-byte waits (`waitB` + `inv_dnRd`), `fence rw,rw`, xv6's acquire (`amoB`), the
cpu field stores (`pcB`), `fence rw,w; sw zero,0(s1)` — THE CLOSING RELEASE (`inv_close`, in place: the death),
`addi a3,a3,1; bne a3,t3,0`.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.OwnBE4H1

namespace Weak.Prom.OB.E4

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Own (OSt upd upd_eq upd_ne fulO rmwOk)
open Weak.Prom.Own.X (xOW XP xp_of)
open Weak.Prom.OA (XI xOf xStep Lk Ct addiwV isCLd isCSt)
open Weak.Prom.OA.P (L1 J)
open Weak.Prom.OA.C (Pc)
open Weak.Prom.OA.E4 (q7 img7 xs7 atI fI wsM wsM_refl wsM_trans fI_of p0 b0 xOf_p0)
open Weak.Prom.PF (LPstep LPstep_at LPstep_rd LPstep_rd_eq LPstep_len ldVal instrR qPosts qPost regWP ctrlP
  memEv Trace PEv msgAt li_val)
open Weak.Prom.Ref (Instr two64 aluOp brEval sext)
open Weak.Prom.Ref.Lit (X Y Z)
open PLabel
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode

/-- Hart 0's fixed registers in round `k`. -/
def rB (k : Nat) : List (Nat × Nat) := [(9, X), (11, Y), (12, Z), (13, k), (28, 3)]

theorem rB_reg {k : Nat} {p : Nat × Nat} (hp : p ∈ rB k) : p.1 = 9 ∨ p.1 = 11 ∨ p.1 = 12 ∨ p.1 = 13 ∨ p.1 = 28 := by
  simp only [rB, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl <;> simp

theorem rB_step {s s' : LP} {pc rd v k : Nat} (h : RV s (rB k)) (hs : LPstep s s' pc rd v)
    (hrd : rd = 0 ∨ rd = 5 ∨ rd = 6 ∨ rd = 7 ∨ rd = 14 ∨ rd = 15) : RV s' (rB k) :=
  rv_step h hs (fun p hp => by have := rB_reg hp; omega)

theorem rB_succ {s s' : LP} {pc v k : Nat} (h : RV s (rB k)) (hs : LPstep s s' pc 13 v) (h13 : s'.rd 13 = k + 1) :
    RV s' (rB (k + 1)) := by
  refine ⟨by rw [LPstep_len hs]; exact h.1, fun p hp => ?_⟩
  have hk : ∀ r w, (r, w) ∈ rB k → r ≠ 13 → s'.rd r = w := fun r w hm hr => by
    rw [LPstep_rd hs r (.inl hr)]; exact rv_get h hm
  simp only [rB, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with e | e | e | e | e <;> rw [e]
  · exact hk 9 X (by simp [rB]) (by decide)
  · exact hk 11 Y (by simp [rB]) (by decide)
  · exact hk 12 Z (by simp [rB]) (by decide)
  · exact h13
  · exact hk 28 3 (by simp [rB]) (by decide)

/-- Hart 0's record: stage, round, tenure start, close floor. -/
def F0 (l : Loc) (st : Stg) (k u cf : Nat) : Prop := l.st = st ∧ l.k = k ∧ l.u = u ∧ l.cf = cf ∧ l.ld = none

section h0

variable {hlc : HasLC} {GF : BundledGFunctors} [GhostVarG GF Loc] [InvGS_gen hlc GF]

theorem p0_at {s : LP} {k : Nat} {ins : Instr} (hprog : s.prog = b0) (hpc : s.pc = k)
    (hx : p0[k]? = some (.i ins)) (hpl : (XI.i ins).plain = true) : s.prog[s.pc]? = some ins ∧ XP xs7 s :=
  ⟨atI hprog (by rw [hpc]; exact hx), xp_of (by rw [hprog]; exact xOf_p0) (by rw [hpc]; exact hx) hpl⟩

set_option maxHeartbeats 4000000 in
/-- **ONE ROUND OF HART 0**. -/
theorem h0Round (M : List PMsg) (γ : Nat → GName) (hnoinv : ∀ t a, ¬ cmoAt M isInvalK t a) (k : Nat)
    (hk : k = 1 ∨ k = 2) :
    ⊢ ∀ (s : LP) (ws : PState) (l : Loc) (u cf : Nat), ⌜s.prog = b0 ∧ s.q = [] ∧ s.pc = 0 ∧ RV s (rB k) ∧ fI ws ∧
        F0 l .D0 k u cf ∧ cf ≤ coh ws Lk ∧ u ≤ ws.wVwNew⌝ -∗ gl (γ 0) l -∗
      (∀ (s' : LP) (ws' : PState) (l' : Loc) (u' cf' : Nat), ⌜k + 1 ≠ 3 ∧ s'.prog = b0 ∧ s'.q = [] ∧ s'.pc = 0 ∧
          RV s' (rB (k + 1)) ∧ fI ws' ∧ F0 l' .D0 (k + 1) u' cf' ∧ cf' ≤ coh ws' Lk ∧ u' ≤ ws'.wVwNew⌝ -∗
        gl (γ 0) l' -∗ wpH (hlc := hlc) (GF := GF) M γ 0 s' ws') -∗
      wpH (hlc := hlc) M γ 0 s ws := by
  iintro %s %ws %l %u %cf %hs Hl HK
  obtain ⟨hprog, hq, hpc, hrv, hfi, ⟨hst, hlk, hlu, hlcf, hld⟩, hcf, hu⟩ := hs
  have hT : xOf xs7 (p0.map XI.base) = some p0 := xOf_p0
  have hlen := hrv.1
  have h9 : ∀ s', RV s' (rB k) → s'.rd 9 = X := fun s' h => rv_get h (by simp [rB])
  have h11 : ∀ s', RV s' (rB k) → s'.rd 11 = Y := fun s' h => rv_get h (by simp [rB])
  have h12 : ∀ s', RV s' (rB k) → s'.rd 12 = Z := fun s' h => rv_get h (by simp [rB])
  have h13 : ∀ s', RV s' (rB k) → s'.rd 13 = k := fun s' h => rv_get h (by simp [rB])
  have adLk : ∀ s', RV s' (rB k) → (((s'.rd 9 + 0) % two64 : Nat) : Int) = Lk := fun s' h => by
    rw [h9 s' h]; simp [Lk, X, two64]
  have adCt : ∀ s', RV s' (rB k) → (((s'.rd 11 + 0) % two64 : Nat) : Int) = Ct := fun s' h => by
    rw [h11 s' h]; simp [Ct, Y, two64]
  have heL : ∀ d a c ts' tvs, ¬ isCLd (LStore false false Lk d a c, some ts') tvs := fun _ _ _ _ _ ⟨_, e⟩ => by cases e
  have hsL : ∀ d a c ts' t', ¬ isCSt (LStore false false Lk d a c, some ts') t' := fun _ _ _ _ _ ⟨_, _, _, e⟩ => by
    simp only [Prod.mk.injEq, LStore.injEq] at e; simp [Lk, Ct, X, Y] at e
  have heC : ∀ d a c ts' tvs, ¬ isCLd (LStore false false Ct d a c, some ts') tvs := fun _ _ _ _ _ ⟨_, e⟩ => by cases e
  -- 0: li t1,J
  obtain ⟨hp0', hpl0⟩ := p0_at hprog hpc (rfl : p0[0]? = some (.i (Weak.Prom.Ref.Lit.li 6 J))) rfl
  iapply (wpX_alui hq hpl0 hp0' (by decide))
  iintro %s1 %hs1
  obtain ⟨hP1, hc1, hq1⟩ := LPstep_at hs1 hprog (by rw [hpc])
  have hrv1 := rB_step hrv hs1 (by omega)
  -- 1: sw t1,0(s1) — kfree junk in the lock word (dead phase)
  obtain ⟨hp1, hpl1⟩ := p0_at hP1 hc1 (rfl : p0[1]? = some (.i (Weak.Prom.Ref.Lit.sw 6 9))) rfl
  iapply (wpX_sd (sz := 4) (rs2 := 6) (rs1 := 9) (off := 0) hq1 hpl1 hp1 (by rw [h9 s1 hrv1]; simp [aligned, X, two64]))
  inext
  iintro %σ %ts %o' %hful %hmsg %hcb %hpre HX _
  rw [adLk s1 hrv1] at hmsg hcb ⊢
  obtain ⟨hm, _⟩ := msgAt_take hmsg (by omega)
  have hplk : plk0 ⟨Lk, toBytes (s1.rd 6) 4, some 0, .plain⟩ := ⟨rfl, rfl, toBytes_len _ 4, rfl⟩
  have hcts : cf < ts := by
    have := PF.cohBelow_b0 hcb (by simp [toBytes_len]); simp only [PF.instrR_coh, PF.regWP_coh] at this; omega
  imod xstepS (hlc := hlc) (σ' := nxT σ 0 o' (LStore false false Lk (toBytes (s1.rd 6) 4) (srcR 9) (srcR 6), some ts))
    (by decide) (fun S ls hI hl => ⟨S, inv_ful hI hful hm ⟨0, by decide, rfl, .inl hplk⟩ (lkw_ovC rfl (toBytes_len _ 4))
      (lkw_ovF rfl (toBytes_len _ 4)) (fun _ => ⟨rfl, hplk, by rw [hl, hst]; simp [isD], by rw [hl, hlcf]; exact hcts⟩)
      (heL _ _ _ _) (.inl rfl) (by rw [hl]; exact hld)⟩) $$ HX Hl with ⟨HX, Hl⟩
  imodintro
  iframe HX
  iintro %s2 %hs2
  obtain ⟨hP2, hc2, hq2⟩ := LPstep_at hs2 hP1 (by rw [hc1])
  have hrv2 := rB_step hrv1 hs2 (.inl rfl)
  iapply wpH_gen
  iintro %ws2 %e2
  have hm2 : wsM ws ws2 := by rw [e2]; exact wsM_instrR (wsM_stR (wsM_instrR (wsM_regWP (wsM_refl ws))))
  have hfi2 : fI ws2 := by rw [e2]; exact fI_instrR (fI_stR (fI_instrR (fI_regWP hfi)))
  -- 2: sd t1,0(a1) — kfree junk in the field (dead phase)
  obtain ⟨hp2, hpl2⟩ := p0_at hP2 hc2 (rfl : p0[2]? = some (.i (Weak.Prom.Ref.Lit.sd 6 11))) rfl
  iapply (wpX_sd (sz := 8) (rs2 := 6) (rs1 := 11) (off := 0) hq2 hpl2 hp2 (by rw [h11 s2 hrv2]; simp [aligned, Y, two64]))
  inext
  iintro %σ2 %ts2 %o2 %hful2 %hmsg2 %hcb2 %hpre2 HX _
  rw [adCt s2 hrv2] at hmsg2 hcb2 ⊢
  obtain ⟨hm2', _⟩ := msgAt_take hmsg2 (by omega)
  have hu2 : u < ts2 := by
    have := (PF.stPreA_ge ws2 false false (srcsView ws2 (srcR 11)) (srcsView ws2 (srcR 6))).2.2.2.1
    have := hm2.2.2.2.2; omega
  imod xstep (hlc := hlc) (σ' := nxT σ2 0 o2 (LStore false false Ct (toBytes (s2.rd 6) 8) (srcR 11) (srcR 6), some ts2))
    (Q := fun l' => F0 l' .D1 k u cf ∧ l'.f = ts2) (by decide) (fun S ls hI hl => by
      obtain ⟨S', hS⟩ := inv_h0fld hI (by rw [hl, hst]; simp) hful2 hm2' (by rw [hl, hlu]; exact hu2)
        (fun e => by rw [hl, hst] at e; cases e) (fun e => by rw [hl, hst] at e; cases e)
      refine ⟨S', _, ?_, (by rw [hl] at hS; exact hS)⟩
      exact ⟨⟨by simp [hst], hlk, hlu, hlcf, hld⟩, rfl⟩) $$ HX Hl with ⟨%l1, %hl1, HX, Hl⟩
  obtain ⟨⟨hst1, hlk1, hlu1, hlcf1, hld1⟩, hlf1⟩ := hl1
  imodintro
  iframe HX
  iintro %s3 %hs3
  obtain ⟨hP3, hc3, hq3⟩ := LPstep_at hs3 hP2 (by rw [hc2])
  have hrv3 := rB_step hrv2 hs3 (.inl rfl)
  iapply wpH_gen
  iintro %ws3 %e3
  have hm3 : wsM ws2 ws3 := by rw [e3]; exact wsM_instrR (wsM_stR (wsM_refl _))
  have hfi3 : fI ws3 := by rw [e3]; exact fI_instrR (fI_stR hfi2)
  have hf3 : ts2 ≤ coh ws3 Ct := by
    rw [e3, PF.instrR_coh]; exact PF.storeRun_coh0 _ _ _ _ _ _ _ (by simp [toBytes_len])
  -- 3: sw zero,0(s1) — INITLOCK (a lock-word store of the dead phase)
  obtain ⟨hp3, hpl3⟩ := p0_at hP3 hc3 (rfl : p0[3]? = some (.i (Weak.Prom.Ref.Lit.sw 0 9))) rfl
  have hr0 : ∀ s' : LP, s'.rd 0 = 0 := fun _ => by simp [LP.rd]
  iapply (wpX_sd (sz := 4) (rs2 := 0) (rs1 := 9) (off := 0) hq3 hpl3 hp3 (by rw [h9 s3 hrv3]; simp [aligned, X, two64]))
  inext
  iintro %σ3 %ts3 %o3 %hful3 %hmsg3 %hcb3 %hpre3 HX _
  rw [adLk s3 hrv3, hr0] at hmsg3 hcb3 ⊢
  obtain ⟨hm3', _⟩ := msgAt_take hmsg3 (by omega)
  have hplk3 : plk0 ⟨Lk, toBytes 0 4, some 0, .plain⟩ := ⟨rfl, rfl, toBytes_len _ 4, rfl⟩
  have hcts3 : cf < ts3 := by
    have := PF.cohBelow_b0 hcb3 (by simp [toBytes_len])
    have := hm2.1 Lk; have := hm3.1 Lk
    omega
  imod xstepS (hlc := hlc) (σ' := nxT σ3 0 o3 (LStore false false Lk (toBytes 0 4) (srcR 9) (srcR 0), some ts3))
    (by decide) (fun S ls hI hl => ⟨S, inv_ful hI hful3 hm3' ⟨0, by decide, rfl, .inl hplk3⟩ (lkw_ovC rfl (toBytes_len _ 4))
      (lkw_ovF rfl (toBytes_len _ 4)) (fun _ => ⟨rfl, hplk3, by rw [hl, hst1]; simp [isD], by rw [hl, hlcf1]; exact hcts3⟩)
      (heL _ _ _ _) (.inl rfl) (by rw [hl]; exact hld1)⟩) $$ HX Hl with ⟨HX, Hl⟩
  imodintro
  iframe HX
  iintro %s4 %hs4
  obtain ⟨hP4, hc4, hq4⟩ := LPstep_at hs4 hP3 (by rw [hc3])
  have hrv4 := rB_step hrv3 hs4 (.inl rfl)
  iapply wpH_gen
  iintro %ws4 %e4
  have hm4 : wsM ws3 ws4 := by rw [e4]; exact wsM_instrR (wsM_stR (wsM_refl _))
  have hfi4 : fI ws4 := by rw [e4]; exact fI_instrR (fI_stR hfi3)
  -- 4: li t2,5
  obtain ⟨hp4, hpl4⟩ := p0_at hP4 hc4 (rfl : p0[4]? = some (.i (Weak.Prom.Ref.Lit.li 7 5))) rfl
  iapply (wpX_alui hq4 hpl4 hp4 (by decide))
  iintro %s5 %hs5
  obtain ⟨hP5, hc5, hq5⟩ := LPstep_at hs5 hP4 (by rw [hc4])
  have hrv5 := rB_step hrv4 hs5 (by omega)
  have h7 : s5.rd 7 = 5 := li_val hs5 (by decide) (by rw [hrv4.1]; decide) (by decide)
  -- 5: sd t2,0(a1) — the field's initialisation 5
  obtain ⟨hp5, hpl5⟩ := p0_at hP5 hc5 (rfl : p0[5]? = some (.i (Weak.Prom.Ref.Lit.sd 7 11))) rfl
  iapply (wpX_sd (sz := 8) (rs2 := 7) (rs1 := 11) (off := 0) hq5 hpl5 hp5 (by rw [h11 s5 hrv5]; simp [aligned, Y, two64]))
  inext
  iintro %σ5 %ts5 %o5 %hful5 %hmsg5 %hcb5 %hpre5 HX _
  rw [adCt s5 hrv5, h7] at hmsg5 hcb5 ⊢
  obtain ⟨hm5', _⟩ := msgAt_take hmsg5 (by omega)
  have hu5 : u < ts5 := by
    have := (PF.stPreA_ge (instrR (regWP ws4 7 (srcR 0))) false false (srcsView (instrR (regWP ws4 7 (srcR 0))) (srcR 11))
      (srcsView (instrR (regWP ws4 7 (srcR 0))) (srcR 7))).2.2.2.1
    have := hm2.2.2.2.2; have := hm3.2.2.2.2; have := hm4.2.2.2.2
    simp only [PF.instrR_vwNew, PF.regWP_vwNew] at *; omega
  have hf5 : ts2 < ts5 := by
    have := PF.cohBelow_b0 hcb5 (by simp [toBytes_len]); have := hm4.1 Ct
    simp only [PF.instrR_coh, PF.regWP_coh] at *; omega
  imod xstep (hlc := hlc) (σ' := nxT σ5 0 o5 (LStore false false Ct (toBytes 5 8) (srcR 11) (srcR 7), some ts5))
    (Q := fun l' => F0 l' .D2 k u cf) (by decide) (fun S ls hI hl => by
      obtain ⟨S', hS⟩ := inv_h0fld hI (by rw [hl, hst1]; simp) hful5 hm5' (by rw [hl, hlu1]; exact hu5)
        (fun _ => by rw [hl, hlf1]; exact hf5) (fun _ => rfl)
      refine ⟨S', _, ?_, (by rw [hl] at hS; exact hS)⟩
      exact ⟨by simp [hst1], hlk1, hlu1, hlcf1, hld1⟩) $$ HX Hl with ⟨%l2, %hl2, HX, Hl⟩
  obtain ⟨hst2, hlk2, hlu2, hlcf2, hld2⟩ := hl2
  imodintro
  iframe HX
  iintro %s6 %hs6
  obtain ⟨hP6, hc6, hq6⟩ := LPstep_at hs6 hP5 (by rw [hc5])
  have hrv6 := rB_step hrv5 hs6 (.inl rfl)
  iapply wpH_gen
  iintro %ws6 %e6
  have hm6 : wsM ws4 ws6 := by rw [e6]; exact wsM_instrR (wsM_stR (wsM_instrR (wsM_regWP (wsM_refl _))))
  have hfi6 : fI ws6 := by rw [e6]; exact fI_instrR (fI_stR (fI_instrR (fI_regWP hfi4)))
  -- 6: fence rw,w
  obtain ⟨hp6, hpl6⟩ := p0_at hP6 hc6 (rfl : p0[6]? = some (.i Weak.Prom.Ref.Lit.fRWW)) rfl
  iapply (wpX_fence hq6 hpl6 hp6)
  iintro %s7 %hs7
  obtain ⟨hP7, hc7, hq7⟩ := LPstep_at hs7 hP6 (by rw [hc6])
  have hrv7 := rB_step hrv6 hs7 (.inl rfl)
  -- 7: sb a3,0(a2) — THE PUBLICATION (in place)
  obtain ⟨hp7, hpl7⟩ := p0_at hP7 hc7 (rfl : p0[7]? = some (.i (Weak.Prom.Ref.Lit.sb 13 12))) rfl
  have adZ : (((s7.rd 12 + 0) % two64 : Nat) : Int) = L1 := by rw [h12 s7 hrv7]; simp [L1, Z, two64]
  iapply (wpX_sd (sz := 1) (rs2 := 13) (rs1 := 12) (off := 0) hq7 hpl7 hp7 (by simp [aligned, Nat.mod_one]))
  inext
  iintro %σ7 %ts7 %o7 %hful7 %hmsg7 %_ %_ HX _
  rw [adZ, h13 s7 hrv7] at hmsg7 ⊢
  have hful7' := hful7
  rcases hful7' with ⟨hn, _, _⟩ | ⟨hrc7, _, _, hts7, _⟩
  · exact (hn (Weak.Prom.Own.MPL.relClass_fW _ _ _ _ _ rfl rfl rfl _ _ _ _)).elim
  obtain ⟨hm7', _⟩ := msgAt_take hmsg7 (by omega)
  imod xstep (hlc := hlc) (σ' := nxT σ7 0 o7 (LStore false false L1 (toBytes k 1) (srcR 12) (srcR 13), some ts7))
    (Q := fun l' => F0 l' .P k u cf ∧ l'.p = ts7 ∧ l'.d1 = false ∧ l'.d2 = false) (by decide) (fun S ls hI hl => by
      have hk' : (ls 0).k = k := by rw [hl]; exact hlk2
      obtain ⟨S', hS⟩ := inv_pub (a := srcR 12) (c := srcR 13) hI (by rw [hl]; exact hst2) hful7 hrc7
        (by rw [hk']; exact hm7')
      rw [hk'] at hS
      refine ⟨S', _, ?_, (by rw [hl] at hS; exact hS)⟩
      exact ⟨⟨rfl, hlk2, hlu2, hlcf2, hld2⟩, rfl, rfl, rfl⟩) $$ HX Hl with ⟨%l3, %hl3, HX, Hl⟩
  obtain ⟨⟨hst3, hlk3, hlu3, hlcf3, hld3⟩, hlp3, hd13, hd23⟩ := hl3
  imodintro
  iframe HX
  iintro %s8 %hs8
  obtain ⟨hP8, hc8, hq8⟩ := LPstep_at hs8 hP7 (by rw [hc7])
  have hrv8 := rB_step hrv7 hs8 (.inl rfl)
  iapply wpH_gen
  iintro %ws8 %e8
  have hm8 : wsM ws6 ws8 := by rw [e8]; exact wsM_instrR (wsM_stR (wsM_instrR (wsM_fenceP (wsM_refl _))))
  have hfi8 : fI ws8 := by rw [e8]; exact fI_instrR (fI_stR (fI_instrR (fI_fence hfi6)))
  have hp8 : ts7 ≤ ws8.wVwOld := by rw [e8]; simp; omega
  have hcf8 : cf ≤ coh ws8 Lk := by
    have := hm8.1 Lk; have := hm6.1 Lk; have := hm4.1 Lk; have := hm3.1 Lk; have := hm2.1 Lk; omega
  have hu8 : u ≤ ws8.wVwNew := by
    have := hm8.2.2.2.2; have := hm6.2.2.2.2; have := hm4.2.2.2.2; have := hm3.2.2.2.2; have := hm2.2.2.2.2; omega
  have hRK : ∀ s', RV s' (rB k) → s'.rd 12 = Z ∧ s'.rd 13 = k ∧ s'.regs.length = 32 :=
    fun s' h => ⟨h12 s' h, h13 s' h, h.1⟩
  have hRKs : ∀ s s' pc rd v, RV s (rB k) → LPstep s s' pc rd v → rd = 0 ∨ rd = 5 → RV s' (rB k) :=
    fun s s' pc rd v h hs hrd => rB_step h hs (by omega)
  -- 8–9: wait for acquirer 1's done byte
  ihave Hw1 := waitB (hlc := hlc) M γ 0 (by decide) p0 hT 8 1 k (by decide) (by omega) rfl rfl (by decide)
    (fun s => RV s (rB k)) hRK hRKs hnoinv l3 hld3 (fun _ => setD l3 1)
    (fun σ t v a hmb hv S ls hI hl => ⟨S, by
      have := inv_dnRd (a := a) hI (.inl rfl) (by rw [hl]; exact hst3) hmb (by rw [hl, hlk3]; exact hv)
      rw [hl] at this; exact this⟩) ws8
  iapply Hw1 $$ %s8 %ws8 %⟨hP8, hq8, hc8, hrv8, hfi8, wsM_refl _⟩ Hl
  iintro %s10 %ws10 %t1 %⟨hP10, hq10, hc10, hrv10, hfi10, hm10, -⟩ Hl
  obtain ⟨g1, g2, g3, g4, g5, g6, g7⟩ := setD_st l3 1
  -- 10–11: wait for acquirer 2's done byte
  ihave Hw2 := waitB (hlc := hlc) M γ 0 (by decide) p0 hT 10 2 k (by decide) (by omega) rfl rfl (by decide)
    (fun s => RV s (rB k)) hRK hRKs hnoinv (setD l3 1) (by rw [g7]; exact hld3) (fun _ => setD (setD l3 1) 2)
    (fun σ t v a hmb hv S ls hI hl => ⟨S, by
      have := inv_dnRd (a := a) hI (.inr rfl) (by rw [hl, g1]; exact hst3) hmb (by rw [hl, g6, hlk3]; exact hv)
      rw [hl] at this; exact this⟩) ws10
  iapply Hw2 $$ %s10 %ws10 %⟨hP10, hq10, hc10, hrv10, hfi10, wsM_refl _⟩ Hl
  iintro %s12 %ws12 %t2 %⟨hP12, hq12, hc12, hrv12, hfi12, hm12, -⟩ Hl
  obtain ⟨g1', g2', g3', g4', g5', g6', g7'⟩ := setD_st (setD l3 1) 2
  have hd1 : (setD (setD l3 1) 2).d1 = true := by simp [setD]
  have hd2 : (setD (setD l3 1) 2).d2 = true := by simp [setD]
  -- 12: fence rw,rw
  obtain ⟨hp12, hpl12⟩ := p0_at hP12 hc12 (rfl : p0[12]? = some (.i Weak.Prom.Ref.Lit.fRWRW)) rfl
  iapply (wpX_fence hq12 hpl12 hp12)
  iintro %s13 %hs13
  obtain ⟨hP13, hc13, hq13⟩ := LPstep_at hs13 hP12 (by rw [hc12])
  have hrv13 := rB_step hrv12 hs13 (.inl rfl)
  -- 13: li a4,1
  obtain ⟨hp13, hpl13⟩ := p0_at hP13 hc13 (rfl : p0[13]? = some (.i (Weak.Prom.Ref.Lit.li 14 1))) rfl
  iapply (wpX_alui hq13 hpl13 hp13 (by decide))
  iintro %s14 %hs14
  obtain ⟨hP14, hc14, hq14⟩ := LPstep_at hs14 hP13 (by rw [hc13])
  have hrv14 := rB_step hrv13 hs14 (by omega)
  have h14 : s14.rd 14 = 1 := li_val hs14 (by decide) (by rw [hrv13.1]; decide) (by decide)
  iapply wpH_gen
  iintro %ws14 %e14
  have hfi14 : fI ws14 := by rw [e14]; exact fI_instrR (fI_regWP (fI_instrR (fI_fence hfi12)))
  have hm14 : wsM ws12 ws14 := by rw [e14]; exact wsM_instrR (wsM_regWP (wsM_instrR (wsM_fenceP (wsM_refl _))))
  have hp14 : (setD (setD l3 1) 2).p ≤ ws14.wVwNew := by
    rw [g5', g5, hlp3, e14]
    have := hm10.2.2.1; have := hm12.2.2.1
    simp only [PF.instrR_vwNew, PF.regWP_vwNew, PF.fence_vwNew, if_true]; omega
  -- 14–17: xv6's acquire (pipeclose)
  ihave Ha := amoB (hlc := hlc) M γ 0 p0 hT 14 rfl rfl rfl rfl (by decide)
    (fun s => RV s (rB k) ∧ s.rd 14 = 1) (fun s h => ⟨h9 s h.1, h.2, h.1.1⟩)
    (fun s s' pc rd v h hs hrd => ⟨rB_step h.1 hs (by omega), by rw [LPstep_rd hs 14 (by omega)]; exact h.2⟩)
    hnoinv (setD (setD l3 1) 2) (.inl ⟨rfl, by rw [g1', g1]; exact hst3⟩) ws14 hp14
  iapply Ha $$ %s14 %ws14 %⟨hP14, hq14, hc14, ⟨hrv14, h14⟩, hfi14, wsM_refl _⟩ Hl
  iintro %s18 %ws18 %u' %⟨hP18, hq18, hc18, ⟨hrv18, _⟩, hfi18, hm18, hu18r, hu18w⟩ Hl
  rw [show hS 0 = .H0 by simp [hS]]
  -- 18, 19: sd a0,16(s1); sd zero,16(s1)
  ihave Hp1 := pcB (hlc := hlc) M γ 0 (by decide) p0 hT 18 10 rfl (fun s => RV s (rB k))
    (fun s h => ⟨h9 s h, h.1⟩) (fun s s' pc v h hs => rv_step h hs (fun _ _ => .inr rfl))
    { setD (setD l3 1) 2 with st := .H0, u := u' } (by simp only; rw [g7', g7]; exact hld3)
  iapply Hp1 $$ %s18 %ws18 %⟨hP18, hq18, hc18, hrv18, hfi18⟩ Hl
  iintro %s19 %ws19 %⟨hP19, hq19, hc19, hrv19, hfi19, hm19⟩ Hl
  ihave Hp2 := pcB (hlc := hlc) M γ 0 (by decide) p0 hT 19 0 rfl (fun s => RV s (rB k))
    (fun s h => ⟨h9 s h, h.1⟩) (fun s s' pc v h hs => rv_step h hs (fun _ _ => .inr rfl))
    { setD (setD l3 1) 2 with st := .H0, u := u' } (by simp only; rw [g7', g7]; exact hld3)
  iapply Hp2 $$ %s19 %ws19 %⟨hP19, hq19, hc19, hrv19, hfi19⟩ Hl
  iintro %s20 %ws20 %⟨hP20, hq20, hc20, hrv20, hfi20, hm20⟩ Hl
  -- 20: fence rw,w
  obtain ⟨hp20, hpl20⟩ := p0_at hP20 hc20 (rfl : p0[20]? = some (.i Weak.Prom.Ref.Lit.fRWW)) rfl
  iapply (wpX_fence hq20 hpl20 hp20)
  iintro %s21 %hs21
  obtain ⟨hP21, hc21, hq21⟩ := LPstep_at hs21 hP20 (by rw [hc20])
  have hrv21 := rB_step hrv20 hs21 (.inl rfl)
  -- 21: sw zero,0(s1) — THE CLOSING RELEASE (in place): the death of this lifetime
  obtain ⟨hp21, hpl21⟩ := p0_at hP21 hc21 (rfl : p0[21]? = some (.i (Weak.Prom.Ref.Lit.sw 0 9))) rfl
  iapply (wpX_sd (sz := 4) (rs2 := 0) (rs1 := 9) (off := 0) hq21 hpl21 hp21 (by rw [h9 s21 hrv21]; simp [aligned, X, two64]))
  inext
  iintro %σ21 %ts21 %o21 %hful21 %hmsg21 %_ %_ HX _
  rw [adLk s21 hrv21, hr0] at hmsg21 ⊢
  have hful21' := hful21
  rcases hful21' with ⟨hn, _, _⟩ | ⟨hrc21, _, _, hts21, _⟩
  · exact (hn (Weak.Prom.Own.MPL.relClass_fW _ _ _ _ _ rfl rfl rfl _ _ _ _)).elim
  obtain ⟨hm21', _⟩ := msgAt_take hmsg21 (by omega)
  imod xstep (hlc := hlc) (σ' := nxT σ21 0 o21 (LStore false false Lk (toBytes 0 4) (srcR 9) (srcR 0), some ts21))
    (Q := fun l' => F0 l' .D0 (k + 1) u' ts21) (by decide) (fun S ls hI hl => by
      obtain ⟨S', hS⟩ := inv_close (a := srcR 9) (c := srcR 0) hI (by rw [hl]) (by rw [hl]; simp only; exact hd1)
        (by rw [hl]; simp only; exact hd2) (by rw [hl]; simp only; rw [g6', g6, hlk3]; omega) hful21 hrc21 hm21'
      refine ⟨S', _, ?_, (by rw [hl] at hS; exact hS)⟩
      exact ⟨rfl, by simp only; rw [g6', g6, hlk3], rfl, rfl, by simp only; rw [g7', g7]; exact hld3⟩)
    $$ HX Hl with ⟨%l5, %hl5, HX, Hl⟩
  imodintro
  iframe HX
  iintro %s22 %hs22
  obtain ⟨hP22, hc22, hq22⟩ := LPstep_at hs22 hP21 (by rw [hc21])
  have hrv22 := rB_step hrv21 hs22 (.inl rfl)
  iapply wpH_gen
  iintro %ws22 %e22
  have hfi22 : fI ws22 := by rw [e22]; exact fI_instrR (fI_stR (fI_instrR (fI_fence hfi20)))
  have hcf22 : ts21 ≤ coh ws22 Lk := by
    rw [e22, PF.instrR_coh]; exact PF.storeRun_coh0 _ _ _ _ _ _ _ (by simp [toBytes_len])
  have hu22 : u' ≤ ws22.wVwNew := by
    have := hm19.2.2.2.2; have := hm20.2.2.2.2
    rw [e22]; simp only [PF.instrR_vwNew, PF.storeRun_vwNew, PF.fence_vwNew]; split <;> omega
  -- 22: addi a3,a3,1
  obtain ⟨hp22, hpl22⟩ := p0_at hP22 hc22 (rfl : p0[22]? = some (.i (Weak.Prom.Ref.Lit.addi 13 13 1))) rfl
  iapply (wpX_alui hq22 hpl22 hp22 (by decide))
  iintro %s23 %hs23
  obtain ⟨hP23, hc23, hq23⟩ := LPstep_at hs23 hP22 (by rw [hc22])
  have h13' : s23.rd 13 = k + 1 := by
    rw [LPstep_rd_eq hs23 (by decide) (by rw [hrv22.1]; decide), h13 s22 hrv22]
    simp [aluOp, two64]; omega
  have hrv23 : RV s23 (rB (k + 1)) := rB_succ hrv22 hs23 h13'
  -- 23: bne a3,t3,0
  have h28 : s23.rd 28 = 3 := rv_get hrv23 (by simp [rB])
  iapply (wpX_brx hq23 (by rw [hP23]; exact hT) (by rw [hc23]; rfl) (by rw [hP23]; decide))
  iintro %s24 %hs24
  by_cases hk3 : k + 1 = 3
  · have hbr : (if brEval .ne (s23.rd 13) (s23.rd 28) then 0 else s23.pc + 1) = 24 := by
      simp [brEval, h13', h28, hk3, hc23]
    rw [hbr] at hs24
    obtain ⟨hP24, hc24, hq24⟩ := LPstep_at hs24 hP23 rfl
    iapply (wpX_end hq24 (by rw [hP24, hc24]; decide))
  · have hbr : (if brEval .ne (s23.rd 13) (s23.rd 28) then 0 else s23.pc + 1) = 0 := by
      simp [brEval, h13', h28]; omega
    rw [hbr] at hs24
    obtain ⟨hP24, hc24, hq24⟩ := LPstep_at hs24 hP23 rfl
    iapply HK $$ %s24 %_ %l5 %u' %ts21 %⟨hk3, hP24, hq24, hc24, rv_step hrv23 hs24 (fun _ _ => .inr rfl),
      fI_instrR (fI_ctrlP (fI_instrR (fI_regWP hfi22))), hl5, hcf22, hu22⟩ Hl

end h0

end Weak.Prom.OB.E4
