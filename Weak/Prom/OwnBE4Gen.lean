/-
Weak/Prom: **E-b4 — the text-generic blocks** (stage E-b4): xv6-shaped pieces of hart text, stated for ANY text `T`
of the test holding the block at offset `w`, with the rest of the hart's proof as a continuation (reusable as S5
leaves).

* `waitB` — `lbu t0,o(a2); bne t0,a3,w`: a flag wait; when the byte reads the round `k` the pure step `hpure`
  updates the hart's record (the publication read, the done-byte read); the read source is below
  `max vrOld vwOld` afterwards (the forward-bank invariant `fI`);
* `amoB` — xv6's acquire spin loop `mv a5,a4; amoswap.w.aq a5,a5,(s1); sext.w a5,a5; bnez a5,w` (`inv_amoS`,
  `inv_amoF`): on exit the hart owns the lock with tenure `u` below both new-floors;
* `pcB` — `sd rX,16(s1)`: a store to the untracked `cpu` field.
Track-neutral machine facts used from E-a4 (OwnAE4Gen.lean / OwnAPipeH1.lean, listed in PROGRESS-Eb4.md): `fI`,
`wsM` and their step lemmas, `le_fwd`, `postA`, `postA_st`, `postA_vr`.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.OwnBE4Iris
import Weak.Prom.OwnAE4Gen

namespace Weak.Prom.OB.E4

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Own (OSt upd upd_eq upd_ne fulO rmwOk)
open Weak.Prom.Own.X (xOW XP xp_of)
open Weak.Prom.OA (XI xOf xStep Lk Ct addiwV isCLd isCSt)
open Weak.Prom.OA.P (L1 postA postA_vr)
open Weak.Prom.OA.C (Pc)
open Weak.Prom.OA.E4 (q7 img7 xs7 atI fI wsM wsM_trans fI_ld fI_st wsM_ld wsM_st wsM_fence fI_of wsM_eq le_fwd
  postA_st)
open Weak.Prom.PF (LPstep LPstep_at LPstep_rd LPstep_rd_eq LPstep_len ldVal instrR qPosts qPost amoD regWP ctrlP memEv Trace PEv msgAt)
open Weak.Prom.Ref (Instr two64 aluOp brEval sext)
open Weak.Prom.Ref.Lit (X Y Z)
open PLabel
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode

/-! ## Machine-state facts through a step (pattern-directed: compose them outside-in) -/

theorem fI_instrR {ws : PState} (h : fI ws) : fI (instrR ws) := fI_of h rfl rfl
theorem fI_regWP {ws : PState} {r : Nat} {srcs : List Dsrc} (h : fI ws) : fI (regWP ws r srcs) := fI_of h rfl rfl
theorem fI_ctrlP {ws : PState} {srcs : List Dsrc} (h : fI ws) : fI (ctrlP ws srcs) := fI_of h rfl rfl
theorem fI_fence {ws : PState} {a b c d : Bool} (h : fI ws) : fI (fencePost ws a b c d) := fI_of h rfl rfl
theorem fI_qreg {ws : PState} {r : Nat} {d : List Dsrc} (h : fI ws) : fI (qPosts ws (regWL r d ++ [LInstr])) := by
  unfold regWL; split
  · exact fI_instrR h
  · exact fI_instrR (fI_regWP h)
theorem fI_stR {ws : PState} {rl : Bool} {va fv : Nat} {base : Int} {n ts : Nat} (h : fI ws) :
    fI (storeRun ws rl va fv base n ts) := fI_st h rl va fv base n ts
theorem fI_ldR {ws : PState} {aq rl : Bool} {va : Nat} {base : Int} {tvs : List (Nat × BitVec 8)} (h : fI ws) :
    fI (loadRun ws aq rl va base tvs) := fI_ld h aq rl va base tvs

theorem wsM_instrR {a b : PState} (h : wsM a b) : wsM a (instrR b) := wsM_trans h (wsM_eq (fun _ => rfl) rfl rfl rfl rfl)
theorem wsM_regWP {a b : PState} {r : Nat} {srcs : List Dsrc} (h : wsM a b) : wsM a (regWP b r srcs) :=
  wsM_trans h (wsM_eq (fun _ => rfl) rfl rfl rfl rfl)
theorem wsM_ctrlP {a b : PState} {srcs : List Dsrc} (h : wsM a b) : wsM a (ctrlP b srcs) :=
  wsM_trans h (wsM_eq (fun _ => rfl) rfl rfl rfl rfl)
theorem wsM_fenceP {a b : PState} {p q r t : Bool} (h : wsM a b) : wsM a (fencePost b p q r t) :=
  wsM_trans h (wsM_fence b p q r t)
theorem wsM_qreg {a b : PState} {r : Nat} {d : List Dsrc} (h : wsM a b) : wsM a (qPosts b (regWL r d ++ [LInstr])) := by
  unfold regWL; split
  · exact wsM_instrR h
  · exact wsM_instrR (wsM_regWP h)
theorem wsM_stR {a b : PState} {rl : Bool} {va fv : Nat} {base : Int} {n ts : Nat} (h : wsM a b) :
    wsM a (storeRun b rl va fv base n ts) := wsM_trans h (wsM_st b rl va fv base n ts)
theorem wsM_ldR {a b : PState} {aq rl : Bool} {va : Nat} {base : Int} {tvs : List (Nat × BitVec 8)} (h : wsM a b) :
    wsM a (loadRun b aq rl va base tvs) := wsM_trans h (wsM_ld b aq rl va base tvs)

section gen

variable {hlc : HasLC} {GF : BundledGFunctors} [GhostVarG GF Loc] [InvGS_gen hlc GF]

/-- Hart `h`'s wp under the state interpretation. -/
abbrev wpH (M : List PMsg) (γ : Nat → GName) (h : Nat) (s : LP) (ws : PState) : IProp GF :=
  wpX (hlc := hlc) xs7 (XX (GF := GF) M γ) img7 M h s ws

/-- The state after `lbu t0,o(a2); bne t0,a3`. -/
abbrev wsW (ws : PState) (o : Nat) (tvs : List (Nat × BitVec 8)) : PState :=
  instrR (ctrlP (qPosts (loadRun ws false false (srcsView ws (srcR 12)) (L1 + o) tvs)
    (regWL 5 [.DLdRes] ++ [LInstr])) (srcR 5 ++ srcR 13))

theorem ldval1 (t : Nat) (v : BitVec 8) : ldVal false 1 [(t, v)] % two64 = v.toNat := by
  have := v.isLt
  simp [ldVal, ofBytes, Weak.Prom.Ref.bytesVal, two64]; omega

/-- **THE FLAG WAIT** (Löb at `pc = w`). -/
theorem waitB (M : List PMsg) (γ : Nat → GName) (h : Nat) (hh : h < 3) (T : List XI)
    (hT : xOf xs7 (T.map XI.base) = some T) (w o k : Nat) (ho : o < 3) (hk : 0 < k ∧ k < 256)
    (hx0 : T[w]? = some (.i (.load 1 false 5 12 o))) (hx1 : T[w + 1]? = some (.i (.br .ne 5 13 w)))
    (hxl : w ≤ T.length) (RK : LP → Prop) (hR : ∀ s, RK s → s.rd 12 = Z ∧ s.rd 13 = k ∧ s.regs.length = 32)
    (hRs : ∀ s s' pc rd v, RK s → LPstep s s' pc rd v → rd = 0 ∨ rd = 5 → RK s')
    (hnoinv : ∀ t a, ¬ cmoAt M isInvalK t a) (l : Loc) (hld : l.ld = none) (lf : Nat → Loc)
    (hpure : ∀ (σ : TSt (List Nat)) t v a, memByte img7 (M.take σ.o.n) t (L1 + o) = some v → v.toNat = k →
      ∀ S ls, Inv M σ S ls → ls h = l →
        ∃ S', Inv M (nxT σ h σ.o (LLoad false false (L1 + o) [(t, v)] a, none)) S' (upd ls h (lf t)))
    (ws0 : PState) :
    ⊢ ∀ (s : LP) (ws : PState), ⌜s.prog = T.map XI.base ∧ s.q = [] ∧ s.pc = w ∧ RK s ∧ fI ws ∧ wsM ws0 ws⌝ -∗
      gl (γ h) l -∗
      (∀ (s' : LP) (ws' : PState) (t : Nat), ⌜s'.prog = T.map XI.base ∧ s'.q = [] ∧ s'.pc = w + 2 ∧ RK s' ∧
          fI ws' ∧ wsM ws0 ws' ∧ t ≤ max ws'.wVrOld ws'.wVwOld⌝ -∗ gl (γ h) (lf t) -∗ wpH (hlc := hlc) (GF := GF) M γ h s' ws') -∗
      wpH (hlc := hlc) M γ h s ws := by
  iloeb as IH
  iintro %s %ws %hs Hl HK
  obtain ⟨hprog, hq, hpc, hrk, hfi, hmo⟩ := hs
  obtain ⟨h12, h13, hlen⟩ := hR s hrk
  have hX' : xOf xs7 s.prog = some T := by rw [hprog]; exact hT
  have hZo : (Z + o) % two64 = Z + o := Nat.mod_eq_of_lt (by simp [Z, two64]; omega)
  have hadr : (((s.rd 12 + o) % two64 : Nat) : Int) = L1 + o := by rw [h12, hZo]; simp [L1]
  have hpl : XP xs7 s := xp_of hX' (by rw [hpc]; exact hx0) rfl
  iapply (wpX_ld (sz := 1) (sgn := false) (rd := 5) (rs1 := 12) (off := o) hq hpl (atI hprog (by rw [hpc]; exact hx0))
    (by rw [h12]; simp [aligned, Nat.mod_one]))
  inext
  iintro %σ %tvs %hl0 %hlo HX _
  obtain ⟨t0, v0, r0, rfl⟩ := Weak.Prom.PF.tvs_cons hl0 (by decide)
  have hr0 : r0 = [] := by simpa using hl0
  subst hr0
  rw [hadr] at hlo ⊢
  obtain ⟨⟨hmb, _⟩, _⟩ := hlo
  have hnc : ∀ tvs, ¬ isCLd (LLoad false false (L1 + o) [(t0, v0)] (srcR 12), none) tvs := fun tvs ⟨_, e⟩ => by
    simp only [Prod.mk.injEq, LLoad.injEq] at e; simp [L1, Ct, Weak.Prom.Ref.Lit.Z, Weak.Prom.Ref.Lit.Y] at e; omega
  have hns : ∀ ts, ¬ isCSt (LLoad false false (L1 + o) [(t0, v0)] (srcR 12), none) ts := fun ts ⟨_, _, _, e⟩ => by
    cases e
  -- the post-state facts
  have hfi2 : fI (wsW ws o [(t0, v0)]) := fI_of (fI_ld hfi false false (srcsView ws (srcR 12)) (L1 + o) _) rfl rfl
  have hmo2 : wsM ws0 (wsW ws o [(t0, v0)]) := wsM_trans (wsM_trans hmo
    (wsM_ld ws false false (srcsView ws (srcR 12)) (L1 + o) _)) (wsM_eq (fun _ => rfl) rfl rfl rfl rfl)
  have hle : t0 ≤ max (wsW ws o [(t0, v0)]).wVrOld (wsW ws o [(t0, v0)]).wVwOld := by
    have hb0 := (PF.loadRun_b0 ws false false (srcsView ws (srcR 12)) (L1 + o) t0 v0 []).2.1
    have hvo := (PF.loadRun_mono ws false false (srcsView ws (srcR 12)) (L1 + o) [(t0, v0)]).2.2.1
    simp only [regWL, qPosts, qPost, PF.regWP_vrOld, PF.instrR_vrOld, PF.ctrlP_vrOld, PF.regWP_vwOld, PF.instrR_vwOld,
      PF.ctrlP_vwOld, show (5 : Nat) ≠ 0 by decide, if_false, List.singleton_append]
    rcases le_fwd ws false (L1 + o) t0 with h1 | ⟨vf, h1⟩
    · omega
    · have := hfi _ _ _ h1; omega
  by_cases hz : v0.toNat = k
  · imod xstep (hlc := hlc) (σ' := nxT σ h σ.o (LLoad false false (L1 + o) [(t0, v0)] (srcR 12), none))
      (Q := fun l' => l' = lf t0) hh (fun S ls hI hl => by
        obtain ⟨S', hS⟩ := hpure σ t0 v0 (srcR 12) hmb hz S ls hI hl
        exact ⟨S', lf t0, rfl, hS⟩) $$ HX Hl with ⟨%l', %e, HX, Hl⟩
    subst e
    imodintro
    iframe HX
    iintro %s1 %hs1
    obtain ⟨hP1, hc1, hq1⟩ := LPstep_at hs1 hprog (by rw [hpc])
    have rk1 := hRs s s1 _ _ _ hrk hs1 (.inr rfl)
    have e5 : s1.rd 5 = v0.toNat := by rw [LPstep_rd_eq hs1 (by decide) (by omega), ldval1]
    have e13 : s1.rd 13 = k := (hR s1 rk1).2.1
    iapply (wpX_brx hq1 (by rw [hP1]; exact hT) (by rw [hc1]; exact hx1) (by rw [hP1, List.length_map]; exact hxl))
    iintro %s2 %hs2
    have hbr : (if brEval .ne (s1.rd 5) (s1.rd 13) then w else s1.pc + 1) = w + 2 := by
      simp [brEval, e5, e13, hz, hc1]
    rw [hbr] at hs2
    obtain ⟨hP2, hc2, hq2⟩ := LPstep_at hs2 hP1 rfl
    have rk2 := hRs s1 s2 _ _ _ rk1 hs2 (.inl rfl)
    iapply HK $$ %s2 %(wsW ws o [(t0, v0)]) %t0 %⟨hP2, hq2, hc2, rk2, hfi2, hmo2, hle⟩ Hl
  · imod xstepS (hlc := hlc) (σ' := nxT σ h σ.o (LLoad false false (L1 + o) [(t0, v0)] (srcR 12), none)) hh
      (fun S ls hI hl => ⟨S, inv_ld hI hnc hns (by rw [hl]; exact hld)⟩) $$ HX Hl with ⟨HX, Hl⟩
    imodintro
    iframe HX
    iintro %s1 %hs1
    obtain ⟨hP1, hc1, hq1⟩ := LPstep_at hs1 hprog (by rw [hpc])
    have rk1 := hRs s s1 _ _ _ hrk hs1 (.inr rfl)
    have e5 : s1.rd 5 = v0.toNat := by rw [LPstep_rd_eq hs1 (by decide) (by omega), ldval1]
    have e13 : s1.rd 13 = k := (hR s1 rk1).2.1
    iapply (wpX_brx hq1 (by rw [hP1]; exact hT) (by rw [hc1]; exact hx1) (by rw [hP1, List.length_map]; exact hxl))
    iintro %s2 %hs2
    have hbr : (if brEval .ne (s1.rd 5) (s1.rd 13) then w else s1.pc + 1) = w := by
      simp [brEval, e5, e13, hz]
    rw [hbr] at hs2
    obtain ⟨hP2, hc2, hq2⟩ := LPstep_at hs2 hP1 rfl
    have rk2 := hRs s1 s2 _ _ _ rk1 hs2 (.inl rfl)
    iapply IH $$ %s2 %(wsW ws o [(t0, v0)]) %⟨hP2, hq2, hc2, rk2, hfi2, hmo2⟩ Hl HK

theorem amoD_one (tvs : List (Nat × BitVec 8)) : amoD .swap 4 1 tvs = toBytes 1 4 := by
  simp [amoD, Weak.Prom.Ref.amoOp]

theorem postA_vw (ws : PState) (base : Int) (tvs : List (Nat × BitVec 8)) (ts n : Nat) :
    ts ≤ (postA ws 9 base tvs ts n).wVwNew := by
  simp only [postA, regWL, show (15 : Nat) ≠ 0 by decide, if_false, List.singleton_append, qPosts, qPost,
    PF.instrR_vwNew, PF.ctrlP_vwNew, PF.regWP_vwNew, PF.amoPost_vwNew, if_true]
  omega

/-- **XV6's ACQUIRE SPIN LOOP** (Löb at `pc = w`, `mv a5,a4`). -/
theorem amoB (M : List PMsg) (γ : Nat → GName) (h : Nat) (T : List XI) (hT : xOf xs7 (T.map XI.base) = some T)
    (w : Nat) (hx0 : T[w]? = some (.i (.alu .add 15 0 14)))
    (hx1 : T[w + 1]? = some (.i (Weak.Prom.Ref.Lit.amoswapW true false 15 15 9)))
    (hx2 : T[w + 2]? = some (.addiw 15 15 0)) (hx3 : T[w + 3]? = some (.i (.br .ne 15 0 w))) (hxl : w ≤ T.length)
    (RK : LP → Prop) (hR : ∀ s, RK s → s.rd 9 = X ∧ s.rd 14 = 1 ∧ s.regs.length = 32)
    (hRs : ∀ s s' pc rd v, RK s → LPstep s s' pc rd v → rd = 0 ∨ rd = 15 → RK s')
    (hnoinv : ∀ t a, ¬ cmoAt M isInvalK t a) (l : Loc)
    (hacq : (h = 0 ∧ l.st = .P) ∨ ((h = 1 ∨ h = 2) ∧ l.st = .A)) (ws0 : PState) (hp0 : l.p ≤ ws0.wVwNew) :
    ⊢ ∀ (s : LP) (ws : PState), ⌜s.prog = T.map XI.base ∧ s.q = [] ∧ s.pc = w ∧ RK s ∧ fI ws ∧ wsM ws0 ws⌝ -∗
      gl (γ h) l -∗
      (∀ (s' : LP) (ws' : PState) (u : Nat), ⌜s'.prog = T.map XI.base ∧ s'.q = [] ∧ s'.pc = w + 4 ∧ RK s' ∧
          fI ws' ∧ wsM ws0 ws' ∧ u ≤ ws'.wVrNew ∧ u ≤ ws'.wVwNew⌝ -∗ gl (γ h) { l with st := hS h, u := u } -∗
        wpH (hlc := hlc) (GF := GF) M γ h s' ws') -∗
      wpH (hlc := hlc) M γ h s ws := by
  have hh : h < 3 := by rcases hacq with ⟨e, _⟩ | ⟨e, _⟩ <;> omega
  iloeb as IH
  iintro %s %ws %hs Hl HK
  obtain ⟨hprog, hq, hpc, hrk, hfi, hmo⟩ := hs
  obtain ⟨h9, h14, hlen⟩ := hR s hrk
  have hX' : xOf xs7 s.prog = some T := by rw [hprog]; exact hT
  -- mv a5,a4
  iapply (wpX_alu hq (xp_of hX' (by rw [hpc]; exact hx0) rfl) (atI hprog (by rw [hpc]; exact hx0)) (by decide))
  iintro %s1 %hs1
  obtain ⟨hP1, hc1, hq1⟩ := LPstep_at hs1 hprog (by rw [hpc])
  have rk1 := hRs s s1 _ _ _ hrk hs1 (.inr rfl)
  obtain ⟨h9', _, hlen1⟩ := hR s1 rk1
  have e15 : s1.rd 15 = 1 := by
    rw [LPstep_rd_eq hs1 (by decide) (by omega), h14]; simp [aluOp, LP.rd, two64]
  have hX1 : xOf xs7 s1.prog = some T := by rw [hP1]; exact hT
  -- amoswap.w.aq a5,a5,(s1)
  iapply (wpX_amo hq1 (xp_of hX1 (by rw [hc1]; exact hx1) rfl) (atI hP1 (by rw [hc1]; exact hx1))
    (by rw [h9']; simp [aligned, X]))
  inext
  iintro %σ %tvs %ts %o' %hl4 %hful %hok HX _
  rw [e15, amoD_one, h9'] at hok ⊢
  obtain ⟨_, hmsg, hlo, hexc, hcoh, hpre⟩ := hok
  obtain ⟨t0, b0, rest, rfl⟩ := Weak.Prom.PF.tvs_cons hl4 (by decide)
  have hrl : rest.length = 3 := by simpa using hl4
  have hts1 : 1 ≤ ts := by
    rcases hful with ⟨_, h1, _⟩ | ⟨_, _, _, h1, _⟩
    · have := (List.getElem?_eq_some_iff.1 (Weak.Prom.Own.MP.take_get hmsg)); omega
    · omega
  obtain ⟨hmA, htn⟩ := msgAt_take hmsg hts1
  have hmA' : msgAt M ts = some (acqM h) := hmA
  have hne : ∀ tvs', ¬ isCLd (LRmw true false Lk ((t0, b0) :: rest) (toBytes 1 4) (srcR 9) (srcR 15), some ts) tvs' :=
    fun _ ⟨_, e⟩ => by cases e
  have hns : ∀ ts', ¬ isCSt (LRmw true false Lk ((t0, b0) :: rest) (toBytes 1 4) (srcR 9) (srcR 15), some ts) ts' :=
    fun _ ⟨_, _, _, e⟩ => by cases e
  -- the post-state facts
  have hfi1 : fI (instrR (PF.regWP ws 15 (srcR 0 ++ srcR 14))) := fI_of hfi rfl rfl
  have hmo1 : wsM ws0 (instrR (PF.regWP ws 15 (srcR 0 ++ srcR 14))) := wsM_trans hmo (wsM_eq (fun _ => rfl) rfl rfl rfl rfl)
  obtain ⟨hfi4, hmo4, _⟩ := postA_st (instrR (PF.regWP ws 15 (srcR 0 ++ srcR 14))) (X : Int) ((t0, b0) :: rest) ts
    (toBytes 1 4).length hfi1
  have hvr4 := (postA_vr (instrR (PF.regWP ws 15 (srcR 0 ++ srcR 14))) 9 (X : Int) ((t0, b0) :: rest) ts
    (toBytes 1 4).length).2
  have hvw4 := postA_vw (instrR (PF.regWP ws 15 (srcR 0 ++ srcR 14))) (X : Int) ((t0, b0) :: rest) ts
    (toBytes 1 4).length
  have hmo4' := wsM_trans hmo1 hmo4
  have hpts : l.p < ts := by
    have a1 := (PF.stPre_ge (loadRun (instrR (PF.regWP ws 15 (srcR 0 ++ srcR 14))) true false
      (srcsView (instrR (PF.regWP ws 15 (srcR 0 ++ srcR 14))) (srcR 9)) (X : Int) ((t0, b0) :: rest)) false
      (srcsView (instrR (PF.regWP ws 15 (srcR 0 ++ srcR 14))) (srcR 9))
      (srcsView (instrR (PF.regWP ws 15 (srcR 0 ++ srcR 14))) (srcR 15))).2.2.2.1
    have a2 := (PF.loadRun_mono (instrR (PF.regWP ws 15 (srcR 0 ++ srcR 14))) true false
      (srcsView (instrR (PF.regWP ws 15 (srcR 0 ++ srcR 14))) (srcR 9)) (X : Int) ((t0, b0) :: rest)).2.2.2.2.2.2.2.2.1
    have a3 := hmo.2.2.2.2
    simp only [PF.instrR_vwNew, PF.regWP_vwNew] at a2
    omega
  -- success or failure
  have hw4 := Own.X.L1c.ofBytes4_lt hl4
  by_cases hsucc : ofBytes (((t0, b0) :: rest).map Prod.snd) = 0
  · have hb0 : b0 = 0 := Own.Lk1c.amo_x5 hrl (by rw [hsucc]; decide)
    obtain ⟨⟨hmb0, _⟩, _⟩ := hlo
    rw [hb0] at hmb0
    have ht0 : t0 < ts := by
      have c1 := PF.cohBelow_b0 hcoh (by simp [toBytes_len])
      have c2 := PF.loadRun_coh0 (instrR (PF.regWP ws 15 (srcR 0 ++ srcR 14))) true false
        (srcsView (instrR (PF.regWP ws 15 (srcR 0 ++ srcR 14))) (srcR 9)) (X : Int) t0 b0 rest
      omega
    have hcl : clean M h t0 ts := by
      intro t a1 a2 ⟨m, hm, hb⟩
      refine Classical.byContradiction fun hne' => ?_
      apply hexc.1
      refine ⟨t, a1, by omega, m, ?_, hb, fun e => hne' (by rw [au_msg (by omega) hm, e])⟩
      rw [List.getElem?_take, if_pos (by omega)]; rw [← msgAt_sub (by omega)]; exact hm
    imod xstep (hlc := hlc) (σ' := nxT σ h o' (LRmw true false Lk ((t0, b0) :: rest) (toBytes 1 4) (srcR 9)
        (srcR 15), some ts)) (Q := fun l' => ∃ u, u ≤ ts ∧ l' = { l with st := hS h, u := u }) hh
      (fun S ls hI hl => by
        have hA : acqSt ls h := by
          rcases hacq with ⟨rfl, e⟩ | ⟨hh', e⟩
          · exact .inl ⟨rfl, by rw [hl]; exact e⟩
          · exact .inr ⟨hh', by rw [hl]; exact e⟩
        obtain ⟨S', u, hu, hS⟩ := inv_amoS hI hA hful hmA' hmb0 ht0 hcl
          (by rw [hl]; exact hpts) hne hns
        exact ⟨S', _, ⟨u, hu, by rw [hl]⟩, hS⟩) $$ HX Hl with ⟨%l', %hq', HX, Hl⟩
    obtain ⟨u, hu, rfl⟩ := hq'
    imodintro
    iframe HX
    iintro %s2 %hs2
    obtain ⟨hP2, hc2, hq2⟩ := LPstep_at hs2 hP1 (by rw [hc1])
    have rk2 := hRs s1 s2 _ _ _ rk1 hs2 (.inr rfl)
    have e15' : s2.rd 15 = Weak.Prom.Ref.sext 4 (ofBytes (((t0, b0) :: rest).map Prod.snd)) % two64 :=
      LPstep_rd_eq hs2 (by decide) (by rw [hlen1]; omega)
    have hX2 : xOf xs7 s2.prog = some T := by rw [hP2]; exact hT
    iapply (wpX_addiw hq2 hX2 (by rw [hc2]; exact hx2) (by decide))
    iintro %s3 %hs3
    obtain ⟨hP3, hc3, hq3⟩ := LPstep_at hs3 hP2 (by rw [hc2])
    have rk3 := hRs s2 s3 _ _ _ rk2 hs3 (.inr rfl)
    have e15'' : s3.rd 15 = 0 := by
      rw [LPstep_rd_eq hs3 (by decide) (by rw [LPstep_len hs2, hlen1]; omega), e15']
      exact (Own.X.L1c.addiw_sext _ hw4).2 hsucc
    iapply (wpX_brx hq3 (by rw [hP3]; exact hT) (by rw [hc3]; exact hx3) (by rw [hP3, List.length_map]; exact hxl))
    iintro %s4 %hs4
    have h00 : s3.rd 0 = 0 := by simp [LP.rd]
    have hbr : (if brEval .ne (s3.rd 15) (s3.rd 0) then w else s3.pc + 1) = w + 4 := by
      simp [brEval, e15'', h00, hc3]
    rw [hbr] at hs4
    obtain ⟨hP4, hc4, hq4⟩ := LPstep_at hs4 hP3 rfl
    have rk4 := hRs s3 s4 _ _ _ rk3 hs4 (.inl rfl)
    iapply HK $$ %s4 %_ %u %⟨hP4, hq4, hc4, rk4, hfi4, hmo4', by omega, by omega⟩ Hl
  · imod xstepS (hlc := hlc) (σ' := nxT σ h o' (LRmw true false Lk ((t0, b0) :: rest) (toBytes 1 4) (srcR 9)
        (srcR 15), some ts)) hh
      (fun S ls hI hl => by
        have hA : acqSt ls h := by
          rcases hacq with ⟨rfl, e⟩ | ⟨hh', e⟩
          · exact .inl ⟨rfl, by rw [hl]; exact e⟩
          · exact .inr ⟨hh', by rw [hl]; exact e⟩
        exact inv_amoF hI hA hful hmA' hne hns) $$ HX Hl with ⟨HX, Hl⟩
    imodintro
    iframe HX
    iintro %s2 %hs2
    obtain ⟨hP2, hc2, hq2⟩ := LPstep_at hs2 hP1 (by rw [hc1])
    have rk2 := hRs s1 s2 _ _ _ rk1 hs2 (.inr rfl)
    have e15' : s2.rd 15 = Weak.Prom.Ref.sext 4 (ofBytes (((t0, b0) :: rest).map Prod.snd)) % two64 :=
      LPstep_rd_eq hs2 (by decide) (by rw [hlen1]; omega)
    have hX2 : xOf xs7 s2.prog = some T := by rw [hP2]; exact hT
    iapply (wpX_addiw hq2 hX2 (by rw [hc2]; exact hx2) (by decide))
    iintro %s3 %hs3
    obtain ⟨hP3, hc3, hq3⟩ := LPstep_at hs3 hP2 (by rw [hc2])
    have rk3 := hRs s2 s3 _ _ _ rk2 hs3 (.inr rfl)
    have e15'' : s3.rd 15 ≠ 0 := by
      rw [LPstep_rd_eq hs3 (by decide) (by rw [LPstep_len hs2, hlen1]; omega), e15']
      exact fun e => hsucc ((Own.X.L1c.addiw_sext _ hw4).1 e)
    iapply (wpX_brx hq3 (by rw [hP3]; exact hT) (by rw [hc3]; exact hx3) (by rw [hP3, List.length_map]; exact hxl))
    iintro %s4 %hs4
    have h00 : s3.rd 0 = 0 := by simp [LP.rd]
    have hbr : (if brEval .ne (s3.rd 15) (s3.rd 0) then w else s3.pc + 1) = w := by
      simp [brEval, e15'', h00]
    rw [hbr] at hs4
    obtain ⟨hP4, hc4, hq4⟩ := LPstep_at hs4 hP3 rfl
    have rk4 := hRs s3 s4 _ _ _ rk3 hs4 (.inl rfl)
    iapply IH $$ %s4 %_ %⟨hP4, hq4, hc4, rk4, hfi4, hmo4'⟩ Hl HK

/-- The cpu field's address. -/
theorem pc_adr {s : LP} (h9 : s.rd 9 = X) : (((s.rd 9 + 16) % two64 : Nat) : Int) = Pc := by
  rw [h9]; simp [Pc, Lk, X, two64]

/-- **A STORE TO THE CPU FIELD** `sd rX,16(s1)` (untracked). -/
theorem pcB (M : List PMsg) (γ : Nat → GName) (h : Nat) (hh : h < 3) (T : List XI)
    (hT : xOf xs7 (T.map XI.base) = some T) (w rs2 : Nat) (hx0 : T[w]? = some (.i (Weak.Prom.Ref.Lit.sd rs2 9 16)))
    (RK : LP → Prop) (hR : ∀ s, RK s → s.rd 9 = X ∧ s.regs.length = 32)
    (hRs : ∀ s s' pc v, RK s → LPstep s s' pc 0 v → RK s') (l : Loc) (hld : l.ld = none) :
    ⊢ ∀ (s : LP) (ws : PState), ⌜s.prog = T.map XI.base ∧ s.q = [] ∧ s.pc = w ∧ RK s ∧ fI ws⌝ -∗
      gl (γ h) l -∗
      (∀ (s' : LP) (ws' : PState), ⌜s'.prog = T.map XI.base ∧ s'.q = [] ∧ s'.pc = w + 1 ∧ RK s' ∧
          fI ws' ∧ wsM ws ws'⌝ -∗ gl (γ h) l -∗ wpH (hlc := hlc) (GF := GF) M γ h s' ws') -∗
      wpH (hlc := hlc) M γ h s ws := by
  iintro %s %ws %hs Hl HK
  obtain ⟨hprog, hq, hpc, hrk, hfi⟩ := hs
  obtain ⟨h9, hlen⟩ := hR s hrk
  have hX' : xOf xs7 s.prog = some T := by rw [hprog]; exact hT
  iapply (wpX_sd (sz := 8) (rs2 := rs2) (rs1 := 9) (off := 16) hq (xp_of hX' (by rw [hpc]; exact hx0) rfl)
    (atI hprog (by rw [hpc]; exact hx0)) (by rw [h9]; simp [aligned, X, two64]))
  inext
  iintro %σ %ts %o' %hful %hmsg %_ %_ HX _
  rw [pc_adr h9] at hmsg ⊢
  have hts1 : 1 ≤ ts := by
    rcases hful with ⟨_, h1, _⟩ | ⟨_, _, _, h1, _⟩
    · have := (List.getElem?_eq_some_iff.1 (Weak.Prom.Own.MP.take_get hmsg)); omega
    · omega
  obtain ⟨hm, _⟩ := msgAt_take hmsg hts1
  have hcpu : cpuS ⟨Pc, toBytes (s.rd rs2) 8, some h, .plain⟩ := ⟨rfl, toBytes_len _ 8, rfl⟩
  imod xstepS (hlc := hlc) (σ' := nxT σ h o' (LStore false false Pc (toBytes (s.rd rs2) 8) (srcR 9) (srcR rs2),
      some ts)) hh (fun S ls hI hl => ⟨S, inv_ful hI hful hm ⟨h, hh, rfl, .inr (.inr (.inr hcpu))⟩ (cpu_ovC hcpu)
        (cpu_ovF hcpu) (fun hov => absurd hov (cpu_ovL hcpu)) (fun _ ⟨_, e⟩ => by cases e)
        (.inr fun _ ⟨_, _, _, e⟩ => by
          simp only [Prod.mk.injEq, LStore.injEq] at e; simp [Pc, Lk, Ct, X, Y] at e)
        (by rw [hl]; exact hld)⟩) $$ HX Hl with ⟨HX, Hl⟩
  imodintro
  iframe HX
  iintro %s1 %hs1
  obtain ⟨hP1, hc1, hq1⟩ := LPstep_at hs1 hprog (by rw [hpc])
  have hfi1 := fI_st hfi false (srcsView ws (srcR 9)) (max (srcsView ws (srcR 9)) (srcsView ws (srcR rs2))) Pc
    (toBytes (s.rd rs2) 8).length ts
  have hmo1 := wsM_st ws false (srcsView ws (srcR 9)) (max (srcsView ws (srcR 9)) (srcsView ws (srcR rs2))) Pc
    (toBytes (s.rd rs2) 8).length ts
  iapply HK $$ %s1 %(instrR (storeRun ws false (srcsView ws (srcR 9)) (max (srcsView ws (srcR 9))
    (srcsView ws (srcR rs2))) Pc (toBytes (s.rd rs2) 8).length ts))
    %⟨hP1, hq1, hc1, hRs s s1 _ _ hrk hs1, fI_of hfi1 rfl rfl,
      wsM_trans hmo1 (wsM_eq (fun _ => rfl) rfl rfl rfl rfl)⟩ Hl

/-- Name the current machine state. -/
theorem wpH_gen {M : List PMsg} {γ : Nat → GName} {h : Nat} {s : LP} {W : PState} :
    ⊢ (∀ w, ⌜w = W⌝ -∗ wpH (hlc := hlc) (GF := GF) M γ h s w) -∗ wpH (hlc := hlc) M γ h s W := by
  iintro H
  iapply H $$ %W
  ipureintro; rfl

end gen

end Weak.Prom.OB.E4
