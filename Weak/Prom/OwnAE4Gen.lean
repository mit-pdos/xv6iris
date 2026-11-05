/-
Weak/Prom: **E-a4 — the text-generic blocks** shared by hart 0 and the acquirers (stage E-a4; the steps of
E-a2's `floop5`/`loop5`/`cpu1_5`/`cpu0_5`/`rel5` over the lifecycle protocol, stated for ANY text `X` of the test
holding the block at offset `w`, with the rest of the hart's proof as a continuation).

* `waitG` — `lbu t0,o(a2); bne t0,a3,w`: the flag byte read `k` from a message `t` below the next fence's frontier
  (`t ≤ max vrOld vwOld`: a non-forwarded byte lies below `vrOld`; a forwarded one is the hart's own store, below
  `vwOld` — the invariant `fI`).
* `loopG` — xv6's acquire spin loop on the lock born at `b` (`acq7`).
* `cpu1G` — `sd a0,16(s1)`; `relG` — `sd zero,16(s1); fence rw,w; sw zero,0(s1)`: the release's AUTHOR decides
  its slot's content (the resource, or the death mark of a closing release that keeps the resource); a release
  beyond the window takes its `pend` from the hart's own part.
* `roundG` — `addi a3,a3,1; bne a3,t3,0`.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.OwnAE4Lock

namespace Weak.Prom.OA.E4

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.PF Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Ref (Instr Test two64)
open Weak.Prom.Ref.Lit (X Y Z)
open Weak.Prom.OA.P (L1 J SV bSlot dshotD dpendD msgAt_of cAt5 postA postA_vr postA_wf postA_coh a5_val alg_L2
  amo_msg1 mv_15)
open Weak.Prom.OA.C (Pc alg_pc base_pc st_nonC Pc_ne_Ct Lk_ne_Ct st_coh st_coh0 st_vwOld st_vrNew)
open Weak.Prom.OA.E
open Weak.Prom.OA.EP (tL1 tL2 isL2O isCO cB lk_wr)
open Weak.Prom.OA.E2
open PLabel
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode

/-! ## 1. State facts -/

/-- The forward bank's entries lie below the old write view (every hart's own stores). -/
def fI (ws : PState) : Prop := ∀ a tf vf, get? ws.wFwd a = some (tf, vf) → tf ≤ ws.wVwOld

/-- Views and coherence only grow. -/
def wsM (ws0 ws : PState) : Prop :=
  (∀ a, coh ws0 a ≤ coh ws a) ∧ ws0.wVrOld ≤ ws.wVrOld ∧ ws0.wVwOld ≤ ws.wVwOld ∧ ws0.wVrNew ≤ ws.wVrNew ∧
    ws0.wVwNew ≤ ws.wVwNew

theorem wsM_refl (ws : PState) : wsM ws ws := ⟨fun _ => Nat.le_refl _, Nat.le_refl _, Nat.le_refl _,
  Nat.le_refl _, Nat.le_refl _⟩

theorem wsM_trans {a b c : PState} (h1 : wsM a b) (h2 : wsM b c) : wsM a c :=
  ⟨fun x => Nat.le_trans (h1.1 x) (h2.1 x), Nat.le_trans h1.2.1 h2.2.1, Nat.le_trans h1.2.2.1 h2.2.2.1,
   Nat.le_trans h1.2.2.2.1 h2.2.2.2.1, Nat.le_trans h1.2.2.2.2 h2.2.2.2.2⟩

theorem fI_ld {ws : PState} (h : fI ws) (aq rl : Bool) (va : Nat) (base : Int) (tvs : List (Nat × BitVec 8)) :
    fI (loadRun ws aq rl va base tvs) := by
  have := loadRun_mono ws aq rl va base tvs
  intro a tf vf hg; rw [this.2.1] at hg; rw [this.2.2.1]; exact h a tf vf hg

theorem fI_st {ws : PState} (h : fI ws) (rl : Bool) (va fv : Nat) (base : Int) (n ts : Nat) :
    fI (storeRun ws rl va fv base n ts) := by
  have hm := storeRun_mono ws rl va fv base n ts
  intro a tf vf hg
  rw [hm.2.2.2.2.2.2.2.2.2.2.2 a] at hg; rw [hm.2.2.1]
  split at hg
  · cases hg; omega
  · exact Nat.le_trans (h a tf vf hg) (Nat.le_max_left _ _)

theorem wsM_ld (ws : PState) (aq rl : Bool) (va : Nat) (base : Int) (tvs : List (Nat × BitVec 8)) :
    wsM ws (loadRun ws aq rl va base tvs) := by
  have h := loadRun_mono ws aq rl va base tvs
  exact ⟨h.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.1, Nat.le_of_eq h.2.2.1.symm, h.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.1⟩

theorem wsM_st (ws : PState) (rl : Bool) (va fv : Nat) (base : Int) (n ts : Nat) :
    wsM ws (storeRun ws rl va fv base n ts) := by
  have h := storeRun_mono ws rl va fv base n ts
  exact ⟨h.2.2.2.2.2.2.2.2.2.1, Nat.le_of_eq h.2.1.symm, by rw [h.2.2.1]; omega, Nat.le_of_eq h.2.2.2.1.symm,
    Nat.le_of_eq h.2.2.2.2.1.symm⟩

theorem wsM_fence (ws : PState) (pr pw sr sw : Bool) : wsM ws (fencePost ws pr pw sr sw) :=
  ⟨fun _ => Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, by simp only [fence_vrNew]; split <;> omega,
   by simp only [fence_vwNew]; split <;> omega⟩

theorem fI_of {ws ws' : PState} (h : fI ws) (h1 : ws'.wFwd = ws.wFwd) (h2 : ws'.wVwOld = ws.wVwOld) : fI ws' :=
  fun a tf vf hg => by rw [h1] at hg; rw [h2]; exact h a tf vf hg

theorem wsM_eq {ws ws' : PState} (hc : ∀ a, coh ws' a = coh ws a) (h1 : ws'.wVrOld = ws.wVrOld)
    (h2 : ws'.wVwOld = ws.wVwOld) (h3 : ws'.wVrNew = ws.wVrNew) (h4 : ws'.wVwNew = ws.wVwNew) : wsM ws ws' :=
  ⟨fun a => Nat.le_of_eq (hc a).symm, Nat.le_of_eq h1.symm, Nat.le_of_eq h2.symm, Nat.le_of_eq h3.symm,
   Nat.le_of_eq h4.symm⟩

/-- The state after `lbu t0,o(a2); bne t0,a3`. -/
abbrev wsLd (ws : PState) (o : Nat) (tvs : List (Nat × BitVec 8)) : PState :=
  instrR (ctrlP (qPosts (loadRun ws false false (srcsView ws (srcR 12)) ((Z : Int) + o) tvs)
    (regWL 5 [.DLdRes] ++ [LInstr])) (srcR 5 ++ srcR 13))

/-- A read byte is below its forwarded view, or the hart's own forwarded store. -/
theorem le_fwd (ws : PState) (aq : Bool) (a : Int) (t : Nat) :
    t ≤ fwdView ws aq a t ∨ ∃ vf, get? ws.wFwd a = some (t, vf) := by
  unfold fwdView
  cases h : get? ws.wFwd a with
  | none => exact .inl (Nat.le_refl _)
  | some p =>
    obtain ⟨tf, vf⟩ := p
    simp only
    by_cases e : t = tf
    · subst e; exact .inr ⟨vf, rfl⟩
    · rw [if_neg e]; exact .inl (Nat.le_refl _)

/-- The AMO block's post-state. -/
theorem postA_st (ws : PState) (base : Int) (tvs : List (Nat × BitVec 8)) (ts n : Nat) (hf : fI ws) :
    fI (postA ws 9 base tvs ts n) ∧ wsM ws (postA ws 9 base tvs ts n) ∧
      ∀ j : Nat, j < n → ts ≤ coh (postA ws 9 base tvs ts n) (base + j) := by
  have hl := wsM_ld ws true false (srcsView ws (srcR 9)) base tvs
  have hs := wsM_st (loadRun ws true false (srcsView ws (srcR 9)) base tvs) false (srcsView ws (srcR 9)) ts base n ts
  have hc := (storeRun_mono (loadRun ws true false (srcsView ws (srcR 9)) base tvs) false (srcsView ws (srcR 9)) ts
    base n ts).2.2.2.2.2.2.2.2.2.2.1
  refine ⟨fI_st (fI_ld hf true false (srcsView ws (srcR 9)) base tvs) false (srcsView ws (srcR 9)) ts base n ts,
    wsM_trans (wsM_trans hl hs) ?_, hc⟩
  refine ⟨fun _ => Nat.le_refl _, ?_, Nat.le_refl _, ?_, ?_⟩ <;>
    simp only [postA, regWL, show (15 : Nat) ≠ 0 by decide, if_false, List.singleton_append, qPosts, qPost,
      instrR_vrNew, ctrlP_vrNew, regWP_vrNew, amoPost_vrNew, if_true, instrR_vrOld, ctrlP_vrOld, regWP_vrOld,
      amoPost_vrOld, instrR_vwNew, ctrlP_vwNew, regWP_vwNew, amoPost_vwNew] <;> omega

/-! ## 2. The postcondition, the trace obligation -/

section gen

variable {GF : BundledGFunctors} [GhostVarG GF HSt] [GhostVarG GF Bool] [TokenG GF] [SavedPropG GF] [InvGS GF]

/-- A fancy update before a step. -/
theorem wpKA_fupd {g : AGN} {π : Proto} {w : HW LP Unit Unit} {Qs : Nat → Trace → Prop} {s : LP}
    {Φ : Unit → IProp GF} : (|={⊤}=> wpKA g π w Qs s Φ) ⊢ wpKA g π w Qs s Φ := by
  unfold wpKA wpA
  letI : IrisGS_gen .hasLC (CExpr LP Unit Unit) GF := aIrisGS g π w.img w.M (fun h => ΨK w.M (Qs h))
  exact fupd_wp

abbrev Φ7 (g : AGN) (M : List PMsg) : Unit → IProp GF := fun _ => iprop(⌜∃ V, grd π7 img7 M V True⌝ ∨ dshot g)

/-- The guarded trace invariant, or doom. -/
def QE7 (g : AGN) (M : List PMsg) (h : Nat) (ev : Trace) : IProp GF :=
  iprop(⌜∃ V, grd π7 img7 M V (qs7 M h ev)⌝ ∨ dshot g)

instance (g : AGN) (M : List PMsg) (h : Nat) (ev : Trace) : Persistent (QE7 (GF := GF) g M h ev) := by
  unfold QE7; infer_instance

theorem qs7_snoc {M : List PMsg} {h : Nat} {ev : Trace} {e : PEv} (he : ∀ tvs, ¬ isCLd e tvs)
    (hs : ∀ ts, ¬ isCSt e ts) (q : qs7 M h ev) : qs7 M h (ev ++ [e]) := by
  by_cases h0 : h = 0
  · simp only [qs7, if_pos h0] at q ⊢; exact noLd_snoc q he
  · simp only [qs7, if_neg h0] at q ⊢; exact q7_snoc q he hs

theorem QE7_snoc (g : AGN) (M : List PMsg) {h : Nat} {ev : Trace} {e : PEv} (he : ∀ tvs, ¬ isCLd e tvs)
    (hs : ∀ ts, ¬ isCSt e ts) : QE7 (GF := GF) g M h ev ⊢ QE7 g M h (ev ++ [e]) := by
  unfold QE7
  iintro (%hQ | #Hd)
  · ileft; ipureintro; obtain ⟨V, hV⟩ := hQ; exact ⟨V, grd_imp (qs7_snoc he hs) hV⟩
  · iright; iexact Hd

/-- A store, its okMsg, the trace obligation. -/
theorem QE7_st (g : AGN) (M : List PMsg) {h : Nat} {ev : Trace} {e : PEv} {V : Nat} {φ : Prop}
    (he : ∀ tvs, ¬ isCLd e tvs) (hs : ∀ ts, ¬ isCSt e ts) (hφ : φ) :
    QE7 (GF := GF) g M h ev ⊢ ⌜(∃ V, grd π7 img7 M V (qs7 M h (ev ++ [e]))) ∧ grd π7 img7 M V φ⌝ ∨ dshot g := by
  unfold QE7
  iintro (%hQ | #Hd)
  · ileft; ipureintro; obtain ⟨V', hV⟩ := hQ; exact ⟨⟨V', grd_imp (qs7_snoc he hs) hV⟩, grd_intro hφ⟩
  · iright; iexact Hd

/-- Hart 0's field stores (it has no field load). -/
theorem QE7_snoc0 (g : AGN) (M : List PMsg) {ev : Trace} {e : PEv} (he : ∀ tvs, ¬ isCLd e tvs) :
    QE7 (GF := GF) g M 0 ev ⊢ QE7 g M 0 (ev ++ [e]) := by
  unfold QE7
  iintro (%hQ | #Hd)
  · ileft; ipureintro; obtain ⟨V, hV⟩ := hQ
    exact ⟨V, grd_imp (fun q => by simp only [qs7] at q ⊢; exact noLd_snoc q he) hV⟩
  · iright; iexact Hd

/-- A store's obligation from the extended trace's. -/
theorem QE7_ob (g : AGN) (M : List PMsg) {h : Nat} {ev : Trace} {V : Nat} {φ : Prop} (hφ : φ) :
    QE7 (GF := GF) g M h ev ⊢ ⌜(∃ V, grd π7 img7 M V (qs7 M h ev)) ∧ grd π7 img7 M V φ⌝ ∨ dshot g := by
  unfold QE7
  iintro (%hQ | #Hd)
  · ileft; ipureintro; exact ⟨hQ, grd_intro hφ⟩
  · iright; iexact Hd

/-! ## 3. Waiting for a flag byte -/

set_option maxHeartbeats 2000000 in
/-- **THE FLAG WAIT** (Löb at `pc = w`; see the header). -/
theorem waitG (g : AGN) (M : List PMsg) (h : Nat) (T : List XI) (hT : xOf xs7 (T.map XI.base) = some T)
    (w o k : Nat) (ho : o < 3) (hk : 0 < k ∧ k < 256)
    (hx0 : T[w]? = some (.i (.load 1 false 5 12 o))) (hx1 : T[w + 1]? = some (.i (.br .ne 5 13 w)))
    (hxl : w ≤ T.length) (RK : LP → Prop) (hR : ∀ s, RK s → s.rd 12 = Z ∧ s.rd 13 = k ∧ s.regs.length = 32)
    (hRs : ∀ s s' pc rd v, RK s → LPstep s s' pc rd v → rd = 0 ∨ rd = 5 → RK s')
    (hnoinv : ∀ t a, ¬ cmoAt M isInvalK t a) (R : IProp GF) (ws0 : PState) :
    ⊢ ∀ (s : LP) (ws : PState) (pr : GSet Nat) (ev : Trace),
      ⌜s.prog = T.map XI.base ∧ s.q = [] ∧ s.pc = w ∧ RK s ∧ fI ws ∧ wsM ws0 ws⌝ -∗ QE7 g M h ev -∗ R -∗
      (∀ (s' : LP) (ws' : PState) (pr' : GSet Nat) (ev' : Trace) (t : Nat),
        ⌜s'.prog = T.map XI.base ∧ s'.q = [] ∧ s'.pc = w + 2 ∧ RK s' ∧ fI ws' ∧ wsM ws0 ws' ∧
          1 ≤ t ∧ t ≤ M.length ∧ t ≤ max ws'.wVrOld ws'.wVwOld ∧
          ((fB o M t = true ∧ val7 M t = k) ∨ fJ7 M t = true)⌝ -∗
        QE7 g M h ev' -∗ R -∗ lhA g π7 (w7 M h) (qs7 M h) ws' pr' ev' -∗ wpKA g π7 (w7 M h) (qs7 M) s' (Φ7 g M)) -∗
      lhA g π7 (w7 M h) (qs7 M h) ws pr ev -∗ wpKA g π7 (w7 M h) (qs7 M) s (Φ7 g M) := by
  have hw := litW_x xs7 img7 M h
  iloeb as IH
  iintro %s %ws %pr %ev %hs #HQ HR HK Hl
  obtain ⟨hprog, hq, hpc, hrk, hfi, hmo⟩ := hs
  obtain ⟨h12, h13, hlen⟩ := hR s hrk
  have hX' : xOf xs7 s.prog = some T := by rw [hprog]; exact hT
  have hZo : (Z + o) % two64 = Z + o := Nat.mod_eq_of_lt (by simp [Z, two64]; omega)
  iapply (wpKA_ld (sz := 1) (sgn := false) (rd := 5) (rs1 := 12) (off := o) (base := (Z : Int) + o) hw
    (litAg_x hq hX' (by rw [hpc]; exact hx0) rfl) hq (atI hprog (by rw [hpc]; exact hx0))
    (by rw [h12]; simp [aligned, Nat.mod_one]) (by rw [h12, hZo]; omega))
  iframe Hl
  inext
  iintro %tvs0 %hl0 %hlo0 _ _
  have hnc := ld_nonC (a := (Z : Int) + o) (by simp [Z, Ct, Y]; omega) tvs0 (srcR 12)
  ihave #HQ1 := QE7_snoc g M hnc.1 hnc.2 $$ HQ
  imodintro
  isplitr
  · unfold QE7; iexact HQ1
  iintro %s1 %hs1 _ _
  imodintro
  iintro Hl
  obtain ⟨hP1, hc1, hq1⟩ := LPstep_at hs1 hprog (by rw [hpc])
  have rk1 := hRs s s1 _ _ _ hrk hs1 (.inr rfl)
  have e5 : s1.rd 5 = ldVal false 1 tvs0 % two64 := LPstep_rd_eq hs1 (by decide) (by omega)
  have e13 : s1.rd 13 = k := (hR s1 rk1).2.1
  iapply (wpKA_brx (Xs := xs7) hw (xAg_x xs7 img7 M h s1) hq1 (by rw [hP1]; exact hT) (by rw [hc1]; exact hx1)
    (by rw [hP1, List.length_map]; exact hxl))
  iframe Hl
  inext
  iintro %s2 %hs2 _ _
  imodintro
  iintro Hl
  have rk2 := hRs s1 s2 _ _ _ rk1 hs2 (.inl rfl)
  have hfi2 : fI (wsLd ws o tvs0) := fI_of (fI_ld hfi false false (srcsView ws (srcR 12)) ((Z : Int) + o) tvs0) rfl rfl
  have hmo2 : wsM ws0 (wsLd ws o tvs0) := wsM_trans (wsM_trans hmo
    (wsM_ld ws false false (srcsView ws (srcR 12)) ((Z : Int) + o) tvs0)) (wsM_eq (fun _ => rfl) rfl rfl rfl rfl)
  by_cases hz : s1.rd 5 = s1.rd 13
  · -- the flag is `k`: fall through
    have hbr : (if Weak.Prom.Ref.brEval .ne (s1.rd 5) (s1.rd 13) then w else s1.pc + 1) = w + 2 := by
      simp [Weak.Prom.Ref.brEval, hz, hc1]
    rw [hbr] at hs2
    obtain ⟨hP2, hc2, hq2⟩ := LPstep_at hs2 hP1 rfl
    obtain ⟨t0, v0, r0, rfl⟩ := tvs_cons hl0 (by decide)
    have hr0 : r0 = [] := by simpa using hl0
    subst hr0
    have hv0 : v0.toNat = k := by
      have : ldVal false 1 [(t0, v0)] = v0.toNat := by
        simp [ldVal, ofBytes, Weak.Prom.Ref.bytesVal]
      rw [e5, e13, this, Nat.mod_eq_of_lt (by have := v0.isLt; simp [two64]; omega)] at hz; exact hz
    obtain ⟨hmb, _⟩ := loadOk_b0 hlo0
    obtain ⟨n, m, ht0, hmn, hby⟩ := src_of_val hmb (img7_eq _) (fun e => by
      subst e; simp at hv0; omega)
    have hmt : msgAt M t0 = some m := by rw [ht0]; exact msgAt_of (by omega) (by simpa using hmn)
    have htM := msgAt_le hmt
    have hcls := flag_src ho hmt hby
    have hle : t0 ≤ max (wsLd ws o [(t0, v0)]).wVrOld (wsLd ws o [(t0, v0)]).wVwOld := by
      have hb0 := (loadRun_b0 ws false false (srcsView ws (srcR 12)) ((Z : Int) + o) t0 v0 []).2.1
      have hvo := (loadRun_mono ws false false (srcsView ws (srcR 12)) ((Z : Int) + o) [(t0, v0)]).2.2.1
      simp only [regWL, qPosts, qPost, regWP_vrOld, instrR_vrOld, ctrlP_vrOld, regWP_vwOld, instrR_vwOld,
        ctrlP_vwOld, show (5 : Nat) ≠ 0 by decide, if_false, List.singleton_append]
      rcases le_fwd ws false ((Z : Int) + o) t0 with h1 | ⟨vf, h1⟩
      · omega
      · have := hfi _ _ _ h1; omega
    iapply HK $$ %s2 %(wsLd ws o [(t0, v0)]) %_ %_ %t0 %⟨hP2, hq2, hc2, rk2, hfi2,
      hmo2, htM.1, htM.2, hle, hcls.imp (fun h => ⟨h.1, by rw [h.2, hv0]⟩) id⟩ HQ1 HR Hl
  · -- not yet: back to the wait
    have hbr : (if Weak.Prom.Ref.brEval .ne (s1.rd 5) (s1.rd 13) then w else s1.pc + 1) = w := by
      simp [Weak.Prom.Ref.brEval, hz]
    rw [hbr] at hs2
    obtain ⟨hP2, hc2, hq2⟩ := LPstep_at hs2 hP1 rfl
    iapply IH $$ %s2 %(wsLd ws o tvs0) %_ %_ %⟨hP2, hq2, hc2, rk2, hfi2, hmo2⟩
      HQ1 HR HK Hl

/-! ## 4. The acquire loop -/

set_option maxHeartbeats 2000000 in
/-- **THE ACQUIRE SPIN LOOP** of a participant of round `k` on the lock born at `b` (Löb at `pc = w`, `mv a5,a4`). -/
theorem loopG (g : AGN) (M : List PMsg) (sv : SV) (ak ek : Nat → Nat → GName) (h : Nat) (hh : h < 3)
    (hdd : g.dd = fun _ => False) (hnoinv : ∀ t a, ¬ cmoAt M isInvalK t a) (T : List XI)
    (hT : xOf xs7 (T.map XI.base) = some T) (w : Nat)
    (hx0 : T[w]? = some (.i (.alu .add 15 0 14)))
    (hx1 : T[w + 1]? = some (.i (Weak.Prom.Ref.Lit.amoswapW true false 15 15 9)))
    (hx2 : T[w + 2]? = some (.addiw 15 15 0)) (hx3 : T[w + 3]? = some (.i (.br .ne 15 0 w))) (hxl : w ≤ T.length)
    (RK : LP → Prop) (hR : ∀ s, RK s → s.rd 9 = X ∧ s.rd 14 = 1 ∧ s.regs.length = 32)
    (hRs : ∀ s s' pc rd v, RK s → LPstep s s' pc rd v → rd = 0 ∨ rd = 15 → RK s')
    (b k c sp B : Nat) (hb : zw M b = true) (hcB : c < B) (hsB : sp < B) (R : IProp GF) (ws0 : PState) :
    ⊢ ∀ (s : LP) (ws : PState) (pr : GSet Nat) (ev : Trace) (lo : Nat),
      ⌜s.prog = T.map XI.base ∧ s.q = [] ∧ s.pc = w ∧ RK s ∧ fI ws ∧ wsM ws0 ws ∧ B ≤ ws.wVrNew ∧
        B ≤ ws.wVwNew ∧ (∀ j : Nat, j < 4 → b ≤ max ws.wVrNew (coh ws (Lk + j))) ∧ b ≤ lo ∧
        lo ≤ max ws.wVrNew (coh ws Lk)⌝ -∗
      ctx7 (GF := GF) g M sv ak ek -∗ lkB g M sv.tk ak ek b k -∗ hdl M sv b (Rb7 g M c sp) -∗
      obg g M sv.tk h lo 0 -∗ ([∗list] t ∈ rB M h b lo, pend g t) -∗ eP ek h k -∗ QE7 g M h ev -∗ R -∗
      (∀ (s' : LP) (ws' : PState) (pr' : GSet Nat) (ev' : Trace) (ts lw sq : Nat),
        ⌜s'.prog = T.map XI.base ∧ s'.q = [] ∧ s'.pc = w + 4 ∧ RK s' ∧ fI ws' ∧ wsM ws0 ws' ∧ b ≤ ts ∧
          (∀ j : Nat, j < 4 → ts ≤ coh ws' (Lk + j)) ∧ ts ≤ ws'.wVrNew ∧ ts ≤ ws'.wVwNew ∧ lw ≤ ws'.wVrNew ∧
          lw ≤ ws'.wVwNew ∧ sq ≤ ws'.wVwNew⌝ -∗
        obg g M sv.tk h ts 0 -∗ ([∗list] t ∈ rB M h b ts, pend g t) -∗ eP ek h k -∗ cPts5 g M lw -∗
        pPts5 g M sq -∗ QE7 g M h ev' -∗ R -∗ lhA g π7 (w7 M h) (qs7 M h) ws' pr' ev' -∗
        wpKA g π7 (w7 M h) (qs7 M) s' (Φ7 g M)) -∗
      lhA g π7 (w7 M h) (qs7 M h) ws pr ev -∗ wpKA g π7 (w7 M h) (qs7 M) s (Φ7 g M) := by
  have hw := litW_x xs7 img7 M h
  iloeb as IH
  iintro %s0 %ws0' %pr0 %ev %lo %hs #Hctx #Hlk #HL Hbag HrB Hek #HQ HR HK Hl
  obtain ⟨hprog0, hq0, hpc0, hrk0, hfi0, hmo0, hBr, hBw, hbv0, hbl, hlo0⟩ := hs
  obtain ⟨h9_0, h14, hlen0⟩ := hR s0 hrk0
  have hX0 : xOf xs7 s0.prog = some T := by rw [hprog0]; exact hT
  -- `mv a5,a4`
  iapply (C.wpKA_alu hw (litAg_x hq0 hX0 (by rw [hpc0]; exact hx0) rfl) hq0 (atI hprog0 (by rw [hpc0]; exact hx0))
    (by decide))
  iframe Hl
  inext
  iintro %s %hsA _ _
  imodintro
  iintro Hl
  obtain ⟨hprog, hpc, hq⟩ := LPstep_at hsA hprog0 (by rw [hpc0])
  have hrk := hRs _ _ _ _ _ hrk0 hsA (.inr rfl)
  have h9 : s.rd 9 = X := (hR s hrk).1
  have h15 : s.rd 15 = 1 := mv_15 hsA h14 hlen0
  have hlen : s.regs.length = 32 := (hR s hrk).2.2
  have hX1 : xOf xs7 s.prog = some T := by rw [hprog]; exact hT
  -- `amoswap.w.aq a5,a5,(s1)`
  iapply (wpKA_amo (base := Lk) hw (litAg_x hq hX1 (by rw [hpc]; exact hx1) rfl) hq
    (atI hprog (by rw [hpc]; exact hx1)) (alg_L2 h9) (by rw [h9]))
  iframe Hl
  inext
  iintro %tvs %ts %hlen4 %_ %hmsg %hlo1 %hex %hcoh %_ _ _
  have hd1 : amoD .swap 4 (s.rd 15) tvs = toBytes 1 4 := amo_msg1 h15
  have hlenD : (amoD .swap 4 (s.rd 15) tvs).length = 4 := by rw [hd1]; rfl
  rw [hd1] at hmsg
  rw [hlenD] at hcoh
  have hcohB : ∀ j : Nat, j < 4 → coh (loadRun (instrR (regWP ws0' 15 (srcR 0 ++ srcR 14))) true false
      (srcsView (instrR (regWP ws0' 15 (srcR 0 ++ srcR 14))) (srcR 9)) Lk tvs) (Lk + j) < ts :=
    fun j hj => cohBelow_at hcoh hj
  have hmt := msgAt_of (by have := hcohB 0 (by decide); omega) hmsg
  have htsM := msgAt_le hmt
  obtain ⟨hA, hbyH⟩ := A2_of hh hmt
  have hpre : max ws0'.wVrNew (coh ws0' Lk) ≤ coh (loadRun (instrR (regWP ws0' 15 (srcR 0 ++ srcR 14))) true false
      (srcsView (instrR (regWP ws0' 15 (srcR 0 ++ srcR 14))) (srcR 9)) Lk tvs) Lk := by
    obtain ⟨t0, v0, r0, rfl⟩ := tvs_cons hlen4 (by decide)
    have := (loadRun_b0 (instrR (regWP ws0' 15 (srcR 0 ++ srcR 14))) true false
      (srcsView (instrR (regWP ws0' 15 (srcR 0 ++ srcR 14))) (srcR 9)) Lk t0 v0 r0).2.2.1
    have := (loadRun_mono (instrR (regWP ws0' 15 (srcR 0 ++ srcR 14))) true false
      (srcsView (instrR (regWP ws0' 15 (srcR 0 ++ srcR 14))) (srcR 9)) Lk ((t0, v0) :: r0)).2.2.2.2.2.2.2.2.2.2.1 Lk
    have := (PF.ldPre_ge (instrR (regWP ws0' 15 (srcR 0 ++ srcR 14))) true false
      (srcsView (instrR (regWP ws0' 15 (srcR 0 ++ srcR 14))) (srcR 9))).2.1
    have e : coh (instrR (regWP ws0' 15 (srcR 0 ++ srcR 14))) Lk = coh ws0' Lk := rfl
    have e' : (instrR (regWP ws0' 15 (srcR 0 ++ srcR 14))).wVrNew = ws0'.wVrNew := rfl
    omega
  have hlts : lo < ts := by
    have h0 := hcohB 0 (by decide); rw [show Lk + ((0 : Nat) : Int) = Lk from by simp] at h0; omega
  icases obg_take g M sv.tk hlts hA hbyH htsM $$ Hbag with ⟨⟨Hp, Ht⟩, Hbag⟩
  imod shoot $$ Hp with #Hsh
  imodintro
  isplitr
  · iapply QE7_st g M (rmw_nonC _ _ _ _ _ _ _).1 (rmw_nonC _ _ _ _ _ _ _).2 (ok7_lk hlenD) $$ HQ
  isplitr
  · unfold fulT; ileft; iexact Hsh
  iintro %s1 %hs1 #Hfr Hc
  have hts_f := postA_wf (instrR (regWP ws0' 15 (srcR 0 ++ srcR 14))) 9 Lk tvs ts
    (amoD .swap 4 (s.rd 15) tvs).length
  have hsrc : bytesAll (fun x u _ => u ≤ coh (loadRun (instrR (regWP ws0' 15 (srcR 0 ++ srcR 14))) true false
      (srcsView (instrR (regWP ws0' 15 (srcR 0 ++ srcR 14))) (srcR 9)) Lk tvs) x) Lk tvs :=
    bytesAll_mono (fun _ _ _ hh => hh.2) _ _
      (loadBytes_coh true (ldPre (instrR (regWP ws0' 15 (srcR 0 ++ srcR 14))) true false
        (srcsView (instrR (regWP ws0' 15 (srcR 0 ++ srcR 14))) (srcR 9))) (instrR (regWP ws0' 15 (srcR 0 ++ srcR 14)))
        Lk tvs).2
  have hwts : wrB M Lk ts := by simpa using lk_wr (toBytes_length 1 4) (j := 0) (by decide) hmt
  obtain ⟨hP1, hc1, hq1⟩ := LPstep_at hs1 hprog (by rw [hpc])
  have hrk1 := hRs _ _ _ _ _ hrk hs1 (.inr rfl)
  have hlen1 : s1.regs.length = 32 := (hR s1 hrk1).2.2
  have e15 := LPstep_rd_eq hs1 (by decide) (by omega)
  have hvp := (PF.ldPre_ge (instrR (regWP ws0' 15 (srcR 0 ++ srcR 14))) true false
    (srcsView (instrR (regWP ws0' 15 (srcR 0 ++ srcR 14))) (srcR 9))).2.1
  have ev0 : (instrR (regWP ws0' 15 (srcR 0 ++ srcR 14))).wVrNew = ws0'.wVrNew := rfl
  have ec0 : ∀ a, coh (instrR (regWP ws0' 15 (srcR 0 ++ srcR 14))) a = coh ws0' a := fun _ => rfl
  have hpo := postA_st (instrR (regWP ws0' 15 (srcR 0 ++ srcR 14))) Lk tvs ts
    (amoD .swap 4 (s.rd 15) tvs).length (fI_of hfi0 rfl rfl)
  have hvr := postA_vr (instrR (regWP ws0' 15 (srcR 0 ++ srcR 14))) 9 Lk tvs ts (amoD .swap 4 (s.rd 15) tvs).length
  have hvw := postA_vw (instrR (regWP ws0' 15 (srcR 0 ++ srcR 14))) 9 Lk tvs ts (amoD .swap 4 (s.rd 15) tvs).length
  have hmo1 : wsM ws0 (postA (instrR (regWP ws0' 15 (srcR 0 ++ srcR 14))) 9 Lk tvs ts
      (amoD .swap 4 (s.rd 15) tvs).length) := wsM_trans hmo0 (wsM_trans (wsM_eq (fun _ => rfl) rfl rfl rfl rfl) hpo.2.1)
  have hcj : ∀ j : Nat, j < 4 → ts ≤ coh (postA (instrR (regWP ws0' 15 (srcR 0 ++ srcR 14))) 9 Lk tvs ts
      (amoD .swap 4 (s.rd 15) tvs).length) (Lk + j) := fun j hj => hpo.2.2 j (by rw [hlenD]; exact hj)
  obtain ⟨-, -, -, hmrn, hmwn⟩ := hpo.2.1
  have ew0 : (instrR (regWP ws0' 15 (srcR 0 ++ srcR 14))).wVwNew = ws0'.wVwNew := rfl
  have hcl : ts ≤ coh (postA (instrR (regWP ws0' 15 (srcR 0 ++ srcR 14))) 9 Lk tvs ts
      (amoD .swap 4 (s.rd 15) tvs).length) Lk := by
    have h0 := hcj 0 (by decide); rw [show Lk + ((0 : Nat) : Int) = Lk from by simp] at h0; exact h0
  ihave #HQ2 := QE7_snoc g M (rmw_nonC true false tvs (amoD .swap 4 (s.rd 15) tvs) (srcR 9) (srcR 15) ts).1
    (rmw_nonC true false tvs (amoD .swap 4 (s.rd 15) tvs) (srcR 9) (srcR 15) ts).2 $$ HQ
  have hvp' : ws0'.wVrNew ≤ ldPre (instrR (regWP ws0' 15 (srcR 0 ++ srcR 14))) true false
      (srcsView (instrR (regWP ws0' 15 (srcR 0 ++ srcR 14))) (srcR 9)) := hvp
  imod acq7 g M sv ak ek h hdd (π := π7) (ws := instrR (regWP ws0' 15 (srcR 0 ++ srcR 14))) (k := k) (c := c)
    (sp := sp) hh hb hlen4 hlo1 hex hsrc hcohB
    (fun j hj => show b ≤ max (ldPre (instrR (regWP ws0' 15 (srcR 0 ++ srcR 14))) true false
      (srcsView (instrR (regWP ws0' 15 (srcR 0 ++ srcR 14))) (srcR 9))) (coh ws0' (Lk + j)) from by
        have := hbv0 j hj; omega)
    (show lo ≤ max (ldPre (instrR (regWP ws0' 15 (srcR 0 ++ srcR 14))) true false
      (srcsView (instrR (regWP ws0' 15 (srcR 0 ++ srcR 14))) (srcR 9))) (coh ws0' Lk) from by omega)
    hts_f hwts hnoinv $$ [Hbag HrB Hek Ht Hc] with ⟨Hbag, HrB, Hek, (%hv | ⟨%hv, %lw, %sq, %hls, HC, HP⟩)⟩
  · iframe Hctx Hlk HL Hfr Hbag HrB Hek Ht Hc
  all_goals imodintro
  all_goals iintro Hl
  · -- held: `sext.w`, `bnez` back to the loop head
    iapply (wpKA_addiw (Xs := xs7) hw (xAg_x xs7 img7 M h s1) hq1 (by rw [hP1]; exact hT) (by rw [hc1]; exact hx2)
      (by decide))
    iframe Hl
    inext
    iintro %s2 %hs2 _ _
    imodintro
    iintro Hl
    obtain ⟨hP2, hc2, hq2⟩ := LPstep_at hs2 hP1 (by rw [hc1])
    have hrk2 := hRs _ _ _ _ _ hrk1 hs2 (.inr rfl)
    have f15 : s2.rd 15 = 1 := a5_val (.inr rfl) e15 hv hs2 hlen1
    iapply (wpKA_brx (Xs := xs7) hw (xAg_x xs7 img7 M h s2) hq2 (by rw [hP2]; exact hT) (by rw [hc2]; exact hx3)
      (by rw [hP2, List.length_map]; exact hxl))
    iframe Hl
    inext
    iintro %s3 %hs3 _ _
    imodintro
    iintro Hl
    have hbr : (if Weak.Prom.Ref.brEval .ne (s2.rd 15) (s2.rd 0) then w else s2.pc + 1) = w := by rw [f15]; rfl
    rw [hbr] at hs3
    obtain ⟨hP3, hc3, hq3⟩ := LPstep_at hs3 hP2 rfl
    have hrk3 := hRs _ _ _ _ _ hrk2 hs3 (.inl rfl)
    iapply IH $$ %s3 %(postA (instrR (regWP ws0' 15 (srcR 0 ++ srcR 14))) 9 Lk tvs ts
        (amoD .swap 4 (s.rd 15) tvs).length) %_ %_ %ts %⟨hP3, hq3, hc3, hrk3, hpo.1, hmo1, by omega, by omega,
      fun j hj => by have := hcj j hj; omega, by omega, by omega⟩
      Hctx Hlk HL [Hbag] [HrB] Hek HQ2 HR HK Hl
    · iapply obg_up g M sv.tk (Nat.le_of_lt hlts) (Nat.le_refl _) $$ Hbag
    · unfold rB
      iapply bsl_filter_mono (pend g) _ _ (fun t ht => by
        simp only [Bool.and_eq_true, decide_eq_true_eq] at ht ⊢
        exact ⟨⟨⟨by omega, ht.1.1.2⟩, ht.1.2⟩, ht.2⟩) (rng M) $$ HrB
  · -- acquired: `sext.w`, `bnez` falls through
    iapply (wpKA_addiw (Xs := xs7) hw (xAg_x xs7 img7 M h s1) hq1 (by rw [hP1]; exact hT) (by rw [hc1]; exact hx2)
      (by decide))
    iframe Hl
    inext
    iintro %s2 %hs2 _ _
    imodintro
    iintro Hl
    obtain ⟨hP2, hc2, hq2⟩ := LPstep_at hs2 hP1 (by rw [hc1])
    have hrk2 := hRs _ _ _ _ _ hrk1 hs2 (.inr rfl)
    have f15 : s2.rd 15 = 0 := a5_val (.inl rfl) e15 hv hs2 hlen1
    iapply (wpKA_brx (Xs := xs7) hw (xAg_x xs7 img7 M h s2) hq2 (by rw [hP2]; exact hT) (by rw [hc2]; exact hx3)
      (by rw [hP2, List.length_map]; exact hxl))
    iframe Hl
    inext
    iintro %s3 %hs3 _ _
    imodintro
    iintro Hl
    have hbr : (if Weak.Prom.Ref.brEval .ne (s2.rd 15) (s2.rd 0) then w else s2.pc + 1) = w + 4 := by
      rw [f15, hc2]; rfl
    rw [hbr] at hs3
    obtain ⟨hP3, hc3, hq3⟩ := LPstep_at hs3 hP2 rfl
    have hrk3 := hRs _ _ _ _ _ hrk2 hs3 (.inl rfl)
    iapply HK $$ %s3 %(postA (instrR (regWP ws0' 15 (srcR 0 ++ srcR 14))) 9 Lk tvs ts
        (amoD .swap 4 (s.rd 15) tvs).length) %_ %_ %ts %lw %sq %⟨hP3, hq3, hc3, hrk3, hpo.1, hmo1, by omega, hcj,
      by omega, by omega, by rcases hls with h1 | h1 <;> omega, by rcases hls with h1 | h1 <;> omega,
      by rcases hls with h1 | h1 <;> omega⟩ [Hbag] [HrB]
      Hek HC HP HQ2 HR Hl
    · iapply obg_up g M sv.tk (Nat.le_of_lt hlts) (Nat.le_refl _) $$ Hbag
    · unfold rB
      iapply bsl_filter_mono (pend g) _ _ (fun t ht => by
        simp only [Bool.and_eq_true, decide_eq_true_eq] at ht ⊢
        exact ⟨⟨⟨by omega, ht.1.1.2⟩, ht.1.2⟩, ht.2⟩) (rng M) $$ HrB

/-! ## 5. The cpu field, the release, the round step -/

/-- The state after a plain store. -/
abbrev wsSt (ws : PState) (rs1 rs2 : Nat) (base : Int) (n ts : Nat) : PState :=
  instrR (acqPost (storeRun ws false (srcsView ws (srcR rs1)) (max (srcsView ws (srcR rs1)) (srcsView ws (srcR rs2)))
    base n ts) false ts)

theorem wsSt_props (ws : PState) (rs1 rs2 : Nat) (base : Int) (n ts : Nat) (hf : fI ws) :
    fI (wsSt ws rs1 rs2 base n ts) ∧ wsM ws (wsSt ws rs1 rs2 base n ts) ∧
      (wsSt ws rs1 rs2 base n ts).wVwOld = max ws.wVwOld ts ∧ (0 < n → ts ≤ coh (wsSt ws rs1 rs2 base n ts) base) ∧
      (∀ j : Nat, j < n → ts ≤ coh (wsSt ws rs1 rs2 base n ts) (base + j)) := by
  have hm := storeRun_mono ws false (srcsView ws (srcR rs1)) (max (srcsView ws (srcR rs1)) (srcsView ws (srcR rs2)))
    base n ts
  exact ⟨fI_of (fI_st hf false (srcsView ws (srcR rs1)) (max (srcsView ws (srcR rs1)) (srcsView ws (srcR rs2)))
      base n ts) rfl rfl,
    wsM_trans (wsM_st ws false (srcsView ws (srcR rs1)) (max (srcsView ws (srcR rs1)) (srcsView ws (srcR rs2)))
      base n ts) (wsM_eq (fun _ => rfl) rfl rfl rfl rfl),
    hm.2.2.1, fun hn => storeRun_coh0 ws false (srcsView ws (srcR rs1))
      (max (srcsView ws (srcR rs1)) (srcsView ws (srcR rs2))) base n ts hn, hm.2.2.2.2.2.2.2.2.2.2.1⟩

/-- **`sd a0,16(s1)`** (xv6 `lk->cpu = mycpu()`): its `pend` from the cpu field's bag. -/
theorem cpu1G (g : AGN) (M : List PMsg) (h : Nat) (T : List XI) (hT : xOf xs7 (T.map XI.base) = some T) (w : Nat)
    (hx : T[w]? = some (.i (Weak.Prom.Ref.Lit.sd 10 9 16))) (RK : LP → Prop) (hR : ∀ s, RK s → s.rd 9 = X)
    (hRs : ∀ s s' pc v, RK s → LPstep s s' pc 0 v → RK s') (R : IProp GF) (ws0 : PState)
    (s : LP) (ws : PState) (pr : GSet Nat) (ev : Trace) (sq : Nat)
    (hs : s.prog = T.map XI.base ∧ s.q = [] ∧ s.pc = w ∧ RK s ∧ fI ws ∧ wsM ws0 ws ∧ sq ≤ ws.wVwNew) :
    pPts5 (GF := GF) g M sq ∗ QE7 g M h ev ∗ R ∗
      (∀ (s' : LP) (ws' : PState) (pr' : GSet Nat) (ev' : Trace) (ts : Nat),
        ⌜s'.prog = T.map XI.base ∧ s'.q = [] ∧ s'.pc = w + 1 ∧ RK s' ∧ fI ws' ∧ wsM ws0 ws' ∧
          ts ≤ coh ws' Pc ∧ ts ≤ ws'.wVwOld⌝ -∗
        pPts5 g M ts -∗ QE7 g M h ev' -∗ R -∗ lhA g π7 (w7 M h) (qs7 M h) ws' pr' ev' -∗
        wpKA g π7 (w7 M h) (qs7 M) s' (Φ7 g M)) ∗
      lhA g π7 (w7 M h) (qs7 M h) ws pr ev ⊢ wpKA g π7 (w7 M h) (qs7 M) s (Φ7 g M) := by
  obtain ⟨hprog, hq, hpc, hrk, hfi, hmo, hsq⟩ := hs
  have hw := litW_x xs7 img7 M h
  have h9 := hR s hrk
  have hX : xOf xs7 s.prog = some T := by rw [hprog]; exact hT
  iintro ⟨Hpp, #HQ, HR, HK, Hl⟩
  iapply (wpKA_sw (sz := 8) (rs2 := 10) (rs1 := 9) (off := 16) (base := Pc) hw
    (litAg_x hq hX (by rw [hpc]; exact hx) rfl) hq (atI hprog (by rw [hpc]; exact hx)) (alg_pc h9) (base_pc h9))
  iframe Hl
  inext
  iintro %ts %_ %hmsg %_ %hext _ _
  have hpre := (PF.stPreA_ge ws false false (srcsView ws (srcR 9)) (srcsView ws (srcR 10))).2.2.2.1
  have hmt := msgAt_of (by omega) hmsg
  icases pPts5_take (GF := GF) g M (by omega : sq < ts) (PO_of (toBytes_length _ _) hmt) (msgAt_le hmt) $$ Hpp
    with ⟨Hpd, Hpp⟩
  imod shoot $$ Hpd with #Hsh
  have hnc := st_nonC Pc_ne_Ct (toBytes (s.rd 10) 8) (srcR 9) (srcR 10) ts
  ihave #HQ1 := QE7_snoc g M hnc.1 hnc.2 $$ HQ
  imodintro
  isplitr
  · iapply QE7_st g M hnc.1 hnc.2 (ok7_far (toBytes_length _ _) (.inr rfl)) $$ HQ
  isplitr
  · unfold fulT; ileft; iexact Hsh
  iintro %s1 %hs1 _ _
  imodintro
  iintro Hl
  obtain ⟨hP1, hc1, hq1⟩ := LPstep_at hs1 hprog (by rw [hpc])
  obtain ⟨f1, m1, e1, c1, -⟩ := wsSt_props ws 9 10 Pc (toBytes (s.rd 10) 8).length ts hfi
  iapply HK $$ %s1 %(wsSt ws 9 10 Pc (toBytes (s.rd 10) 8).length ts) %_ %_ %ts
    %⟨hP1, hq1, hc1, hRs _ _ _ _ hrk hs1, f1, wsM_trans hmo m1, c1 (by rw [toBytes_length]; decide),
      by rw [e1]; omega⟩ Hpp HQ1 HR Hl

/-- **THE RELEASE BLOCK** `sd zero,16(s1); fence rw,w; sw zero,0(s1)` of a participant: the release's AUTHOR
decides its window slot's content — the resource (`cl = false`) or the death mark (`cl = true`, a closing release,
which keeps the resource); a release beyond the window takes its `pend` from the hart's own part. -/
theorem relG (g : AGN) (M : List PMsg) (sv : SV) (ak ek : Nat → Nat → GName) (h : Nat) (hh : h < 3) (T : List XI)
    (hT : xOf xs7 (T.map XI.base) = some T) (w : Nat)
    (hx0 : T[w]? = some (.i (Weak.Prom.Ref.Lit.sd 0 9 16))) (hx1 : T[w + 1]? = some (.i Weak.Prom.Ref.Lit.fRWW))
    (hx2 : T[w + 2]? = some (.i (Weak.Prom.Ref.Lit.sw 0 9))) (RK : LP → Prop) (hR : ∀ s, RK s → s.rd 9 = X)
    (hRs : ∀ s s' pc v, RK s → LPstep s s' pc 0 v → RK s') (R : IProp GF) (ws0 : PState) (cl : Bool) (b k : Nat)
    (s : LP) (ws : PState) (pr : GSet Nat) (ev : Trace) (lo lw sq : Nat)
    (hs : s.prog = T.map XI.base ∧ s.q = [] ∧ s.pc = w ∧ RK s ∧ fI ws ∧ wsM ws0 ws ∧ b ≤ lo ∧ lo ≤ coh ws Lk ∧
      (cl = false → lw ≤ ws.wVwOld) ∧ sq ≤ coh ws Pc) :
    ctx7 (GF := GF) g M sv ak ek ∗ lkB g M sv.tk ak ek b k ∗ obg g M sv.tk h lo 0 ∗
      ([∗list] t ∈ rB M h b lo, pend g t) ∗ cPts5 g M lw ∗ pPts5 g M sq ∗
      (⌜cl = false⌝ ∨ (⌜cl = true⌝ ∗ dM ek k)) ∗ QE7 g M h ev ∗ R ∗
      (∀ (s' : LP) (ws' : PState) (pr' : GSet Nat) (ev' : Trace) (r tc : Nat),
        ⌜s'.prog = T.map XI.base ∧ s'.q = [] ∧ s'.pc = w + 3 ∧ RK s' ∧ fI ws' ∧ wsM ws0 ws' ∧ b < r ∧
          r ≤ coh ws' Lk ∧ r ≤ ws'.wVwOld ∧ tc ≤ coh ws' Pc ∧ tc ≤ ws'.wVwOld⌝ -∗
        obg g M sv.tk h r 0 -∗ ([∗list] t ∈ rB M h b r, pend g t) -∗
        (⌜cl = false⌝ ∨ (⌜cl = true⌝ ∗ cPts5 g M lw ∗ pPts5 g M tc)) -∗ QE7 g M h ev' -∗ R -∗
        lhA g π7 (w7 M h) (qs7 M h) ws' pr' ev' -∗ wpKA g π7 (w7 M h) (qs7 M) s' (Φ7 g M)) ∗
      lhA g π7 (w7 M h) (qs7 M h) ws pr ev ⊢ wpKA g π7 (w7 M h) (qs7 M) s (Φ7 g M) := by
  obtain ⟨hprog, hq, hpc, hrk, hfi, hmo, hbl, hlo, hlw, hsq⟩ := hs
  have hw := litW_x xs7 img7 M h
  have h9 := hR s hrk
  have hX : xOf xs7 s.prog = some T := by rw [hprog]; exact hT
  iintro ⟨#Hctx, #Hlk, Hbag, HrB, Hc, Hpp, Hmo, #HQ, HR, HK, Hl⟩
  -- `sd zero,16(s1)`
  iapply (wpKA_sw (sz := 8) (rs2 := 0) (rs1 := 9) (off := 16) (base := Pc) hw
    (litAg_x hq hX (by rw [hpc]; exact hx0) rfl) hq (atI hprog (by rw [hpc]; exact hx0)) (alg_pc h9) (base_pc h9))
  iframe Hl
  inext
  iintro %ts %_ %hmsg %hcoh %_ _ _
  rw [toBytes_length] at hcoh
  have hc0 : coh ws Pc < ts := by have := cohBelow_at (j := 0) hcoh (by decide); simpa using this
  have hmt := msgAt_of (by omega) hmsg
  icases pPts5_take (GF := GF) g M (by omega : sq < ts) (PO_of (toBytes_length _ _) hmt) (msgAt_le hmt) $$ Hpp
    with ⟨Hpd, Hpp⟩
  imod shoot $$ Hpd with #Hsh
  have hnc := st_nonC Pc_ne_Ct (toBytes (s.rd 0) 8) (srcR 9) (srcR 0) ts
  ihave #HQ1 := QE7_snoc g M hnc.1 hnc.2 $$ HQ
  imodintro
  isplitr
  · iapply QE7_st g M hnc.1 hnc.2 (ok7_far (toBytes_length _ _) (.inr rfl)) $$ HQ
  isplitr
  · unfold fulT; ileft; iexact Hsh
  iintro %s1 %hs1 _ _
  imodintro
  iintro Hl
  obtain ⟨hP1, hc1, hq1⟩ := LPstep_at hs1 hprog (by rw [hpc])
  have hrk1 := hRs _ _ _ _ hrk hs1
  obtain ⟨f1, m1, e1, -, -⟩ := wsSt_props ws 9 0 Pc (toBytes (s.rd 0) 8).length ts hfi
  have hX1 : xOf xs7 s1.prog = some T := by rw [hP1]; exact hT
  -- `fence rw,w`
  iapply (wpKA_fence hw (litAg_x hq1 hX1 (by rw [hc1]; exact hx1) rfl) hq1 (atI hP1 (by rw [hc1]; exact hx1)))
  iframe Hl
  inext
  iintro %s2 %hs2 _ _
  imodintro
  iintro Hl
  obtain ⟨hP2, hc2, hq2⟩ := LPstep_at hs2 hP1 (by rw [hc1])
  have hrk2 := hRs _ _ _ _ hrk1 hs2
  have h9' := hR s2 hrk2
  have hX2 : xOf xs7 s2.prog = some T := by rw [hP2]; exact hT
  -- `sw zero,0(s1)`: THE RELEASE
  iapply (wpKA_sw (sz := 4) (rs2 := 0) (rs1 := 9) (off := 0) (base := Lk) hw
    (litAg_x hq2 hX2 (by rw [hc2]; exact hx2) rfl) hq2 (atI hP2 (by rw [hc2]; exact hx2))
    (alg_of h9' (by decide) (by decide)) (base_of h9' (by decide)))
  iframe Hl
  inext
  iintro %r %_ %hmsg' %hcoh' %hext' _ _
  have hd0 : toBytes (s2.rd 0) 4 = toBytes 0 4 := rfl
  rw [hd0] at hmsg' hcoh'
  have hcL : coh (instrR (fencePost (wsSt ws 9 0 Pc (toBytes (s.rd 0) 8).length ts) true true false true)) Lk < r := by
    have := cohBelow_at (j := 0) hcoh' (by decide); simpa using this
  have hcL0 : coh ws Lk ≤ coh (instrR (fencePost (wsSt ws 9 0 Pc (toBytes (s.rd 0) 8).length ts) true true false true))
      Lk := m1.1 Lk
  have hmr := msgAt_of (by omega) hmsg'
  obtain ⟨hR2, hbyH⟩ := R2_of hh hmr
  have hrM := msgAt_le hmr
  have hvr : (instrR (fencePost (wsSt ws 9 0 Pc (toBytes (s.rd 0) 8).length ts) true true false true)).wVwNew < r :=
    Nat.lt_of_le_of_lt (PF.stPreA_ge _ false false _ _).2.2.2.1 hext'
  have hvw : ts ≤ (instrR (fencePost (wsSt ws 9 0 Pc (toBytes (s.rd 0) 8).length ts) true true false
      true)).wVwNew ∧ (cl = false → lw ≤ (instrR (fencePost (wsSt ws 9 0 Pc (toBytes (s.rd 0) 8).length ts) true true
      false true)).wVwNew) := by
    simp only [instrR_vwNew, fence_vwNew, ite_true]; rw [e1]; exact ⟨by omega, fun h => by have := hlw h; omega⟩
  have hbr : b < r := by omega
  -- the token of `r`, from the hart's part
  unfold obg
  icases Hbag with ⟨HbA, HbL⟩
  unfold bgL
  icases bsl_filter_take (fun t => token (sv.tk t))
    (fun t => decide (lo < t) && decide (t ≠ 0) && (isA2 M t || isR2 M t) && byH M h t)
    (fun t => decide (lo < t) && decide (t ≠ r) && (isA2 M t || isR2 M t) && byH M h t) r
    (by simp [show lo < r by omega, show r ≠ 0 by omega, hR2, hbyH])
    (fun t ht => by simp only [Bool.and_eq_true, decide_eq_true_eq] at ht ⊢
                    exact ⟨⟨⟨⟨ht.1.1.1, by omega⟩, ht.1.2⟩, ht.2⟩, ht.1.1.2⟩) (rng M)
    (mem_rng.2 hrM) (nodup_rng M) $$ HbL with ⟨Ht, HbL⟩
  -- THE AUTHOR DECIDES: window slot (resource or death mark), or beyond the window (own part)
  ihave HD : |={⊤}=> shot g r ∗ ([∗list] t ∈ rB M h b r, pend g t) ∗
      (⌜cl = false⌝ ∨ (⌜cl = true⌝ ∗ cPts5 g M lw ∗ pPts5 g M ts)) $$ [Ht HrB Hc Hpp Hmo]
  · rcases inW_or_bey (M := M) hbr with hW | hB
    · unfold lkB
      icases Hlk with ⟨Hrs, -⟩
      ihave #Hrh := bsl_mem (F := fun h => [∗list] r ∈ (rng M).filter (fun t => inW M b t && isR2 M t &&
        byH M h t), rSl g M sv.tk ek k r) (List.mem_range.2 hh) $$ Hrs
      ihave #Hslot := bsl_mem (F := fun r => rSl g M sv.tk ek k r)
        (List.mem_filter.2 ⟨mem_rng.2 hrM, by simp [hW, hR2, hbyH]⟩) $$ Hrh
      have hrB : ∀ t, (decide (r < t) && isR2 M t && byH M h t && bey M b t) = true →
          (decide (lo < t) && isR2 M t && byH M h t && bey M b t) = true := fun t ht => by
        simp only [Bool.and_eq_true, decide_eq_true_eq] at ht ⊢; exact ⟨⟨⟨by omega, ht.1.1.2⟩, ht.1.2⟩, ht.2⟩
      icases Hmo with (%hcl | ⟨%hcl, #HdM⟩)
      · imod rdep7 g M sv.tk ek k r $$ [Ht Hc Hpp] with #Hsh
        · iframe Hslot Ht; ileft; unfold Rs5; isplitl [Hc]
          · iexists lw; iframe Hc; ipureintro; have := hvw.2 hcl; omega
          · iapply pPts5_mono g M (by have := hvw.1; omega : ts ≤ r) $$ Hpp
        imodintro; iframe Hsh; isplitl [HrB]
        · unfold rB; iapply bsl_filter_mono (pend g) _ _ hrB (rng M) $$ HrB
        · ileft; ipureintro; exact hcl
      · imod rdep7 g M sv.tk ek k r $$ [Ht] with #Hsh
        · iframe Hslot Ht; iright; iexact HdM
        imodintro; iframe Hsh; isplitl [HrB]
        · unfold rB; iapply bsl_filter_mono (pend g) _ _ hrB (rng M) $$ HrB
        · iright; iframe Hc Hpp; ipureintro; exact hcl
    · unfold rB
      icases bsl_filter_take (pend g) (fun t => decide (lo < t) && isR2 M t && byH M h t && bey M b t)
        (fun t => decide (r < t) && isR2 M t && byH M h t && bey M b t) r (by simp [show lo < r by omega, hR2, hbyH, hB])
        (fun t ht => by simp only [Bool.and_eq_true, decide_eq_true_eq] at ht ⊢
                        exact ⟨⟨⟨⟨by omega, ht.1.1.2⟩, ht.1.2⟩, ht.2⟩, by omega⟩) (rng M) (mem_rng.2 hrM) (nodup_rng M)
        $$ HrB with ⟨Hp, HrB⟩
      imod shoot $$ Hp with #Hsh
      imodintro; iframe Hsh HrB
      icases Hmo with (%hcl | ⟨%hcl, -⟩)
      · ileft; ipureintro; exact hcl
      · iright; iframe Hc Hpp; ipureintro; exact hcl
  imod HD with ⟨#Hsh, HrB, Hkeep⟩
  have hnc' := st_nonC Lk_ne_Ct (toBytes (s2.rd 0) 4) (srcR 9) (srcR 0) r
  ihave #HQ2 := QE7_snoc g M hnc'.1 hnc'.2 $$ HQ1
  imodintro
  isplitr
  · iapply QE7_st g M hnc'.1 hnc'.2 (ok7_lk (toBytes_length _ 4)) $$ HQ1
  isplitr
  · unfold fulT; ileft; iexact Hsh
  iintro %s3 %hs3 _ _
  imodintro
  iintro Hl
  obtain ⟨hP3, hc3, hq3⟩ := LPstep_at hs3 hP2 (by rw [hc2])
  obtain ⟨f3, m3, e3, c3, -⟩ := wsSt_props (instrR (fencePost (wsSt ws 9 0 Pc (toBytes (s.rd 0) 8).length ts)
    true true false true)) 9 0 Lk (toBytes (s2.rd 0) 4).length r (fI_of f1 rfl rfl)
  obtain ⟨-, -, -, -, cP⟩ := wsSt_props ws 9 0 Pc (toBytes (s.rd 0) 8).length ts hfi
  have m13 : wsM (wsSt ws 9 0 Pc (toBytes (s.rd 0) 8).length ts) (wsSt (instrR (fencePost (wsSt ws 9 0 Pc
      (toBytes (s.rd 0) 8).length ts) true true false true)) 9 0 Lk (toBytes (s2.rd 0) 4).length r) :=
    wsM_trans (wsM_trans (wsM_fence _ true true false true) (wsM_eq (fun _ => rfl) rfl rfl rfl rfl)) m3
  have htc := cP 0 (by rw [toBytes_length]; decide)
  rw [show Pc + ((0 : Nat) : Int) = Pc from by simp] at htc
  iapply HK $$ %s3 %(wsSt (instrR (fencePost (wsSt ws 9 0 Pc (toBytes (s.rd 0) 8).length ts) true true false true))
      9 0 Lk (toBytes (s2.rd 0) 4).length r) %_ %_ %r %ts
    %⟨hP3, hq3, by have := hc3; omega, hRs _ _ _ _ hrk2 hs3, f3,
      wsM_trans (wsM_trans (wsM_trans hmo m1) (wsM_trans (wsM_fence _ true true false true)
        (wsM_eq (fun _ => rfl) rfl rfl rfl rfl))) m3, hbr, c3 (by rw [toBytes_length]; decide), by rw [e3]; omega,
      Nat.le_trans htc (m13.1 Pc), by have := m13.2.2.1; rw [e1] at this; omega⟩
    [HbA HbL] HrB Hkeep HQ2 HR Hl
  isplitl [HbA]
  · unfold bgA
    iapply bsl_filter_mono (pend g) _ _ (fun t ht => by
      simp only [Bool.and_eq_true, decide_eq_true_eq] at ht ⊢; exact ⟨⟨⟨by omega, by omega⟩, ht.1.2⟩, ht.2⟩)
      (rng M) $$ HbA
  · iapply bsl_filter_mono (fun t => token (sv.tk t)) _ _ (fun t ht => by
      simp only [Bool.and_eq_true, decide_eq_true_eq] at ht ⊢; exact ⟨⟨⟨by omega, by omega⟩, ht.1.2⟩, ht.2⟩)
      (rng M) $$ HbL

/-- **THE ROUND STEP** `addi a3,a3,1; bne a3,t3,0`: the next round (`k + 1 < 3`), or the end. -/
theorem roundG (g : AGN) (M : List PMsg) (h : Nat) (T : List XI) (hT : xOf xs7 (T.map XI.base) = some T) (w : Nat)
    (hx0 : T[w]? = some (.i (Weak.Prom.Ref.Lit.addi 13 13 1))) (hx1 : T[w + 1]? = some (.i (.br .ne 13 28 0)))
    (hlen : T.length = w + 2) (R : IProp GF) (s : LP) (ws : PState) (pr : GSet Nat) (ev : Trace) (k : Nat)
    (hs : s.prog = T.map XI.base ∧ s.q = [] ∧ s.pc = w ∧ s.rd 13 = k ∧ s.rd 28 = 3 ∧ s.regs.length = 32 ∧ k < 3 ∧
      fI ws) :
    R ∗ (∀ (s' : LP) (ws' : PState),
        ⌜k + 1 < 3 ∧ s'.prog = T.map XI.base ∧ s'.q = [] ∧ s'.pc = 0 ∧ s'.rd 13 = k + 1 ∧
          (∀ r, r ≠ 13 → s'.rd r = s.rd r) ∧ s'.regs.length = 32 ∧ fI ws' ∧ wsM ws ws'⌝ -∗
        R -∗ lhA g π7 (w7 M h) (qs7 M h) ws' pr ev -∗ wpKA g π7 (w7 M h) (qs7 M) s' (Φ7 g M)) ∗
      lhA g π7 (w7 M h) (qs7 M h) ws pr ev ⊢ wpKA g π7 (w7 M h) (qs7 M) s (Φ7 g M) := by
  obtain ⟨hprog, hq, hpc, h13, h28, hl, hk, hfi⟩ := hs
  have hw := litW_x xs7 img7 M h
  have hX : xOf xs7 s.prog = some T := by rw [hprog]; exact hT
  iintro ⟨HR, HK, Hl⟩
  iapply (wpKA_alui hw (litAg_x hq hX (by rw [hpc]; exact hx0) rfl) hq (atI hprog (by rw [hpc]; exact hx0))
    (by decide))
  iframe Hl
  inext
  iintro %s1 %hs1 _ _
  imodintro
  iintro Hl
  obtain ⟨hP1, hc1, hq1⟩ := LPstep_at hs1 hprog (by rw [hpc])
  have e13 : s1.rd 13 = k + 1 := by
    rw [LPstep_rd_eq hs1 (by decide) (by omega), h13]; simp [Weak.Prom.Ref.aluOp, two64]; omega
  have e28 : s1.rd 28 = 3 := by rw [LPstep_rd hs1 28 (.inl (by decide)), h28]
  iapply (wpKA_brx (Xs := xs7) hw (xAg_x xs7 img7 M h s1) hq1 (by rw [hP1]; exact hT) (by rw [hc1]; exact hx1)
    (by simp))
  iframe Hl
  inext
  iintro %s2 %hs2 _ _
  imodintro
  iintro Hl
  have hl2 : s2.regs.length = 32 := hs2.2.2.2.1.trans (hs1.2.2.2.1.trans hl)
  by_cases hn : k + 1 < 3
  · have hbr : (if Weak.Prom.Ref.brEval .ne (s1.rd 13) (s1.rd 28) then 0 else s1.pc + 1) = 0 := by
      rw [e13, e28]; simp [Weak.Prom.Ref.brEval]; omega
    rw [hbr] at hs2
    obtain ⟨hP2, hc2, hq2⟩ := LPstep_at hs2 hP1 rfl
    iapply HK $$ %s2 %(instrR (ctrlP (instrR (regWP ws 13 (srcR 13))) (srcR 13 ++ srcR 28)))
      %⟨hn, hP2, hq2, hc2, by rw [LPstep_rd hs2 13 (.inr rfl), e13],
        fun r hr => by rw [LPstep_rd hs2 r (.inr rfl), LPstep_rd hs1 r (.inl hr)], hl2, fI_of hfi rfl rfl,
        wsM_eq (fun _ => rfl) rfl rfl rfl rfl⟩ HR Hl
  · have hbr : (if Weak.Prom.Ref.brEval .ne (s1.rd 13) (s1.rd 28) then 0 else s1.pc + 1) = w + 2 := by
      rw [e13, e28, hc1]; simp [Weak.Prom.Ref.brEval]; omega
    rw [hbr] at hs2
    obtain ⟨hP2, hc2, hq2⟩ := LPstep_at hs2 hP1 rfl
    have hend : s2.prog.length ≤ s2.pc := by rw [hP2, hc2, List.length_map, hlen]; exact Nat.le_refl _
    iapply (wpKA_end (v := ()) (litAg_xn hq2 (fun x hx => by
        rw [hP2, hT, hc2] at hx; simp only [Option.bind_some] at hx
        rw [List.getElem?_eq_none (by omega)] at hx; cases hx)) hq2 hend
      (by show litDone s2 = some (); unfold litDone; rw [if_pos ⟨hq2, hend⟩]))
    iframe Hl
    imodintro
    ileft; ipureintro; exact ⟨0, grd_intro trivial⟩

end gen

end Weak.Prom.OA.E4
