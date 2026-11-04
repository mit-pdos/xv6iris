/-
Weak/Prom: **G4 targets (1c) xv6's EXACT acquire/release text and (3) a `holding()`-shaped racy read, PROVED on
track (b)** (stage S4b part 3, tag S4b3; plan rev 7 §4 "Gate G4" (1c), (3)).

Test `lk1cT` over the LOOP FRONT END (track (a)'s OwnAFront.lean `xStep`, reused read-only; kit OwnKitX.lean), the
lock word `lk` = 0x2000 (4 bytes; xv6's `locked`), its `cpu` field at `lk + 16` (8 bytes), a counter `c` = 0x1000
(8 bytes), image 0.  Both harts run (s1 = x9 = lk, a0 = x10 = the hart's cpu value, x11 = c):
```
 0  li     a4,1                    xv6 acquire (Xv6/KernelImage.lean:2259–2274)
 1  again: mv a5,a4
 2  amoswap.w.aq a5,a5,(s1)
 3  sext.w a5,a5                    (= addiw a5,a5,0)
 4  bnez   a5,again                 (backward: the spin loop)
 5  sd     a0,16(s1)                lk->cpu = mycpu()   (a0 preloaded: `jal mycpu` is not modelled)
 6  ld x7,(x11); addi x7,x7,1; sd x7,(x11)        the critical-section counter (plan G4 (1))
 9  lw     a3,0(s1)                 holding(lk): lk->locked   (G4 (3), xv6 release's `holding` call)
10  beqz   a3,END                   if(!holding(lk)) panic("release")
11  sd     zero,16(s1)              xv6 release (Xv6/KernelImage.lean:2359–2364)
12  fence  rw,w
13  sw     zero,0(s1)
```
Verdict `g4_lock1c`: in every valid machine-v2 run, if both harts finished, their final x7 differ (mutual exclusion
of the critical sections) and both holding() reads returned nonzero (x13 ≠ 0: the `panic` branch is never taken).
Finite runs (a hart that spins forever does not finish; the prefix lemma S3d is separate).

Mechanism: plan §3's release class (OwnLang.lean's language, NOT the Pre class): the release `sw zero,0(s1)` after
`fence rw,w` is release-class (`relClass_fW`), so its DEPOSIT is in place; the acquire is (1a)'s AMO leaf with THE
(b1) PULL; a failed attempt loops (phase 0); `holding()`'s racy read is the PURE protocol fact `lk_ldL` (a read of
the lock word by the holder returns 1 — its acquire or another hart's attempt — or a dead message): R-b1's
"⟦·⟧-guarded" racy read, here with no frontier argument (the lock word's writes during a tenure are all value 1).
The `cpu` field is not tracked (`lk_untr`).  0 named inputs; PO-fetch `x_fetchBounded`, `x_invalFree` (R-b5).
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.OwnLock1cDefs
import Weak.Prom.OwnKitX
import Weak.Prom.OwnLock

namespace Weak.Prom.Own.X.L1c

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Nfr (invalFree relClass)
open Weak.Prom.Own (OSt OW fulO litOW litDoneR litDoneR_end take_msg upd upd_eq upd_ne agentStep doneOf σ0
  hartsFrom ownAdequacy)
open Weak.Prom.OA (XI xOf xStep addiwV)
open Weak.Prom.Own.Lk (MG hv Pg Rbox lkGF xr_inj pr_inj Pg_other upd_other Rg lkImg lkImg_zero C Lw LSt LkS
  cohBelow_get loadRun_coh_j val8_small)
open Weak.Prom.Own.Lk1c
open Weak.Prom.Own.MP (wrA au wrA_of_memByte)
open Weak.Prom.Own.MPL (XRec loadOk_byte val8 rd_regs relClass_fW wrX)
open Weak.Prom.PF (LPstep LPstep_at LPstep_rd LPstep_rd_eq ldVal instrR amoD)
open Weak.Prom.Ref (Instr Test two64)
open PLabel
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode

/-! ## 1. The test, pure facts -/

/-- One hart's text (both harts run it; see the header). -/
def lk1cX : List XI :=
  [.i (Weak.Prom.Ref.Lit.li 14 1), .i (Weak.Prom.Ref.Lit.addi 15 14 0),
   .i (Weak.Prom.Ref.Lit.amoswapW true false 15 15 9), .addiw 15 15 0, .i (.br .ne 15 0 1),
   .i (Weak.Prom.Ref.Lit.sd 10 9 16), .i (Weak.Prom.Ref.Lit.ld 7 11), .i (Weak.Prom.Ref.Lit.addi 7 7 1),
   .i (Weak.Prom.Ref.Lit.sd 7 11), .i (Weak.Prom.Ref.Lit.lw 13 9), .i (.br .eq 13 0 14),
   .i (Weak.Prom.Ref.Lit.sd 0 9 16), .i Weak.Prom.Ref.Lit.fRWW, .i (Weak.Prom.Ref.Lit.sw 0 9)]

def lk1cProg : List Instr := lk1cX.map XI.base

def lk1cXs : List (List XI) := [lk1cX]

def regs1c (cpu : Nat) : List (Nat × Nat) :=
  [(9, Weak.Prom.Ref.Lit.Y), (10, cpu), (11, Weak.Prom.Ref.Lit.X)]

/-- G4 (1c) + (3): two harts (cpu values 1, 2), xv6's acquire/release around the counter. -/
def lk1cT : Test :=
  { harts := [lk1cProg, lk1cProg]
    regs0 := [regs1c 1, regs1c 2]
    img := []
    cond := Weak.Prom.Ref.Lit.mpFF.cond }

theorem lk1cImg : testImg lk1cT = lkImg := rfl

theorem xOf_lk1c : xOf lk1cXs lk1cProg = some lk1cX := by decide

/-- The `cpu` field's messages are untracked: they write neither the lock byte nor a counter byte. -/
theorem cpu_untr {M : List PMsg} {t k v : Nat} (h : M[t - 1]? = some ⟨Lw + 16, toBytes v 8, some k, .plain⟩) :
    ¬ wrL M t ∧ ¬ wrX M t := by
  refine ⟨?_, ?_⟩
  · rintro ⟨j, hj, m, hm, hb⟩
    rw [h] at hm; cases hm
    simp only [PMsg.byteAt] at hb
    rw [if_neg (by omega)] at hb
    simp at hb
  · rintro ⟨j, hj, m, hm, hb⟩
    rw [h] at hm; cases hm
    simp only [PMsg.byteAt] at hb
    rw [if_neg (by simp only [Lw, Weak.Prom.Own.MPL.X, Weak.Prom.Own.MPL.Y, Weak.Prom.Ref.Lit.X,
      Weak.Prom.Ref.Lit.Y]; omega)] at hb
    simp at hb

theorem storeBytes_views : ∀ (ws : PState) (a : Int) (n ts fv : Nat),
    (storeBytes ws a n ts fv).wVrNew = ws.wVrNew ∧ (storeBytes ws a n ts fv).wVwNew = ws.wVwNew
  | _, _, 0, _, _ => ⟨rfl, rfl⟩
  | ws, a, n + 1, ts, fv => by
    simp only [storeBytes]
    exact storeBytes_views _ (a + 1) n ts fv

theorem storeRun_vrNew (ws : PState) (rl : Bool) (va fv : Nat) (base : Int) (n ts : Nat) :
    (instrR (storeRun ws rl va fv base n ts)).wVrNew = ws.wVrNew := (storeBytes_views ws base n ts fv).1

theorem storeRun_vwNew (ws : PState) (rl : Bool) (va fv : Nat) (base : Int) (n ts : Nat) :
    (instrR (storeRun ws rl va fv base n ts)).wVwNew = ws.wVwNew := (storeBytes_views ws base n ts fv).2

theorem loadBytes_vrNew (vpre : Nat) : ∀ (ws : PState) (a : Int) (tvs : List (Nat × BitVec 8)),
    (loadBytes false vpre ws a tvs).wVrNew = ws.wVrNew ∧ (loadBytes false vpre ws a tvs).wVwNew = ws.wVwNew
  | _, _, [] => ⟨rfl, rfl⟩
  | ws, a, (t, _) :: r => by
    simp only [loadBytes]
    exact loadBytes_vrNew vpre _ (a + 1) r

/-- `sext.w` of a sign-extended word is zero iff the word is. -/
theorem addiw_sext (w : Nat) (hw : w < 2 ^ 32) :
    (addiwV (Weak.Prom.Ref.sext 4 w % two64) 0 % two64 = 0) ↔ w = 0 := by
  simp only [addiwV, Weak.Prom.Ref.sext, two64]
  constructor
  · intro h
    split at h <;> split at h <;> omega
  · intro h; subst h; decide

theorem ofBytes4_lt {tvs : List (Nat × BitVec 8)} (hl : tvs.length = 4) : ofBytes (tvs.map Prod.snd) < 2 ^ 32 := by
  match tvs, hl with
  | [(_, b0), (_, b1), (_, b2), (_, b3)], _ =>
    have h0 := b0.isLt; have h1 := b1.isLt; have h2 := b2.isLt; have h3 := b3.isLt
    simp only [ofBytes, Weak.Prom.Ref.bytesVal, List.map, List.foldr]
    omega

/-- A sign-extended word is zero iff the word is. -/
theorem sext4_zero (w : Nat) (hw : w < 2 ^ 32) : Weak.Prom.Ref.sext 4 w % two64 = 0 ↔ w = 0 := by
  simp only [Weak.Prom.Ref.sext, two64]
  constructor
  · intro h; split at h <;> omega
  · intro h; subst h; decide

theorem ofBytes4_of_zero {tvs : List (Nat × BitVec 8)} (hl : tvs.length = 4)
    (h : ∀ (j t : Nat) (b : BitVec 8), tvs[j]? = some (t, b) → b = 0) : ofBytes (tvs.map Prod.snd) = 0 := by
  match tvs, hl with
  | [(t0, b0), (t1, b1), (t2, b2), (t3, b3)], _ =>
    have h0 := h 0 t0 b0 rfl; have h1 := h 1 t1 b1 rfl; have h2 := h 2 t2 b2 rfl; have h3 := h 3 t3 b3 rfl
    subst h0 h1 h2 h3
    rfl

/-! ## 2. The state interpretation and the knowledge -/

variable {hlc : HasLC} {GF : BundledGFunctors} [GhostVarG GF MG]

/-- THE STATE INTERPRETATION, focused on hart `k` (as OwnLock.lean, over the (1c) protocol). -/
abbrev Xf (M : List PMsg) (γc γm γo : GName) (k ko : Nat) (σ : OSt (List Nat)) : IProp GF :=
  iprop(∃ g : LkS, hv γc (.xr g.cr) ∗ hv γm (Pg g k) ∗ hv γo (Pg g ko) ∗ ⌜LkOk lkImg M σ g⌝ ∗
    Rbox γc g.spoil g.ls g.cr)

abbrev Xl (M : List PMsg) (γc γ0 γ1 : GName) (σ : OSt (List Nat)) : IProp GF := Xf M γc γ0 γ1 0 1 σ

theorem Xl_swap (M : List PMsg) (γc γ0 γ1 : GName) (σ : OSt (List Nat)) :
    Xl (GF := GF) M γc γ0 γ1 σ ⊣⊢ Xf M γc γ1 γ0 1 0 σ := by
  constructor
  · iintro ⟨%g, Hc, H0, H1, %hok, Hb⟩
    iexists g; iframe; ipureintro; exact hok
  · iintro ⟨%g, Hc, H1, H0, %hok, Hb⟩
    iexists g; iframe; ipureintro; exact hok

/-- At the end. -/
def KG (γm : GName) (x7 x13 : Nat) : IProp GF :=
  iprop(Rg γm ∨ ∃ p rd mk, hv γm (.pr p rd mk) ∗ ⌜mk ≠ none ∨ ∃ v, rd = some v ∧ x7 = (v + 1) % two64 ∧ x13 ≠ 0⌝)

/-- After the holding() read, up to the release. -/
def KF (γc γm : GName) (k x7 x13 : Nat) : IProp GF :=
  iprop(Rg γm ∨ ∃ cr rd mk, hv γm (.pr 1 rd mk) ∗ hv γc (.xr cr) ∗
    ⌜cr.hold = some k ∧ (mk ≠ none ∨ ∃ v, rd = some v ∧ x7 = (v + 1) % two64 ∧ x13 ≠ 0)⌝)

/-- Before the holding() read. -/
def KH (γc γm : GName) (k x7 : Nat) (ws : PState) : IProp GF :=
  iprop(Rg γm ∨ ∃ cr rd mk, hv γm (.pr 1 rd mk) ∗ hv γc (.xr cr) ∗
    ⌜cr.hold = some k ∧ cr.tstart ≤ ws.wVrNew ∧ (mk ≠ none ∨ ∃ v, rd = some v ∧ x7 = (v + 1) % two64)⌝)

/-- Before the counter store (`x7` the value to store). -/
def KE (γc γm : GName) (k x7 ts : Nat) (ws : PState) : IProp GF :=
  iprop(Rg γm ∨ ∃ cr mk, hv γm (.pr 1 none mk) ∗ hv γc (.xr cr) ∗
    ⌜cr.hold = some k ∧ cr.tstart ≤ ts ∧ cr.tstar < ts ∧ ts ≤ ws.wVwNew ∧ ts ≤ ws.wVrNew ∧
      (mk = none → x7 = (cr.v + 1) % two64 ∧ cr.v ≤ 2) ∧ ∀ m, mk = some m → ∃ j : Nat, j < 8 ∧ m ≤ coh ws (C + j)⌝)

/-- Before the `addi` (`x7` the loaded value). -/
def KC (γc γm : GName) (k x7 ts : Nat) (ws : PState) : IProp GF :=
  iprop(Rg γm ∨ ∃ cr mk, hv γm (.pr 1 none mk) ∗ hv γc (.xr cr) ∗
    ⌜cr.hold = some k ∧ cr.tstart ≤ ts ∧ cr.tstar < ts ∧ ts ≤ ws.wVwNew ∧ ts ≤ ws.wVrNew ∧
      (mk = none → x7 = cr.v ∧ cr.v ≤ 2) ∧ ∀ m, mk = some m → ∃ j : Nat, j < 8 ∧ m ≤ coh ws (C + j)⌝)

/-- At the critical section's entry. -/
def KB (γc γm : GName) (k ts : Nat) (ws : PState) : IProp GF :=
  iprop(Rg γm ∨ ∃ cr, hv γm (.pr 1 none none) ∗ hv γc (.xr cr) ∗
    ⌜cr.hold = some k ∧ cr.tstar < ts ∧ cr.tstart ≤ ts ∧ ts ≤ ws.wVrNew ∧ ts ≤ ws.wVwNew⌝)

theorem KB_congr {γc γm : GName} {k ts : Nat} {ws ws' : PState} (h1 : ws.wVrNew ≤ ws'.wVrNew)
    (h2 : ws.wVwNew ≤ ws'.wVwNew) : KB (GF := GF) γc γm k ts ws ⊢ KB γc γm k ts ws' := by
  unfold KB
  iintro (Hr | ⟨%cr, Hm, Hc, %hc⟩)
  · ileft; iexact Hr
  · iright; iexists cr; iframe; ipureintro
    obtain ⟨a1, a2, a3, a4, a5⟩ := hc
    exact ⟨a1, a2, a3, by omega, by omega⟩

/-- Facts of a hart state of the text. -/
structure HS (s : LP) (p : Nat) : Prop where
  prog : s.prog = lk1cProg
  pc : s.pc = p
  q : s.q = []
  r9 : s.rd 9 = Weak.Prom.Ref.Lit.Y
  r11 : s.rd 11 = Weak.Prom.Ref.Lit.X
  len : s.regs.length = 32

theorem HS.next {s s' : LP} {p p' rd v : Nat} (h : HS s p) (hs : LPstep s s' p' rd v) (h9 : rd ≠ 9)
    (h11 : rd ≠ 11) : HS s' p' :=
  ⟨(LPstep_at hs h.prog rfl).1, (LPstep_at hs h.prog rfl).2.1, (LPstep_at hs h.prog rfl).2.2,
    by rw [LPstep_rd hs 9 (by omega), h.r9], by rw [LPstep_rd hs 11 (by omega), h.r11],
    by rw [hs.2.2.2.1, h.len]⟩

theorem HS.succ {s s' : LP} {p rd v : Nat} (h : HS s p) (hs : LPstep s s' (s.pc + 1) rd v) (h9 : rd ≠ 9)
    (h11 : rd ≠ 11) : HS s' (p + 1) :=
  ⟨(LPstep_at hs h.prog (by rw [h.pc])).1, (LPstep_at hs h.prog (by rw [h.pc])).2.1,
    (LPstep_at hs h.prog (by rw [h.pc])).2.2, by rw [LPstep_rd hs 9 (by omega), h.r9],
    by rw [LPstep_rd hs 11 (by omega), h.r11], by rw [hs.2.2.2.1, h.len]⟩

theorem HS.xof {s : LP} {p : Nat} (h : HS s p) : xOf lk1cXs s.prog = some lk1cX := by rw [h.prog]; exact xOf_lk1c

theorem HS.xp {s : LP} {p : Nat} (h : HS s p) {x : XI} (hx : lk1cX[p]? = some x) (hpl : x.plain = true) :
    XP lk1cXs s := xp_of h.xof (by rw [h.pc]; exact hx) hpl

/-! ## 3. The generic hart -/

section hart

variable [InvGS_gen hlc GF] (M : List PMsg) (γc γm γo : GName) (k ko : Nat) (X : OSt (List Nat) → IProp GF)

abbrev WK (s : LP) (ws : PState) : IProp GF := wpT (hlc := hlc) lk1cXs X lkImg M k s ws (fun _ => iprop(True))

/-- THE END. -/
theorem hG (hX : ∀ σ, (X σ ⊢ Xf M γc γm γo k ko σ) ∧ (Xf M γc γm γo k ko σ ⊢ X σ)) (s : LP) (ws : PState)
    (hP : s.prog.length ≤ s.pc) (hq : s.q = []) :
    KG (GF := GF) γm (s.rd 7) (s.rd 13) ⊢ WK M k X s ws := by
  iintro H
  iapply (wpT_end hq hP)
  iintro %σ %_ HX
  ihave HX := (hX σ).1 $$ HX
  icases HX with ⟨%g, Hc, Hm, Ho, %hok, Hb⟩
  have hsp : ∀ (hk : specH s.regs g k), hv γc (.xr g.cr) ∗ hv γm (Pg g k) ∗ hv γo (Pg g ko) ∗
      Rbox γc g.spoil g.ls g.cr ⊢ |={⊤}=> X { σ with done := upd σ.done k (some s.regs) } ∗ iprop(True) := by
    intro hk
    iintro ⟨Hc, Hm, Ho, Hb⟩
    imodintro
    isplitl
    · iapply (hX _).2
      iexists g
      iframe
      ipureintro; exact lk_fin hok hk
    · ipureintro; trivial
  unfold KG Rg
  icases H with (⟨%rd, %mk, Hmy⟩ | ⟨%p, %rd, %mk, Hmy, %hrd⟩)
  · unfold hv
    ihave %e := ghost_var_agree γm _ _ _ _ $$ Hmy Hm
    obtain ⟨e1, _, _⟩ := pr_inj e
    have hb := (hok.spoil (hok.ph3 k e1.symm)).1
    iapply (hsp (.inl hb))
    unfold hv; iframe
  · unfold hv
    ihave %e := ghost_var_agree γm _ _ _ _ $$ Hmy Hm
    obtain ⟨_, e2, e3⟩ := pr_inj e
    have hk : specH s.regs g k := by
      rcases hrd with hm | ⟨v, hv1, hv2, hv3⟩
      · obtain ⟨t, ht⟩ := Option.ne_none_iff_exists'.1 hm
        exact .inl (hok.mk_bad k t (by rw [← e3, ht]))
      · exact .inr ⟨v, by rw [← e2, hv1], by rw [rd_regs s 7 (by omega)]; exact hv2,
          by rw [rd_regs s 13 (by omega)]; exact hv3⟩
    iapply (hsp hk)
    unfold hv; iframe

/-- **THE RELEASE** `sw zero,0(s1)` (plain, release-class after `fence rw,w`: in place): THE DEPOSIT. -/
theorem hF (hX : ∀ σ, (X σ ⊢ Xf M γc γm γo k ko σ) ∧ (Xf M γc γm γo k ko σ ⊢ X σ)) (hko : ko ≠ k)
    (s : LP) (ws : PState) (hs : HS s 13)
    (hrc : ∀ a d asrc vsrc, relClass ws (LStore false false a d asrc vsrc)) :
    KF (GF := GF) γc γm k (s.rd 7) (s.rd 13) ⊢ WK M k X s ws := by
  iintro H
  iapply (wpT_sd (sz := 4) (rs2 := 0) (rs1 := 9) (off := 0) hs.q (hs.xp rfl rfl) (by rw [hs.prog, hs.pc]; rfl)
    (by rw [hs.r9]; decide))
  inext
  iintro %σ %ts %σ' %hful %hmsg %hcoh %hext HX _
  have hrc' := hrc (((s.rd 9 + 0) % two64 : Nat) : Int) (toBytes (s.rd 0) 4) (srcR 9) (srcR 0)
  have hM : M[ts - 1]? = some (relMsg k) := by
    have := (take_msg hmsg).1
    have hb : (((s.rd 9 + 0) % two64 : Nat) : Int) = Lw := by rw [hs.r9]; decide
    have hd : toBytes (s.rd 0) 4 = toBytes 0 4 := rfl
    rw [hb, hd] at this; exact this
  ihave HX := (hX σ).1 $$ HX
  icases HX with ⟨%g, Hc, Hm, Ho, %hok, Hb⟩
  have cont : ∀ s', LPstep s s' (s.pc + 1) 0 0 →
      KG (GF := GF) γm (s'.rd 7) (s'.rd 13) ⊢ WK M k X s' (instrR (storeRun ws false (srcsView ws (srcR 9))
        (max (srcsView ws (srcR 9)) (srcsView ws (srcR 0))) (((s.rd 9 + 0) % two64 : Nat) : Int)
        (toBytes (s.rd 0) 4).length ts)) := by
    intro s' hs'
    obtain ⟨hP', hc', hq'⟩ := LPstep_at hs' hs.prog (by rw [hs.pc])
    exact hG M γc γm γo k ko X hX s' _ (by rw [hP', hc']; exact Nat.le_refl _) hq'
  unfold KF Rg
  icases H with (⟨%rd, %mk, Hmy⟩ | ⟨%cr, %rd, %mk, Hmy, Hcr, %hcr⟩)
  · -- a rogue: spoiled mode
    unfold hv
    ihave %e := ghost_var_agree γm _ _ _ _ $$ Hmy Hm
    obtain ⟨e1, _, _⟩ := pr_inj e
    have hsp := hok.ph3 k e1.symm
    imodintro
    isplitl [Hc Hm Ho Hb]
    · iapply (hX σ').2
      iexists g; unfold hv; iframe; ipureintro; exact lk_relS hok hsp hrc' hful
    iintro %s' %hs'
    iapply (cont s' hs')
    unfold KG Rg hv
    ileft; iexists rd, mk; iexact Hmy
  · unfold hv
    ihave %e := ghost_var_agree γm _ _ _ _ $$ Hmy Hm
    obtain ⟨e1, e2, e3⟩ := pr_inj e
    ihave %ec := ghost_var_agree γc _ _ _ _ $$ Hcr Hc
    obtain rfl := xr_inj ec
    by_cases hsp : g.spoil = true
    · have hok1 := lk_toRogue (h := k) (lk_relS hok hsp hrc' hful) hsp
      imod ghost_var_update_halves (MG.pr 3 rd mk) γm _ _ $$ Hmy Hm with ⟨Hmy, Hm⟩
      imodintro
      isplitl [Hc Hm Ho Hb]
      · iapply (hX σ').2
        iexists { g with ph := upd g.ph k 3 }
        have e4 : Pg { g with ph := upd g.ph k 3 } k = MG.pr 3 rd mk := by simp [Pg, upd, e2, e3]
        have e5 : Pg { g with ph := upd g.ph k 3 } ko = Pg g ko :=
          Pg_other hko (upd_other _ _ _) (fun _ _ => rfl) (fun _ _ => rfl)
        rw [e4, e5]
        unfold hv
        iframe; ipureintro; exact hok1
      iintro %s' %hs'
      iapply (cont s' hs')
      unfold KG Rg hv
      ileft; iexists rd, mk; iexact Hmy
    · have hsp' : g.spoil = false := by simpa using hsp
      obtain ⟨u, hown⟩ := owned_of_ph1 (hok.lock hsp') e1.symm
      have hok' := lk_rel hok hsp' hown hrc' hful hM
      imod ghost_var_update_halves (MG.xr { g.cr with hold := none, tstart := ts }) γc _ _ $$ Hcr Hc with ⟨Hcr, Hc⟩
      imod ghost_var_update_halves (MG.pr 2 rd mk) γm _ _ $$ Hmy Hm with ⟨Hmy, Hm⟩
      imodintro
      isplitl [Hc Hm Ho Hcr]
      · iapply (hX σ').2
        iexists relG g k ts
        have e4 : Pg (relG g k ts) k = MG.pr 2 rd mk := by simp [Pg, relG, upd, e2, e3]
        have e5 : Pg (relG g k ts) ko = Pg g ko :=
          Pg_other hko (upd_other _ _ _) (fun _ _ => rfl) (fun _ _ => rfl)
        have e6 : Rbox (GF := GF) γc (relG g k ts).spoil (relG g k ts).ls (relG g k ts).cr =
            hv γc (.xr { g.cr with hold := none, tstart := ts }) := by simp [relG, hsp', Rbox]
        have e7 : (relG g k ts).cr = { g.cr with hold := none, tstart := ts } := rfl
        rw [e4, e5, e6, e7]
        unfold hv
        iframe; ipureintro; exact hok'
      iintro %s' %hs'
      iapply (cont s' hs')
      unfold KG hv
      iright; iexists 2, rd, mk; iframe Hmy
      ipureintro
      rw [LPstep_rd hs' 7 (.inr rfl), LPstep_rd hs' 13 (.inr rfl)]; exact hcr.2

/-- `fence rw,w`: the release store after it is release-class. -/
theorem hF0 (hX : ∀ σ, (X σ ⊢ Xf M γc γm γo k ko σ) ∧ (Xf M γc γm γo k ko σ ⊢ X σ)) (hko : ko ≠ k)
    (s : LP) (ws : PState) (hs : HS s 12) :
    KF (GF := GF) γc γm k (s.rd 7) (s.rd 13) ⊢ WK M k X s ws := by
  iintro H
  iapply (wpT_fence (f := ⟨true, true, false, false, false, true, false, false⟩) hs.q (hs.xp rfl rfl)
    (by rw [hs.prog, hs.pc]; rfl))
  iintro %s' %hs'
  rw [show s.rd 7 = s'.rd 7 from (LPstep_rd hs' 7 (.inr rfl)).symm,
    show s.rd 13 = s'.rd 13 from (LPstep_rd hs' 13 (.inr rfl)).symm]
  iapply (hF M γc γm γo k ko X hX hko s' _ (hs.succ hs' (by decide) (by decide))
    (fun a d asrc vsrc => relClass_fW ws _ _ _ _ rfl rfl rfl a d asrc vsrc))
  iexact H

/-- `sd zero,16(s1)` (the `cpu` field: untracked). -/
theorem hF1 (hX : ∀ σ, (X σ ⊢ Xf M γc γm γo k ko σ) ∧ (Xf M γc γm γo k ko σ ⊢ X σ)) (hko : ko ≠ k)
    (s : LP) (ws : PState) (hs : HS s 11) :
    KF (GF := GF) γc γm k (s.rd 7) (s.rd 13) ⊢ WK M k X s ws := by
  iintro H
  iapply (wpT_sd (sz := 8) (rs2 := 0) (rs1 := 9) (off := 16) hs.q (hs.xp rfl rfl) (by rw [hs.prog, hs.pc]; rfl)
    (by rw [hs.r9]; decide))
  inext
  iintro %σ %ts %σ' %hful %hmsg %_ %_ HX _
  have hM : M[ts - 1]? = some ⟨Lw + 16, toBytes (s.rd 0) 8, some k, .plain⟩ := by
    have := (take_msg hmsg).1
    have hb : (((s.rd 9 + 16) % two64 : Nat) : Int) = Lw + 16 := by rw [hs.r9]; decide
    rw [hb] at this; exact this
  obtain ⟨hnL, hnX⟩ := cpu_untr hM
  ihave HX := (hX σ).1 $$ HX
  icases HX with ⟨%g, Hc, Hm, Ho, %hok, Hb⟩
  imodintro
  isplitl [Hc Hm Ho Hb]
  · iapply (hX σ').2
    iexists g; iframe; ipureintro; exact lk_untr hok hful hnL hnX
  iintro %s' %hs'
  rw [show s.rd 7 = s'.rd 7 from (LPstep_rd hs' 7 (.inr rfl)).symm,
    show s.rd 13 = s'.rd 13 from (LPstep_rd hs' 13 (.inr rfl)).symm]
  iapply (hF0 M γc γm γo k ko X hX hko s' _ (hs.succ hs' (by decide) (by decide)))
  iexact H

/-- `beqz a3,END` (holding() returned 0 ⇒ `panic`): not taken unless marked. -/
theorem hE2 (hX : ∀ σ, (X σ ⊢ Xf M γc γm γo k ko σ) ∧ (Xf M γc γm γo k ko σ ⊢ X σ)) (hko : ko ≠ k)
    (s : LP) (ws : PState) (hs : HS s 10) :
    KF (GF := GF) γc γm k (s.rd 7) (s.rd 13) ⊢ WK M k X s ws := by
  iintro H
  iapply (wpT_brx (c := .eq) (rs1 := 13) (rs2 := 0) (tgt := 14) hs.q hs.xof (by rw [hs.pc]; rfl)
    (by rw [hs.prog]; decide))
  iintro %s2 %hs2
  have e7 : s2.rd 7 = s.rd 7 := LPstep_rd hs2 7 (.inr rfl)
  have e13 : s2.rd 13 = s.rd 13 := LPstep_rd hs2 13 (.inr rfl)
  by_cases hx : s.rd 13 = 0
  · have hbr : Weak.Prom.Ref.brEval .eq (s.rd 13) (s.rd 0) = true := by
      rw [show s.rd 0 = 0 from rfl, hx]; rfl
    have hp2 : s2.pc = 14 := by rw [hs2.2.1, hbr]; rfl
    obtain ⟨hP2, _, hq2⟩ := LPstep_at hs2 hs.prog rfl
    iapply (hG M γc γm γo k ko X hX s2 _ (by rw [hP2, hp2]; decide) hq2)
    unfold KF KG
    icases H with (Hr | ⟨%cr, %rd, %mk, Hmy, -, %hc⟩)
    · ileft; iexact Hr
    · iright; iexists 1, rd, mk; iframe Hmy; ipureintro
      rcases hc.2 with hm | ⟨_, _, _, h13⟩
      · exact .inl hm
      · exact absurd hx h13
  · have h0 : s.rd 0 = 0 := rfl
    have hbr : Weak.Prom.Ref.brEval .eq (s.rd 13) (s.rd 0) = false := by
      simp [Weak.Prom.Ref.brEval, h0, hx]
    have hp2 : s2.pc = 11 := by rw [hs2.2.1, hbr, hs.pc]; rfl
    rw [← e7, ← e13]
    have h2 := hs.next hs2 (by decide) (by decide)
    iapply (hF1 M γc γm γo k ko X hX hko s2 _ ⟨h2.prog, hp2, h2.q, h2.r9, h2.r11, h2.len⟩)
    iexact H

/-- **THE `holding()` READ** `lw a3,0(s1)` (G4 (3), `lk_ldL`): the holder reads the lock word as held (byte 0 = 1),
or a dead message (marked: `bad`). -/
theorem hE1 (hinv : invalFree M) (hX : ∀ σ, (X σ ⊢ Xf M γc γm γo k ko σ) ∧ (Xf M γc γm γo k ko σ ⊢ X σ))
    (hko : ko ≠ k) (s : LP) (ws : PState) (hs : HS s 9) :
    KH (GF := GF) γc γm k (s.rd 7) ws ⊢ WK M k X s ws := by
  iintro H
  iapply (wpT_ld (sz := 4) (sgn := true) (rd := 13) (rs1 := 9) (off := 0) hs.q (hs.xp rfl rfl)
    (by rw [hs.prog, hs.pc]; rfl) (by rw [hs.r9]; decide))
  inext
  iintro %σ %tvs %hl4 %hlo HX _
  have hb : (((s.rd 9 + 0) % two64 : Nat) : Int) = Lw := by rw [hs.r9]; decide
  rw [hb] at hlo ⊢
  have hP : ws.wVrNew ≤ ldPre ws false false (srcsView ws (srcR 9)) := (PF.ldPre_ge ws false false _).2.1
  obtain ⟨⟨t0, b0⟩, rest, rfl⟩ : ∃ tb r, tvs = tb :: r := by
    cases tvs with
    | nil => simp at hl4
    | cons tb r => exact ⟨tb, r, rfl⟩
  have hl3 : rest.length = 3 := by simp at hl4; omega
  obtain ⟨hmb, ht0n, hnw⟩ := loadOk_byte (j := 0) hinv hlo rfl
  have hmb' : memByte lkImg M t0 Lw = some b0 := by simpa using hmb
  have hnw' : ¬ writesIn (M.take σ.n) Lw t0 (ldPre ws false false (srcsView ws (srcR 9))) := by simpa using hnw
  have cont : ∀ s3, LPstep s s3 (s.pc + 1) 13 (ldVal true 4 ((t0, b0) :: rest)) →
      KF (GF := GF) γc γm k (s3.rd 7) (s3.rd 13) ⊢ WK M k X s3
        (PF.qPosts (loadRun ws false false (srcsView ws (srcR 9)) Lw ((t0, b0) :: rest))
          (regWL 13 [.DLdRes] ++ [LInstr])) :=
    fun s3 hs3 => hE2 M γc γm γo k ko X hX hko s3 _ (hs.succ hs3 (by decide) (by decide))
  have hx13 : ∀ s3, LPstep s s3 (s.pc + 1) 13 (ldVal true 4 ((t0, b0) :: rest)) → b0 = 1 → s3.rd 13 ≠ 0 := by
    intro s3 hs3 hb1 h0
    rw [LPstep_rd_eq hs3 (by decide) (by rw [hs.len]; decide)] at h0
    simp only [ldVal, if_true] at h0
    have := amo_x5 hl3 h0
    rw [hb1] at this; exact absurd this (by decide)
  have he7 : ∀ s3, LPstep s s3 (s.pc + 1) 13 (ldVal true 4 ((t0, b0) :: rest)) → s3.rd 7 = s.rd 7 :=
    fun s3 hs3 => LPstep_rd hs3 7 (.inl (by decide))
  unfold KH Rg
  icases H with (⟨%rd, %mk, Hmy⟩ | ⟨%cr, %rd, %mk, Hmy, Hcr, %hcr⟩)
  · imodintro
    iframe HX
    iintro %s3 %hs3
    iapply (cont s3 hs3)
    unfold KF Rg
    ileft; iexists rd, mk; iexact Hmy
  · ihave HX := (hX σ).1 $$ HX
    icases HX with ⟨%g, Hc, Hm, Ho, %hok, Hb⟩
    unfold hv
    ihave %e := ghost_var_agree γm _ _ _ _ $$ Hmy Hm
    obtain ⟨e1, e2, e3⟩ := pr_inj e
    ihave %ec := ghost_var_agree γc _ _ _ _ $$ Hcr Hc
    obtain rfl := xr_inj ec
    obtain ⟨hh, htv, hrd⟩ := hcr
    by_cases hsp : g.spoil = true
    · have hok1 := lk_toRogue (h := k) hok hsp
      imod ghost_var_update_halves (MG.pr 3 rd mk) γm _ _ $$ Hmy Hm with ⟨Hmy, Hm⟩
      imodintro
      isplitl [Hc Hm Ho Hb]
      · iapply (hX σ).2
        iexists { g with ph := upd g.ph k 3 }
        have e4 : Pg { g with ph := upd g.ph k 3 } k = MG.pr 3 rd mk := by simp [Pg, upd, e2, e3]
        have e5 : Pg { g with ph := upd g.ph k 3 } ko = Pg g ko :=
          Pg_other hko (upd_other _ _ _) (fun _ _ => rfl) (fun _ _ => rfl)
        rw [e4, e5]
        unfold hv
        iframe; ipureintro; exact hok1
      iintro %s3 %hs3
      iapply (cont s3 hs3)
      unfold KF Rg hv
      ileft; iexists rd, mk; iexact Hmy
    · have hsp' : g.spoil = false := by simpa using hsp
      have hL := hok.lock hsp'
      obtain ⟨u, hown⟩ := owned_of_ph1 hL e1.symm
      have hu : g.cr.tstart = u := by have hls := hL.ls_ok; rw [hown] at hls; exact hls.1.2.2.2.2.2
      rcases lk_ldL hok hsp' hown (by omega : u ≤ ldPre ws false false (srcsView ws (srcR 9))) hmb' ht0n hnw'
        with hb1 | hd
      · imodintro
        isplitl [Hc Hm Ho Hb]
        · iapply (hX σ).2
          iexists g; unfold hv; iframe; ipureintro; exact hok
        iintro %s3 %hs3
        iapply (cont s3 hs3)
        unfold KF Rg hv
        iright; iexists g.cr, rd, mk; iframe Hmy Hcr; ipureintro
        refine ⟨hh, ?_⟩
        rcases hrd with hm | ⟨v, hv1, hv2⟩
        · exact .inl hm
        · exact .inr ⟨v, hv1, by rw [he7 s3 hs3]; exact hv2, hx13 s3 hs3 hb1⟩
      · have hok1 := lk_setBad hok hd
        cases hmk : mk with
        | some m =>
          imodintro
          isplitl [Hc Hm Ho Hb]
          · iapply (hX σ).2
            iexists { g with bad := true }
            rw [show Pg ({ g with bad := true } : LkS) k = Pg g k from rfl,
              show Pg ({ g with bad := true } : LkS) ko = Pg g ko from rfl]
            unfold hv; iframe; ipureintro; exact hok1
          iintro %s3 %hs3
          iapply (cont s3 hs3)
          unfold KF Rg hv
          iright; iexists g.cr, rd, some m; iframe Hmy Hcr; ipureintro
          exact ⟨hh, .inl (by simp)⟩
        | none =>
          have hok2 := lk_markBad (h := k) (m := t0) hok1 rfl (by show g.mark k = none; rw [← e3]; exact hmk)
          imod ghost_var_update_halves (MG.pr 1 rd (some t0)) γm _ _ $$ Hmy Hm with ⟨Hmy, Hm⟩
          imodintro
          isplitl [Hc Hm Ho Hb]
          · iapply (hX σ).2
            iexists { ({ g with bad := true } : LkS) with mark := upd g.mark k (some t0) }
            have e4 : Pg { ({ g with bad := true } : LkS) with mark := upd g.mark k (some t0) } k =
                MG.pr 1 rd (some t0) := by simp [Pg, upd, ← e1, ← e2]
            have e5 : Pg { ({ g with bad := true } : LkS) with mark := upd g.mark k (some t0) } ko = Pg g ko :=
              Pg_other hko (fun _ _ => rfl) (fun _ _ => rfl) (upd_other _ _ _)
            rw [e4, e5]
            unfold hv
            iframe; ipureintro; exact hok2
          iintro %s3 %hs3
          iapply (cont s3 hs3)
          unfold KF Rg hv
          iright; iexists g.cr, rd, some t0; iframe Hmy Hcr; ipureintro
          exact ⟨hh, .inl (by simp)⟩

/-- **THE COUNTER STORE** `sd x7,(x11)`: the holder's message becomes the counter's latest (`lk_sdc`). -/
theorem hE (hinv : invalFree M) (hX : ∀ σ, (X σ ⊢ Xf M γc γm γo k ko σ) ∧ (Xf M γc γm γo k ko σ ⊢ X σ))
    (hko : ko ≠ k) (hk2 : k < 2) (s : LP) (ws : PState) (ts : Nat) (hs : HS s 8) :
    KE (GF := GF) γc γm k (s.rd 7) ts ws ⊢ WK M k X s ws := by
  have h11 := hs.r11
  iintro H
  iapply (wpT_sd (sz := 8) (rs2 := 7) (rs1 := 11) (off := 0) hs.q (hs.xp rfl rfl) (by rw [hs.prog, hs.pc]; rfl)
    (by rw [h11]; decide))
  inext
  iintro %σ %ts' %σ' %hful %hmsg %hcoh %hext HX _
  have hb : (((s.rd 11 + 0) % two64 : Nat) : Int) = C := by rw [h11]; decide
  have hM : M[ts' - 1]? = some (cMsg k (s.rd 7)) := by
    have := (take_msg hmsg).1; rw [hb] at this; exact this
  have hvw : ws.wVwNew < ts' := by
    have := (PF.stPreA_ge ws false false (srcsView ws (srcR 11)) (srcsView ws (srcR 7))).2.2.2.1; omega
  have hcj : ∀ j : Nat, j < 8 → coh ws (C + j) < ts' := by
    rw [hb] at hcoh
    intro j hj; exact cohBelow_get hcoh j (by simp [toBytes, Weak.Prom.Ref.byteList]; omega)
  have hvr' : (instrR (storeRun ws false (srcsView ws (srcR 11))
        (max (srcsView ws (srcR 11)) (srcsView ws (srcR 7))) (((s.rd 11 + 0) % two64 : Nat) : Int)
        (toBytes (s.rd 7) 8).length ts')).wVrNew = ws.wVrNew := storeRun_vrNew _ _ _ _ _ _ _
  have cont : ∀ s', LPstep s s' (s.pc + 1) 0 0 → KH (GF := GF) γc γm k (s'.rd 7) (instrR (storeRun ws false
        (srcsView ws (srcR 11)) (max (srcsView ws (srcR 11)) (srcsView ws (srcR 7))) (((s.rd 11 + 0) % two64 : Nat) : Int)
        (toBytes (s.rd 7) 8).length ts')) ⊢
      WK M k X s' (instrR (storeRun ws false (srcsView ws (srcR 11))
        (max (srcsView ws (srcR 11)) (srcsView ws (srcR 7))) (((s.rd 11 + 0) % two64 : Nat) : Int)
        (toBytes (s.rd 7) 8).length ts')) := by
    intro s' hs'
    exact hE1 M γc γm γo k ko X hinv hX hko s' _ (hs.succ hs' (by decide) (by decide))
  ihave HX := (hX σ).1 $$ HX
  icases HX with ⟨%g, Hc, Hm, Ho, %hok, Hb⟩
  unfold KE Rg
  icases H with (⟨%rd, %mk, Hmy⟩ | ⟨%cr, %mk, Hmy, Hcr, %hcr⟩)
  · unfold hv
    ihave %e := ghost_var_agree γm _ _ _ _ $$ Hmy Hm
    obtain ⟨e1, _, _⟩ := pr_inj e
    have hsp := hok.ph3 k e1.symm
    imodintro
    isplitl [Hc Hm Ho Hb]
    · iapply (hX σ').2
      iexists g; unfold hv; iframe; ipureintro; exact lk_sdcS hok hsp hful hM
    iintro %s' %hs'
    iapply (cont s' hs')
    unfold KH Rg hv
    ileft; iexists rd, mk; iexact Hmy
  · unfold hv
    ihave %e := ghost_var_agree γm _ _ _ _ $$ Hmy Hm
    obtain ⟨e1, e2, e3⟩ := pr_inj e
    ihave %ec := ghost_var_agree γc _ _ _ _ $$ Hcr Hc
    obtain rfl := xr_inj ec
    obtain ⟨hh, htst0, htsr, hvw0, hvr0, hmk1, hmk2⟩ := hcr
    by_cases hsp : g.spoil = true
    · have hok1 := lk_toRogue (h := k) (lk_sdcS hok hsp hful hM) hsp
      imod ghost_var_update_halves (MG.pr 3 none mk) γm _ _ $$ Hmy Hm with ⟨Hmy, Hm⟩
      imodintro
      isplitl [Hc Hm Ho Hb]
      · iapply (hX σ').2
        iexists { g with ph := upd g.ph k 3 }
        have e4 : Pg { g with ph := upd g.ph k 3 } k = MG.pr 3 none mk := by simp [Pg, upd, e2, e3]
        have e5 : Pg { g with ph := upd g.ph k 3 } ko = Pg g ko :=
          Pg_other hko (upd_other _ _ _) (fun _ _ => rfl) (fun _ _ => rfl)
        rw [e4, e5]
        unfold hv
        iframe; ipureintro; exact hok1
      iintro %s' %hs'
      iapply (cont s' hs')
      unfold KH Rg hv
      ileft; iexists none, mk; iexact Hmy
    · have hsp' : g.spoil = false := by simpa using hsp
      have hL := hok.lock hsp'
      obtain ⟨u, hown⟩ := owned_of_ph1 hL e1.symm
      have hu : g.cr.tstart = u := by have hls := hL.ls_ok; rw [hown] at hls; exact hls.1.2.2.2.2.2
      have hmk : ∀ m, g.mark k = some m → m < ts' := by
        intro m hm; rw [← e3] at hm; obtain ⟨j, hj, hle⟩ := hmk2 m hm; have := hcj j hj; omega
      have hrd : g.bad = false → s.rd 7 = (g.cr.v % two64 + 1) % two64 ∧ g.rds k = none := by
        intro hbf
        cases hmkc : mk with
        | none =>
          obtain ⟨hv1, hv2⟩ := hmk1 hmkc
          refine ⟨by rw [hv1]; simp only [two64]; omega, e2.symm⟩
        | some m =>
          have := hok.mk_bad k m (by rw [← e3, hmkc]); rw [hbf] at this; cases this
      obtain ⟨g', hok', hsp'', hls', hph', hmk', hcr', hbad', hrds1, hrds2⟩ :=
        lk_sdc hok hk2 hsp' hown hful hM (by rw [← hu]; omega) (by omega) hmk hrd
      have eR : Rbox (GF := GF) γc g'.spoil g'.ls g'.cr = iprop(True) := by rw [hsp'', hls', hown]; rfl
      imod ghost_var_update_halves (MG.xr g'.cr) γc _ _ $$ Hcr Hc with ⟨Hcr, Hc⟩
      have hh' : g'.cr.hold = some k := by rw [hcr']; exact hh
      by_cases hbt : g.bad = true
      · have hrk : g'.rds k = none := by rw [hrds2 hbt, ← e2]
        cases hmkc : mk with
        | none =>
          -- a `bad` the hart did not cause: record a witness mark
          have hok'' := lk_markBad (h := k) (m := 0) hok' (by rw [hbad']; exact hbt)
            (by rw [hmk', ← e3, hmkc])
          imod ghost_var_update_halves (MG.pr 1 none (some 0)) γm _ _ $$ Hmy Hm with ⟨Hmy, Hm⟩
          imodintro
          isplitl [Hc Hm Ho]
          · iapply (hX σ').2
            iexists { g' with mark := upd g'.mark k (some 0) }
            have e4 : Pg { g' with mark := upd g'.mark k (some 0) } k = MG.pr 1 none (some 0) := by
              simp [Pg, upd, hph', hrk, e1]
            have e5 : Pg { g' with mark := upd g'.mark k (some 0) } ko = Pg g ko :=
              Pg_other hko (fun a _ => by simp [hph']) (fun a ha => by
                show g'.rds a = g.rds a; rw [hrds2 hbt]) (fun a ha => by
                show upd g'.mark k (some 0) a = g.mark a; rw [upd_ne _ _ ha, hmk'])
            have eR' : Rbox (GF := GF) γc ({ g' with mark := upd g'.mark k (some 0) } : LkS).spoil
                ({ g' with mark := upd g'.mark k (some 0) } : LkS).ls ({ g' with mark := upd g'.mark k (some 0) } : LkS).cr
                = iprop(True) := eR
            rw [eR', e4, e5]
            unfold hv
            iframe; ipureintro; exact ⟨hok'', trivial⟩
          iintro %s' %hs'
          iapply (cont s' hs')
          unfold KH Rg hv
          iright; iexists g'.cr, none, some 0; iframe Hmy Hcr
          ipureintro; exact ⟨hh', by rw [hvr', hcr']; exact Nat.le_trans htst0 hvr0, .inl (by simp)⟩
        | some m =>
          imodintro
          isplitl [Hc Hm Ho]
          · iapply (hX σ').2
            iexists g'
            have e4 : Pg g' k = Pg g k := by simp [Pg, hph', hrds2 hbt, hmk']
            have e5 : Pg g' ko = Pg g ko :=
              Pg_other hko (fun a _ => by rw [hph']) (fun a _ => by rw [hrds2 hbt]) (fun a _ => by rw [hmk'])
            rw [eR, e4, e5]
            unfold hv
            iframe; ipureintro; exact ⟨hok', trivial⟩
          iintro %s' %hs'
          iapply (cont s' hs')
          unfold KH Rg hv
          iright; iexists g'.cr, none, some m; iframe Hmy Hcr
          ipureintro; exact ⟨hh', by rw [hvr', hcr']; exact Nat.le_trans htst0 hvr0, .inl (by simp)⟩
      · have hbf : g.bad = false := by simpa using hbt
        have hmkn : mk = none := by
          cases hmkc : mk with
          | none => rfl
          | some m => have := hok.mk_bad k m (by rw [← e3, hmkc]); rw [hbf] at this; cases this
        subst hmkn
        obtain ⟨hv1, _⟩ := hmk1 rfl
        have hrk : g'.rds k = some g.cr.v := by rw [hrds1 hbf]; simp [upd]
        imod ghost_var_update_halves (MG.pr 1 (some g.cr.v) none) γm _ _ $$ Hmy Hm with ⟨Hmy, Hm⟩
        imodintro
        isplitl [Hc Hm Ho]
        · iapply (hX σ').2
          iexists g'
          have e4 : Pg g' k = MG.pr 1 (some g.cr.v) none := by simp [Pg, hph', hrk, hmk', ← e1, ← e3]
          have e5 : Pg g' ko = Pg g ko :=
            Pg_other hko (fun a _ => by rw [hph']) (fun a ha => by rw [hrds1 hbf]; exact upd_ne _ _ ha)
              (fun a _ => by rw [hmk'])
          rw [eR, e4, e5]
          unfold hv
          iframe; ipureintro; exact ⟨hok', trivial⟩
        iintro %s' %hs'
        iapply (cont s' hs')
        unfold KH Rg hv
        iright; iexists g'.cr, some g.cr.v, none; iframe Hmy Hcr
        ipureintro
        refine ⟨hh', by rw [hvr', hcr']; exact Nat.le_trans htst0 hvr0, .inr ⟨g.cr.v, rfl, ?_⟩⟩
        rw [LPstep_rd hs' 7 (.inr rfl)]; exact hv1

/-- `addi x7,x7,1`. -/
theorem hD (hinv : invalFree M) (hX : ∀ σ, (X σ ⊢ Xf M γc γm γo k ko σ) ∧ (Xf M γc γm γo k ko σ ⊢ X σ))
    (hko : ko ≠ k) (hk2 : k < 2) (s : LP) (ws : PState) (ts : Nat) (hs : HS s 7) :
    KC (GF := GF) γc γm k (s.rd 7) ts ws ⊢ WK M k X s ws := by
  iintro H
  iapply (wpT_alui (op := .add) (rd := 7) (rs1 := 7) (imm := 1) hs.q (hs.xp rfl rfl) (by rw [hs.prog, hs.pc]; rfl)
    (by decide))
  iintro %s' %hs'
  have e7 : s'.rd 7 = (s.rd 7 + 1) % two64 := by
    rw [LPstep_rd_eq hs' (by decide) (by rw [hs.len]; decide)]; simp [Weak.Prom.Ref.aluOp]
  iapply (hE M γc γm γo k ko X hinv hX hko hk2 s' _ ts (hs.succ hs' (by decide) (by decide)))
  unfold KC KE
  icases H with (Hr | ⟨%cr, %mk, Hmy, Hcr, %hc⟩)
  · ileft; iexact Hr
  · iright; iexists cr, mk; iframe; ipureintro
    obtain ⟨a1, a2, a3, a4, a4', a5, a6⟩ := hc
    exact ⟨a1, a2, a3, a4, a4', fun hm => ⟨by rw [e7, (a5 hm).1], (a5 hm).2⟩, a6⟩


/-- **THE OWNED READ** `ld x7,(x11)` (`lk_ldc`). -/
theorem hC (hinv : invalFree M) (hX : ∀ σ, (X σ ⊢ Xf M γc γm γo k ko σ) ∧ (Xf M γc γm γo k ko σ ⊢ X σ))
    (hko : ko ≠ k) (hk2 : k < 2) (s : LP) (ws : PState) (ts : Nat) (hs : HS s 6) :
    KB (GF := GF) γc γm k ts ws ⊢ WK M k X s ws := by
  have h11 := hs.r11
  iintro H
  iapply (wpT_ld (sz := 8) (sgn := true) (rd := 7) (rs1 := 11) (off := 0) hs.q (hs.xp rfl rfl)
    (by rw [hs.prog, hs.pc]; rfl) (by rw [h11]; decide))
  inext
  iintro %σ %tvs %hl8 %hlo HX _
  have hb : (((s.rd 11 + 0) % two64 : Nat) : Int) = C := by rw [h11]; decide
  rw [hb] at hlo ⊢
  have hP : ws.wVrNew ≤ ldPre ws false false (srcsView ws (srcR 11)) := (PF.ldPre_ge ws false false _).2.1
  have hw3 : (PF.qPosts (loadRun ws false false (srcsView ws (srcR 11)) C tvs) (regWL 7 [.DLdRes] ++ [LInstr])).wVwNew =
      ws.wVwNew := (loadBytes_vrNew _ ws C tvs).2
  have hr3 : (PF.qPosts (loadRun ws false false (srcsView ws (srcR 11)) C tvs) (regWL 7 [.DLdRes] ++ [LInstr])).wVrNew =
      ws.wVrNew := (loadBytes_vrNew _ ws C tvs).1
  have hc3 : ∀ x, coh (PF.qPosts (loadRun ws false false (srcsView ws (srcR 11)) C tvs) (regWL 7 [.DLdRes] ++ [LInstr])) x =
      coh (loadRun ws false false (srcsView ws (srcR 11)) C tvs) x := fun x => rfl
  have cont : ∀ s3, LPstep s s3 (s.pc + 1) 7 (ldVal true 8 tvs) →
      KC (GF := GF) γc γm k (val8 tvs) ts
        (PF.qPosts (loadRun ws false false (srcsView ws (srcR 11)) C tvs) (regWL 7 [.DLdRes] ++ [LInstr])) ⊢
      WK M k X s3 (PF.qPosts (loadRun ws false false (srcsView ws (srcR 11)) C tvs) (regWL 7 [.DLdRes] ++ [LInstr])) := by
    intro s3 hs3
    have e7 : s3.rd 7 = val8 tvs := LPstep_rd_eq hs3 (by decide) (by rw [hs.len]; decide)
    rw [← e7]
    exact hD M γc γm γo k ko X hinv hX hko hk2 s3 _ ts (hs.succ hs3 (by decide) (by decide))
  unfold KB Rg
  icases H with (⟨%rd, %mk, Hmy⟩ | ⟨%cr, Hmy, Hcr, %hcr⟩)
  · imodintro
    iframe HX
    iintro %s3 %hs3
    iapply (cont s3 hs3)
    unfold KC Rg
    ileft; iexists rd, mk; iexact Hmy
  · ihave HX := (hX σ).1 $$ HX
    icases HX with ⟨%g, Hc, Hm, Ho, %hok, Hb⟩
    unfold hv
    ihave %e := ghost_var_agree γm _ _ _ _ $$ Hmy Hm
    obtain ⟨e1, e2, e3⟩ := pr_inj e
    ihave %ec := ghost_var_agree γc _ _ _ _ $$ Hcr Hc
    obtain rfl := xr_inj ec
    obtain ⟨hh, htst, htsr, hvr, hvw⟩ := hcr
    by_cases hsp : g.spoil = true
    · have hok1 := lk_toRogue (h := k) hok hsp
      imod ghost_var_update_halves (MG.pr 3 none none) γm _ _ $$ Hmy Hm with ⟨Hmy, Hm⟩
      imodintro
      isplitl [Hc Hm Ho Hb]
      · iapply (hX σ).2
        iexists { g with ph := upd g.ph k 3 }
        have e4 : Pg { g with ph := upd g.ph k 3 } k = MG.pr 3 none none := by simp [Pg, upd, ← e2, ← e3]
        have e5 : Pg { g with ph := upd g.ph k 3 } ko = Pg g ko :=
          Pg_other hko (upd_other _ _ _) (fun _ _ => rfl) (fun _ _ => rfl)
        rw [e4, e5]
        unfold hv
        iframe; ipureintro; exact hok1
      iintro %s3 %hs3
      iapply (cont s3 hs3)
      unfold KC Rg hv
      ileft; iexists none, none; iexact Hmy
    · have hsp' : g.spoil = false := by simpa using hsp
      obtain ⟨u, hown⟩ := owned_of_ph1 (hok.lock hsp') e1.symm
      have hby : ∀ (j : Nat) t b, tvs[j]? = some (t, b) → memByte lkImg M t (C + j) = some b ∧ t ≤ σ.n ∧
          ¬ writesIn (M.take σ.n) (C + j) t (ldPre ws false false (srcsView ws (srcR 11))) :=
        fun j t b h => loadOk_byte hinv hlo h
      rcases lk_ldc hok hsp' hown e3.symm (by omega) hl8 hby with hgood |
          ⟨j, t, b, hj, htb, g', hok', hbad', hsp'', hls', hcr', hph', hrds', hmk'⟩
      · by_cases hbt : g.bad = true
        · have hok1 := lk_markBad (h := k) (m := 0) hok hbt e3.symm
          imod ghost_var_update_halves (MG.pr 1 none (some 0)) γm _ _ $$ Hmy Hm with ⟨Hmy, Hm⟩
          imodintro
          isplitl [Hc Hm Ho Hb]
          · iapply (hX σ).2
            iexists { g with mark := upd g.mark k (some 0) }
            have e4 : Pg { g with mark := upd g.mark k (some 0) } k = MG.pr 1 none (some 0) := by
              simp [Pg, upd, ← e1, ← e2]
            have e5 : Pg { g with mark := upd g.mark k (some 0) } ko = Pg g ko :=
              Pg_other hko (fun _ _ => rfl) (fun _ _ => rfl) (upd_other _ _ _)
            rw [e4, e5]
            unfold hv
            iframe; ipureintro; exact hok1
          iintro %s3 %hs3
          iapply (cont s3 hs3)
          unfold KC Rg hv
          iright; iexists g.cr, some 0; iframe Hmy Hcr
          ipureintro
          refine ⟨hh, htsr, htst, by rw [hw3]; exact hvw, by rw [hr3]; exact hvr, fun e => (by cases e), fun m hm => ⟨0, by omega, ?_⟩⟩
          cases hm; exact Nat.zero_le _
        · have hbf : g.bad = false := by simpa using hbt
          have hcnt := hok.cnt hbf
          have hc2 : g.cnt ≤ 2 := by have := hcnt.cnt_def; split at this <;> split at this <;> omega
          have hv8 : val8 tvs = g.cr.v := val8_small hgood (by rw [hcnt.v_cnt]; exact hc2)
          imodintro
          isplitl [Hc Hm Ho Hb]
          · iapply (hX σ).2
            iexists g; unfold hv; iframe; ipureintro; exact hok
          iintro %s3 %hs3
          iapply (cont s3 hs3)
          unfold KC Rg hv
          iright; iexists g.cr, none; iframe Hmy Hcr
          ipureintro
          exact ⟨hh, htsr, htst, by rw [hw3]; exact hvw, by rw [hr3]; exact hvr, fun _ => ⟨hv8, by rw [hcnt.v_cnt]; exact hc2⟩,
            fun m hm => by cases hm⟩
      · imod ghost_var_update_halves (MG.pr 1 none (some t)) γm _ _ $$ Hmy Hm with ⟨Hmy, Hm⟩
        imodintro
        isplitl [Hc Hm Ho Hb]
        · iapply (hX σ).2
          iexists g'
          have e4 : Pg g' k = MG.pr 1 none (some t) := by simp [Pg, hph', hrds', hmk', upd, ← e1, ← e2]
          have e5 : Pg g' ko = Pg g ko :=
            Pg_other hko (fun a _ => by rw [hph']) (fun a _ => by rw [hrds']) (fun a ha => by rw [hmk']; exact upd_ne _ _ ha)
          have eR : Rbox (GF := GF) γc g'.spoil g'.ls g'.cr = Rbox γc g.spoil g.ls g.cr := by rw [hsp'', hls', hcr', hsp']
          rw [e4, e5, eR, hcr']
          unfold hv
          iframe; ipureintro; exact hok'
        iintro %s3 %hs3
        iapply (cont s3 hs3)
        unfold KC Rg hv
        iright; iexists g.cr, some t; iframe Hmy Hcr
        ipureintro
        refine ⟨hh, htsr, htst, by rw [hw3]; exact hvw, by rw [hr3]; exact hvr, fun e => (by cases e), fun m hm => ⟨j, hj, ?_⟩⟩
        cases hm; rw [hc3]; exact loadRun_coh_j htb


/-- `sd a0,16(s1)` (`lk->cpu = mycpu()`: untracked). -/
theorem hB5 (hinv : invalFree M) (hX : ∀ σ, (X σ ⊢ Xf M γc γm γo k ko σ) ∧ (Xf M γc γm γo k ko σ ⊢ X σ))
    (hko : ko ≠ k) (hk2 : k < 2) (s : LP) (ws : PState) (ts : Nat) (hs : HS s 5) :
    KB (GF := GF) γc γm k ts ws ⊢ WK M k X s ws := by
  iintro H
  iapply (wpT_sd (sz := 8) (rs2 := 10) (rs1 := 9) (off := 16) hs.q (hs.xp rfl rfl) (by rw [hs.prog, hs.pc]; rfl)
    (by rw [hs.r9]; decide))
  inext
  iintro %σ %ts' %σ' %hful %hmsg %_ %_ HX _
  have hM : M[ts' - 1]? = some ⟨Lw + 16, toBytes (s.rd 10) 8, some k, .plain⟩ := by
    have := (take_msg hmsg).1
    have hb : (((s.rd 9 + 16) % two64 : Nat) : Int) = Lw + 16 := by rw [hs.r9]; decide
    rw [hb] at this; exact this
  obtain ⟨hnL, hnX⟩ := cpu_untr hM
  ihave HX := (hX σ).1 $$ HX
  icases HX with ⟨%g, Hc, Hm, Ho, %hok, Hb⟩
  imodintro
  isplitl [Hc Hm Ho Hb]
  · iapply (hX σ').2
    iexists g; iframe; ipureintro; exact lk_untr hok hful hnL hnX
  iintro %s' %hs'
  iapply (hC M γc γm γo k ko X hinv hX hko hk2 s' _ ts (hs.succ hs' (by decide) (by decide)))
  iapply (KB_congr (Nat.le_of_eq (storeRun_vrNew _ _ _ _ _ _ _).symm) (Nat.le_of_eq (storeRun_vwNew _ _ _ _ _ _ _).symm))
  iexact H



/-- THE LOOP HEAD's specification (`again:` at pc 1): a hart in phase 0, or a rogue. -/
def LoopP : IProp GF :=
  iprop(∀ s ws, ⌜HS s 1 ∧ s.rd 14 = 1⌝ -∗ (hv γm (.pr 0 none none) ∨ Rg γm) -∗ WK M k X s ws)

/-- After the acquire AMO: it failed (x15 ≠ 0; phase 0, or rogue) or it is done (x15 = 0; `KB`). -/
def KA (x15 ts : Nat) (ws : PState) : IProp GF :=
  iprop((⌜x15 ≠ 0⌝ ∗ (hv γm (.pr 0 none none) ∨ Rg γm)) ∨ (⌜x15 = 0⌝ ∗ KB γc γm k ts ws))

/-- `sext.w a5,a5; bnez a5,again`: back to the loop head (Löb hypothesis), or into the critical section. -/
theorem hTail (hinv : invalFree M) (hX : ∀ σ, (X σ ⊢ Xf M γc γm γo k ko σ) ∧ (Xf M γc γm γo k ko σ ⊢ X σ))
    (hko : ko ≠ k) (hk2 : k < 2) (s : LP) (ws : PState) (ts : Nat) (hs : HS s 3) (h14 : s.rd 14 = 1)
    (hw : ∃ w, w < 2 ^ 32 ∧ s.rd 15 = Weak.Prom.Ref.sext 4 w % two64) :
    LoopP M γm k X ∗ KA γc γm k (s.rd 15) ts ws ⊢ WK M k X s ws := by
  unfold LoopP
  iintro ⟨IH, H⟩
  iapply (wpT_addiw (rd := 15) (rs1 := 15) (imm := 0) hs.q hs.xof (by rw [hs.pc]; rfl) (by decide))
  iintro %s3 %hs3
  have hs3' : HS s3 4 := hs.succ hs3 (by decide) (by decide)
  have e15 : s3.rd 15 = 0 ↔ s.rd 15 = 0 := by
    obtain ⟨w, hwl, hwe⟩ := hw
    rw [LPstep_rd_eq hs3 (by decide) (by rw [hs.len]; decide), hwe, addiw_sext w hwl, sext4_zero w hwl]
  have e14 : s3.rd 14 = 1 := by rw [LPstep_rd hs3 14 (.inl (by decide)), h14]
  iapply (wpT_brx (c := .ne) (rs1 := 15) (rs2 := 0) (tgt := 1) hs3'.q hs3'.xof (by rw [hs3'.pc]; rfl)
    (by rw [hs3'.prog]; decide))
  iintro %s4 %hs4
  have h0 : s3.rd 0 = 0 := rfl
  have hst : ∀ p, s4.pc = p → HS s4 p := fun p hp =>
    ⟨(LPstep_at hs4 hs3'.prog rfl).1, hp, (LPstep_at hs4 hs3'.prog rfl).2.2,
      by rw [LPstep_rd hs4 9 (.inr rfl), hs3'.r9], by rw [LPstep_rd hs4 11 (.inr rfl), hs3'.r11],
      by rw [hs4.2.2.2.1, hs3'.len]⟩
  by_cases hx : s3.rd 15 = 0
  · have hbr : Weak.Prom.Ref.brEval .ne (s3.rd 15) (s3.rd 0) = false := by rw [h0, hx]; rfl
    have hp : s4.pc = 5 := by rw [hs4.2.1, hbr, hs3'.pc]; rfl
    iapply (hB5 M γc γm γo k ko X hinv hX hko hk2 s4 _ ts (hst 5 hp))
    unfold KA
    icases H with (⟨%h, -⟩ | ⟨-, HK⟩)
    · exact absurd (e15.1 hx) h
    · iapply (KB_congr (ws := ws) (ws' := instrR (PF.ctrlP (instrR (PF.regWP ws 15 (srcR 15))) (srcR 15 ++ srcR 0)))
        (Nat.le_refl _) (Nat.le_refl _))
      iexact HK
  · have hbr : Weak.Prom.Ref.brEval .ne (s3.rd 15) (s3.rd 0) = true := by
      simp [Weak.Prom.Ref.brEval, h0, hx]
    have hp : s4.pc = 1 := by rw [hs4.2.1, hbr]; rfl
    have hp4 : HS s4 1 ∧ s4.rd 14 = 1 := ⟨hst 1 hp, by rw [LPstep_rd hs4 14 (.inr rfl), e14]⟩
    unfold KA
    icases H with (⟨-, Hg⟩ | ⟨%h, -⟩)
    · iapply IH
      · ipureintro; exact hp4
      · iexact Hg
    · exact absurd (e15.2 h) hx

/-- **THE SPIN LOOP** (`again:` at pc 1, by Löb induction): `mv a5,a4; amoswap.w.aq a5,a5,(s1)` and the tail.
The AMO leaf (`lk_acq`, THE (b1) PULL consumed): R moves to the hart; or the attempt failed (phase 0: loop); or
rogue; a taken lock whose word has a nonzero high byte (a dead message, `lk_hiByte`) spoils the protocol. -/
theorem hAmo (hinv : invalFree M) (hX : ∀ σ, (X σ ⊢ Xf M γc γm γo k ko σ) ∧ (Xf M γc γm γo k ko σ ⊢ X σ))
    (hko : ko ≠ k) (hk2 : k < 2) (s1 : LP) (ws : PState) (hs1' : HS s1 2) (e15 : s1.rd 15 = 1)
    (e14 : s1.rd 14 = 1) :
    ▷ LoopP M γm k X ∗ (hv (GF := GF) γm (.pr 0 none none) ∨ Rg γm) ⊢ WK M k X s1 ws := by
  iintro ⟨IH, Hmy⟩
  iapply (wpT_amo (op := .swap) (sz := 4) (aq := true) (rl := false) (rd := 15) (rs2 := 15) (rs1 := 9) hs1'.q
    (hs1'.xp rfl rfl) (by rw [hs1'.prog, hs1'.pc]; rfl) (by rw [hs1'.r9]; decide))
  inext
  iintro %σ %tvs %ts %σ' %hl4 %hful %hrmw HX _
  have hb : ((s1.rd 9 : Nat) : Int) = Lw := by rw [hs1'.r9]; rfl
  have hd : amoD .swap 4 (s1.rd 15) tvs = toBytes 1 4 := by rw [PF.amoD_swap, e15]
  rw [hb, hd] at hrmw hful
  rw [hb, hd]
  obtain ⟨_, hmsg, hlo, hex, hcoh, _⟩ := hrmw
  have hM : M[ts - 1]? = some (acqMsg k) := (take_msg hmsg).1
  ihave HX := (hX σ).1 $$ HX
  icases HX with ⟨%g, Hc, Hm, Ho, %hok, Hb⟩
  obtain ⟨⟨t0, b0⟩, rest, rfl⟩ : ∃ tb r, tvs = tb :: r := by
    cases tvs with
    | nil => simp at hl4
    | cons tb r => exact ⟨tb, r, rfl⟩
  have hl3 : rest.length = 3 := by simp at hl4; omega
  obtain ⟨hmb, ht0n, _⟩ := loadOk_byte (j := 0) hinv hlo rfl
  have hmb' : memByte lkImg M t0 Lw = some b0 := by simpa using hmb
  obtain ⟨_, _, _, htsn, _, _, _⟩ := ful_facts hok.pr hful
  have ht0 : t0 < ts := by
    have h1 := (PF.loadRun_b0 ws true false (srcsView ws (srcR 9)) Lw t0 b0 rest).2.2.2.1
    have h2 := PF.cohBelow_b0 hcoh (by simp [toBytes, Weak.Prom.Ref.byteList])
    omega
  have hwin : ∀ t, t0 < t → t < ts → wrL0 M t → au M t = some k := by
    intro t h1 h2 hw
    obtain ⟨m, hm, hbm⟩ := hw
    have hex0 : ¬ writesInBy (M.take σ'.n) (fun tid => tid ≠ some k) Lw t0 (ts - 1) := hex.1
    have hau : au M t = m.tid := by simp [au, hm]
    rw [hau]
    exact Classical.byContradiction fun hne => hex0 ⟨t, h1, by omega, m,
      by rw [List.getElem?_take, if_pos (by omega)]; exact hm, hbm, hne⟩
  -- the post-AMO state and the continuation (the tail)
  let ws1 := PF.qPosts (amoPost (storeRun (loadRun ws true false (srcsView ws (srcR 9)) Lw ((t0, b0) :: rest))
    false (srcsView ws (srcR 9)) ts Lw (toBytes 1 4).length ts) true ts) (regWL 15 [.DLdRes] ++ [LInstr])
  have hv1 : ts ≤ ws1.wVrNew ∧ ts ≤ ws1.wVwNew := by
    show ts ≤ (amoPost (storeRun (loadRun ws true false (srcsView ws (srcR 9)) Lw ((t0, b0) :: rest))
      false (srcsView ws (srcR 9)) ts Lw (toBytes 1 4).length ts) true ts).wVrNew ∧
      ts ≤ (amoPost (storeRun (loadRun ws true false (srcsView ws (srcR 9)) Lw ((t0, b0) :: rest))
      false (srcsView ws (srcR 9)) ts Lw (toBytes 1 4).length ts) true ts).wVwNew
    simp only [amoPost, if_true]; omega
  let w := ofBytes (((t0, b0) :: rest).map Prod.snd)
  have hwl : w < 2 ^ 32 := ofBytes4_lt hl4
  have cont : ∀ s2, LPstep s1 s2 (s1.pc + 1) 15 (Weak.Prom.Ref.sext 4 w) →
      LoopP M γm k X ∗ KA γc γm k (s2.rd 15) ts ws1 ⊢ WK M k X s2 ws1 := fun s2 hs2 =>
    hTail M γc γm γo k ko X hinv hX hko hk2 s2 ws1 ts (hs1'.succ hs2 (by decide) (by decide))
      (by rw [LPstep_rd hs2 14 (.inl (by decide)), e14])
      ⟨w, hwl, LPstep_rd_eq hs2 (by decide) (by rw [hs1'.len]; decide)⟩
  have hx15 : ∀ s2, LPstep s1 s2 (s1.pc + 1) 15 (Weak.Prom.Ref.sext 4 w) → (s2.rd 15 = 0 ↔ w = 0) := by
    intro s2 hs2
    rw [LPstep_rd_eq hs2 (by decide) (by rw [hs1'.len]; decide)]; exact sext4_zero w hwl
  have hb0w : b0 ≠ 0 → w ≠ 0 := by
    intro hb0 hw0
    apply hb0; apply amo_x5 hl3
    show Weak.Prom.Ref.sext 4 w % two64 = 0
    rw [hw0]; decide
  unfold hv
  icases Hmy with (Hmy | Hr)
  · -- phase 0: THE AMO LEAF
    ihave %e := ghost_var_agree γm _ _ _ _ $$ Hmy Hm
    obtain ⟨e1, e2, e3⟩ := pr_inj e
    rcases lk_acq hok (lkImg_zero Lw) e1.symm hful hM hmb' ht0 hwin with
        ⟨hb0, g', hok', hph', hrds', hmk', hsp', hcase'⟩ | ⟨hb0, g', hok', hsp', hph', hrds', hmk', hcr'⟩ |
        ⟨hb0, hspf, u, g', hok', hsp', hls', hph', hrds', hmk', hu, hhold, hts', htst, _, _, hcase'⟩
    · -- FAILED (phase stays 0): the loop
      have e4 : Pg g' k = MG.pr 0 none none := by simp [Pg, hph', hrds', hmk', upd, ← e2, ← e3]
      have e4' : Pg g k = MG.pr 0 none none := by simp [Pg, ← e1, ← e2, ← e3]
      have e5 : Pg g' ko = Pg g ko :=
        Pg_other hko (fun a ha => by rw [hph']; exact upd_ne _ _ ha) (fun a _ => by rw [hrds']) (fun a _ => by rw [hmk'])
      rw [e4']
      rcases hcase' with ⟨hls', hcr'⟩ | ⟨hspf, hfree, u', hpl⟩
      · imodintro
        isplitl [Hc Hm Ho Hb]
        · iapply (hX σ').2
          iexists g'
          have eR : Rbox (GF := GF) γc g'.spoil g'.ls g'.cr = Rbox γc g.spoil g.ls g.cr := by rw [hsp', hls', hcr']
          rw [e4, e5, eR, hcr']
          unfold hv
          iframe; ipureintro; exact hok'
        iintro %s2 %hs2
        iapply (cont s2 hs2)
        isplitl [IH]
        · iexact IH
        unfold KA
        ileft; isplitr
        · ipureintro; exact fun h => hb0w hb0 ((hx15 s2 hs2).1 h)
        · ileft; unfold hv; iexact Hmy
      · have eB : Rbox (GF := GF) γc g.spoil g.ls g.cr = hv γc (.xr g.cr) := by rw [hspf, hfree]; rfl
        rw [eB]
        unfold hv
        imod ghost_var_update_halves (MG.xr g'.cr) γc _ _ $$ Hc Hb with ⟨Hc, Hb⟩
        imodintro
        isplitl [Hc Hm Ho Hb]
        · iapply (hX σ').2
          iexists g'
          have eR : Rbox (GF := GF) γc g'.spoil g'.ls g'.cr = hv γc (.xr g'.cr) := by rw [hsp', hspf, hpl]; rfl
          rw [e4, e5, eR]
          unfold hv
          iframe; ipureintro; exact hok'
        iintro %s2 %hs2
        iapply (cont s2 hs2)
        isplitl [IH]
        · iexact IH
        unfold KA
        ileft; isplitr
        · ipureintro; exact fun h => hb0w hb0 ((hx15 s2 hs2).1 h)
        · ileft; unfold hv; iexact Hmy
    · -- A ROGUE (answer 0 from a dead message, or spoiled)
      have e4 : Pg g' k = MG.pr 3 none none := by simp [Pg, hph', hrds', hmk', upd, ← e2, ← e3]
      have e5 : Pg g' ko = Pg g ko :=
        Pg_other hko (fun a ha => by rw [hph']; exact upd_ne _ _ ha) (fun a _ => by rw [hrds']) (fun a _ => by rw [hmk'])
      imod ghost_var_update_halves (MG.pr 3 none none) γm _ _ $$ Hmy Hm with ⟨Hmy, Hm⟩
      imodintro
      isplitl [Hc Hm Ho]
      · iapply (hX σ').2
        iexists g'
        have eR : Rbox (GF := GF) γc g'.spoil g'.ls g'.cr = iprop(True) := by rw [hsp']; rfl
        rw [e4, e5, eR, hcr']
        unfold hv
        iframe; ipureintro; exact ⟨hok', trivial⟩
      iintro %s2 %hs2
      iapply (cont s2 hs2)
      isplitl [IH]
      · iexact IH
      unfold KA KB Rg hv
      by_cases hz : s2.rd 15 = 0
      · iright; isplitr
        · ipureintro; exact hz
        · ileft; iexists none, none; iexact Hmy
      · ileft; isplitr
        · ipureintro; exact hz
        · iright; iexists none, none; iexact Hmy
    · -- THE LOCK IS TAKEN: R moves to the hart
      have e5 : Pg g' ko = Pg g ko :=
        Pg_other hko (fun a ha => by rw [hph']; exact upd_ne _ _ ha) (fun a _ => by rw [hrds']) (fun a _ => by rw [hmk'])
      have hcr0 : g'.cr = g.cr ∨ (g.ls = .free ∧ g'.cr = { g.cr with hold := some k, tstart := u }) := by
        rcases hcase' with ⟨_, h⟩ | ⟨h1, h2⟩
        · exact .inl h
        · exact .inr ⟨h1, h2⟩
      have eB : Rbox (GF := GF) γc g.spoil g.ls g.cr = hv γc (.xr g.cr) := by
        rcases hcase' with ⟨hpl, _⟩ | ⟨hfree, _⟩
        · rw [hspf, hpl]; rfl
        · rw [hspf, hfree]; rfl
      rw [eB]
      unfold hv
      -- both halves of the counter's ghost follow the new record
      imod ghost_var_update_halves (MG.xr g'.cr) γc _ _ $$ Hc Hb with ⟨Hc, Hb⟩
      by_cases hhi : ∀ (j t : Nat) (b : BitVec 8), 1 ≤ j → ((t0, b0) :: rest)[j]? = some (t, b) → b = 0
      · -- every byte read 0: x15 = 0, the critical section
        have hw0 : w = 0 := by
          apply ofBytes4_of_zero hl4
          intro j t b hj
          rcases Nat.eq_zero_or_pos j with rfl | hj1
          · simp at hj; obtain ⟨_, rfl⟩ := hj; exact hb0
          · exact hhi j t b hj1 hj
        have e4 : Pg g' k = MG.pr 1 none none := by simp [Pg, hph', hrds', hmk', upd, ← e2, ← e3]
        imod ghost_var_update_halves (MG.pr 1 none none) γm _ _ $$ Hmy Hm with ⟨Hmy, Hm⟩
        have eR : Rbox (GF := GF) γc g'.spoil g'.ls g'.cr = iprop(True) := by rw [hsp', hls']; rfl
        imodintro
        isplitl [Hc Hm Ho]
        · iapply (hX σ').2
          iexists g'
          rw [e4, e5, eR]
          unfold hv
          iframe; ipureintro; exact ⟨hok', trivial⟩
        iintro %s2 %hs2
        iapply (cont s2 hs2)
        isplitl [IH]
        · iexact IH
        unfold KA KB Rg hv
        iright; isplitr
        · ipureintro; exact (hx15 s2 hs2).2 hw0
        · iright; iexists g'.cr; iframe Hmy Hb
          ipureintro
          exact ⟨hhold, by omega, by omega, hv1.1, hv1.2⟩
      · -- a nonzero high byte: a dead lock message; SPOIL, rogue
        have hdead : ∃ t, g'.Dl t := by
          refine Classical.byContradiction fun hno => hhi fun j t b hj1 hj => ?_
          have hj4 : j < 4 := by
            have := (List.getElem?_eq_some_iff.1 hj).1; simp at this; omega
          obtain ⟨hmbj, htj, _⟩ := loadOk_byte (j := j) hinv hlo hj
          rcases lk_hiByte (lkImg_zero) hok' hsp' hj1 hj4 hmbj htj with h0 | hdj
          · exact h0
          · exact absurd ⟨t, hdj⟩ hno
        obtain ⟨td, hd⟩ := hdead
        have hok'' := lk_spoil (h := k) hok' hd
        have e4 : Pg { g' with bad := true, spoil := true, ph := upd g'.ph k 3 } k = MG.pr 3 none none := by
          simp [Pg, hph', hrds', hmk', upd, ← e2, ← e3]
        have e5' : Pg { g' with bad := true, spoil := true, ph := upd g'.ph k 3 } ko = Pg g ko := by
          rw [← e5]; exact Pg_other hko (upd_other _ _ _) (fun _ _ => rfl) (fun _ _ => rfl)
        imod ghost_var_update_halves (MG.pr 3 none none) γm _ _ $$ Hmy Hm with ⟨Hmy, Hm⟩
        imodintro
        isplitl [Hc Hm Ho]
        · iapply (hX σ').2
          iexists { g' with bad := true, spoil := true, ph := upd g'.ph k 3 }
          have eR : Rbox (GF := GF) γc ({ g' with bad := true, spoil := true, ph := upd g'.ph k 3 } : LkS).spoil
              ({ g' with bad := true, spoil := true, ph := upd g'.ph k 3 } : LkS).ls
              ({ g' with bad := true, spoil := true, ph := upd g'.ph k 3 } : LkS).cr = iprop(True) := rfl
          rw [e4, e5', eR]
          unfold hv
          iframe; ipureintro; exact ⟨hok'', trivial⟩
        iintro %s2 %hs2
        iapply (cont s2 hs2)
        isplitl [IH]
        · iexact IH
        unfold KA KB Rg hv
        by_cases hz : s2.rd 15 = 0
        · iright; isplitr
          · ipureintro; exact hz
          · ileft; iexists none, none; iexact Hmy
        · ileft; isplitr
          · ipureintro; exact hz
          · iright; iexists none, none; iexact Hmy
  · -- A ROGUE AT THE LOOP HEAD: spoiled mode
    unfold Rg hv
    icases Hr with ⟨%rd, %mk, Hmy⟩
    ihave %e := ghost_var_agree γm _ _ _ _ $$ Hmy Hm
    obtain ⟨e1, _, _⟩ := pr_inj e
    have hsp := hok.ph3 k e1.symm
    have hnd : ¬ g.Dl ts := fun hd => (hok.dl ts hd).2.2.2.2 ⟨k, hM⟩
    imodintro
    isplitl [Hc Hm Ho Hb]
    · iapply (hX σ').2
      iexists g; unfold hv; iframe; ipureintro; exact lk_fulS hok hsp hful hnd
    iintro %s2 %hs2
    iapply (cont s2 hs2)
    isplitl [IH]
    · iexact IH
    unfold KA KB Rg hv
    by_cases hz : s2.rd 15 = 0
    · iright; isplitr
      · ipureintro; exact hz
      · ileft; iexists rd, mk; iexact Hmy
    · ileft; isplitr
      · ipureintro; exact hz
      · iright; iexists rd, mk; iexact Hmy

/-- **THE SPIN LOOP** (`again:` at pc 1, by Löb induction): `mv a5,a4`, then the AMO (`hAmo`). -/
theorem hLoop (hinv : invalFree M) (hX : ∀ σ, (X σ ⊢ Xf M γc γm γo k ko σ) ∧ (Xf M γc γm γo k ko σ ⊢ X σ))
    (hko : ko ≠ k) (hk2 : k < 2) : ⊢ LoopP (GF := GF) M γm k X := by
  iloeb as IH
  unfold LoopP
  iintro %s %ws %hs0 Hmy
  obtain ⟨hs, h14⟩ := hs0
  iapply (wpT_alui (op := .add) (rd := 15) (rs1 := 14) (imm := 0) hs.q (hs.xp rfl rfl) (by rw [hs.prog, hs.pc]; rfl)
    (by decide))
  iintro %s1 %hs1
  have e15 : s1.rd 15 = 1 := by
    rw [LPstep_rd_eq hs1 (by decide) (by rw [hs.len]; decide)]; simp [Weak.Prom.Ref.aluOp, h14, two64]
  have e14 : s1.rd 14 = 1 := by rw [LPstep_rd hs1 14 (.inl (by decide)), h14]
  iapply (hAmo M γc γm γo k ko X hinv hX hko hk2 s1 _ (hs.succ hs1 (by decide) (by decide)) e15 e14)
  isplitr
  · unfold LoopP; iexact IH
  · iexact Hmy

/-- `li a4,1`, then the loop. -/
theorem hStart (hinv : invalFree M) (hX : ∀ σ, (X σ ⊢ Xf M γc γm γo k ko σ) ∧ (Xf M γc γm γo k ko σ ⊢ X σ))
    (hko : ko ≠ k) (hk2 : k < 2) (s : LP) (hs : HS s 0) :
    hv (GF := GF) γm (.pr 0 none none) ⊢ WK M k X s psInit := by
  iintro Hmy
  iapply (wpT_alui (op := .add) (rd := 14) (rs1 := 0) (imm := 1) hs.q (hs.xp rfl rfl) (by rw [hs.prog, hs.pc]; rfl)
    (by decide))
  iintro %s1 %hs1
  have e14 : s1.rd 14 = 1 := by
    rw [LPstep_rd_eq hs1 (by decide) (by rw [hs.len]; decide)]; simp [Weak.Prom.Ref.aluOp, LP.rd, two64]
  have hL := hLoop M γc γm γo k ko X hinv hX hko hk2
  unfold LoopP at hL
  iapply hL
  · ipureintro; exact ⟨hs.succ hs1 (by decide) (by decide), e14⟩
  · ileft; iexact Hmy

end hart

/-! ## 4. The agent, the end, the verdict -/

section top

variable [InvGS_gen hlc GF] (M : List PMsg) (γc γ0 γ1 : GName)

/-- THE PROMISE AGENT, with THE (b1) PULL (as OwnLock.lean, over the (1c) protocol). -/
theorem lk_agentI :
    ⊢ □ (∀ σ σ', ⌜agentStep (xOW lk1cXs lkImg M) σ σ'⌝ -∗ Xl (GF := GF) M γc γ0 γ1 σ -∗ |={⊤}=> Xl M γc γ0 γ1 σ') := by
  imodintro
  iintro %σ %σ' %ha HX
  icases HX with ⟨%g, Hc, H0, H1, %hok, Hb⟩
  obtain ⟨g', hok', hph, hrds, hmk, hsp, _, _, hcase⟩ := lk_agent (img := lkImg) (M := M) hok ha
  have e0 : Pg g' 0 = Pg g 0 := by simp [Pg, hph, hrds, hmk]
  have e1 : Pg g' 1 = Pg g 1 := by simp [Pg, hph, hrds, hmk]
  rcases hcase with ⟨hls, hcr⟩ | ⟨hspf, hfree, i, u, hpl⟩
  · imodintro
    iexists g'
    have eR : Rbox (GF := GF) γc g'.spoil g'.ls g'.cr = Rbox γc g.spoil g.ls g.cr := by rw [hsp, hls, hcr]
    rw [e0, e1, eR, hcr]
    iframe; ipureintro; exact hok'
  · have eB : Rbox (GF := GF) γc g.spoil g.ls g.cr = hv γc (.xr g.cr) := by rw [hspf, hfree]; rfl
    rw [eB]
    unfold hv
    imod ghost_var_update_halves (MG.xr g'.cr) γc _ _ $$ Hc Hb with ⟨Hc, Hb⟩
    imodintro
    iexists g'
    have eR : Rbox (GF := GF) γc g'.spoil g'.ls g'.cr = hv γc (.xr g'.cr) := by rw [hsp, hspf, hpl]; rfl
    rw [e0, e1, eR]
    unfold hv
    iframe; ipureintro; exact hok'

theorem lk_finalI :
    ⊢ ∀ σ, ⌜σ.n = (xOW lk1cXs lkImg M).M.length ∧ ∀ h, σ.pr h = ∅⌝ -∗ Xl (GF := GF) M γc γ0 γ1 σ -∗
      |={⊤,∅}=> ⌜∀ r0 r1, σ.done 0 = some r0 → σ.done 1 = some r1 → lkSpec r0 r1⌝ := by
  iintro %σ %hfin HX
  icases HX with ⟨%g, -, -, -, %hok, -⟩
  iapply fupd_mask_intro_discard Std.LawfulSet.empty_subset
  ipureintro
  exact lk_final hok hfin.2

end top

/-- Hart `cpu - 1`'s initial program state. -/
def q1c (cpu : Nat) : LP :=
  ⟨lk1cProg, 0, (List.range 32).map (fun r => (((regs1c cpu).lookup r).getD 0) % two64), []⟩

theorem progs_lk1cT : progs lk1cT = [q1c 1, q1c 2] := rfl

/-- **G4 TARGETS (1c) AND (3) ON TRACK (b): XV6'S EXACT ACQUIRE/RELEASE TEXT** (`li a4,1; again: mv a5,a4;
amoswap.w.aq a5,a5,(s1); sext.w a5,a5; bnez a5,again; sd a0,16(s1)` … `sd zero,16(s1); fence rw,w; sw zero,0(s1)`,
with release's `holding()` read `lw a3,0(s1); beqz a3,panic` inlined) around a counter (`ld; addi; sd`).  In every
valid machine-v2 run of `lk1cT` (loop front end), if both harts finished, their final x7 (counter value + 1) differ
— mutual exclusion — and both `holding()` reads returned nonzero (x13 ≠ 0: `panic` is never reached). -/
theorem g4_lock1c {evs : List PEvt} {cfg : PCfg LP Unit}
    (hvr : validRun (xStep lk1cXs) (testImg lk1cT) () (progs lk1cT) evs cfg)
    {r0 r1 : List Nat} (h0 : doneOf (xOW lk1cXs lkImg cfg.pcLog) (progs lk1cT).length cfg 0 = some r0)
    (h1 : doneOf (xOW lk1cXs lkImg cfg.pcLog) (progs lk1cT).length cfg 1 = some r1) : lkSpec r0 r1 := by
  rw [lk1cImg] at hvr
  have hps : ∀ p ∈ progs lk1cT, p.q = [] := by
    rw [progs_lk1cT]; intro p hp; simp at hp; rcases hp with rfl | rfl <;> rfl
  have hinv := x_invalFree hvr hps
  have key := ownAdequacy (hlc := HasLC.hasLC) (GF := lkGF) (w := xOW lk1cXs lkImg cfg.pcLog) (ps := progs lk1cT)
    (fun done => ∀ r0 r1, done 0 = some r0 → done 1 = some r1 → lkSpec r0 r1) (fun {_} => by
      iintro
      imod ghost_var_alloc (MG.xr ⟨none, 0, 0, 0⟩) with ⟨%γc, Hc⟩
      imod ghost_var_alloc (MG.pr 0 none none) with ⟨%γ0, H0⟩
      imod ghost_var_alloc (MG.pr 0 none none) with ⟨%γ1, H1⟩
      have s1 := ghost_var_split (GF := lkGF) γc (MG.xr ⟨none, 0, 0, 0⟩) (1 : Qp).half (1 : Qp).half
      have s2 := ghost_var_split (GF := lkGF) γ0 (MG.pr 0 none none) (1 : Qp).half (1 : Qp).half
      have s3 := ghost_var_split (GF := lkGF) γ1 (MG.pr 0 none none) (1 : Qp).half (1 : Qp).half
      rw [Qp.half_add_half] at s1 s2 s3
      ihave ⟨Hc1, Hc2⟩ := s1 $$ Hc
      ihave ⟨H01, H02⟩ := s2 $$ H0
      ihave ⟨H11, H12⟩ := s3 $$ H1
      imodintro
      iexists Xl cfg.pcLog γc γ0 γ1
      isplitl [Hc1 Hc2 H01 H11]
      · iexists g0
        have eR : Rbox (GF := lkGF) γc g0.spoil g0.ls g0.cr = hv γc (.xr ⟨none, 0, 0, 0⟩) := rfl
        have ec : (g0.cr : XRec) = ⟨none, 0, 0, 0⟩ := rfl
        have ep : ∀ j, Pg g0 j = MG.pr 0 none none := fun _ => rfl
        rw [eR, ep 0, ep 1, ec]
        unfold hv
        iframe
        ipureintro; exact lk_init (M := cfg.pcLog) lkImg_zero
      isplitr
      · iapply lk_agentI
      isplitl [H02 H12]
      · rw [progs_lk1cT]
        simp only [hartsFrom]
        iapply BigSepL.bigSepL_cons.2
        isplitl [H02]
        · ihave H := hStart (hlc := HasLC.hasLC) cfg.pcLog γc γ0 γ1 0 1 (Xl cfg.pcLog γc γ0 γ1) hinv
            (fun σ => ⟨.rfl, .rfl⟩) (by decide) (by decide) (q1c 1)
            ⟨rfl, rfl, rfl, by decide, by decide, by decide⟩ $$ [H02]
          · unfold hv; iexact H02
          iapply H
        iapply BigSepL.bigSepL_cons.2
        isplitl [H12]
        · ihave H := hStart (hlc := HasLC.hasLC) cfg.pcLog γc γ1 γ0 1 0 (Xl cfg.pcLog γc γ0 γ1) hinv
            (fun σ => ⟨(Xl_swap cfg.pcLog γc γ0 γ1 σ).1, (Xl_swap cfg.pcLog γc γ0 γ1 σ).2⟩) (by decide) (by decide)
            (q1c 2) ⟨rfl, rfl, rfl, by decide, by decide, by decide⟩ $$ [H12]
          · unfold hv; iexact H12
          iapply H
        exact BigSepL.bigSepL_nil_intro
      · iapply lk_finalI) hvr rfl (x_fetchBounded hvr hps) hinv
  exact key r0 r1 h0 h1

/-- **G4 (1c) + (3), on the final configuration**: if both harts ran their whole text, their final x7 differ and
both `holding()` reads (x13) were nonzero. -/
theorem g4_lock1c_regs {evs : List PEvt} {cfg : PCfg LP Unit}
    (hvr : validRun (xStep lk1cXs) (testImg lk1cT) () (progs lk1cT) evs cfg)
    {a0 a1 : PAgent LP} (ha0 : cfg.pcAgs[0]? = some a0) (ha1 : cfg.pcAgs[1]? = some a1)
    (hd0 : a0.paSt.q = [] ∧ a0.paSt.prog.length ≤ a0.paSt.pc) (hd1 : a1.paSt.q = [] ∧ a1.paSt.prog.length ≤ a1.paSt.pc) :
    a0.paSt.rd 7 ≠ a1.paSt.rd 7 ∧ a0.paSt.rd 13 ≠ 0 ∧ a1.paSt.rd 13 ≠ 0 := by
  have h := g4_lock1c hvr (r0 := a0.paSt.regs) (r1 := a1.paSt.regs)
    (by simp only [doneOf, show (0 : Nat) < (progs lk1cT).length by rw [progs_lk1cT]; decide, if_true, ha0,
      Option.bind_some]; exact litDoneR_end hd0.1 hd0.2)
    (by simp only [doneOf, show (1 : Nat) < (progs lk1cT).length by rw [progs_lk1cT]; decide, if_true, ha1,
      Option.bind_some]; exact litDoneR_end hd1.1 hd1.2)
  unfold lkSpec at h
  rw [rd_regs _ 7 (by omega), rd_regs _ 7 (by omega), rd_regs _ 13 (by omega), rd_regs _ 13 (by omega)] at h
  exact h

end Weak.Prom.Own.X.L1c
