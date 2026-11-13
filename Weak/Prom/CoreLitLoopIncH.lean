/-
Weak/Prom: **MP FOREVER WITH A COUNTER — the harts, in the logic, and the theorems** (owner request 2026-11-13;
plan rev 7 §2 "Leaf rules", "Adequacy A0", §5 row 8 per iteration).  The program, the Ψs and the property are in
CoreLitLoopInc.lean.
* `lit_mpLoopInc` — over every final memory and every valid run (no `done` premise: no hart ever finishes), every
  hart's trace satisfies `qLoopInc M` (RVWMO rule 4 twice, rule 1 and the coherence axiom for hart 0's
  same-address stores; the manual's MP+fence.w.w+fence.r.r row, per iteration, with distinct values).
* `loopInc_noDone` — no hart is ever done (pure, from the front end).
Logic: the base logic A0 (`PF.adequacy`, export (ii), via CoreLitLoop's `kitAdeqX`) with `Proto.triv`; the kit
(CoreKit.lean) over the loop front end's worlds, plus CoreLitLoop's `wpK_brx`.  Each hart's wp is a Löb induction
at its loop head.  Hart 0's loop invariant carries the iteration number `i` (`t1 = rv i`, `2 i` memory entries)
and two view facts (`I0`: every own store is below `vwOld`, every data store below `vwNew`).
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.CoreLitLoopInc

namespace Weak.Prom.PF.LoopInc

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.PF Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.OA (XI xNext xStep xW xOf)
open Weak.Prom.Ref (Instr Test two64 brEval aluOp)
open Weak.Prom.Ref.Lit (X Y)
open Weak.Prom.PF.Loop (adj adj_snoc ldRet ldF ldD ldF_D wpK_brx qPostsL rr_le kitAdeqX instrNext_pc h1S)
open PLabel
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode

/-! ## 1. Hart 1's Ψ, step by step -/

theorem fwdHit_empty {ws : PState} (hf : ws.wFwd = ∅) (a : Int) (t : Nat) : fwdHit ws a t = false := by
  unfold fwdHit; rw [hf, lookupEmpty]

/-- **A load without forwarding is single-copy atomic** (machine v2's `loadOk`, M9: every non-forwarded byte's floor
is raised to the common read point). -/
theorem sca_of {img : Image} {M : List PMsg} {ws : PState} {vpre : Nat} {base : Int} {tvs : List (Nat × BitVec 8)}
    (hf : ws.wFwd = ∅) (hnc : noCmo M) (hlo : loadOk img M ws vpre base tvs) : scaP M base tvs := by
  have hnf : nonFwdMax ws base tvs = bytesMax (fun _ t => t) base tvs := by
    unfold nonFwdMax
    have : (fun a t => if fwdHit ws a t then 0 else t) = (fun (_ : Int) (t : Nat) => t) :=
      funext fun a => funext fun t => by rw [fwdHit_empty hf]; rfl
    rw [this]
  unfold loadOk at hlo
  unfold scaP
  refine bytesAll_mono (fun a t v h hc => ?_) base tvs hlo
  have hw := h.2.resolve_right (noInval hnc)
  rw [fwdHit_empty hf, hnf] at hw
  exact hw (writesIn_mono hc (by simp only [Bool.false_eq_true, if_false]; omega))

theorem Q1_flag {M : List PMsg} {ev : Trace} {tvs : List (Nat × BitVec 8)} (h : Q1 M ev) (hl : tvs.length = 4)
    (hs : noCmo M → scaP M Y tvs) :
    Q1 M (ev ++ [(LLoad false false (Y : Int) tvs (srcR 13), none)]) := by
  have hF : ldF (LLoad false false (Y : Int) tvs (srcR 13), none) := ⟨tvs, by simp, hl⟩
  refine ⟨fun e he => ?_, adj_snoc h.2 (fun _ _ _ hD => (ldF_D hF hD).elim)⟩
  rcases List.mem_append.1 he with he | he
  · exact h.1 e he
  · rw [List.mem_singleton] at he; subst he; exact .inl ⟨tvs, rfl, hl, hs⟩

theorem Q1_data {M : List PMsg} {ev : Trace} {eF : PEv} {tvs : List (Nat × BitVec 8)} (h : Q1 M (ev ++ [eF]))
    (hl : tvs.length = 4) (hs : noCmo M → scaP M X tvs)
    (hord : noCmo M → ¬ writesIn M (X : Int) (src0 (LLoad false false (X : Int) tvs (srcR 12), none)) (src0 eF)) :
    Q1 M (ev ++ [eF] ++ [(LLoad false false (X : Int) tvs (srcR 12), none)]) := by
  refine ⟨fun e he => ?_, adj_snoc h.2 (fun e0 he0 _ _ => ?_)⟩
  · rcases List.mem_append.1 he with he | he
    · exact h.1 e he
    · rw [List.mem_singleton] at he; subst he; exact .inr ⟨tvs, rfl, hl, hs⟩
  · simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or, Option.some.injEq] at he0
    subst he0
    exact hord

/-! ## 2. Hart 0's views -/

theorem vwNew_le_stPreA (ws : PState) (aq rl : Bool) (va vd : Nat) : ws.wVwNew ≤ stPreA ws aq rl va vd := by
  simp only [stPreA, stPre]; omega

/-- `st; fence w,w; st`: every store before the fence is below the second store's pre-view (rule 4). -/
theorem ww_le2 (ws : PState) (va fv : Nat) (base : Int) (n tx : Nat) (aq rl : Bool) (va' vd' : Nat) :
    max ws.wVwOld tx ≤ stPreA (instrR (fencePost (instrR (acqPost (storeRun ws false va fv base n tx) false tx))
      false true false true)) aq rl va' vd' := by
  have h := (storeRun_mono ws false va fv base n tx).2.2.1
  simp only [stPreA, stPre, instrR, fencePost, acqPost, if_true, if_false, Bool.false_eq_true]
  omega

/-- The views at the next loop head. -/
theorem head_views (ws : PState) (va fv va2 fv2 : Nat) (b b2 : Int) (n n2 tx ty : Nat) (r1 r2 : List Dsrc) :
    let ws5 := instrR (ctrlP (instrR (regWP (instrR (acqPost (storeRun (instrR (fencePost (instrR (acqPost
      (storeRun ws false va fv b n tx) false tx)) false true false true)) false va2 fv2 b2 n2 ty) false ty)) 6 r1)) r2)
    ws5.wVwOld = max (max ws.wVwOld tx) ty ∧ ws5.wVwNew = max ws.wVwNew (max ws.wVwOld tx) := by
  have h1 := storeRun_mono ws false va fv b n tx
  have h2 := storeRun_mono (instrR (fencePost (instrR (acqPost (storeRun ws false va fv b n tx) false tx))
    false true false true)) false va2 fv2 b2 n2 ty
  simp only [instrR, ctrlP, regWP, acqPost, fencePost, if_true, if_false, Bool.false_eq_true] at h2 ⊢
  rw [h2.2.2.1, h2.2.2.2.2.1, h1.2.2.1, h1.2.2.2.2.1]
  exact ⟨rfl, by omega⟩

/-! ## 3. The harts, by Löb induction -/

section harts

variable {hlc : HasLC} {GF : BundledGFunctors} [GhostVarG GF HSt] [InvGS_gen hlc GF]

/-- Hart 0 at its loop head, in iteration `i`. -/
def h0S (i : Nat) (s : LP) : Prop :=
  s.prog = bI0 ∧ s.q = [] ∧ s.pc = 0 ∧ s.regs.length = 32 ∧ s.rd 6 = rv i ∧ s.rd 12 = X ∧ s.rd 13 = Y

/-- Hart 0's view invariant at the loop head: `2 i` entries, all below `vwOld`, the data stores below `vwNew`. -/
def I0 (i : Nat) (ws : PState) (ev : Trace) : Prop :=
  ev.length = 2 * i ∧ (∀ e ∈ ev, tsOf e ≤ ws.wVwOld) ∧ (∀ j e, ev[j]? = some e → j % 2 = 0 → tsOf e ≤ ws.wVwNew)

/-- **HART 0's LOOP** (Löb at `pc = 0`, for every iteration number). -/
theorem h0_loop (img : Image) (M : List PMsg) (h : Nat) (γ : GName) :
    ⊢@{IProp GF} ∀ (i : Nat) (s : LP) (ws : PState) (pr : GSet Nat) (ev : Trace), ⌜h0S i s⌝ -∗ ⌜Q0 ev⌝ -∗
      lh γ Proto.triv (xW xsLoopInc img M h) Q0 ws pr ev -∗ ⌜I0 i ws ev⌝ -∗
      wpK γ Proto.triv (xW xsLoopInc img M h) Q0 s (fun _ => iprop(⌜∃ V, grd Proto.triv img M V True⌝)) := by
  have hw := OA.litW_x xsLoopInc img M h
  iloeb as IH
  iintro %i %s0 %ws0 %pr0 %ev %hs %hQ Hl %hI
  obtain ⟨hP0, hq0, hc0, hl0, h6, h12, h13⟩ := hs
  obtain ⟨hlen, hold, hnew⟩ := hI
  -- `sw t1,0(a2)`
  iapply (wpK_sw (sz := 4) (rs2 := 6) (rs1 := 12) (off := 0) (base := (X : Int)) hw
    (OA.litAg_x hq0 (by rw [hP0]; exact xOf_I0) (by rw [hc0]; rfl) rfl) hq0 (by rw [hP0, hc0]; rfl)
    (alg_of h12 (by decide) (by decide)) (base_of h12 (by decide)))
  iframe Hl
  inext
  iintro %tx %_ %_ %_ %hx
  have htx : 0 < tx := by omega
  have hDi : stD i (LStore false false (X : Int) (toBytes (s0.rd 6) 4) (srcR 12) (srcR 6), some tx) :=
    ⟨tx, htx, by rw [h6]; rfl⟩
  have hQa := Q0_snoc hQ (by rw [hlen]; exact sh0_even hDi)
    (fun j e' he' hj => Nat.lt_of_le_of_lt (hnew j e' he' (by omega))
      (Nat.lt_of_le_of_lt (vwNew_le_stPreA _ _ _ _ _) hx))
    (fun _ hp _ => absurd hp (by omega))
  imodintro
  isplitr
  · ipureintro; exact ⟨0, grd_intro hQa⟩
  isplitr
  · ipureintro; exact grd_intro trivial
  iintro %s1 %hs1 Hl
  obtain ⟨hP1, hc1, hq1⟩ := LPstep_at hs1 hP0 (by rw [hc0])
  -- `fence w,w`
  iapply (wpK_fence (f := ⟨false, true, false, false, false, true, false, false⟩) hw
    (OA.litAg_x hq1 (by rw [hP1]; exact xOf_I0) (by rw [hc1]; rfl) rfl) hq1 (by rw [hP1, hc1]; rfl))
  iframe Hl
  inext
  iintro %s2 %hs2 Hl
  obtain ⟨hP2, hc2, hq2⟩ := LPstep_at hs2 hP1 (by rw [hc1])
  have e6 : s2.rd 6 = rv i := by rw [LPstep_rd hs2 6 (.inr rfl), LPstep_rd hs1 6 (.inr rfl), h6]
  have e12 : s2.rd 12 = X := by rw [LPstep_rd hs2 12 (.inr rfl), LPstep_rd hs1 12 (.inr rfl), h12]
  have e13 : s2.rd 13 = Y := by rw [LPstep_rd hs2 13 (.inr rfl), LPstep_rd hs1 13 (.inr rfl), h13]
  -- `sw t1,0(a3)`
  iapply (wpK_sw (sz := 4) (rs2 := 6) (rs1 := 13) (off := 0) (base := (Y : Int)) hw
    (OA.litAg_x hq2 (by rw [hP2]; exact xOf_I0) (by rw [hc2]; rfl) rfl) hq2 (by rw [hP2, hc2]; rfl)
    (alg_of e13 (by decide) (by decide)) (base_of e13 (by decide)))
  iframe Hl
  inext
  iintro %ty %_ %_ %_ %hy
  have hall : ∀ e' ∈ ev ++ [(LStore false false (X : Int) (toBytes (s0.rd 6) 4) (srcR 12) (srcR 6), some tx)],
      tsOf e' < ty := by
    have hle := Nat.lt_of_le_of_lt (ww_le2 _ _ _ _ _ _ _ _ _ _) hy
    intro e' he'
    rcases List.mem_append.1 he' with he' | he'
    · have := hold e' he'; omega
    · rw [List.mem_singleton] at he'; subst he'; show tx < ty; omega
  have hFi : stF i (LStore false false (Y : Int) (toBytes (s2.rd 6) 4) (srcR 13) (srcR 6), some ty) :=
    ⟨ty, by omega, by rw [e6]; rfl⟩
  have hQb := Q0_snoc hQa (e := (LStore false false (Y : Int) (toBytes (s2.rd 6) 4) (srcR 13) (srcR 6), some ty))
    (by simp only [List.length_append, List.length_singleton, hlen]; exact sh0_odd hFi)
    (fun j e' he' _ => hall e' (List.mem_of_getElem? he'))
    (fun e' _ he' => hall e' (List.mem_of_getElem? he'))
  imodintro
  isplitr
  · ipureintro; exact ⟨0, grd_intro hQb⟩
  isplitr
  · ipureintro; exact grd_intro trivial
  iintro %s3 %hs3 Hl
  obtain ⟨hP3, hc3, hq3⟩ := LPstep_at hs3 hP2 (by rw [hc2])
  have f6 : s3.rd 6 = rv i := by rw [LPstep_rd hs3 6 (.inr rfl), e6]
  have f12 : s3.rd 12 = X := by rw [LPstep_rd hs3 12 (.inr rfl), e12]
  have f13 : s3.rd 13 = Y := by rw [LPstep_rd hs3 13 (.inr rfl), e13]
  have hl3 : s3.regs.length = 32 := by rw [LPstep_len hs3, LPstep_len hs2, LPstep_len hs1, hl0]
  -- `addi t1,t1,1`
  iapply (wpK_alui (op := .add) (rd := 6) (rs1 := 6) (imm := 1) hw
    (OA.litAg_x hq3 (by rw [hP3]; exact xOf_I0) (by rw [hc3]; rfl) rfl) hq3 (by rw [hP3, hc3]; rfl) (by decide))
  iframe Hl
  inext
  iintro %s4 %hs4 Hl
  obtain ⟨hP4, hc4, hq4⟩ := LPstep_at hs4 hP3 (by rw [hc3])
  have g6 : s4.rd 6 = rv (i + 1) := by rw [LPstep_rd_eq hs4 (by decide) (by omega), f6, addi_rv]
  have g12 : s4.rd 12 = X := by rw [LPstep_rd hs4 12 (.inl (by decide)), f12]
  have g13 : s4.rd 13 = Y := by rw [LPstep_rd hs4 13 (.inl (by decide)), f13]
  have hl4 : s4.regs.length = 32 := by rw [LPstep_len hs4, hl3]
  -- `beq zero,zero,0`
  iapply (wpK_brx (Xs := xsLoopInc) hw (OA.xAg_x xsLoopInc img M h s4) hq4 (by rw [hP4]; exact xOf_I0)
    (by rw [hc4]; rfl) (Nat.zero_le _))
  iframe Hl
  inext
  iintro %s5 %hs5 Hl
  have hs5' : LPstep s4 s5 0 0 0 := by simpa [brEval] using hs5
  obtain ⟨hP5, hc5, hq5⟩ := LPstep_at hs5' hP4 rfl
  have hS5 : h0S (i + 1) s5 := ⟨hP5, hq5, hc5, by rw [LPstep_len hs5', hl4],
    by rw [LPstep_rd hs5' 6 (.inr rfl), g6], by rw [LPstep_rd hs5' 12 (.inr rfl), g12],
    by rw [LPstep_rd hs5' 13 (.inr rfl), g13]⟩
  iapply IH $$ %(i + 1) %s5 %_ %_ %_ %hS5 %hQb Hl
  ipureintro
  obtain ⟨hvo, hvn⟩ := head_views ws0 _ _ _ _ _ _ _ _ tx ty _ _
  refine ⟨by simp only [List.length_append, List.length_singleton, hlen]; omega, fun e' he' => ?_,
    fun j e' he' hj => ?_⟩
  · rw [hvo]
    rcases List.mem_append.1 he' with he' | he'
    · have := hall e' he'; omega
    · rw [List.mem_singleton] at he'; subst he'; show ty ≤ _; omega
  · rw [hvn]
    rcases get_snoc he' with ⟨hj1, he'⟩ | ⟨hj1, _⟩
    · rcases get_snoc he' with ⟨_, he'⟩ | ⟨_, rfl⟩
      · have := hnew j e' he' hj; omega
      · show tx ≤ _; omega
    · simp only [List.length_append, List.length_singleton, hlen] at hj1; omega

theorem h0_wp (img : Image) (M : List PMsg) (h : Nat) (s0 : LP) (hs : h0S 0 s0) :
    ⊢@{IProp GF} wpPF Proto.triv (xW xsLoopInc img M h) (ΨK M Q0) s0
      (fun _ => iprop(⌜∃ V, grd Proto.triv img M V True⌝)) := by
  iapply (wpK_start Q0_nil)
  iintro %γ %P0 Hl
  ihave H := h0_loop (GF := GF) img M h γ
  iapply H $$ %0 %s0 %_ %_ %_ %hs %Q0_nil Hl
  ipureintro
  exact ⟨rfl, fun _ he => (by cases he), fun _ _ he => (by simp at he)⟩

/-- **HART 1's LOOP** (Löb at `pc = 0`; CoreLitLoop's proof, recording single-copy atomicity). -/
theorem h1_loop (img : Image) (M : List PMsg) (h : Nat) (γ : GName)
    (hnoinv : ∀ t a, ¬ cmoAt M isInvalK t a) :   -- MachFix-R-b5
    ⊢@{IProp GF} ∀ (s : LP) (ws : PState) (pr : GSet Nat) (ev : Trace), ⌜h1S s⌝ -∗ ⌜Q1 M ev⌝ -∗
      lh γ Proto.triv (xW xsLoopInc img M h) (Q1 M) ws pr ev -∗ ⌜ws.wFwd = ∅⌝ -∗
      wpK γ Proto.triv (xW xsLoopInc img M h) (Q1 M) s (fun _ => iprop(⌜∃ V, grd Proto.triv img M V True⌝)) := by
  have hw := OA.litW_x xsLoopInc img M h
  iloeb as IH
  iintro %s0 %ws0 %pr0 %ev %hs %hQ Hl %hf
  obtain ⟨hP0, hq0, hc0, h12, h13⟩ := hs
  -- `lw a0,0(a3)`
  iapply (wpK_ld (sz := 4) (sgn := true) (rd := 10) (rs1 := 13) (off := 0) (base := (Y : Int)) hw
    (OA.litAg_x hq0 (by rw [hP0]; exact xOf_I1) (by rw [hc0]; rfl) rfl) hq0 (by rw [hP0, hc0]; rfl)
    (alg_of h13 (by decide) (by decide)) (base_of h13 (by decide)))
  iframe Hl
  inext
  iintro %tvs0 %hl0 %hlo0
  have hQa := Q1_flag hQ hl0 (fun hnc => sca_of hf hnc hlo0)
  imodintro
  isplitr
  · ipureintro; exact ⟨0, grd_intro hQa⟩
  iintro %s1 %hs1 Hl
  obtain ⟨hP1, hc1, hq1⟩ := LPstep_at hs1 hP0 (by rw [hc0])
  have e12 : s1.rd 12 = X := by rw [LPstep_rd hs1 12 (.inl (by decide)), h12]
  have e13 : s1.rd 13 = Y := by rw [LPstep_rd hs1 13 (.inl (by decide)), h13]
  -- `fence r,r`
  iapply (wpK_fence (f := ⟨true, false, false, false, true, false, false, false⟩) hw
    (OA.litAg_x hq1 (by rw [hP1]; exact xOf_I1) (by rw [hc1]; rfl) rfl) hq1 (by rw [hP1, hc1]; rfl))
  iframe Hl
  inext
  iintro %s2 %hs2 Hl
  obtain ⟨hP2, hc2, hq2⟩ := LPstep_at hs2 hP1 (by rw [hc1])
  have f12 : s2.rd 12 = X := by rw [LPstep_rd hs2 12 (.inr rfl), e12]
  have f13 : s2.rd 13 = Y := by rw [LPstep_rd hs2 13 (.inr rfl), e13]
  -- `lw a1,0(a2)`
  iapply (wpK_ld (sz := 4) (sgn := true) (rd := 11) (rs1 := 12) (off := 0) (base := (X : Int)) hw
    (OA.litAg_x hq2 (by rw [hP2]; exact xOf_I1) (by rw [hc2]; rfl) rfl) hq2 (by rw [hP2, hc2]; rfl)
    (alg_of f12 (by decide) (by decide)) (base_of f12 (by decide)))
  iframe Hl
  inext
  iintro %tvs1 %hl1 %hlo1
  have hord : noCmo M → ¬ writesIn M (X : Int) (src0 (LLoad false false (X : Int) tvs1 (srcR 12), none))
      (src0 (LLoad false false (Y : Int) tvs0 (srcR 13), none)) := by
    intro hnc
    obtain ⟨t0, v0, r0, rfl⟩ := tvs_cons hl0 (by decide)
    obtain ⟨t1, v1, r1, rfl⟩ := tvs_cons hl1 (by decide)
    have hw1 := (loadOk_b0nc hnc hlo1).2
    intro hc
    apply hw1
    refine writesIn_mono hc ?_
    show t0 ≤ _
    exact Nat.le_trans (rr_le hf _ _ _ _ _ _ _) (Nat.le_max_left _ _)
  have hQb := Q1_data hQa hl1
    (fun hnc => sca_of (by simp only [instrR, fencePost, (qPostsL _ _).1, (loadRun_mono _ _ _ _ _ _).2.1, hf])
      hnc hlo1) hord
  imodintro
  isplitr
  · ipureintro; exact ⟨0, grd_intro hQb⟩
  iintro %s3 %hs3 Hl
  obtain ⟨hP3, hc3, hq3⟩ := LPstep_at hs3 hP2 (by rw [hc2])
  have g12 : s3.rd 12 = X := by rw [LPstep_rd hs3 12 (.inl (by decide)), f12]
  have g13 : s3.rd 13 = Y := by rw [LPstep_rd hs3 13 (.inl (by decide)), f13]
  -- `beq zero,zero,0`
  iapply (wpK_brx (Xs := xsLoopInc) hw (OA.xAg_x xsLoopInc img M h s3) hq3 (by rw [hP3]; exact xOf_I1)
    (by rw [hc3]; rfl) (Nat.zero_le _))
  iframe Hl
  inext
  iintro %s4 %hs4 Hl
  have hs4' : LPstep s3 s4 0 0 0 := by simpa [brEval] using hs4
  obtain ⟨hP4, hc4, hq4⟩ := LPstep_at hs4' hP3 rfl
  have hS4 : h1S s4 := ⟨hP4, hq4, hc4, by rw [LPstep_rd hs4' 12 (.inr rfl), g12],
    by rw [LPstep_rd hs4' 13 (.inr rfl), g13]⟩
  iapply IH $$ %s4 %_ %_ %_ %hS4 %hQb Hl
  ipureintro
  simp only [instrR, ctrlP, fencePost, (qPostsL _ _).1, (loadRun_mono _ _ _ _ _ _).2.1, hf]

theorem h1_wp (img : Image) (M : List PMsg) (h : Nat) (s0 : LP) (hs : h1S s0)
    (hnoinv : ∀ t a, ¬ cmoAt M isInvalK t a) :
    ⊢@{IProp GF} wpPF Proto.triv (xW xsLoopInc img M h) (ΨK M (Q1 M)) s0
      (fun _ => iprop(⌜∃ V, grd Proto.triv img M V True⌝)) := by
  iapply (wpK_start (Q1_nil M))
  iintro %γ %P0 Hl
  ihave H := h1_loop (GF := GF) img M h γ hnoinv
  iapply H $$ %s0 %_ %_ %_ %hs %(Q1_nil M) Hl
  ipureintro
  rfl

end harts

/-! ## 4. THE THEOREMS -/

/-- **MP FOREVER WITH A COUNTER, IN THE LOGIC** (owner request 2026-11-13).  Over every final memory and every
valid run of machine v2 with the loop front end — finished or not (no hart ever finishes, `loopInc_noDone`) —
every hart's trace satisfies `qLoopInc M`: for every flag load immediately followed by a data load, if the flag
load read a message, it returned `wv k` for that flag message's index `k`, and the data load returned `wv k'` for
the index `k' ≥ k` of the data message it read.  Proved by A0 (`PF.adequacy`, export (ii)) with `Proto.triv`. -/
theorem lit_mpLoopInc : ∀ (M : List PMsg) (run : PFRun LP Unit),
    PF.validRun (xStep xsLoopInc) imgLoopInc () (progs tLoopInc) M run → ∀ h, qLoopInc M (run.trace h) := by
  intro M run hrun
  have hnoinv := OA.x_noInvalT hrun   -- MachFix-R-b5
  obtain ⟨hQ, hnc, hpart, hwf, -⟩ := kitAdeqX (Xs := xsLoopInc) (T := tLoopInc) (Qs M) (Qs_nil M)
    (fun h p hp _ => by
      obtain ⟨hpr, hpc, hq, hlen, hrd⟩ := PF.progs_get hp
      match h with
      | 0 =>
        exact h0_wp _ M 0 p ⟨by rw [hpr]; rfl, hq, hpc, hlen, by rw [hrd 6 (by decide) (by decide)]; rfl,
          by rw [hrd 12 (by decide) (by decide)]; rfl, by rw [hrd 13 (by decide) (by decide)]; rfl⟩
      | 1 =>
        exact h1_wp _ M 1 p ⟨by rw [hpr]; rfl, hq, hpc, by rw [hrd 12 (by decide) (by decide)]; rfl,
          by rw [hrd 13 (by decide) (by decide)]; rfl⟩ hnoinv
      | n + 2 =>
        have hl : (progs tLoopInc).length = 2 := rfl
        rw [List.getElem?_eq_none (by omega)] at hp; cases hp) hrun
  intro h
  match h with
  | 0 =>
    intro i e0 e1 v0 v1 h0 _ hr0
    have hs := (hQ 0 : Q0 _).1 i e0 h0
    rcases Nat.mod_two_eq_zero_or_one i with hp | hp
    · obtain ⟨_, _, rfl⟩ := hs.1 hp; simp [ldRet] at hr0
    · obtain ⟨_, _, rfl⟩ := hs.2 hp; simp [ldRet] at hr0
  | 1 => exact reader_ok hQ hnc hpart hwf
  | n + 2 =>
    intro i e0 e1 v0 v1 h0
    have h2 : memEv (run.trace (n + 2)) = [] := hQ (n + 2)
    rw [h2] at h0; simp at h0

/-! ## 5. No hart is ever done (pure, from the front end) -/

/-- The reachable-state invariant: a hart's own program, `pc` below its length. -/
def invI (s : LP) : Prop := (s.prog = bI0 ∨ s.prog = Loop.bL1) ∧ s.pc < s.prog.length

theorem step_plainI {s s' : LP} {l : PLabel} {X0 : List XI} {ins : Instr} (hq : s.q = [])
    (hX : xOf xsLoopInc s.prog = some X0) (hx : X0[s.pc]? = some (.i ins)) (hpl : (XI.i ins).plain = true)
    (hnb : ∀ c r1 r2 t, ins ≠ .br c r1 r2 t) (hnj : ∀ t, ins ≠ .jmp t) (h : xNext xsLoopInc s l = some s') :
    s'.prog = s.prog ∧ s'.pc = s.pc + 1 := by
  rw [OA.xNext_plain hq (fun y hy => by
    rw [hX] at hy; simp only [Option.bind_some, hx, Option.some.injEq] at hy; subst hy; exact hpl)] at h
  have hins : s.prog[s.pc]? = some ins := OA.base_at (OA.xOf_spec hX) hx
  unfold litNext at h
  rw [hq] at h
  simp only [hins] at h
  obtain ⟨h1, h2 | ⟨c, r1, r2, t, he⟩ | ⟨t, he⟩⟩ := instrNext_pc h
  · exact ⟨h1, h2⟩
  · exact absurd he (hnb c r1 r2 t)
  · exact absurd he (hnj t)

theorem step_invI {s s' : LP} {l : PLabel} (h : xNext xsLoopInc s l = some s') (hi : invI s) : invI s' := by
  obtain ⟨hP, hpc⟩ := hi
  cases hq : s.q with
  | cons l0 rest =>
    rw [OA.xNext_q (by rw [hq]; simp)] at h
    unfold litNext at h
    rw [hq] at h
    simp only at h
    split at h
    · cases h; exact ⟨hP, hpc⟩
    · cases h
  | nil =>
    rcases hP with hP | hP
    · have hX : xOf xsLoopInc s.prog = some pI0 := by rw [hP]; exact xOf_I0
      have hl : s.prog.length = 5 := by rw [hP]; rfl
      rw [hl] at hpc
      have plain : ∀ k, k < 4 → s.pc = k → invI s' := fun k hk hc => by
        match k, hk with
        | 0, _ | 1, _ | 2, _ | 3, _ =>
          obtain ⟨h1, h2⟩ := step_plainI hq hX (by rw [hc]; rfl) rfl (fun _ _ _ _ he => by cases he)
            (fun _ he => by cases he) h
          exact ⟨.inl (h1.trans hP), by rw [h1, hl]; omega⟩
      rcases (by omega : s.pc < 4 ∨ s.pc = 4) with hc | hc
      · exact plain s.pc hc rfl
      · obtain ⟨_, rfl⟩ := OA.xNext_br hq hX (by rw [hc]; rfl) (by rw [hP]; decide) h
        exact ⟨.inl hP, by simp [brEval, hl]⟩
    · have hX : xOf xsLoopInc s.prog = some Loop.pL1 := by rw [hP]; exact xOf_I1
      have hl : s.prog.length = 4 := by rw [hP]; rfl
      rw [hl] at hpc
      have plain : ∀ k, k < 3 → s.pc = k → invI s' := fun k hk hc => by
        match k, hk with
        | 0, _ | 1, _ | 2, _ =>
          obtain ⟨h1, h2⟩ := step_plainI hq hX (by rw [hc]; rfl) rfl (fun _ _ _ _ he => by cases he)
            (fun _ he => by cases he) h
          exact ⟨.inr (h1.trans hP), by rw [h1, hl]; omega⟩
      rcases (by omega : s.pc < 3 ∨ s.pc = 3) with hc | hc
      · exact plain s.pc hc rfl
      · obtain ⟨_, rfl⟩ := OA.xNext_br hq hX (by rw [hc]; rfl) (by rw [hP]; decide) h
        exact ⟨.inr hP, by simp [brEval, hl]⟩

theorem solo_invI {img : Image} {M : List PMsg} {i : Nat} :
    ∀ {x y : LP × PState × GSet Nat} {tr : Trace}, soloSteps (anyFab (xStep xsLoopInc)) img M i x tr y →
      invI x.1 → invI y.1 := by
  intro x y tr hs
  induction hs with
  | refl => exact id
  | step x l ots p' ws' prom' tr y hp _ _ ih =>
    intro hi
    obtain ⟨_, _, hp⟩ := hp
    exact ih (step_invI hp hi)

/-- **NO HART EVER FINISHES** (pure, from the front end): every reachable program state of each hart has `pc`
below its program's length, so `litDone` is `none`. -/
theorem loopInc_noDone : ∀ (M : List PMsg) (run : PFRun LP Unit),
    PF.validRun (xStep xsLoopInc) imgLoopInc () (progs tLoopInc) M run → ∀ h v, ¬ run.done litDone h v := by
  rintro M run ⟨hv, -⟩ h v ⟨ag, hag, hdv⟩
  have hl := validRun_len hv
  have hh : h < (progs tLoopInc).length := by rw [← hl]; exact (List.getElem?_eq_some_iff.1 hag).1
  obtain ⟨ag', hag', P0, _, hs⟩ := validRun_soloD hv h _ (List.getElem?_eq_getElem hh)
  rw [hag] at hag'; cases hag'
  have hi0 : invI (progs tLoopInc)[h] := by
    have h2 : h < 2 := hh
    match h, h2 with
    | 0, _ => exact ⟨.inl rfl, by show 0 < 5; decide⟩
    | 1, _ => exact ⟨.inr rfl, by show 0 < 4; decide⟩
  obtain ⟨_, hpc⟩ := solo_invI hs hi0
  have hpc' : ag.paSt.pc < ag.paSt.prog.length := hpc
  unfold litDone at hdv
  split at hdv
  · next hc => have := hc.2; omega
  · cases hdv

end Weak.Prom.PF.LoopInc

#print axioms Weak.Prom.PF.LoopInc.lit_mpLoopInc
#print axioms Weak.Prom.PF.LoopInc.loopInc_noDone
