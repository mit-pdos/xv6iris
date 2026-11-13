/-
Weak/Prom: **MP FOREVER — a tiny, genuinely NON-TERMINATING program proved in the logic** (owner request
2026-11-13 "I want that example. ASAP"; plan rev 7 §2 "Leaf rules", "Adequacy A0", §5 row 8 per iteration).

The program `tLoop` (image all zero; DATA = `X = 0x1000`, FLAG = `Y = 0x2000`; both harts loop UNCONDITIONALLY
with `beq zero,zero,0`, a backward branch of the loop front end `xStep`, OwnAFront.lean):
  hart 0:  0: sw t1,0(a2)   1: fence w,w   2: sw t1,0(a3)   3: beq zero,zero,0     (t1 = x6 = 1, a2 = X, a3 = Y)
  hart 1:  0: lw a0,0(a3)   1: fence r,r   2: lw a1,0(a2)   3: beq zero,zero,0     (a2 = x12 = X, a3 = x13 = Y)
Theorems:
* `lit_mpLoop` — over every final memory and every valid run (no `done` premise: no hart ever finishes), every
  hart's trace satisfies `qLoop`: among its memory entries, a data load immediately after a flag load that
  returned 1 returned 1 (RVWMO rule 4 twice; the manual's MP+fence.w.w+fence.r.r row, per iteration).
* `loop_noDone` — no hart is ever done (pure, from the front end: every reachable program state has `pc < 4`).
Logic: the base logic A0 (`PF.adequacy`, CoreAdeq.lean; export (ii)) with `Proto.triv`; the kit (CoreKit.lean)
over the loop front end's worlds `xW` (litmus worlds: `OA.litW_x`, `OA.litAg_x`), plus ONE kit composition
`wpK_brx` (the A0 twin of track (a)'s `wpKA_brx`, composed from `wpK_q1`, `wpK_drainA`).  Each hart's wp is a
Löb induction at the loop head; its Ψ is a property of every adjacent pair / every entry of its memory entries.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.OwnAFront
import Weak.Prom.CoreLitH

namespace Weak.Prom.PF.Loop

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.PF Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.OA (XI xNext xStep xW xOf)
open Weak.Prom.Ref (Instr Test two64 brEval)
open Weak.Prom.Ref.Lit (X Y)
open PLabel
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode

/-! ## 1. The program -/

/-- Hart 0: `sw t1,0(a2); fence w,w; sw t1,0(a3); beq zero,zero,0`. -/
def pL0 : List XI :=
  [.i (Weak.Prom.Ref.Lit.sw 6 12), .i Weak.Prom.Ref.Lit.fWW, .i (Weak.Prom.Ref.Lit.sw 6 13),
   .i (Weak.Prom.Ref.Lit.beq 0 0 0)]

/-- Hart 1: `lw a0,0(a3); fence r,r; lw a1,0(a2); beq zero,zero,0`. -/
def pL1 : List XI :=
  [.i (Weak.Prom.Ref.Lit.lw 10 13), .i Weak.Prom.Ref.Lit.fRR, .i (Weak.Prom.Ref.Lit.lw 11 12),
   .i (Weak.Prom.Ref.Lit.beq 0 0 0)]

abbrev bL0 : List Instr := pL0.map XI.base
abbrev bL1 : List Instr := pL1.map XI.base
abbrev xsLoop : List (List XI) := [pL0, pL1]

/-- THE TEST: two harts, image all zero. -/
def tLoop : Test :=
  { harts := [bL0, bL1]
    regs0 := [[(6, 1), (12, X), (13, Y)], [(12, X), (13, Y)]]
    img := []
    cond := Weak.Prom.Ref.Lit.mpFF.cond }

abbrev imgLoop : Image := testImg tLoop

theorem xOf_L0 : xOf xsLoop bL0 = some pL0 := by decide
theorem xOf_L1 : xOf xsLoop bL1 = some pL1 := by decide

/-! ## 2. The trace invariants and the property -/

/-- The word both stores write. -/
abbrev dL : List (BitVec 8) := toBytes 1 4

def stD (e : PEv) : Prop := isSt (X : Int) dL [.DReg 12] [.DReg 6] e
def stF (e : PEv) : Prop := isSt (Y : Int) dL [.DReg 13] [.DReg 6] e

/-- Hart 0's Ψ: every memory entry is a data store, or a flag store above some data store of the hart. -/
def Q0 (ev : Trace) : Prop := ∀ e ∈ ev, stD e ∨ (stF e ∧ ∃ e' ∈ ev, stD e' ∧ tsOf e' < tsOf e)

def ldF (e : PEv) : Prop := isLd (Y : Int) 4 [.DReg 13] e
def ldD (e : PEv) : Prop := isLd (X : Int) 4 [.DReg 12] e

/-- `R` of every adjacent pair. -/
def adj (R : PEv → PEv → Prop) (ev : Trace) : Prop :=
  ∀ i e0 e1, ev[i]? = some e0 → ev[i + 1]? = some e1 → R e0 e1

/-- Hart 1's Ψ: every memory entry is a flag or a data load; a data load right after a flag load sees no write to
the data between its byte-0 source and the flag load's. -/
def Q1 (M : List PMsg) (ev : Trace) : Prop :=
  (∀ e ∈ ev, ldF e ∨ ldD e) ∧
    adj (fun e0 e1 => ldF e0 → ldD e1 → noCmo M → ¬ writesIn M (X : Int) (src0 e1) (src0 e0)) ev

def Qs (M : List PMsg) : Nat → Trace → Prop
  | 0 => Q0
  | 1 => Q1 M
  | _ => q0

theorem Q1_nil (M : List PMsg) : Q1 M [] := ⟨fun _ he => (by cases he), fun _ _ _ h => (by simp at h)⟩

theorem Qs_nil (M : List PMsg) : ∀ h, Qs M h []
  | 0 => fun _ he => by cases he
  | 1 => Q1_nil M
  | _ + 2 => rfl

/-- The value a plain load at `a` returned (`obsOf`, plan §0 [R6.2]). -/
def ldRet (a : Int) (e : PEv) : Option Nat :=
  match e.1 with
  | LLoad _ _ b tvs _ => if b = a then some (obsOf tvs) else none
  | _ => none

/-- **THE PROPERTY**: among the memory entries of the trace, every data load that immediately follows a flag load
that returned 1 returned 1. -/
def qLoop (τ : Trace) : Prop :=
  ∀ i e0 e1, (memEv τ)[i]? = some e0 → (memEv τ)[i + 1]? = some e1 → ldRet (Y : Int) e0 = some 1 →
    ∀ v, ldRet (X : Int) e1 = some v → v = 1

theorem adj_snoc {R : PEv → PEv → Prop} {ev : Trace} {e : PEv} (h : adj R ev)
    (hl : ∀ e0, ev.getLast? = some e0 → R e0 e) : adj R (ev ++ [e]) := by
  intro i e0 e1 h0 h1
  have hi1 : i + 1 < ev.length + 1 := by
    have := (List.getElem?_eq_some_iff.1 h1).1; simpa using this
  by_cases hi : i + 1 < ev.length
  · rw [List.getElem?_append_left (by omega)] at h0
    rw [List.getElem?_append_left hi] at h1
    exact h i e0 e1 h0 h1
  · have hi' : i + 1 = ev.length := by omega
    rw [List.getElem?_append_right (by omega), hi', Nat.sub_self] at h1
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h1
    subst h1
    rw [List.getElem?_append_left (by omega)] at h0
    exact hl e0 (by rw [List.getLast?_eq_getElem?, show ev.length - 1 = i by omega]; exact h0)

theorem Q0_snoc {ev : Trace} {e : PEv} (h : Q0 ev)
    (he : stD e ∨ (stF e ∧ ∃ e' ∈ ev, stD e' ∧ tsOf e' < tsOf e)) : Q0 (ev ++ [e]) := by
  intro x hx
  rcases List.mem_append.1 hx with hx | hx
  · rcases h x hx with h1 | ⟨h1, e', he', h2⟩
    · exact .inl h1
    · exact .inr ⟨h1, e', List.mem_append_left _ he', h2⟩
  · rw [List.mem_singleton] at hx; subst hx
    rcases he with h1 | ⟨h1, e', he', h2⟩
    · exact .inl h1
    · exact .inr ⟨h1, e', List.mem_append_left _ he', h2⟩

theorem ldF_D {e : PEv} (hF : ldF e) (hD : ldD e) : False := by
  obtain ⟨_, rfl, _⟩ := hF
  obtain ⟨_, he, _⟩ := hD
  simp [Weak.Prom.Ref.Lit.X, Weak.Prom.Ref.Lit.Y] at he

theorem Q1_flag {M : List PMsg} {ev : Trace} {tvs : List (Nat × BitVec 8)} (h : Q1 M ev) (hl : tvs.length = 4) :
    Q1 M (ev ++ [(LLoad false false (Y : Int) tvs (srcR 13), none)]) := by
  have hF : ldF (LLoad false false (Y : Int) tvs (srcR 13), none) := ⟨tvs, by simp, hl⟩
  refine ⟨fun e he => ?_, adj_snoc h.2 (fun _ _ _ hD => (ldF_D hF hD).elim)⟩
  rcases List.mem_append.1 he with he | he
  · exact h.1 e he
  · rw [List.mem_singleton] at he; subst he; exact .inl hF

theorem Q1_data {M : List PMsg} {ev : Trace} {eF : PEv} {tvs : List (Nat × BitVec 8)} (h : Q1 M (ev ++ [eF]))
    (hl : tvs.length = 4)
    (hord : noCmo M → ¬ writesIn M (X : Int) (src0 (LLoad false false (X : Int) tvs (srcR 12), none)) (src0 eF)) :
    Q1 M (ev ++ [eF] ++ [(LLoad false false (X : Int) tvs (srcR 12), none)]) := by
  have hD : ldD (LLoad false false (X : Int) tvs (srcR 12), none) := ⟨tvs, by simp, hl⟩
  refine ⟨fun e he => ?_, adj_snoc h.2 (fun e0 he0 _ _ => ?_)⟩
  · rcases List.mem_append.1 he with he | he
    · exact h.1 e he
    · rw [List.mem_singleton] at he; subst he; exact .inr hD
  · simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or, Option.some.injEq] at he0
    subst he0
    exact hord

/-! ## 3. The backward branch, in the kit -/

section kit

variable {V : Type} {hlc : HasLC} {GF : BundledGFunctors} [GhostVarG GF HSt] [InvGS_gen hlc GF]
variable {γ : GName} {π : Proto} {w : HW LP Unit V} {Q : Trace → Prop} {Φ : V → IProp GF}

/-- **BRANCH instruction, any target** (loop front end; the A0 twin of `OA.wpKA_brx`): `LCtrl (rs1 ++ rs2)`
(rule 11), `LInstr`. -/
theorem wpK_brx {Xs : List (List XI)} (hw : LitW w) {s : LP} {X0 : List XI} {c : Weak.Prom.Ref.BrC}
    {rs1 rs2 tgt : Nat} {ws : PState} {pr : GSet Nat} {ev : Trace} (hag : OA.XAg Xs w s) (hq : s.q = [])
    (hX : xOf Xs s.prog = some X0) (hx : X0[s.pc]? = some (.i (.br c rs1 rs2 tgt))) (ht : tgt ≤ s.prog.length) :
    lh γ π w Q ws pr ev ∗
    ▷ (∀ s', ⌜LPstep s s' (if brEval c (s.rd rs1) (s.rd rs2) then tgt else s.pc + 1) 0 0⌝ -∗
        lh γ π w Q (instrR (ctrlP ws (srcR rs1 ++ srcR rs2))) pr ev -∗ wpK γ π w Q s' Φ)
    ⊢ wpK γ π w Q s Φ := by
  iintro ⟨Hl, Hk⟩
  iapply (wpK_q1
    (k := { s with regs := s.regs, pc := if brEval c (s.rd rs1) (s.rd rs2) then tgt else s.pc + 1, q := [LInstr] })
    (l0 := LCtrl (srcR rs1 ++ srcR rs2)) (ws1 := ctrlP ws (srcR rs1 ++ srcR rs2)) rfl
    (hw.2 s (.inr (OA.pc_lt_x hX hx)))
    (fun l s' hs => OA.xNext_br hq hX hx ht ((hag l s').1 hs)) rfl)
  iframe Hl
  inext
  iintro Hl
  iapply (wpK_drainA hw [LInstr] _ { s with pc := if brEval c (s.rd rs1) (s.rd rs2) then tgt else s.pc + 1, q := [] }
    _ (instrR (ctrlP ws (srcR rs1 ++ srcR rs2))) (by simp) (by simp [quietL]) rfl rfl rfl)
  iframe Hl
  inext
  iintro Hl
  iapply Hk $$ %_ %(LPstep_same s _) Hl

end kit

/-! ## 4. View facts -/

/-- `st; fence w,w; st`: the first store's timestamp is below the second's pre-view (FULFIL, rule 4). -/
theorem ww_le (ws : PState) (va fv : Nat) (base : Int) (n tx va' vd' : Nat) :
    tx ≤ stPreA (instrR (fencePost (instrR (acqPost (storeRun ws false va fv base n tx) false tx)) false true false true))
      false false va' vd' := by
  have h := (storeRun_mono ws false va fv base n tx).2.2.1
  simp only [stPreA, stPre, instrR, fencePost, acqPost, if_true, if_false, Bool.false_eq_true]
  omega

theorem qPostsL (ws : PState) (rd : Nat) :
    (qPosts ws (regWL rd [.DLdRes] ++ [LInstr])).wFwd = ws.wFwd ∧
    (qPosts ws (regWL rd [.DLdRes] ++ [LInstr])).wVrOld = ws.wVrOld ∧
    (qPosts ws (regWL rd [.DLdRes] ++ [LInstr])).wVrNew = ws.wVrNew := by
  unfold regWL; split <;> exact ⟨rfl, rfl, rfl⟩

/-- `ld; fence r,r`: the load's byte-0 source is below the next load's pre-view (X4 without forwarding, rule 4). -/
theorem rr_le {ws : PState} (hf : ws.wFwd = ∅) (va : Nat) (base : Int) (t : Nat) (v : BitVec 8)
    (r : List (Nat × BitVec 8)) (rd va2 : Nat) :
    t ≤ ldPre (instrR (fencePost (qPosts (loadRun ws false false va base ((t, v) :: r))
      (regWL rd [.DLdRes] ++ [LInstr])) true false true false)) false false va2 := by
  have hb := (loadRun_b0 ws false false va base t v r).2.1
  rw [fwdView_empty hf] at hb
  have hq := (qPostsL (loadRun ws false false va base ((t, v) :: r)) rd).2.1
  simp only [ldPre, instrR, fencePost, if_true, if_false, Bool.false_eq_true]
  omega

/-! ## 5. The harts, by Löb induction -/

section harts

variable {hlc : HasLC} {GF : BundledGFunctors} [GhostVarG GF HSt] [InvGS_gen hlc GF]

/-- Hart 0 at its loop head. -/
def h0S (s : LP) : Prop := s.prog = bL0 ∧ s.q = [] ∧ s.pc = 0 ∧ s.rd 6 = 1 ∧ s.rd 12 = X ∧ s.rd 13 = Y

/-- **HART 0's LOOP** (Löb at `pc = 0`). -/
theorem h0_loop (img : Image) (M : List PMsg) (h : Nat) (γ : GName) :
    ⊢@{IProp GF} ∀ (s : LP) (ws : PState) (pr : GSet Nat) (ev : Trace), ⌜h0S s⌝ -∗ ⌜Q0 ev⌝ -∗
      lh γ Proto.triv (xW xsLoop img M h) Q0 ws pr ev -∗
      wpK γ Proto.triv (xW xsLoop img M h) Q0 s (fun _ => iprop(⌜∃ V, grd Proto.triv img M V True⌝)) := by
  have hw := OA.litW_x xsLoop img M h
  iloeb as IH
  iintro %s0 %ws0 %pr0 %ev %hs %hQ Hl
  obtain ⟨hP0, hq0, hc0, h6, h12, h13⟩ := hs
  -- `sw t1,0(a2)`
  iapply (wpK_sw (sz := 4) (rs2 := 6) (rs1 := 12) (off := 0) (base := (X : Int)) hw
    (OA.litAg_x hq0 (by rw [hP0]; exact xOf_L0) (by rw [hc0]; rfl) rfl) hq0 (by rw [hP0, hc0]; rfl)
    (alg_of h12 (by decide) (by decide)) (base_of h12 (by decide)))
  iframe Hl
  inext
  iintro %tx %_ %_ %_ %hx
  have htx : 0 < tx := by omega
  have hQa := Q0_snoc hQ
    (e := (LStore false false (X : Int) (toBytes (s0.rd 6) 4) (srcR 12) (srcR 6), some tx))
    (.inl ⟨tx, htx, by rw [h6]; rfl⟩)
  imodintro
  isplitr
  · ipureintro; exact ⟨0, grd_intro hQa⟩
  isplitr
  · ipureintro; exact grd_intro trivial
  iintro %s1 %hs1 Hl
  obtain ⟨hP1, hc1, hq1⟩ := LPstep_at hs1 hP0 (by rw [hc0])
  -- `fence w,w`
  iapply (wpK_fence (f := ⟨false, true, false, false, false, true, false, false⟩) hw
    (OA.litAg_x hq1 (by rw [hP1]; exact xOf_L0) (by rw [hc1]; rfl) rfl) hq1 (by rw [hP1, hc1]; rfl))
  iframe Hl
  inext
  iintro %s2 %hs2 Hl
  obtain ⟨hP2, hc2, hq2⟩ := LPstep_at hs2 hP1 (by rw [hc1])
  have e6 : s2.rd 6 = 1 := by rw [LPstep_rd hs2 6 (.inr rfl), LPstep_rd hs1 6 (.inr rfl), h6]
  have e12 : s2.rd 12 = X := by rw [LPstep_rd hs2 12 (.inr rfl), LPstep_rd hs1 12 (.inr rfl), h12]
  have e13 : s2.rd 13 = Y := by rw [LPstep_rd hs2 13 (.inr rfl), LPstep_rd hs1 13 (.inr rfl), h13]
  -- `sw t1,0(a3)`
  iapply (wpK_sw (sz := 4) (rs2 := 6) (rs1 := 13) (off := 0) (base := (Y : Int)) hw
    (OA.litAg_x hq2 (by rw [hP2]; exact xOf_L0) (by rw [hc2]; rfl) rfl) hq2 (by rw [hP2, hc2]; rfl)
    (alg_of e13 (by decide) (by decide)) (base_of e13 (by decide)))
  iframe Hl
  inext
  iintro %ty %_ %_ %_ %hy
  have hlt : tx < ty := Nat.lt_of_le_of_lt (ww_le _ _ _ _ _ _ _ _) hy
  have hQb := Q0_snoc hQa
    (e := (LStore false false (Y : Int) (toBytes (s2.rd 6) 4) (srcR 13) (srcR 6), some ty))
    (.inr ⟨⟨ty, by omega, by rw [e6]; rfl⟩, _, List.mem_append_right _ (List.mem_singleton_self _),
      ⟨tx, htx, by rw [h6]; rfl⟩, hlt⟩)
  imodintro
  isplitr
  · ipureintro; exact ⟨0, grd_intro hQb⟩
  isplitr
  · ipureintro; exact grd_intro trivial
  iintro %s3 %hs3 Hl
  obtain ⟨hP3, hc3, hq3⟩ := LPstep_at hs3 hP2 (by rw [hc2])
  -- `beq zero,zero,0`
  iapply (wpK_brx (Xs := xsLoop) hw (OA.xAg_x xsLoop img M h s3) hq3 (by rw [hP3]; exact xOf_L0)
    (by rw [hc3]; rfl) (Nat.zero_le _))
  iframe Hl
  inext
  iintro %s4 %hs4 Hl
  have hs4' : LPstep s3 s4 0 0 0 := by simpa [brEval] using hs4
  obtain ⟨hP4, hc4, hq4⟩ := LPstep_at hs4' hP3 rfl
  have hS4 : h0S s4 := ⟨hP4, hq4, hc4,
    by rw [LPstep_rd hs4' 6 (.inr rfl), LPstep_rd hs3 6 (.inr rfl), e6],
    by rw [LPstep_rd hs4' 12 (.inr rfl), LPstep_rd hs3 12 (.inr rfl), e12],
    by rw [LPstep_rd hs4' 13 (.inr rfl), LPstep_rd hs3 13 (.inr rfl), e13]⟩
  iapply IH $$ %s4 %_ %_ %_ %hS4 %hQb Hl

theorem h0_wp (img : Image) (M : List PMsg) (h : Nat) (s0 : LP) (hs : h0S s0) :
    ⊢@{IProp GF} wpPF Proto.triv (xW xsLoop img M h) (ΨK M Q0) s0
      (fun _ => iprop(⌜∃ V, grd Proto.triv img M V True⌝)) := by
  have hQ0 : Q0 [] := fun _ he => by cases he
  iapply (wpK_start hQ0)
  iintro %γ %P0 Hl
  ihave H := h0_loop (GF := GF) img M h γ
  iapply H $$ %s0 %_ %_ %_ %hs %hQ0 Hl

/-- Hart 1 at its loop head. -/
def h1S (s : LP) : Prop := s.prog = bL1 ∧ s.q = [] ∧ s.pc = 0 ∧ s.rd 12 = X ∧ s.rd 13 = Y

/-- **HART 1's LOOP** (Löb at `pc = 0`; the hart never stores, so its forward bank stays empty). -/
theorem h1_loop (img : Image) (M : List PMsg) (h : Nat) (γ : GName)
    (hnoinv : ∀ t a, ¬ cmoAt M isInvalK t a) :   -- MachFix-R-b5
    ⊢@{IProp GF} ∀ (s : LP) (ws : PState) (pr : GSet Nat) (ev : Trace), ⌜h1S s⌝ -∗ ⌜Q1 M ev⌝ -∗
      lh γ Proto.triv (xW xsLoop img M h) (Q1 M) ws pr ev -∗ ⌜ws.wFwd = ∅⌝ -∗
      wpK γ Proto.triv (xW xsLoop img M h) (Q1 M) s (fun _ => iprop(⌜∃ V, grd Proto.triv img M V True⌝)) := by
  have hw := OA.litW_x xsLoop img M h
  iloeb as IH
  iintro %s0 %ws0 %pr0 %ev %hs %hQ Hl %hf
  obtain ⟨hP0, hq0, hc0, h12, h13⟩ := hs
  -- `lw a0,0(a3)`
  iapply (wpK_ld (sz := 4) (sgn := true) (rd := 10) (rs1 := 13) (off := 0) (base := (Y : Int)) hw
    (OA.litAg_x hq0 (by rw [hP0]; exact xOf_L1) (by rw [hc0]; rfl) rfl) hq0 (by rw [hP0, hc0]; rfl)
    (alg_of h13 (by decide) (by decide)) (base_of h13 (by decide)))
  iframe Hl
  inext
  iintro %tvs0 %hl0 %_
  have hQa := Q1_flag hQ hl0
  imodintro
  isplitr
  · ipureintro; exact ⟨0, grd_intro hQa⟩
  iintro %s1 %hs1 Hl
  obtain ⟨hP1, hc1, hq1⟩ := LPstep_at hs1 hP0 (by rw [hc0])
  have e12 : s1.rd 12 = X := by rw [LPstep_rd hs1 12 (.inl (by decide)), h12]
  have e13 : s1.rd 13 = Y := by rw [LPstep_rd hs1 13 (.inl (by decide)), h13]
  -- `fence r,r`
  iapply (wpK_fence (f := ⟨true, false, false, false, true, false, false, false⟩) hw
    (OA.litAg_x hq1 (by rw [hP1]; exact xOf_L1) (by rw [hc1]; rfl) rfl) hq1 (by rw [hP1, hc1]; rfl))
  iframe Hl
  inext
  iintro %s2 %hs2 Hl
  obtain ⟨hP2, hc2, hq2⟩ := LPstep_at hs2 hP1 (by rw [hc1])
  have f12 : s2.rd 12 = X := by rw [LPstep_rd hs2 12 (.inr rfl), e12]
  have f13 : s2.rd 13 = Y := by rw [LPstep_rd hs2 13 (.inr rfl), e13]
  -- `lw a1,0(a2)`
  iapply (wpK_ld (sz := 4) (sgn := true) (rd := 11) (rs1 := 12) (off := 0) (base := (X : Int)) hw
    (OA.litAg_x hq2 (by rw [hP2]; exact xOf_L1) (by rw [hc2]; rfl) rfl) hq2 (by rw [hP2, hc2]; rfl)
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
  have hQb := Q1_data hQa hl1 hord
  imodintro
  isplitr
  · ipureintro; exact ⟨0, grd_intro hQb⟩
  iintro %s3 %hs3 Hl
  obtain ⟨hP3, hc3, hq3⟩ := LPstep_at hs3 hP2 (by rw [hc2])
  have g12 : s3.rd 12 = X := by rw [LPstep_rd hs3 12 (.inl (by decide)), f12]
  have g13 : s3.rd 13 = Y := by rw [LPstep_rd hs3 13 (.inl (by decide)), f13]
  -- `beq zero,zero,0`
  iapply (wpK_brx (Xs := xsLoop) hw (OA.xAg_x xsLoop img M h s3) hq3 (by rw [hP3]; exact xOf_L1)
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
    ⊢@{IProp GF} wpPF Proto.triv (xW xsLoop img M h) (ΨK M (Q1 M)) s0
      (fun _ => iprop(⌜∃ V, grd Proto.triv img M V True⌝)) := by
  iapply (wpK_start (Q1_nil M))
  iintro %γ %P0 Hl
  ihave H := h1_loop (GF := GF) img M h γ hnoinv
  iapply H $$ %s0 %_ %_ %_ %hs %(Q1_nil M) Hl
  ipureintro
  rfl

end harts

/-! ## 6. A0 for the loop front end -/

theorem devFree_x (Xs : List (List XI)) (ps : List LP) : devFreeProg (xStep Xs) ps := by
  intro _ _ _ _ _ d l p' d' hs
  cases d; cases d'
  exact ⟨rfl, fun d0 => by cases d0; exact hs⟩

/-- **A0 for a loop-front-end program** (`PF.adequacy` with `Ψ h = ΨK M (Qs h)`, as CoreKitV.lean `kitAdeq`):
(ii) at every final trace, `noCmo M` (from (iii) and `wrOk`), the partition (iii), `traceWf` (v). -/
theorem kitAdeqX {Xs : List (List XI)} {T : Test} {M : List PMsg} {run : PFRun LP Unit}
    (Qs : Nat → Trace → Prop) (hQ0 : ∀ h, Qs h [])
    (hwp : ∀ h p, (progs T)[h]? = some p → ∀ [InvGS_gen HasLC.hasLC pfGF],
      ⊢@{IProp pfGF} wpPF Proto.triv (xW Xs (testImg T) M h) (ΨK M (Qs h)) p
        (fun v => iprop(⌜∃ V, grd Proto.triv (testImg T) M V ((fun (_ : Nat) (_ : Unit) => True) h v)⌝)))
    (hrun : PF.validRun (xStep Xs) (testImg T) () (progs T) M run) :
    (∀ h, Qs h (memEv (run.trace h))) ∧ noCmo M ∧
    (∀ t, 1 ≤ t → t ≤ M.length → exU (fun h => t ∈ run.fulfils h ∧ tidAt M t = some h)) ∧ run.traceWf M ∧
    run.cfg.pcImg = testImg T := by
  obtain ⟨_, hii, hpart, _, _, hwf, _⟩ := adequacy (hlc := HasLC.hasLC) (GF := pfGF) (pdone := litDone)
    Proto.triv (fun _ _ => True) (fun h => ΨK M (Qs h)) trivial (PO_ad_all _ _ _) (fun h => ⟨hQ0 h, wrOk_nil M⟩)
    (devFree_x Xs _) hwp hrun
  have hfin : ∀ h, ΨK M (Qs h) (run.trace h) := fun h => by simpa using hii h (run.trace h).length
  refine ⟨fun h => (hfin h).1, fun k m hm => ?_, hpart, hwf, validRun_img hrun.1⟩
  have hkl : k < M.length := (List.getElem?_eq_some_iff.1 hm).1
  obtain ⟨h, ⟨hin, _⟩, _⟩ := hpart (k + 1) (by omega) (by omega)
  unfold PFRun.fulfils fulfilsOf at hin
  obtain ⟨e, he, het⟩ := List.mem_filterMap.1 hin
  exact (hfin h).2 e he (k + 1) het m (by simpa [msgAt] using hm)

/-! ## 7. The contradiction (from A0's exports only) -/

section glue

variable {run : PFRun LP Unit} {M : List PMsg}

/-- Every message is hart 0's word 1: at the data, or at the flag above a data message (A0 (ii), (iii), (v)). -/
theorem msg_shape (hQ : ∀ h, Qs M h (memEv (run.trace h)))
    (hpart : ∀ t, 1 ≤ t → t ≤ M.length → exU (fun h => t ∈ run.fulfils h ∧ tidAt M t = some h))
    (hwf : run.traceWf M) {k : Nat} {m : PMsg} (hm : M[k]? = some m) :
    m.data = dL ∧ (m.pa = X ∨ (m.pa = Y ∧ ∃ k' m', k' < k ∧ M[k']? = some m' ∧ m'.pa = X ∧ m'.data = dL)) := by
  obtain ⟨h, e, he, het, hlw⟩ := kit_writer hpart hwf hm
  match h, he with
  | 0, he =>
    rcases (hQ 0 : Q0 _) e he with ⟨t, _, rfl⟩ | ⟨⟨t, _, rfl⟩, e', he', ⟨t', ht', rfl⟩, hlt⟩
    · simp only [labelWrite, Option.some.injEq, Prod.mk.injEq] at hlw
      exact ⟨hlw.2.symm, .inl hlw.1.symm⟩
    · simp only [labelWrite, Option.some.injEq, Prod.mk.injEq] at hlw
      simp only [Option.some.injEq] at het
      have hlt' : t' < t := hlt
      obtain ⟨m', hm', hpa', hd'⟩ := kit_msg hwf he' rfl rfl
      exact ⟨hlw.2.symm, .inr ⟨hlw.1.symm, t' - 1, m', by omega, hm', hpa', hd'⟩⟩
  | 1, he =>
    rcases (hQ 1).1 e he with ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩ <;> cases het
  | n + 2, he =>
    have h0 : memEv (run.trace (n + 2)) = [] := hQ (n + 2)
    rw [h0] at he; cases he

/-- A byte of the data word: byte 0 is 1 when read from a message, every other byte is 0. -/
theorem byteX {img : Image} (himg : ∀ a, img a = some 0)
    (hsh : ∀ (k : Nat) (m : PMsg), M[k]? = some m → m.data = dL ∧ (m.pa = X ∨ m.pa = Y))
    {t : Nat} {a : Int} (j : Nat) (hj : j < 4) (ha : a = (X : Int) + j) {v : BitVec 8}
    (hb : memByte img M t a = some v) : v = if j = 0 ∧ t ≠ 0 then 1 else 0 := by
  subst ha
  cases t with
  | zero =>
    simp only [memByte, himg, Option.some.injEq] at hb
    subst hb; simp
  | succ k =>
    obtain ⟨m, hm, hbm⟩ := memByte_succ hb
    obtain ⟨hd, hpa | hpa⟩ := hsh k m hm
    · rw [byteAt_pd hpa hd, if_pos (by omega), show ((X : Int) + j - X).toNat = j by omega] at hbm
      have hdl : dL = [1, 0, 0, 0] := by decide
      rw [hdl] at hbm
      match j, hj, hbm with
      | 0, _, hbm => simp at hbm; simp [hbm]
      | 1, _, hbm => simp at hbm; simp [hbm]
      | 2, _, hbm => simp at hbm; simp [hbm]
      | 3, _, hbm => simp at hbm; simp [hbm]
    · rw [byteAt_pd hpa hd, if_neg (by simp only [Weak.Prom.Ref.Lit.X, Weak.Prom.Ref.Lit.Y]; omega)] at hbm
      cases hbm

/-- **THE READER'S PAIRS** (plan §2 steps 1–6 for MP, per iteration): the flag load's 1 is a flag message, which
sits above a data message (hart 0's Ψ); the data load's byte 0 therefore cannot read the image (hart 1's Ψ:
no data write between its source and the flag load's), so it reads a data message: the word 1. -/
theorem reader_ok (himg : ∀ a, run.cfg.pcImg a = some 0) (hQ : ∀ h, Qs M h (memEv (run.trace h)))
    (hnc : noCmo M)
    (hpart : ∀ t, 1 ≤ t → t ≤ M.length → exU (fun h => t ∈ run.fulfils h ∧ tidAt M t = some h))
    (hwf : run.traceWf M) : qLoop (run.trace 1) := by
  intro i e0 e1 h0 h1 hr0 v hr1
  have hm0 := List.mem_of_getElem? h0
  have hm1 := List.mem_of_getElem? h1
  have hQ1 : Q1 M (memEv (run.trace 1)) := hQ 1
  have hF : ldF e0 := by
    rcases hQ1.1 e0 hm0 with hh | ⟨tvs, rfl, _⟩
    · exact hh
    · simp [ldRet, Weak.Prom.Ref.Lit.X, Weak.Prom.Ref.Lit.Y] at hr0
  have hD : ldD e1 := by
    rcases hQ1.1 e1 hm1 with ⟨tvs, rfl, _⟩ | hh
    · simp [ldRet, Weak.Prom.Ref.Lit.X, Weak.Prom.Ref.Lit.Y] at hr1
    · exact hh
  have hord := hQ1.2 i e0 e1 h0 h1 hF hD hnc
  obtain ⟨tvs0, rfl, hl0⟩ := hF
  obtain ⟨tvs1, rfl, hl1⟩ := hD
  simp only [ldRet, if_true, Option.some.injEq] at hr0 hr1
  obtain ⟨s0, b0, r0, rfl⟩ := tvs_cons hl0 (by decide)
  have hb0 : memByte run.cfg.pcImg M s0 (Y : Int) = some b0 := kit_read0 hwf hm0 rfl
  have hv0 : b0.toNat = 1 := by have := obsOf_b0 hr0; simpa using this
  obtain ⟨k, m, rfl, hm, hbm⟩ := src_of_val hb0 (himg _) (by intro hh; rw [hh] at hv0; simp at hv0)
  have hsh : ∀ (k : Nat) (m : PMsg), M[k]? = some m → m.data = dL ∧ (m.pa = X ∨ m.pa = Y) := fun _ _ hm =>
    have hs := msg_shape hQ hpart hwf hm
    ⟨hs.1, hs.2.imp_right (·.1)⟩
  obtain ⟨hd, hpa | ⟨_, k', m', hk', hm', hpa', hd'⟩⟩ := msg_shape hQ hpart hwf hm
  · rw [byteAt_none_of hpa hd (by decide)] at hbm; cases hbm
  · match tvs1, hl1 with
    | [(t1, v1), (u1, w1), (u2, w2), (u3, w3)], _ =>
      obtain ⟨hb1, hb2, hb3, hb4, -⟩ := kit_read hwf hm1 (base := (X : Int))
        (tvs := [(t1, v1), (u1, w1), (u2, w2), (u3, w3)]) rfl
      have ht1 : t1 ≠ 0 := by
        rintro rfl
        have hbX : (m'.byteAt (X : Int)).isSome = true := by rw [byteAt_pd hpa' hd']; decide
        exact hord (writesIn_of (lo := 0) (hi := k + 1) hm' hbX (by omega) (by omega))
      have e1 := byteX himg hsh 0 (by decide) (by simp) hb1
      have e2 := byteX himg hsh 1 (by decide) (by omega) hb2
      have e3 := byteX himg hsh 2 (by decide) (by omega) hb3
      have e4 := byteX himg hsh 3 (by decide) (by omega) hb4
      simp only [ht1, ne_eq, not_false_eq_true, and_true, if_true, Nat.succ_ne_zero, false_and,
        if_false] at e1 e2 e3 e4
      subst e1 e2 e3 e4
      rw [← hr1]; rfl

end glue

/-! ## 8. THE THEOREMS -/

/-- **MP FOREVER, IN THE LOGIC** (owner request 2026-11-13).  Over every final memory and every valid run of
machine v2 with the loop front end — finished or not (no hart ever finishes, `loop_noDone`) — every hart's trace
satisfies `qLoop`: among its memory entries, every data load immediately after a flag load that returned 1
returned 1.  Proved by A0 (`PF.adequacy`, export (ii)) with `Proto.triv`. -/
theorem lit_mpLoop : ∀ (M : List PMsg) (run : PFRun LP Unit),
    PF.validRun (xStep xsLoop) imgLoop () (progs tLoop) M run → ∀ h, qLoop (run.trace h) := by
  intro M run hrun
  have hnoinv := OA.x_noInvalT hrun   -- MachFix-R-b5
  obtain ⟨hQ, hnc, hpart, hwf, himg⟩ := kitAdeqX (Xs := xsLoop) (T := tLoop) (Qs M) (Qs_nil M)
    (fun h p hp _ => by
      obtain ⟨hpr, hpc, hq, _, hrd⟩ := PF.progs_get hp
      match h with
      | 0 =>
        exact h0_wp _ M 0 p ⟨by rw [hpr]; rfl, hq, hpc, by rw [hrd 6 (by decide) (by decide)]; rfl,
          by rw [hrd 12 (by decide) (by decide)]; rfl, by rw [hrd 13 (by decide) (by decide)]; rfl⟩
      | 1 =>
        exact h1_wp _ M 1 p ⟨by rw [hpr]; rfl, hq, hpc, by rw [hrd 12 (by decide) (by decide)]; rfl,
          by rw [hrd 13 (by decide) (by decide)]; rfl⟩ hnoinv
      | n + 2 =>
        have hl : (progs tLoop).length = 2 := rfl
        rw [List.getElem?_eq_none (by omega)] at hp; cases hp) hrun
  have himg' : ∀ a, run.cfg.pcImg a = some 0 := fun a => by rw [himg]; rfl
  intro h
  match h with
  | 0 =>
    intro i e0 e1 h0 _ hr0 _ _
    rcases (hQ 0 : Q0 _) e0 (List.mem_of_getElem? h0) with ⟨_, _, rfl⟩ | ⟨⟨_, _, rfl⟩, _⟩ <;> simp [ldRet] at hr0
  | 1 => exact reader_ok himg' hQ hnc hpart hwf
  | n + 2 =>
    intro i e0 e1 h0
    have h2 : memEv (run.trace (n + 2)) = [] := hQ (n + 2)
    rw [h2] at h0; simp at h0

/-! ## 9. No hart is ever done (pure, from the front end) -/

theorem instrNext_pc {n : Nat} {s : LP} {ins : Instr} {l : PLabel} {s' : LP} (h : instrNext n s ins l = some s') :
    s'.prog = s.prog ∧ (s'.pc = s.pc + 1 ∨ (∃ c r1 r2 t, ins = .br c r1 r2 t) ∨ ∃ t, ins = .jmp t) := by
  cases ins <;> simp only [instrNext] at h <;> (repeat' split at h) <;>
    first
    | (cases h; exact ⟨rfl, .inl rfl⟩)
    | (cases h; done)
    | (obtain ⟨_, _, rfl⟩ := go1_eq h; exact ⟨rfl, .inl rfl⟩)
    | (obtain ⟨_, _, rfl⟩ := go1_eq h; exact ⟨rfl, .inr (.inl ⟨_, _, _, _, rfl⟩)⟩)
    | (obtain ⟨_, _, rfl⟩ := go1_eq h; exact ⟨rfl, .inr (.inr ⟨_, rfl⟩)⟩)

/-- The reachable-state invariant: a hart's own program, `pc < 4`. -/
def invL (s : LP) : Prop := (s.prog = bL0 ∨ s.prog = bL1) ∧ s.pc < 4

theorem step_plain {s s' : LP} {l : PLabel} {X0 : List XI} {ins : Instr} (hq : s.q = [])
    (hX : xOf xsLoop s.prog = some X0) (hx : X0[s.pc]? = some (.i ins)) (hpl : (XI.i ins).plain = true)
    (hnb : ∀ c r1 r2 t, ins ≠ .br c r1 r2 t) (hnj : ∀ t, ins ≠ .jmp t) (h : xNext xsLoop s l = some s') :
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

theorem step_inv {s s' : LP} {l : PLabel} (h : xNext xsLoop s l = some s') (hi : invL s) : invL s' := by
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
    · have hX : xOf xsLoop s.prog = some pL0 := by rw [hP]; exact xOf_L0
      rcases (by omega : s.pc = 0 ∨ s.pc = 1 ∨ s.pc = 2 ∨ s.pc = 3) with hc | hc | hc | hc
      · obtain ⟨h1, h2⟩ := step_plain hq hX (by rw [hc]; rfl) rfl (fun _ _ _ _ he => by cases he)
          (fun _ he => by cases he) h
        exact ⟨.inl (h1.trans hP), by omega⟩
      · obtain ⟨h1, h2⟩ := step_plain hq hX (by rw [hc]; rfl) rfl (fun _ _ _ _ he => by cases he)
          (fun _ he => by cases he) h
        exact ⟨.inl (h1.trans hP), by omega⟩
      · obtain ⟨h1, h2⟩ := step_plain hq hX (by rw [hc]; rfl) rfl (fun _ _ _ _ he => by cases he)
          (fun _ he => by cases he) h
        exact ⟨.inl (h1.trans hP), by omega⟩
      · obtain ⟨_, rfl⟩ := OA.xNext_br hq hX (by rw [hc]; rfl) (by rw [hP]; decide) h
        exact ⟨.inl hP, by simp [brEval]⟩
    · have hX : xOf xsLoop s.prog = some pL1 := by rw [hP]; exact xOf_L1
      rcases (by omega : s.pc = 0 ∨ s.pc = 1 ∨ s.pc = 2 ∨ s.pc = 3) with hc | hc | hc | hc
      · obtain ⟨h1, h2⟩ := step_plain hq hX (by rw [hc]; rfl) rfl (fun _ _ _ _ he => by cases he)
          (fun _ he => by cases he) h
        exact ⟨.inr (h1.trans hP), by omega⟩
      · obtain ⟨h1, h2⟩ := step_plain hq hX (by rw [hc]; rfl) rfl (fun _ _ _ _ he => by cases he)
          (fun _ he => by cases he) h
        exact ⟨.inr (h1.trans hP), by omega⟩
      · obtain ⟨h1, h2⟩ := step_plain hq hX (by rw [hc]; rfl) rfl (fun _ _ _ _ he => by cases he)
          (fun _ he => by cases he) h
        exact ⟨.inr (h1.trans hP), by omega⟩
      · obtain ⟨_, rfl⟩ := OA.xNext_br hq hX (by rw [hc]; rfl) (by rw [hP]; decide) h
        exact ⟨.inr hP, by simp [brEval]⟩

theorem solo_inv {img : Image} {M : List PMsg} {i : Nat} :
    ∀ {x y : LP × PState × GSet Nat} {tr : Trace}, soloSteps (anyFab (xStep xsLoop)) img M i x tr y →
      invL x.1 → invL y.1 := by
  intro x y tr hs
  induction hs with
  | refl => exact id
  | step x l ots p' ws' prom' tr y hp _ _ ih =>
    intro hi
    obtain ⟨_, _, hp⟩ := hp
    exact ih (step_inv hp hi)

/-- **NO HART EVER FINISHES** (pure, from the front end): in every valid run, no hart's final program state is
done — every reachable program state of each hart has `pc < 4` (its program's length), so `litDone` is `none`. -/
theorem loop_noDone : ∀ (M : List PMsg) (run : PFRun LP Unit),
    PF.validRun (xStep xsLoop) imgLoop () (progs tLoop) M run → ∀ h v, ¬ run.done litDone h v := by
  rintro M run ⟨hv, -⟩ h v ⟨ag, hag, hdv⟩
  have hl := validRun_len hv
  have hh : h < (progs tLoop).length := by rw [← hl]; exact (List.getElem?_eq_some_iff.1 hag).1
  obtain ⟨ag', hag', P0, _, hs⟩ := validRun_soloD hv h _ (List.getElem?_eq_getElem hh)
  rw [hag] at hag'; cases hag'
  have hi0 : invL (progs tLoop)[h] := by
    have h2 : h < 2 := hh
    match h, h2 with
    | 0, _ => exact ⟨.inl rfl, by show 0 < 4; decide⟩
    | 1, _ => exact ⟨.inr rfl, by show 0 < 4; decide⟩
  obtain ⟨hP, hpc⟩ := solo_inv hs hi0
  unfold litDone at hdv
  split at hdv
  · next hc =>
    have h4 : ag.paSt.prog.length = 4 := by rcases hP with hP | hP <;> rw [hP] <;> rfl
    have := hc.2
    have hpc' : ag.paSt.pc < 4 := hpc
    omega
  · cases hdv

end Weak.Prom.PF.Loop

#print axioms Weak.Prom.PF.Loop.lit_mpLoop
#print axioms Weak.Prom.PF.Loop.loop_noDone

