/-
Weak/Mini: **`mini_lit_mpLoop` — MP FOREVER on MiniMach, proved in MiniLogic** (mini plan rev 4 §2 L6: the
machine-level LEMMA behind the headline `mini_inf_mpLoop`; the full stack's template is
`Weak/Prom/CoreLitLoop.lean` `lit_mpLoop`).

The program `loopP` is CoreLitLoop.lean `tLoop` as an F program (no unrolling: MiniMach's front end loops):
  hart 0:  0: sw x6,0(x12)   1: fence w,w   2: sw x6,0(x13)   3: beq x0,x0,0     (x6 = 1, x12 = X, x13 = Y)
  hart 1:  0: lw x10,0(x13)  1: fence r,r   2: lw x11,0(x12)  3: beq x0,x0,0     (x12 = X, x13 = Y)
(`X = 0x1000` the data, `Y = 0x2000` the flag; image 0; size 4).  Both harts loop UNCONDITIONALLY through the
BACKWARD branch `beq x0,x0,0` (`wp_br`).
* `mini_lit_mpLoop`: over every final memory and every valid run (no `done` premise: no hart ever finishes), every
  hart's trace satisfies `qLoop`: among its memory entries, a data load immediately after a flag load that
  returned 1 returned 1 (RVWMO rule 4 twice, per iteration).
* Each hart's wp is a Löb induction at the loop head (`h0_loop`, `h1_loop`).  Hart 0's Ψ (`Q0`): every memory entry
  is a store of 1 to the data, or to the flag above a data store of the hart.  Hart 1's Ψ (`Q1`): every memory entry
  is a load; a data load right after a flag load sees no write to the data between its timestamp and the flag
  load's.  Hart 1's loop invariant: its forward bank stays empty (it never stores).
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Mini.LitMpFF

namespace Weak.Mini.Logic

open Weak.Mini Weak.Mini.Mach
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode

/-- `fence r,r`. -/
def fRRm : MFence := ⟨true, false, false, false, true, false, false, false⟩

/-- CoreLitLoop.lean `tLoop` as an F program. -/
def loopP : MProg where
  harts := [[.store 6 12 0, .fence fWWm, .store 6 13 0, .br .eq 0 0 0],
            [.load true 10 13 0, .fence fRRm, .load true 11 12 0, .br .eq 0 0 0]]
  regs0 := [[(6, 1), (12, 0x1000), (13, 0x2000)], [(12, 0x1000), (13, 0x2000)]]
  img := []
  sz := 4

/-! ## 1. The property and the trace invariants -/

/-- The value a load at `a` returned. -/
def ldRet (a : Nat) (e : MLab × Option Nat) : Option Nat :=
  match e.1 with
  | .load b _ v _ => if b = a then some v else none
  | _ => none

/-- **THE PROPERTY**: among the memory entries of the trace, every data load (at `0x1000`) that immediately
follows a flag load (at `0x2000`) that returned 1 returned 1. -/
def qLoop (τ : Trace) : Prop :=
  ∀ i e0 e1, (memEv τ)[i]? = some e0 → (memEv τ)[i + 1]? = some e1 → ldRet 0x2000 e0 = some 1 →
    ∀ v, ldRet 0x1000 e1 = some v → v = 1

/-- Hart 0's Ψ: every memory entry is a store of 1 to the data, or to the flag above a data store of the hart. -/
def Q0 (ev : Trace) : Prop :=
  ∀ e ∈ ev, ∃ a t asr vsr, e = (.store a 1 asr vsr, some t) ∧
    (a = 0x1000 ∨ (a = 0x2000 ∧ ∃ t' asr' vsr', (.store 0x1000 1 asr' vsr', some t') ∈ ev ∧ t' < t))

/-- Hart 1's Ψ: every memory entry is a load; a data load right after a flag load sees no write to the data in
between their timestamps. -/
def Q1 (M : List MMsg) (ev : Trace) : Prop :=
  (∀ e ∈ ev, ∃ a t v asr, e = (.load a t v asr, none)) ∧
  ∀ i t0 v0 r0 t1 v1 r1, ev[i]? = some (.load 0x2000 t0 v0 r0, none) →
    ev[i + 1]? = some (.load 0x1000 t1 v1 r1, none) → ¬ writesIn M 0x1000 t1 t0

theorem Q0_snoc {ev : Trace} {e : MLab × Option Nat} (h : Q0 ev)
    (he : ∃ a t asr vsr, e = (.store a 1 asr vsr, some t) ∧
      (a = 0x1000 ∨ (a = 0x2000 ∧ ∃ t' asr' vsr', (.store 0x1000 1 asr' vsr', some t') ∈ ev ∧ t' < t))) :
    Q0 (ev ++ [e]) := by
  intro x hx
  have lift : ∀ {a t : Nat}, (a = 0x1000 ∨ (a = 0x2000 ∧ ∃ t' asr' vsr', (.store 0x1000 1 asr' vsr', some t') ∈ ev ∧
      t' < t)) → (a = 0x1000 ∨ (a = 0x2000 ∧ ∃ t' asr' vsr', (.store 0x1000 1 asr' vsr', some t') ∈ ev ++ [e] ∧
      t' < t)) := by
    rintro a t (h1 | ⟨h1, t', a', v', hm, hlt⟩)
    · exact .inl h1
    · exact .inr ⟨h1, t', a', v', List.mem_append_left _ hm, hlt⟩
  rcases List.mem_append.1 hx with hx | hx
  · obtain ⟨a, t, asr, vsr, rfl, hc⟩ := h x hx
    exact ⟨a, t, asr, vsr, rfl, lift hc⟩
  · rw [List.mem_singleton] at hx; subst hx
    obtain ⟨a, t, asr, vsr, rfl, hc⟩ := he
    exact ⟨a, t, asr, vsr, rfl, lift hc⟩

theorem Q1_snoc {M : List MMsg} {ev : Trace} {e : MLab × Option Nat} (h : Q1 M ev)
    (he : ∃ a t v asr, e = (.load a t v asr, none))
    (hl : ∀ t0 v0 r0 t1 v1 r1, ev.getLast? = some (.load 0x2000 t0 v0 r0, none) →
      e = (.load 0x1000 t1 v1 r1, none) → ¬ writesIn M 0x1000 t1 t0) : Q1 M (ev ++ [e]) := by
  refine ⟨fun x hx => ?_, fun i t0 v0 r0 t1 v1 r1 h0 h1 => ?_⟩
  · rcases List.mem_append.1 hx with hx | hx
    · exact h.1 x hx
    · rw [List.mem_singleton] at hx; subst hx; exact he
  · have hi1 : i + 1 < ev.length + 1 := by
      have := (List.getElem?_eq_some_iff.1 h1).1; simpa using this
    by_cases hi : i + 1 < ev.length
    · rw [List.getElem?_append_left (by omega)] at h0
      rw [List.getElem?_append_left hi] at h1
      exact h.2 i t0 v0 r0 t1 v1 r1 h0 h1
    · have hi' : i + 1 = ev.length := by omega
      rw [List.getElem?_append_right (by omega), hi', Nat.sub_self] at h1
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h1
      rw [List.getElem?_append_left (by omega)] at h0
      exact hl t0 v0 r0 t1 v1 r1 (by rw [List.getLast?_eq_getElem?, show ev.length - 1 = i by omega]; exact h0)
        h1

/-! ## 2. The harts, by Löb induction at the loop head -/

section harts

variable {hlc : HasLC} {GF : BundledGFunctors} [GhostVarG GF HSt] [InvGS_gen hlc GF]

/-- Hart 0 at its loop head. -/
def h0S (f : MFront) : Prop := f.pc = 0 ∧ f.q = [] ∧ f.rd 6 = 1 ∧ f.rd 12 = 0x1000 ∧ f.rd 13 = 0x2000

/-- Hart 1 at its loop head. -/
def h1S (f : MFront) : Prop := f.pc = 0 ∧ f.q = [] ∧ f.rd 12 = 0x1000 ∧ f.rd 13 = 0x2000

theorem br_taken (f : MFront) : (if MBrC.eval .eq (f.rd 0) (f.rd 0) = true then 0 else f.pc + 1) = 0 := by
  simp [MBrC.eval, MFront.rd]

/-- **HART 0's LOOP**: `sw; fence w,w; sw; beq` keeps `Q0` (Löb at `pc = 0`). -/
theorem h0_loop (M : List MMsg) (γ : GName) :
    ⊢@{IProp GF} ∀ (f : MFront) (ws : MSt) (τ : Trace), ⌜h0S f⌝ -∗ hartSt γ ws τ -∗
      wpH γ ⟨loopP, M, 0⟩ (fun τ => Q0 (memEv τ)) f (fun _ => iprop(⌜True⌝)) := by
  iloeb as IH
  iintro %f %ws %τ %hs Hst
  obtain ⟨hpc, hq, h6, h12, h13⟩ := hs
  have hv1 : f.rd 6 % wordW loopP = 1 := by rw [h6]; decide
  have hax : (f.rd 12 + 0) % two64 = 0x1000 := by rw [h12]; decide
  -- `sw x6,0(x12)`
  iapply (wp_store hq (by rw [hpc]; rfl) (by rw [hax]; decide) (qstable_mem _))
  iframe Hst
  inext
  iintro %tx %_ %_ %_ %hQ
  isplitr
  · ipureintro
    rw [memEv_mem _ _ _ rfl, hax, hv1]
    exact Q0_snoc hQ ⟨_, tx, _, _, rfl, .inl rfl⟩
  iintro Hst
  -- `fence w,w`
  iapply (wp_fence (f := MFront.mk (f.pc + 1) f.regs []) rfl (by rw [hpc]; rfl) (qstable_mem _))
  iframe Hst
  inext
  iintro Hst
  -- `sw x6,0(x13)`
  have hay : ((MFront.mk (f.pc + 1 + 1) f.regs []).rd 13 + 0) % two64 = 0x2000 := by
    show (f.rd 13 + 0) % two64 = 0x2000
    rw [h13]; decide
  have hv1' : (MFront.mk (f.pc + 1 + 1) f.regs []).rd 6 % wordW loopP = 1 := hv1
  iapply (wp_store (f := MFront.mk (f.pc + 1 + 1) f.regs []) rfl (by rw [hpc]; rfl) (by rw [hay]; decide)
    (qstable_mem _))
  iframe Hst
  inext
  iintro %ty %_ %_ %hext %hQ
  isplitr
  · ipureintro
    have hlt : tx < ty := by
      have h1 := (st_post ws (srcsView ws (srcR 12)) (max (srcsView ws (srcR 12)) (srcsView ws (srcR 6)))
        ((f.rd 12 + 0) % two64) tx).1
      have h2 := (fence_post (qWs (storePost ws (srcsView ws (srcR 12))
        (max (srcsView ws (srcR 12)) (srcsView ws (srcR 6))) ((f.rd 12 + 0) % two64) tx) [.instr])
        fWWm.pr fWWm.pw fWWm.sr fWWm.sw).1 rfl rfl
      have h3 := Nat.lt_of_le_of_lt (stPre_ge _ _ _).2 hext
      exact Nat.lt_of_le_of_lt h1 (Nat.lt_of_le_of_lt h2 h3)
    rw [memEv_qTr _ _ (by simp [isMem]), memEv_qTr _ _ (by simp [isMem]), memEv_mem _ _ _ rfl, hax, hv1] at hQ
    rw [memEv_mem _ _ _ rfl, memEv_qTr _ _ (by simp [isMem]), memEv_qTr _ _ (by simp [isMem]),
      memEv_mem _ _ _ rfl, hax, hay, hv1, hv1']
    exact Q0_snoc hQ ⟨_, ty, _, _, rfl, .inr ⟨rfl, tx, _, _, List.mem_append_right _ (List.mem_singleton_self _), hlt⟩⟩
  iintro Hst
  -- `beq x0,x0,0`: back to the loop head
  iapply (wp_br (f := MFront.mk (f.pc + 1 + 1 + 1) f.regs []) rfl (by rw [hpc]; rfl) (by decide) (qstable_mem _))
  iframe Hst
  inext
  iintro Hst
  rw [br_taken]
  iapply IH
  · ipureintro
    exact ⟨rfl, rfl, h6, h12, h13⟩
  · iexact Hst

/-- **HART 1's LOOP**: `lw; fence r,r; lw; beq` keeps `Q1` (Löb at `pc = 0`; its forward bank stays empty). -/
theorem h1_loop (M : List MMsg) (γ : GName) :
    ⊢@{IProp GF} ∀ (f : MFront) (ws : MSt) (τ : Trace), hartSt γ ws τ -∗ ⌜h1S f⌝ -∗ ⌜∀ a, ws.fwd a = none⌝ -∗
      wpH γ ⟨loopP, M, 1⟩ (fun τ => Q1 M (memEv τ)) f (fun _ => iprop(⌜True⌝)) := by
  iloeb as IH
  iintro %f %ws %τ Hst %hs %hf
  obtain ⟨hpc, hq, h12, h13⟩ := hs
  have hay : (f.rd 13 + 0) % two64 = 0x2000 := by rw [h13]; decide
  -- `lw x10,0(x13)`
  iapply (wp_load hq (by rw [hpc]; rfl) (by rw [hay]; decide) (qstable_mem _))
  iframe Hst
  inext
  iintro %s0 %v0 %_ %_ %hQ
  isplitr
  · ipureintro
    rw [memEv_mem _ _ _ rfl, hay]
    refine Q1_snoc hQ ⟨_, _, _, _, rfl⟩ (fun _ _ _ _ _ _ _ he => ?_)
    simp at he
  iintro Hst
  -- `fence r,r`
  iapply (wp_fence (f := MFront.mk (f.pc + 1) (f.wr 10 (if true = true then sext loopP.sz v0 else v0)) [])
    rfl (by rw [hpc]; rfl) (qstable_mem _))
  iframe Hst
  inext
  iintro Hst
  -- `lw x11,0(x12)`
  have hax : ((MFront.mk (f.pc + 1 + 1) (f.wr 10 (if true = true then sext loopP.sz v0 else v0)) []).rd 12 + 0)
      % two64 = 0x1000 := by rw [rd_wr_ne (by decide), h12]; decide
  iapply (wp_load (f := MFront.mk (f.pc + 1 + 1) (f.wr 10 (if true = true then sext loopP.sz v0 else v0)) [])
    rfl (by rw [hpc]; rfl) (by rw [hax]; decide) (qstable_mem _))
  iframe Hst
  inext
  iintro %s1 %v1 %_ %hok %hQ
  have hp1 := ld_post (ws := ws) (va := srcsView ws (srcR 13)) (vpre := ldPre ws (srcsView ws (srcR 13)))
    (a := (f.rd 13 + 0) % two64) (t := s0) (rd := 10) (hf _) (by decide)
  have hp2 := fence_post (qWs (loadPost ws (srcsView ws (srcR 13)) (ldPre ws (srcsView ws (srcR 13)))
    ((f.rd 13 + 0) % two64) s0) (regWL 10 [.ldres] ++ [.instr])) fRRm.pr fRRm.pw fRRm.sr fRRm.sw
  isplitr
  · ipureintro
    have hord : ¬ writesIn M 0x1000 s1 s0 := by
      intro hw
      apply hok.2
      rw [hax]
      refine writesIn_mono hw ?_
      have h3 := ldPre_ge (qWs (qWs (loadPost ws (srcsView ws (srcR 13)) (ldPre ws (srcsView ws (srcR 13)))
        ((f.rd 13 + 0) % two64) s0) (regWL 10 [.ldres] ++ [.instr])) [.fence fRRm.pr fRRm.pw fRRm.sr fRRm.sw, .instr])
        (srcsView (qWs (qWs (loadPost ws (srcsView ws (srcR 13)) (ldPre ws (srcsView ws (srcR 13)))
          ((f.rd 13 + 0) % two64) s0) (regWL 10 [.ldres] ++ [.instr])) [.fence fRRm.pr fRRm.pw fRRm.sr fRRm.sw, .instr])
          (srcR 12))
      have := hp2.2.1 rfl rfl
      have := hp1.2.1
      omega
    rw [memEv_qTr _ _ (by simp [isMem]), memEv_qTr _ _ (regWL_quiet _ _), memEv_mem _ _ _ rfl, hay] at hQ
    rw [memEv_mem _ _ _ rfl, memEv_qTr _ _ (by simp [isMem]), memEv_qTr _ _ (regWL_quiet _ _),
      memEv_mem _ _ _ rfl, hay, hax]
    refine Q1_snoc hQ ⟨_, _, _, _, rfl⟩ (fun t0 v0' r0 t1 v1' r1 hl he => ?_)
    simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or, Option.some.injEq, Prod.mk.injEq,
      MLab.load.injEq] at hl he
    obtain ⟨⟨_, rfl, _, _⟩, _⟩ := hl
    obtain ⟨⟨_, rfl, _, _⟩, _⟩ := he
    exact hord
  iintro Hst
  -- `beq x0,x0,0`: back to the loop head
  iapply (wp_br (f := MFront.mk (f.pc + 1 + 1 + 1) (MFront.wr (MFront.mk (f.pc + 1 + 1)
      (f.wr 10 (if true = true then sext loopP.sz v0 else v0)) []) 11 (if true = true then sext loopP.sz v1 else v1)) [])
    rfl (by rw [hpc]; rfl) (by decide) (qstable_mem _))
  iframe Hst
  inext
  iintro Hst
  rw [br_taken]
  iapply IH $$ %_ %_ %_ Hst
  · ipureintro
    refine ⟨rfl, rfl, ?_, ?_⟩
    · show (MFront.mk _ (MFront.wr (MFront.mk _ (f.wr 10 _) []) 11 _) []).rd 12 = _
      rw [rd_wr_ne (by decide), rd_wr_ne (by decide), h12]
    · show (MFront.mk _ (MFront.wr (MFront.mk _ (f.wr 10 _) []) 11 _) []).rd 13 = _
      rw [rd_wr_ne (by decide), rd_wr_ne (by decide), h13]
  · ipureintro
    have hf2 : ∀ b, (qWs (qWs (loadPost ws (srcsView ws (srcR 13)) (ldPre ws (srcsView ws (srcR 13)))
        ((f.rd 13 + 0) % two64) s0) (regWL 10 [.ldres] ++ [.instr])) [.fence fRRm.pr fRRm.pw fRRm.sr fRRm.sw, .instr]).fwd b
        = none := fun b => by rw [qWs_fwd]; exact fwdN_ld (rd := 10) hf (by decide) b
    intro a
    rw [qWs_fwd]
    exact fwdN_ld (rd := 11) hf2 (by decide) a

theorem h0_wp (M : List MMsg) (f0 : MFront) (hs : h0S f0) :
    ⊢@{IProp GF} wp loopP M 0 (fun τ => Q0 (memEv τ)) f0 (fun _ => iprop(⌜True⌝)) := by
  unfold wp
  iintro %γ Hst
  ihave H := h0_loop (GF := GF) M γ
  iapply H $$ %f0 %msInit %([] : Trace) %hs Hst

theorem h1_wp (M : List MMsg) (f0 : MFront) (hs : h1S f0) :
    ⊢@{IProp GF} wp loopP M 1 (fun τ => Q1 M (memEv τ)) f0 (fun _ => iprop(⌜True⌝)) := by
  unfold wp
  iintro %γ Hst
  ihave H := h1_loop (GF := GF) M γ
  iapply H $$ %f0 %msInit %([] : Trace) Hst %hs %(fun _ => rfl)

end harts

/-! ## 3. The lemma -/

/-- Ψ of the loop: `Q0` for hart 0, `Q1` for hart 1, nothing for other indices. -/
def QsLoop (M : List MMsg) : Nat → Trace → Prop
  | 0 => Q0
  | 1 => Q1 M
  | _ => fun ev => ev = []

theorem QsLoop_nil (M : List MMsg) : ∀ h, QsLoop M h []
  | 0 => fun _ he => by cases he
  | 1 => ⟨fun _ he => (by cases he), fun _ _ _ _ _ _ _ h => (by simp at h)⟩
  | _ + 2 => rfl

/-- **MP FOREVER on MiniMach** (machine-level lemma, proved in MiniLogic by Löb induction at the loop heads).
Over every final memory and every valid run of `loopP` — no hart ever finishes, and no `done` premise is
needed — every hart's trace satisfies `qLoop`. -/
theorem mini_lit_mpLoop : ∀ (Mm : List MMsg) (r : MRun), miniValidRun loopP Mm r → ∀ h, qLoop (r.trace h) := by
  intro Mm r hv
  obtain ⟨hQ, hW, hR, hS⟩ := adeqMem hv (QsLoop Mm) (QsLoop_nil Mm) (fun h hs hh _ => by
    obtain ⟨hlt, rfl⟩ := mInit_get hh
    match h, hlt with
    | 0, _ => exact h0_wp _ _ ⟨rfl, rfl, by decide, by decide, by decide⟩
    | 1, _ => exact h1_wp _ _ ⟨rfl, rfl, by decide, by decide⟩)
  have hQ0 : Q0 (memEv (r.trace 0)) := hQ 0
  have hQ1 : Q1 Mm (memEv (r.trace 1)) := hQ 1
  -- every store entry is hart 0's, of the word 1
  have hst : ∀ (j : Nat) a w asrc vsrc s, (MLab.store a w asrc vsrc, some s) ∈ memEv (r.trace j) →
      j = 0 ∧ w = 1 := by
    intro j a w asrc vsrc s hs
    match j, hs with
    | 0, hs =>
      obtain ⟨_, _, _, _, he, _⟩ := hQ0 _ hs
      simp only [Prod.mk.injEq, MLab.store.injEq] at he
      exact ⟨rfl, he.1.2.1⟩
    | 1, hs =>
      obtain ⟨_, _, _, _, he⟩ := hQ1.1 _ hs
      simp at he
    | n + 2, hs =>
      have h0 : memEv (r.trace (n + 2)) = [] := hQ (n + 2)
      rw [h0] at hs; cases hs
  intro h i e0 e1 h0 h1 hr0 v hr1
  match h with
  | 0 =>
    obtain ⟨_, _, _, _, rfl, _⟩ := hQ0 _ (List.mem_of_getElem? h0)
    simp [ldRet] at hr0
  | n + 2 =>
    have he : memEv (r.trace (n + 2)) = [] := hQ (n + 2)
    rw [he] at h0; simp at h0
  | 1 =>
    obtain ⟨a0, t0, v0, r0, rfl⟩ := hQ1.1 _ (List.mem_of_getElem? h0)
    obtain ⟨a1, t1, v1, r1, rfl⟩ := hQ1.1 _ (List.mem_of_getElem? h1)
    simp only [ldRet] at hr0 hr1
    by_cases ha0 : a0 = 0x2000
    case neg => rw [if_neg ha0] at hr0; cases hr0
    by_cases ha1 : a1 = 0x1000
    case neg => rw [if_neg ha1] at hr1; cases hr1
    subst ha0 ha1
    simp only [if_true, Option.some.injEq] at hr0 hr1
    subst hr0 hr1
    have hord := hQ1.2 i _ _ _ _ _ _ h0 h1
    -- the flag load's 1 is hart 0's flag store, above a data store
    obtain ⟨j, _, _, hj⟩ := read_src hR hW rfl (memEv_sub (List.mem_of_getElem? h0)) (by decide)
    obtain ⟨rfl, -⟩ := hst j _ _ _ _ _ hj
    obtain ⟨_, _, _, _, he, hc⟩ := hQ0 _ hj
    simp only [Prod.mk.injEq, MLab.store.injEq, Option.some.injEq] at he
    obtain ⟨⟨rfl, -, -, -⟩, rfl⟩ := he
    rcases hc with hc | ⟨-, tx, _, _, hx, hlt⟩
    · exact absurd hc (by decide)
    obtain ⟨_, htx, htx0, hMx⟩ := hS 0 _ _ _ _ _ (memEv_sub hx)
    cases htx
    -- the data load: not from the image (the data store lies in between), so a message of 1
    cases t1 with
    | zero => exact absurd (writesIn_of (k := tx - 1) hMx rfl (by omega) (by omega)) hord
    | succ k =>
      obtain ⟨m, hk, _, hmv⟩ := memv_succ (hR 1 _ _ _ _ _ (memEv_sub (List.mem_of_getElem? h1)))
      obtain ⟨asrc, vsrc, hmw⟩ := hW k m hk
      have := (hst _ _ _ _ _ _ hmw).2
      rw [hmv] at this
      exact this

end Weak.Mini.Logic
