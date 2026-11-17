/-
Weak/Mini: **`mini_lit_mpFF` — MP+fence.w.w+fence.r.rw is FORBIDDEN on MiniMach, proved in MiniLogic** (mini plan
rev 4 §2 L6: the machine-level LEMMA behind the headline `mini_forbidden mpFF`; the full stack's template is
`Weak/Prom/CoreLitMP.lean` `lit_mpFF`, plan rev 7 §5 row 8).

The program `mpFFP` is RefTests.lean `mpFF` (:111) as an F program: hart 0 `sw x5,0(x6); fence w,w; sw x5,0(x7)`
(`x5 = 1`, `x6 = X = 0x1000`, `x7 = Y = 0x2000`) ‖ hart 1 `lw x5,0(x6); fence r,rw; lw x7,0(x8)` (`x6 = Y`,
`x8 = X`); image 0; size 4.  Outcome `x5 = 1 ∧ x7 = 0` of hart 1: FORBIDDEN (rule 4).
* Hart 0 proves `QWW`: its memory entries are a prefix of `st X 1 @tx; st Y 1 @ty` with `tx < ty` (FULFIL gives
  `vwOld ≥ tx`, `fence w,w` the store floor `vwNew ≥ vwOld`, EXT of the second store `vwNew ≤ pv < ty`).
* Hart 1 proves `QRR`: a prefix of `ld Y @s0; ld X @s1` with no write to `X` in `(s1, s0]` (LOAD (X4) `vrOld ≥ s0`,
  `fence r,·` the load floor `vrNew ≥ vrOld`, the second load's `loadOk` at a pre-view `≥ vrNew`).
* The contradiction from `adeqMem`'s exports only: `ld Y` of 1 reads hart 0's `st Y @ty`, so `s0 = ty > tx`;
  `ld X` of 0 reads the image (`s1 = 0`: every message holds 1), so hart 0's `st X @tx` is a write to `X` in
  `(0, s0]`.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Mini.LitLbdd

namespace Weak.Mini.Logic

open Weak.Mini Weak.Mini.Mach
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode

/-- `fence w,w`. -/
def fWWm : MFence := ⟨false, true, false, false, false, true, false, false⟩
/-- `fence r,rw`. -/
def fRRWm : MFence := ⟨true, false, false, false, true, true, false, false⟩

/-- RefTests.lean `mpFF` (:111) as an F program. -/
def mpFFP : MProg where
  harts := [[.store 5 6 0, .fence fWWm, .store 5 7 0], [.load true 5 6 0, .fence fRRWm, .load true 7 8 0]]
  regs0 := [[(5, 1), (6, 0x1000), (7, 0x2000)], [(6, 0x2000), (8, 0x1000)]]
  img := []
  sz := 4

/-- The writer's memory entries: a prefix of `st x 1 @tx; st y 1 @ty` with `tx < ty`. -/
def QWW (x y : Nat) (ev : Trace) : Prop :=
  ∃ tx ty a1 b1 a2 b2, tx < ty ∧ ev <+: [(.store x 1 a1 b1, some tx), (.store y 1 a2 b2, some ty)]

/-- The reader's memory entries: a prefix of `ld y @s0; ld x @s1` with no write to `x` in `(s1, s0]`. -/
def QRR (M : List MMsg) (y x : Nat) (ev : Trace) : Prop :=
  ∃ s0 s1 v0 v1 a0 a1, ¬ writesIn M x s1 s0 ∧ ev <+: [(.load y s0 v0 a0, none), (.load x s1 v1 a1, none)]

theorem not_writesIn_self (M : List MMsg) (x s : Nat) : ¬ writesIn M x s s := fun ⟨_, h1, h2, _⟩ => by omega

section harts

variable {hlc : HasLC} {GF : BundledGFunctors} [GhostVarG GF HSt] [InvGS_gen hlc GF]

/-- **The writer in the logic**: `sw x5,0(x6); fence w,w; sw x5,0(x7)` proves `QWW x y`. -/
theorem ww_hart (M : List MMsg) (h x y : Nat) (f0 : MFront)
    (hprog : mpFFP.prog h = [.store 5 6 0, .fence fWWm, .store 5 7 0]) (hpc : f0.pc = 0) (hq : f0.q = [])
    (h5 : f0.rd 5 = 1) (hx : f0.rd 6 = x) (hy : f0.rd 7 = y) (hxa : x % 4 = 0) (hya : y % 4 = 0)
    (hxl : x < two64) (hyl : y < two64) :
    ⊢@{IProp GF} wp mpFFP M h (fun τ => QWW x y (memEv τ)) f0 (fun _ => iprop(⌜True⌝)) := by
  unfold wp
  iintro %γ Hst
  have hax : (f0.rd 6 + 0) % two64 = x := by rw [hx, Nat.add_zero, Nat.mod_eq_of_lt hxl]
  have hv1 : f0.rd 5 % wordW mpFFP = 1 := by rw [h5]; decide
  -- `sw x5,0(x6)`
  iapply (wp_store hq (by rw [hprog, hpc]; rfl) (by rw [hax]; exact hxa) (qstable_mem _))
  iframe Hst
  inext
  iintro %tx %_ %_ %_ %_
  isplitr
  · ipureintro
    rw [memEv_mem _ _ _ rfl, hax, hv1]
    exact ⟨tx, tx + 1, _, _, [], [], by omega, ⟨[(.store y 1 [] [], some (tx + 1))], rfl⟩⟩
  iintro Hst
  -- `fence w,w`
  iapply (wp_fence (f := MFront.mk (f0.pc + 1) f0.regs []) rfl (by rw [hprog, hpc]; rfl) (qstable_mem _))
  iframe Hst
  inext
  iintro Hst
  -- `sw x5,0(x7)`
  have hay : ((MFront.mk (f0.pc + 1 + 1) f0.regs []).rd 7 + 0) % two64 = y := by
    show (f0.rd 7 + 0) % two64 = y
    rw [hy, Nat.add_zero, Nat.mod_eq_of_lt hyl]
  iapply (wp_store (f := MFront.mk (f0.pc + 1 + 1) f0.regs []) rfl (by rw [hprog, hpc]; rfl)
    (by rw [hay]; exact hya) (qstable_mem _))
  iframe Hst
  inext
  iintro %ty %_ %_ %hext %_
  isplitr
  · ipureintro
    have hlt : tx < ty := by
      have h1 := (st_post msInit (srcsView msInit (srcR 6)) (max (srcsView msInit (srcR 6)) (srcsView msInit (srcR 5)))
        ((f0.rd 6 + 0) % two64) tx).1
      have h2 := (fence_post (qWs (storePost msInit (srcsView msInit (srcR 6))
        (max (srcsView msInit (srcR 6)) (srcsView msInit (srcR 5))) ((f0.rd 6 + 0) % two64) tx) [.instr])
        fWWm.pr fWWm.pw fWWm.sr fWWm.sw).1 rfl rfl
      have h3 := Nat.lt_of_le_of_lt (stPre_ge _ _ _).2 hext
      exact Nat.lt_of_le_of_lt h1 (Nat.lt_of_le_of_lt h2 h3)
    have hv1' : (MFront.mk (f0.pc + 1 + 1) f0.regs []).rd 5 % wordW mpFFP = 1 := hv1
    rw [memEv_mem _ _ _ rfl, memEv_qTr _ _ (by simp [isMem]), memEv_qTr _ _ (by simp [isMem]), memEv_mem _ _ _ rfl,
      hax, hay, hv1, hv1']
    exact ⟨tx, ty, _, _, _, _, hlt, List.prefix_refl _⟩
  iintro Hst
  iapply (wp_done (f := MFront.mk (f0.pc + 1 + 1 + 1) _ []) rfl (by rw [hprog, hpc]; rfl))
  iframe Hst

/-- **The reader in the logic**: `lw x5,0(x6); fence r,rw; lw x7,0(x8)` proves `QRR M y x`. -/
theorem rr_hart (M : List MMsg) (h x y : Nat) (f0 : MFront)
    (hprog : mpFFP.prog h = [.load true 5 6 0, .fence fRRWm, .load true 7 8 0]) (hpc : f0.pc = 0)
    (hq : f0.q = []) (hy : f0.rd 6 = y) (hx : f0.rd 8 = x) (hxa : x % 4 = 0) (hya : y % 4 = 0)
    (hxl : x < two64) (hyl : y < two64) :
    ⊢@{IProp GF} wp mpFFP M h (fun τ => QRR M y x (memEv τ)) f0 (fun _ => iprop(⌜True⌝)) := by
  unfold wp
  iintro %γ Hst
  have hay : (f0.rd 6 + 0) % two64 = y := by rw [hy, Nat.add_zero, Nat.mod_eq_of_lt hyl]
  -- `lw x5,0(x6)`
  iapply (wp_load hq (by rw [hprog, hpc]; rfl) (by rw [hay]; exact hya) (qstable_mem _))
  iframe Hst
  inext
  iintro %s0 %v0 %_ %_ %_
  isplitr
  · ipureintro
    rw [memEv_mem _ _ _ rfl, hay]
    exact ⟨s0, s0, v0, 0, _, [], not_writesIn_self _ _ _, ⟨[(.load x s0 0 [], none)], rfl⟩⟩
  iintro Hst
  -- `fence r,rw`
  iapply (wp_fence (f := MFront.mk (f0.pc + 1) (f0.wr 5 (if true = true then sext mpFFP.sz v0 else v0)) [])
    rfl (by rw [hprog, hpc]; rfl) (qstable_mem _))
  iframe Hst
  inext
  iintro Hst
  -- `lw x7,0(x8)`
  have hax : ((MFront.mk (f0.pc + 1 + 1) (f0.wr 5 (if true = true then sext mpFFP.sz v0 else v0)) []).rd 8 + 0)
      % two64 = x := by rw [rd_wr_ne (by decide), hx, Nat.add_zero, Nat.mod_eq_of_lt hxl]
  iapply (wp_load (f := MFront.mk (f0.pc + 1 + 1) (f0.wr 5 (if true = true then sext mpFFP.sz v0 else v0)) [])
    rfl (by rw [hprog, hpc]; rfl) (by rw [hax]; exact hxa) (qstable_mem _))
  iframe Hst
  inext
  iintro %s1 %v1 %_ %hok %_
  isplitr
  · ipureintro
    have hord : ¬ writesIn M x s1 s0 := by
      intro hw
      apply hok.2
      rw [hax]
      refine writesIn_mono hw ?_
      have h1 := (ld_post (ws := msInit) (va := srcsView msInit (srcR 6))
        (vpre := ldPre msInit (srcsView msInit (srcR 6))) (a := (f0.rd 6 + 0) % two64) (t := s0) (rd := 5)
        rfl (by decide)).2.1
      have h2 := (fence_post (qWs (loadPost msInit (srcsView msInit (srcR 6)) (ldPre msInit (srcsView msInit (srcR 6)))
        ((f0.rd 6 + 0) % two64) s0) (regWL 5 [.ldres] ++ [.instr])) fRRWm.pr fRRWm.pw fRRWm.sr fRRWm.sw).2.1 rfl rfl
      have h3 := ldPre_ge (qWs (qWs (loadPost msInit (srcsView msInit (srcR 6)) (ldPre msInit (srcsView msInit (srcR 6)))
        ((f0.rd 6 + 0) % two64) s0) (regWL 5 [.ldres] ++ [.instr])) [.fence fRRWm.pr fRRWm.pw fRRWm.sr fRRWm.sw, .instr])
        (srcsView (qWs (qWs (loadPost msInit (srcsView msInit (srcR 6)) (ldPre msInit (srcsView msInit (srcR 6)))
          ((f0.rd 6 + 0) % two64) s0) (regWL 5 [.ldres] ++ [.instr])) [.fence fRRWm.pr fRRWm.pw fRRWm.sr fRRWm.sw, .instr])
          (srcR 8))
      omega
    rw [memEv_mem _ _ _ rfl, memEv_qTr _ _ (by simp [isMem]), memEv_qTr _ _ (regWL_quiet _ _), memEv_mem _ _ _ rfl,
      hay, hax]
    exact ⟨s0, s1, v0, v1, _, _, hord, List.prefix_refl _⟩
  iintro Hst
  iapply (wp_done (f := MFront.mk (f0.pc + 1 + 1 + 1) _ []) rfl (by rw [hprog, hpc]; rfl))
  iframe Hst

end harts

/-- Ψ of mpFF: the writer at `X`/`Y`, the reader at `Y`/`X`, nothing for other indices. -/
def QsMP (M : List MMsg) : Nat → Trace → Prop
  | 0 => QWW 0x1000 0x2000
  | 1 => QRR M 0x2000 0x1000
  | _ => fun ev => ev = []

theorem QsMP_nil (M : List MMsg) : ∀ h, QsMP M h []
  | 0 => ⟨0, 1, [], [], [], [], by omega, List.nil_prefix⟩
  | 1 => ⟨0, 0, 0, 0, [], [], not_writesIn_self _ _ _, List.nil_prefix⟩
  | _ + 2 => rfl

/-- **MP+fence.w.w+fence.r.rw is FORBIDDEN on MiniMach** (machine-level lemma, proved in MiniLogic): over every
final memory and every valid run of `mpFFP`, not (hart 1's first load returns 1 and its second returns 0). -/
theorem mini_lit_mpFF : ∀ (Mm : List MMsg) (r : MRun), miniValidRun mpFFP Mm r →
    ¬ (r.obsLoad 1 0 = some 1 ∧ r.obsLoad 1 1 = some 0) := by
  intro Mm r hv ⟨ho0, ho1⟩
  obtain ⟨hQ, hW, hR, hS⟩ := adeqMem hv (QsMP Mm) (QsMP_nil Mm) (fun h hs hh _ => by
    obtain ⟨hlt, rfl⟩ := mInit_get hh
    match h, hlt with
    | 0, _ => exact ww_hart _ 0 _ _ _ rfl rfl rfl (by decide) (by decide) (by decide) (by decide) (by decide)
                (by decide) (by decide)
    | 1, _ => exact rr_hart _ 1 _ _ _ rfl rfl rfl (by decide) (by decide) (by decide) (by decide) (by decide)
                (by decide))
  rw [obsLoad_mem] at ho0 ho1
  -- the reader's two loads
  obtain ⟨s0, s1, v0, v1, a0, a1, hord, hp1⟩ := (hQ 1 : QRR Mm 0x2000 0x1000 _)
  rcases prefix2 hp1 with he | he | he <;> rw [he] at ho0 ho1 <;> simp [loadVals] at ho0 ho1
  subst ho0 ho1
  have hl0 : (MLab.load 0x2000 s0 1 a0, none) ∈ r.trace 1 := memEv_sub (by rw [he]; simp)
  have hl1 : (MLab.load 0x1000 s1 0 a1, none) ∈ r.trace 1 := memEv_sub (by rw [he]; simp)
  -- the writer's stores
  obtain ⟨tx, ty, b1, c1, b2, c2, hxy, hp0⟩ := (hQ 0 : QWW 0x1000 0x2000 _)
  have hw0 : ∀ a w asrc vsrc s, (MLab.store a w asrc vsrc, some s) ∈ memEv (r.trace 0) →
      w = 1 ∧ ((a = 0x1000 ∧ s = tx) ∨ (a = 0x2000 ∧ s = ty)) := by
    intro a w asrc vsrc s hs
    have := hp0.subset hs
    simp at this
    rcases this with ⟨⟨rfl, rfl, _, _⟩, rfl⟩ | ⟨⟨rfl, rfl, _, _⟩, rfl⟩
    · exact ⟨rfl, .inl ⟨rfl, rfl⟩⟩
    · exact ⟨rfl, .inr ⟨rfl, rfl⟩⟩
  have hnost : ∀ (j : Nat) a w asrc vsrc s, (MLab.store a w asrc vsrc, some s) ∈ memEv (r.trace j) → j = 0 := by
    intro j a w asrc vsrc s hs
    match j, hs with
    | 0, _ => rfl
    | 1, hs =>
      have := hp1.subset hs
      simp at this
    | n + 2, hs =>
      have h0 : memEv (r.trace (n + 2)) = [] := hQ (n + 2)
      rw [h0] at hs; cases hs
  -- `ld Y` of 1 reads `st Y @ty`: `s0 = ty`
  obtain ⟨j, _, _, hj⟩ := read_src hR hW rfl hl0 (by decide)
  obtain rfl := hnost j _ _ _ _ _ hj
  obtain ⟨_, ⟨hxa, _⟩ | ⟨_, hs0⟩⟩ := hw0 _ _ _ _ _ hj
  · exact absurd hxa (by decide)
  subst hs0
  -- the writer's first store is in its trace, as is the second
  have hx0 : (MLab.store 0x1000 1 b1 c1, some tx) ∈ memEv (r.trace 0) := by
    rcases prefix2 hp0 with he0 | he0 | he0
    · rw [he0] at hj; cases hj
    · rw [he0] at hj; simp at hj
    · rw [he0]; simp
  obtain ⟨_, htx, htx0, hMx⟩ := hS 0 _ _ _ _ _ (memEv_sub hx0)
  cases htx
  -- `ld X` of 0: from the image (`s1 = 0`), since every message holds 1
  cases s1 with
  | zero =>
    apply hord
    exact writesIn_of (k := tx - 1) hMx rfl (by omega) (by omega)
  | succ k =>
    obtain ⟨m, hk, hpa, hmv⟩ := memv_succ (hR 1 _ _ _ _ _ hl1)
    obtain ⟨asrc, vsrc, hmw⟩ := hW k m hk
    rw [hnost _ _ _ _ _ _ hmw] at hmw
    have := (hw0 _ _ _ _ _ hmw).1
    rw [hmv] at this
    cases this

end Weak.Mini.Logic
