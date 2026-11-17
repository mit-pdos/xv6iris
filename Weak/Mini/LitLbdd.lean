/-
Weak/Mini: **`mini_lit_lbdd` — LB+data+data is FORBIDDEN on MiniMach, proved in MiniLogic** (mini plan rev 4 §2 L6:
the machine-level LEMMA behind the headline `mini_forbidden lbdd`; the full stack's template is
`Weak/Prom/CoreLit.lean` `lit_lbdd`, plan rev 7 §2 "The LB trio").

The program `lbddP` is RefTests.lean `lbdd` (:80) as an F program (`= Weak.Mini.lbddM` of EqRefWit.lean, by
`rfl`): hart 0 `lw x5,0(x6); sw x5,0(x8)` with `x6 = 0x1000`, `x8 = 0x2000`; hart 1 the same with the addresses
swapped; image 0; size 4.
* Each hart proves `QLB x y` of its memory entries: they are a prefix of `ld x @t; st y @ts` with `t < ts`
  (LOAD (X4) `regv x5 ≥ t` (no forwarding: the hart has not stored), REGW (X5), EXT of the store `regv x5 ≤ pv < ts`).
* The contradiction from `adeqMem`'s exports only: a load of 1 reads the OTHER hart's store (`read_src`; the
  image is 0, the hart's own store is to the other word), so `t₀ = ts₁ > t₁ = ts₀ > t₀`.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Mini.LitBase

namespace Weak.Mini.Logic

open Weak.Mini Weak.Mini.Mach
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode

/-- RefTests.lean `lbdd` (:80) as an F program. -/
def lbddP : MProg where
  harts := [[.load true 5 6 0, .store 5 8 0], [.load true 5 6 0, .store 5 8 0]]
  regs0 := [[(6, 0x1000), (8, 0x2000)], [(6, 0x2000), (8, 0x1000)]]
  img := []
  sz := 4

/-- The LB hart's memory entries: a prefix of `ld x @t; st y @ts` with `t < ts`. -/
def QLB (x y : Nat) (ev : Trace) : Prop :=
  ∃ t v w ts asr as' vs', t < ts ∧ ev <+: [(.load x t v asr, none), (.store y w as' vs', some ts)]

section hart

variable {hlc : HasLC} {GF : BundledGFunctors} [GhostVarG GF HSt] [InvGS_gen hlc GF]

/-- **The LB+data+data hart in the logic**: `lw x5,0(x6); sw x5,0(x8)` proves `QLB x y` at every step. -/
theorem lbdd_hart (M : List MMsg) (h x y : Nat) (f0 : MFront)
    (hprog : lbddP.prog h = [.load true 5 6 0, .store 5 8 0]) (hpc : f0.pc = 0) (hq : f0.q = [])
    (hx : f0.rd 6 = x) (hy : f0.rd 8 = y) (hxa : x % 4 = 0) (hya : y % 4 = 0) (hxl : x < two64)
    (hyl : y < two64) :
    ⊢@{IProp GF} wp lbddP M h (fun τ => QLB x y (memEv τ)) f0 (fun _ => iprop(⌜True⌝)) := by
  unfold wp
  iintro %γ Hst
  have hax : (f0.rd 6 + 0) % two64 = x := by rw [hx, Nat.add_zero, Nat.mod_eq_of_lt hxl]
  iapply (wp_load hq (by rw [hprog, hpc]; rfl) (by rw [hax]; exact hxa) (qstable_mem _))
  iframe Hst
  inext
  iintro %t %v %_ %_ %_
  isplitr
  · ipureintro
    rw [memEv_mem _ _ _ rfl, hax]
    exact ⟨t, v, 0, t + 1, _, [], [], by omega, ⟨[(.store y 0 [] [], some (t + 1))], rfl⟩⟩
  iintro Hst
  have hy1 : (MFront.mk (f0.pc + 1) (f0.wr 5 (if true = true then sext lbddP.sz v else v)) []).rd 8 = y := by
    rw [rd_wr_ne (by decide), hy]
  have hay : ((MFront.mk (f0.pc + 1) (f0.wr 5 (if true = true then sext lbddP.sz v else v)) []).rd 8 + 0) % two64
      = y := by rw [hy1, Nat.add_zero, Nat.mod_eq_of_lt hyl]
  iapply (wp_store rfl (by rw [hprog, hpc]; rfl) (by rw [hay]; exact hya) (qstable_mem _))
  iframe Hst
  inext
  iintro %ts %_ %_ %hext %_
  isplitr
  · ipureintro
    have hlt : t < ts := by
      have h1 := (ld_post (ws := msInit) (va := srcsView msInit (srcR 6))
        (vpre := ldPre msInit (srcsView msInit (srcR 6))) (a := (f0.rd 6 + 0) % two64) (t := t) (rd := 5)
        rfl (by decide)).1
      rw [srcsView_reg _ (by decide : (5 : Nat) ≠ 0)] at hext
      have h2 := (stPre_ge (qWs (loadPost msInit (srcsView msInit (srcR 6)) (ldPre msInit (srcsView msInit (srcR 6)))
        ((f0.rd 6 + 0) % two64) t) (regWL 5 [.ldres] ++ [.instr]))
        (srcsView (qWs (loadPost msInit (srcsView msInit (srcR 6)) (ldPre msInit (srcsView msInit (srcR 6)))
          ((f0.rd 6 + 0) % two64) t) (regWL 5 [.ldres] ++ [.instr])) (srcR 8))
        ((qWs (loadPost msInit (srcsView msInit (srcR 6)) (ldPre msInit (srcsView msInit (srcR 6)))
          ((f0.rd 6 + 0) % two64) t) (regWL 5 [.ldres] ++ [.instr])).regv 5)).1
      omega
    rw [memEv_mem _ _ _ rfl, memEv_qTr _ _ (regWL_quiet _ _), memEv_mem _ _ _ rfl, hax, hay]
    exact ⟨t, v, _, ts, _, _, _, hlt, List.prefix_refl _⟩
  iintro Hst
  iapply (wp_done (f := MFront.mk (f0.pc + 1 + 1) _ []) rfl (by rw [hprog, hpc]; rfl))
  iframe Hst

end hart

/-- Ψ of lbdd: `QLB` at `0x1000`/`0x2000` for hart 0, swapped for hart 1, nothing for other indices. -/
def QsLB : Nat → Trace → Prop
  | 0 => QLB 0x1000 0x2000
  | 1 => QLB 0x2000 0x1000
  | _ => fun ev => ev = []

theorem QLB_nil (x y : Nat) : QLB x y [] := ⟨0, 0, 0, 1, [], [], [], by omega, List.nil_prefix⟩

theorem QsLB_nil : ∀ h, QsLB h []
  | 0 => QLB_nil _ _
  | 1 => QLB_nil _ _
  | _ + 2 => rfl

/-- What a hart's `QLB` gives, when its first load returned `1`. -/
theorem QLB_out {x y : Nat} {ev : Trace} (hQ : QLB x y ev) (hobs : (loadVals ev)[0]? = some 1) :
    ∃ t ts asr, t < ts ∧ (.load x t 1 asr, none) ∈ ev ∧
      ∀ a w as' vs' s, (.store a w as' vs', some s) ∈ ev → a = y ∧ s = ts := by
  obtain ⟨t, v, w, ts, asr, as', vs', hlt, hp⟩ := hQ
  have hst : ∀ a w' as'' vs'' s, (.store a w' as'' vs'', some s) ∈ ev → a = y ∧ s = ts := by
    intro a w' as'' vs'' s he
    have := hp.subset he
    simp at this
    exact ⟨this.1.1, this.2⟩
  rcases prefix2 hp with rfl | rfl | rfl
  · simp [loadVals] at hobs
  · simp [loadVals] at hobs
    subst hobs
    exact ⟨t, ts, asr, hlt, by simp, hst⟩
  · simp [loadVals] at hobs
    subst hobs
    exact ⟨t, ts, asr, hlt, by simp, hst⟩

/-- **LB+data+data is FORBIDDEN on MiniMach** (machine-level lemma, proved in MiniLogic): over every final memory
and every valid run of `lbddP`, not both harts' first loads return 1. -/
theorem mini_lit_lbdd : ∀ (Mm : List MMsg) (r : MRun), miniValidRun lbddP Mm r →
    ¬ (r.obsLoad 0 0 = some 1 ∧ r.obsLoad 1 0 = some 1) := by
  intro Mm r hv ⟨ho0, ho1⟩
  obtain ⟨hQ, hW, hR, _⟩ := adeqMem hv QsLB QsLB_nil (fun h hs hh _ => by
    obtain ⟨hlt, rfl⟩ := mInit_get hh
    match h, hlt with
    | 0, _ => exact lbdd_hart _ 0 _ _ _ rfl rfl rfl (by decide) (by decide) (by decide) (by decide) (by decide)
                (by decide)
    | 1, _ => exact lbdd_hart _ 1 _ _ _ rfl rfl rfl (by decide) (by decide) (by decide) (by decide) (by decide)
                (by decide))
  rw [obsLoad_mem] at ho0 ho1
  obtain ⟨t0, ts0, as0, hlt0, hl0, hs0⟩ := QLB_out (hQ 0) ho0
  obtain ⟨t1, ts1, as1, hlt1, hl1, hs1⟩ := QLB_out (hQ 1) ho1
  -- each load of 1 reads the other hart's store
  have himg : ∀ a, lbddP.img0 a % wordW lbddP = 0 := fun _ => rfl
  have hother : ∀ {x : Nat} {t : Nat} (j : Nat) {asrc vsrc : List MSrc},
      (.store x 1 asrc vsrc, some t) ∈ memEv (r.trace j) →
      (j = 0 ∧ x = 0x2000 ∧ t = ts0) ∨ (j = 1 ∧ x = 0x1000 ∧ t = ts1) := by
    intro x t j asrc vsrc he
    match j, he with
    | 0, he => exact .inl ⟨rfl, hs0 _ _ _ _ _ he⟩
    | 1, he => exact .inr ⟨rfl, hs1 _ _ _ _ _ he⟩
    | n + 2, he =>
      have h0 : memEv (r.trace (n + 2)) = [] := hQ (n + 2)
      rw [h0] at he; cases he
  obtain ⟨j0, _, _, he0⟩ := read_src hR hW (himg _) (memEv_sub hl0) (by decide)
  obtain ⟨j1, _, _, he1⟩ := read_src hR hW (himg _) (memEv_sub hl1) (by decide)
  rcases hother j0 he0 with ⟨_, hx, _⟩ | ⟨_, _, e0⟩
  · exact absurd hx (by decide)
  rcases hother j1 he1 with ⟨_, _, e1⟩ | ⟨_, hx, _⟩
  · omega
  · exact absurd hx (by decide)

end Weak.Mini.Logic
