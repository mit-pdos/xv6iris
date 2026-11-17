/-
Weak/Mini: **hart 1 of `loopP` alternates flag and data loads — on the machine and in the reference** (mini plan
rev 4 §2 L6; the helper facts behind the headline `mini_inf_mpLoop`, Head.lean; the full stack's counterparts are
`Weak/Prom/InfLoopMach.lean` `alt_run` and `Weak/Prom/InfLoop.lean` `par1`).

* MACHINE (`mini_alt_loop`): in every valid run of `loopP`, hart 1's memory entries are loads, the `n`-th at the flag
  `0x2000` for even `n` and at the data `0x1000` for odd `n` (`QA`).  Proved in MiniLogic: a Löb induction at the
  loop head (as `h1_loop`, LitLoop.lean) carrying "the number of memory entries so far is even".
* REFERENCE (`loop1_ev`, `loop0_noLd`): in every candidate run of `loopP`, hart 1's event `i` is a load of the flag
  (`i % 3 = 0`), the `fence r,r` (`i % 3 = 1`) or a load of the data (`i % 3 = 2`); hart 0 has no load.  By
  induction on the number of steps (the closed form of the loop).
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Mini.LitLoop
import Weak.Mini.PfxMain

namespace Weak.Mini.Logic

open Weak.Mini Weak.Mini.Mach
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode

/-! ## 1. The machine: hart 1's memory entries alternate -/

/-- The address of hart 1's `n`-th memory entry: the flag for even `n`, the data for odd `n`. -/
def altA (n : Nat) : Nat := if n % 2 = 0 then 0x2000 else 0x1000

/-- Every memory entry is a load, the `n`-th at `altA n`. -/
def QA (ev : Trace) : Prop := ∀ n e, ev[n]? = some e → ∃ t v asr, e = (MLab.load (altA n) t v asr, none)

theorem QA_snoc {ev : Trace} (h : QA ev) {a t v : Nat} {asr : List MSrc} (ha : a = altA ev.length) :
    QA (ev ++ [(.load a t v asr, none)]) := by
  unfold QA at h ⊢
  intro n e he
  by_cases hn : n < ev.length
  · rw [List.getElem?_append_left hn] at he; exact h n e he
  · have hl := (List.getElem?_eq_some_iff.1 he).1
    simp only [List.length_append, List.length_singleton] at hl
    have hn' : n = ev.length := by omega
    subst hn'
    rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self] at he
    simp only [List.getElem?_cons_zero, Option.some.injEq] at he
    exact ⟨t, v, asr, by rw [← he, ha]⟩

theorem memEv_qTr_len (τ : Trace) (labs : List MLab) (h : ∀ l ∈ labs, isMem l = false) :
    (memEv (qTr τ labs)).length = (memEv τ).length := by rw [memEv_qTr τ labs h]

section hart

variable {hlc : HasLC} {GF : BundledGFunctors} [GhostVarG GF HSt] [InvGS_gen hlc GF]

/-- **HART 1 ALTERNATES**: `lw; fence r,r; lw; beq` keeps `QA` (Löb at `pc = 0`, an even number of entries so far). -/
theorem h1alt_loop (M : List MMsg) (γ : GName) :
    ⊢@{IProp GF} ∀ (f : MFront) (ws : Mach.MSt) (τ : Trace), hartSt γ ws τ -∗ ⌜h1S f⌝ -∗
      ⌜(memEv τ).length % 2 = 0⌝ -∗
        wpH γ ⟨loopP, M, 1⟩ (fun τ => QA (memEv τ)) f (fun _ => iprop(⌜True⌝)) := by
  iloeb as IH
  iintro %f %ws %τ Hst %hs %hev
  obtain ⟨hpc, hq, h12, h13⟩ := hs
  have hay : (f.rd 13 + 0) % two64 = 0x2000 := by rw [h13]; decide
  -- `lw x10,0(x13)`
  iapply (wp_load hq (by rw [hpc]; rfl) (by rw [hay]; decide) (qstable_mem _))
  iframe Hst
  inext
  iintro %s0 %v0 %_ %_ %hQ
  isplitr
  · ipureintro
    rw [memEv_mem _ _ _ rfl]
    exact QA_snoc hQ (by rw [hay, altA, if_pos hev])
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
  iintro %s1 %v1 %_ %_ %hQ
  isplitr
  · ipureintro
    rw [memEv_mem _ _ _ rfl]
    refine QA_snoc hQ ?_
    rw [memEv_qTr_len _ _ (by simp [isMem]), memEv_qTr_len _ _ (regWL_quiet _ _), memEv_mem _ _ _ rfl, hax,
      List.length_append, List.length_singleton, altA, if_neg (by omega)]
  iintro Hst
  -- `beq x0,x0,0`: back to the loop head
  iapply (wp_br (f := MFront.mk (f.pc + 1 + 1 + 1) (MFront.wr (MFront.mk (f.pc + 1 + 1)
      (f.wr 10 (if true = true then sext loopP.sz v0 else v0)) []) 11
        (if true = true then sext loopP.sz v1 else v1)) [])
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
    rw [memEv_qTr_len _ _ (by simp [isMem]), memEv_qTr_len _ _ (regWL_quiet _ _), memEv_mem _ _ _ rfl,
      List.length_append, memEv_qTr_len _ _ (by simp [isMem]), memEv_qTr_len _ _ (regWL_quiet _ _),
      memEv_mem _ _ _ rfl, List.length_append]
    simp only [List.length_singleton]
    omega

theorem h1alt_wp (M : List MMsg) (f0 : MFront) (hs : h1S f0) :
    ⊢@{IProp GF} wp loopP M 1 (fun τ => QA (memEv τ)) f0 (fun _ => iprop(⌜True⌝)) := by
  unfold wp
  iintro %γ Hst
  ihave H := h1alt_loop (GF := GF) M γ
  iapply H $$ %f0 %msInit %([] : Trace) Hst %hs %rfl

end hart

/-- Ψ: `Q0` for hart 0 (LitLoop.lean), `QA` for hart 1, nothing for other indices. -/
def QsAlt : Nat → Trace → Prop
  | 0 => Q0
  | 1 => QA
  | _ => fun ev => ev = []

theorem QsAlt_nil : ∀ h, QsAlt h []
  | 0 => fun _ he => by cases he
  | 1 => show QA [] from fun _ _ he => by simp at he
  | _ + 2 => rfl

/-- **On MiniMach, hart 1 of `loopP` alternates flag and data loads** (every valid run). -/
theorem mini_alt_loop {Mm : List MMsg} {r : MRun} (hv : miniValidRun loopP Mm r) : QA (memEv (r.trace 1)) := by
  obtain ⟨hQ, _⟩ := adeqMem hv QsAlt QsAlt_nil (fun h hs hh _ => by
    obtain ⟨hlt, rfl⟩ := mInit_get hh
    match h, hlt with
    | 0, _ => exact h0_wp _ _ ⟨rfl, rfl, by decide, by decide, by decide⟩
    | 1, _ => exact h1alt_wp _ _ ⟨rfl, rfl, by decide, by decide⟩)
  exact hQ 1

/-! ## 2. The reference: the closed form of `loopP`'s harts -/

open Weak.Mini.Cmp (wr_same rd_wr)

/-- Hart 1's event `i`: a load of the flag (`i % 3 = 0`), the `fence r,r` (`1`), a load of the data (`2`). -/
def Ok1 (i : Nat) (e : MEv) : Prop :=
  (i % 3 = 0 → e.kind = .ld ∧ e.pa = 0x2000) ∧ (i % 3 = 1 → e.kind = .fence fRRm) ∧
    (i % 3 = 2 → e.kind = .ld ∧ e.pa = 0x1000)

/-- Hart 1 after `k` steps: at `pc = k % 4`, `3 (k / 4) + min (k % 4) 3` events, each `Ok1`, `x12`/`x13` intact. -/
def J1 (k : Nat) (s : Weak.Mini.MSt) : Prop :=
  s.pc = k % 4 ∧ s.evs.length = 3 * (k / 4) + min (k % 4) 3 ∧ (s.rd 12).1 = 0x1000 ∧ (s.rd 13).1 = 0x2000 ∧
    ∀ i (hi : i < s.evs.length), Ok1 i s.evs[i]

theorem ok_snoc {l : List MEv} {e : MEv} (hl : ∀ i (hi : i < l.length), Ok1 i l[i]) (he : Ok1 l.length e) :
    ∀ i (hi : i < (l ++ [e]).length), Ok1 i (l ++ [e])[i] := by
  intro i hi
  simp only [List.length_append, List.length_singleton] at hi
  by_cases h : i < l.length
  · rw [List.getElem_append_left h]; exact hl i h
  · have : i = l.length := by omega
    subst this
    simp only [List.getElem_append_right (Nat.le_refl _), Nat.sub_self, List.getElem_cons_zero]
    exact he

theorem exec_ld (sz h : Nat) (V : EvId → Nat) (s : Weak.Mini.MSt) (sgn : Bool) (rd rs1 off : Nat) :
    (exec sz h V s (.load sgn rd rs1 off)).pc = s.pc + 1 ∧
    (exec sz h V s (.load sgn rd rs1 off)).evs = s.evs ++ [⟨.ld, s.ii, MAlu.add.eval (s.rd rs1).1 (off % two64),
      V (h, s.evs.length) % 2 ^ (8 * sz), (s.rd rs1).2, [], s.ctl⟩] ∧
    ∀ r, r ≠ rd → (exec sz h V s (.load sgn rd rs1 off)).rd r = s.rd r := by
  rcases h1 : s.rd rs1 with ⟨v1, t1⟩
  refine ⟨by simp [exec, h1, MSt.adv, (wr_same _ _ _).1, MSt.emit],
    by simp [exec, h1, MSt.adv, (wr_same _ _ _).2.1, MSt.emit], fun r hr => ?_⟩
  simp only [exec, h1]
  show ((MSt.emit s _).wr rd _).rd r = _
  rw [rd_wr, if_neg (by omega)]; rfl

theorem exec_fence (sz h : Nat) (V : EvId → Nat) (s : Weak.Mini.MSt) (f : MFence) :
    (exec sz h V s (.fence f)).pc = s.pc + 1 ∧
    (exec sz h V s (.fence f)).evs = s.evs ++ [⟨.fence f, s.ii, 0, 0, [], [], []⟩] ∧
    ∀ r, (exec sz h V s (.fence f)).rd r = s.rd r :=
  ⟨rfl, rfl, fun _ => rfl⟩

theorem J1_step (V : EvId → Nat) {k : Nat} {s : Weak.Mini.MSt} (hJ : J1 k s) : J1 (k + 1) (mstep loopP V 1 s) := by
  obtain ⟨hpc, hlen, h12, h13, hok⟩ := hJ
  have hc : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 := by omega
  rcases hc with hc | hc | hc | hc
  · -- `lw x10,0(x13)`
    have hi : (loopP.prog 1)[s.pc]? = some (.load true 10 13 0) := by rw [hpc, hc]; rfl
    unfold mstep; rw [hi]
    obtain ⟨hp, he, hr⟩ := exec_ld loopP.sz 1 V s true 10 13 0
    refine ⟨by rw [hp, hpc]; omega, by rw [he, List.length_append, hlen]; simp; omega,
      by rw [hr 12 (by decide)]; exact h12, by rw [hr 13 (by decide)]; exact h13, ?_⟩
    rw [he]
    refine ok_snoc hok ⟨fun _ => ⟨rfl, by rw [h13]; rfl⟩, fun h => by omega, fun h => by omega⟩
  · -- `fence r,r`
    have hi : (loopP.prog 1)[s.pc]? = some (.fence fRRm) := by rw [hpc, hc]; rfl
    unfold mstep; rw [hi]
    obtain ⟨hp, he, hr⟩ := exec_fence loopP.sz 1 V s fRRm
    refine ⟨by rw [hp, hpc]; omega, by rw [he, List.length_append, hlen]; simp; omega,
      by rw [hr 12]; exact h12, by rw [hr 13]; exact h13, ?_⟩
    rw [he]
    refine ok_snoc hok ⟨fun h => by omega, fun _ => rfl, fun h => by omega⟩
  · -- `lw x11,0(x12)`
    have hi : (loopP.prog 1)[s.pc]? = some (.load true 11 12 0) := by rw [hpc, hc]; rfl
    unfold mstep; rw [hi]
    obtain ⟨hp, he, hr⟩ := exec_ld loopP.sz 1 V s true 11 12 0
    refine ⟨by rw [hp, hpc]; omega, by rw [he, List.length_append, hlen]; simp; omega,
      by rw [hr 12 (by decide)]; exact h12, by rw [hr 13 (by decide)]; exact h13, ?_⟩
    rw [he]
    refine ok_snoc hok ⟨fun h => by omega, fun h => by omega, fun _ => ⟨rfl, by rw [h12]; rfl⟩⟩
  · -- `beq x0,x0,0`
    have hi : (loopP.prog 1)[s.pc]? = some (.br .eq 0 0 0) := by rw [hpc, hc]; rfl
    unfold mstep; rw [hi]
    refine ⟨by simp [exec, MSt.rd, MBrC.eval]; omega, by simp [exec, MSt.rd, hlen]; omega, h12, h13, ?_⟩
    simpa [exec, MSt.rd] using hok

theorem J1_all (V : EvId → Nat) : ∀ k, J1 k (mrun loopP V 1 k)
  | 0 => ⟨rfl, rfl, rfl, rfl, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | k + 1 => J1_step V (J1_all V k)

/-- Hart 0 never loads. -/
theorem noLd0 (V : EvId → Nat) : ∀ k, ∀ e ∈ (mrun loopP V 0 k).evs, e.kind ≠ .ld
  | 0 => fun e he => by simp [mrun, MProg.init] at he
  | k + 1 => by
    intro e he
    have ih := noLd0 V k
    change e ∈ (mstep loopP V 0 (mrun loopP V 0 k)).evs at he
    generalize mrun loopP V 0 k = s at ih he
    unfold mstep at he
    split at he
    · rename_i i hi
      have hmem := List.mem_of_getElem? hi
      simp only [MProg.prog, loopP, List.getElem?_cons_zero, Option.getD_some, List.mem_cons, List.not_mem_nil,
        or_false] at hmem
      rcases hmem with rfl | rfl | rfl | rfl
      · rcases h1 : s.rd 12 with ⟨v1, t1⟩; rcases h2 : s.rd 6 with ⟨v2, t2⟩
        simp only [exec, h1, h2, MSt.adv, MSt.emit, List.mem_append, List.mem_singleton] at he
        rcases he with he | rfl
        · exact ih e he
        · simp
      · simp only [exec, MSt.adv, MSt.emit, List.mem_append, List.mem_singleton] at he
        rcases he with he | rfl
        · exact ih e he
        · simp
      · rcases h1 : s.rd 13 with ⟨v1, t1⟩; rcases h2 : s.rd 6 with ⟨v2, t2⟩
        simp only [exec, h1, h2, MSt.adv, MSt.emit, List.mem_append, List.mem_singleton] at he
        rcases he with he | rfl
        · exact ih e he
        · simp
      · simp only [exec, MSt.rd] at he
        exact ih e he
    · exact ih e he

variable {X : MExec}

/-- In every candidate execution of `loopP`, hart 1's existing event `i` is `Ok1 i`. -/
theorem x_ok1 {i : Nat} (hi : (X.evs loopP).has (1, i)) : Ok1 i ((X.evs loopP).ev (1, i)) := by
  obtain ⟨_, k, hk⟩ := hi
  rw [Pfx.xev (k := k) hk]
  exact (J1_all X.V k).2.2.2.2 i hk

/-- In every candidate execution of `loopP`, hart 0's events are not loads. -/
theorem x_noLd0 {i : Nat} (hi : (X.evs loopP).has (0, i)) : ¬ (X.evs loopP).isLd (0, i) := by
  obtain ⟨_, k, hk⟩ := hi
  unfold MEvs.isLd
  rw [Pfx.xev (k := k) hk]
  exact noLd0 X.V k _ (List.getElem_mem hk)

end Weak.Mini.Logic
