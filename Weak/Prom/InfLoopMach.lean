/-
Weak/Prom: **InfLoop part 4 — hart 1's memory entries on the loop machine alternate flag / data** (owner request
2026-11-13 "write the end-to-end infinite-execution theorem for tLoop").

Pure, from the front end (as CoreLitLoop.lean's `loop_noDone`): in every valid `xStep xsLoop` run of `tLoop`, the
`k`-th memory entry (`memEv`) of hart 1 is a plain 4-byte load at `Y` (`k` even) or at `X` (`k` odd), with no
timestamp (`alt_run`).  Consequently the `k`-th load row of the trace (`machRow`) is the answered bytes of the
`k`-th memory entry (`machRow_at`).  This is what turns `lit_mpLoop`'s `qLoop` (stated over adjacent memory
entries and their addresses) into a statement about load VALUES at given load indices.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.InfLoopBridge

namespace Weak.Prom.InfLoop

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.PF Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Ref (Instr Test two64 brEval sext)
open Weak.Prom.Cmp (machRow)
open Weak.Prom.OA (XI xNext xStep xOf)
open Weak.Prom.PF.Loop (tLoop xsLoop pL0 pL1 bL0 bL1 imgLoop)
open Weak.Prom.Ref.Lit (X Y)
open PLabel

/-! ## 1. The trace shape -/

/-- A plain 4-byte load at `a`, answered `tvs`, no timestamp. -/
def isLdE (a : Int) (e : PEv) : Prop := ∃ tvs r, e = (LLoad false false a tvs (srcR r), none) ∧ tvs.length = 4

/-- Hart 1's memory entries alternate: the `k`-th is a load at `Y` (`k` even) or at `X` (`k` odd). -/
def AltT (τ : Trace) : Prop :=
  ∀ k e, (memEv τ)[k]? = some e → isLdE (if k % 2 = 0 then (Y : Int) else (X : Int)) e

/-- The loop-machine invariant of hart 1 (state and trace so far). -/
structure MInv (s : LP) (τ : Trace) : Prop where
  prog : s.prog = bL1
  r12 : s.rd 12 = X
  r13 : s.rd 13 = Y
  pc : s.pc < 4
  q : ∀ l ∈ s.q, quietL l = true
  par : (memEv τ).length % 2 = if s.pc = 1 ∨ s.pc = 2 then 1 else 0
  alt : AltT τ

/-- A non-write label carries no timestamp. -/
theorem ots_none {img : Image} {M : List PMsg} {i : Nat} {prom : GSet Nat} {ws : PState} {l : PLabel}
    {ots : Option Nat} {ws' : PState} {prom' : GSet Nat} (h : memStep img M i prom ws l ots ws' prom')
    (hl : labelWrite l = none) : ots = none := by
  cases h <;> first | rfl | simp [labelWrite] at hl

theorem quiet_noWrite {l : PLabel} (hq : quietL l = true) : labelWrite l = none := by
  cases l <;> simp_all [quietL, labelWrite]

theorem alt_snoc_quiet {τ : Trace} {l : PLabel} (hq : quietL l = true) (h : AltT τ) : AltT (τ ++ [(l, none)]) := by
  intro k e hk; rw [memEv_quiet _ _ hq] at hk; exact h k e hk

theorem alt_snoc_ld {τ : Trace} {a : Int} {tvs : List (Nat × BitVec 8)} {r : Nat} (h : AltT τ) (hl : tvs.length = 4)
    (ha : a = if (memEv τ).length % 2 = 0 then (Y : Int) else (X : Int)) :
    AltT (τ ++ [(LLoad false false a tvs (srcR r), none)]) := by
  intro k e hk
  rw [memEv_snoc _ _ (by simp [keepE, quietL])] at hk
  have hlt : k < (memEv τ).length + 1 := by have := (List.getElem?_eq_some_iff.1 hk).1; simpa using this
  by_cases hkl : k < (memEv τ).length
  · rw [List.getElem?_append_left hkl] at hk; exact h k e hk
  · have hk' : k = (memEv τ).length := by omega
    subst hk'
    rw [List.getElem?_append_right (by omega), Nat.sub_self] at hk
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
    subst hk
    exact ⟨tvs, r, by rw [ha], hl⟩

theorem len_snoc_ld (τ : Trace) (a : Int) (tvs : List (Nat × BitVec 8)) (r : Nat) :
    (memEv (τ ++ [(LLoad false false a tvs (srcR r), none)])).length = (memEv τ).length + 1 := by
  rw [memEv_snoc _ _ (by simp [keepE, quietL])]; simp

theorem rd_wr_ne (s : LP) {r r' : Nat} (hne : r ≠ r') (v : Nat) :
    ({ s with regs := s.wr r v, pc := s.pc + 1, q := regWL r [.DLdRes] ++ [LInstr] } : LP).rd r' = s.rd r' := by
  unfold LP.rd LP.wr
  split
  · rfl
  · split
    · rfl
    · simp [List.getElem?_set_ne hne]

theorem ldQ_quiet (r : Nat) : ∀ l ∈ regWL r [.DLdRes] ++ [LInstr], quietL l = true := by
  intro l hl
  unfold regWL at hl
  split at hl <;> simp at hl <;> rcases hl with rfl | rfl <;> rfl

theorem alY : aligned ((Y + 0) % two64) 4 = true := by decide
theorem alX : aligned ((X + 0) % two64) 4 = true := by decide
theorem caY : (((Y + 0) % two64 : Nat) : Int) = (Y : Int) := by decide
theorem caX : (((X + 0) % two64 : Nat) : Int) = (X : Int) := by decide

/-- **ONE LABEL of hart 1** keeps the invariant. -/
theorem minv_step {s s' : LP} {l : PLabel} {τ : Trace} {img : Image} {M : List PMsg} {i : Nat} {prom : GSet Nat}
    {ws : PState} {ots : Option Nat} {ws' : PState} {prom' : GSet Nat} (hx : xNext xsLoop s l = some s')
    (hm : memStep img M i prom ws l ots ws' prom') (hi : MInv s τ) : MInv s' (τ ++ [(l, ots)]) := by
  cases hq : s.q with
  | cons l0 rest =>
    rw [OA.xNext_q (s := s) (by rw [hq]; simp)] at hx
    obtain ⟨rfl, rfl⟩ := litNext_q hq hx
    have hql : quietL l = true := hi.q l (by rw [hq]; simp)
    rw [ots_none hm (quiet_noWrite hql)]
    exact ⟨hi.prog, hi.r12, hi.r13, hi.pc, fun l' hl' => hi.q l' (by rw [hq]; exact List.mem_cons_of_mem _ hl'),
      by rw [memEv_quiet _ _ hql]; exact hi.par, alt_snoc_quiet hql hi.alt⟩
  | nil =>
    have hX : xOf xsLoop s.prog = some pL1 := by rw [hi.prog]; exact Weak.Prom.PF.Loop.xOf_L1
    have hpar := hi.par
    rcases (by have := hi.pc; omega : s.pc = 0 ∨ s.pc = 1 ∨ s.pc = 2 ∨ s.pc = 3) with hc | hc | hc | hc <;>
      rw [hc] at hpar
    · -- lw a0, 0(a3)
      have hins : s.prog[s.pc]? = some (.load 4 true 10 13 0) := by rw [hi.prog, hc]; rfl
      rw [OA.xNext_plain hq (fun x hx' => by
        rw [hX, hc, Option.bind_some, show pL1[0]? = some (XI.i (.load 4 true 10 13 0)) from rfl] at hx'; cases hx'; rfl)] at hx
      have ha : aligned ((s.rd 13 + 0) % two64) 4 = true := by rw [hi.r13]; exact alY
      obtain ⟨tvs, rfl, rfl, hl⟩ := litNext_load hq hins ha hx
      rw [ots_none hm rfl]
      refine ⟨hi.prog, by rw [rd_wr_ne _ (by decide)]; exact hi.r12, by rw [rd_wr_ne _ (by decide)]; exact hi.r13,
        by simp [hc], ldQ_quiet 10, ?_, alt_snoc_ld hi.alt hl ?_⟩
      · rw [len_snoc_ld]; simp [hc] at hpar ⊢; omega
      · rw [hi.r13, caY]; simp at hpar; simp [hpar]
    · -- fence r,r
      have hins : s.prog[s.pc]? = some (.fence ⟨true, false, false, false, true, false, false, false⟩) := by
        rw [hi.prog, hc]; rfl
      rw [OA.xNext_plain hq (fun x hx' => by
        rw [hX, hc, Option.bind_some, show pL1[1]? = some (XI.i (.fence ⟨true, false, false, false, true, false, false, false⟩)) from rfl] at hx'; cases hx'; rfl)] at hx
      obtain ⟨rfl, rfl⟩ := litNext_fence hq hins hx
      rw [ots_none hm rfl]
      exact ⟨hi.prog, hi.r12, hi.r13, by simp [hc], by simp [quietL],
        by rw [memEv_quiet _ _ rfl]; simp [hc] at hpar ⊢; omega, alt_snoc_quiet rfl hi.alt⟩
    · -- lw a1, 0(a2)
      have hins : s.prog[s.pc]? = some (.load 4 true 11 12 0) := by rw [hi.prog, hc]; rfl
      rw [OA.xNext_plain hq (fun x hx' => by
        rw [hX, hc, Option.bind_some, show pL1[2]? = some (XI.i (.load 4 true 11 12 0)) from rfl] at hx'; cases hx'; rfl)] at hx
      have ha : aligned ((s.rd 12 + 0) % two64) 4 = true := by rw [hi.r12]; exact alX
      obtain ⟨tvs, rfl, rfl, hl⟩ := litNext_load hq hins ha hx
      rw [ots_none hm rfl]
      refine ⟨hi.prog, by rw [rd_wr_ne _ (by decide)]; exact hi.r12, by rw [rd_wr_ne _ (by decide)]; exact hi.r13,
        by simp [hc], ldQ_quiet 11, ?_, alt_snoc_ld hi.alt hl ?_⟩
      · rw [len_snoc_ld]; simp [hc] at hpar ⊢; omega
      · rw [hi.r12, caX]; simp at hpar; simp [hpar]
    · -- beq zero, zero, 0
      obtain ⟨rfl, rfl⟩ := OA.xNext_br hq hX (by rw [hc]; rfl) (by rw [hi.prog]; decide) hx
      rw [ots_none hm rfl]
      exact ⟨hi.prog, hi.r12, hi.r13, by simp [brEval], by simp [quietL],
        by rw [memEv_quiet _ _ rfl]; simp [brEval] at hpar ⊢; omega, alt_snoc_quiet rfl hi.alt⟩

theorem minv_solo {img : Image} {M : List PMsg} {i : Nat} :
    ∀ {x y : LP × PState × GSet Nat} {tr : Trace}, soloSteps (anyFab (xStep xsLoop)) img M i x tr y →
      ∀ τ, MInv x.1 τ → MInv y.1 (τ ++ tr) := by
  intro x y tr hs
  induction hs with
  | refl => intro τ h; simpa using h
  | step x l ots p' ws' prom' tr y hp hm _ ih =>
    intro τ hi
    obtain ⟨_, _, hp⟩ := hp
    have := ih _ (minv_step hp hm hi)
    simpa using this

/-- **HART 1's MEMORY ENTRIES ALTERNATE** in every valid loop-machine run of `tLoop`. -/
theorem alt_run {M : List PMsg} {run : PFRun LP Unit}
    (hv : PF.validRun (xStep xsLoop) imgLoop () (progs tLoop) M run) : AltT (run.trace 1) := by
  obtain ⟨ag, _, P0, _, hs⟩ := validRun_soloD hv.1 1 _ (progs_at tLoop (by decide : 1 < tLoop.harts.length))
  have h0 : MInv (LP.mk (tLoop.prog 1) 0
      ((List.range 32).map (fun r => ((((tLoop.regs0[1]?).getD []).lookup r).getD 0) % two64)) []) [] :=
    ⟨rfl, by decide, by decide, by decide, (fun _ h => by cases h), by decide, (fun _ _ h => by simp [memEv] at h)⟩
  have := minv_solo hs [] h0
  exact this.alt

/-! ## 2. The load rows are the memory entries' answers -/

theorem filterMap_get {α β : Type} (f : α → Option β) :
    ∀ (l : List α), (∀ a ∈ l, (f a).isSome = true) → ∀ (k : Nat), (l.filterMap f)[k]? = (l[k]?).bind f
  | [], _, k => by simp
  | a :: l, hl, k => by
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 (hl a (by simp))
    rw [List.filterMap_cons, hb]
    cases k with
    | zero => simp [hb]
    | succ k =>
      simp only [List.getElem?_cons_succ]
      exact filterMap_get f l (fun a' ha' => hl a' (List.mem_cons_of_mem _ ha')) k

/-- Under the alternation, the `k`-th row of the trace is the answered bytes of the `k`-th memory entry. -/
theorem machRow_at {τ : Trace} (halt : AltT τ) {k : Nat} {r : List Nat} (hr : (machRow τ)[k]? = some r) :
    ∃ tvs src, (memEv τ)[k]? = some (LLoad false false (if k % 2 = 0 then (Y : Int) else (X : Int)) tvs src, none) ∧
      tvs.length = 4 ∧ tvs.map (fun tv => tv.2.toNat) = r := by
  unfold machRow at hr
  rw [List.getElem?_map, ← loadsOf_memEv] at hr
  unfold loadsOf at hr
  rw [filterMap_get _ _ (fun e he => by
    obtain ⟨k', hk', hk''⟩ := List.getElem_of_mem he
    obtain ⟨tvs, r', he', _⟩ := halt k' e (List.getElem?_eq_some_iff.2 ⟨hk', hk''⟩)
    subst he'; rfl)] at hr
  cases he : (memEv τ)[k]? with
  | none => rw [he] at hr; cases hr
  | some e =>
    obtain ⟨tvs, r', rfl, hl⟩ := halt k e he
    rw [he] at hr
    simp only [Option.bind_some, loadLikeTvs, Option.map_some, Option.some.injEq] at hr
    exact ⟨tvs, srcR r', rfl, hl, hr⟩

end Weak.Prom.InfLoop
