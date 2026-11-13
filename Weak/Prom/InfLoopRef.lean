/-
Weak/Prom: **InfLoop part 2 — what the REFERENCE says about `tLoop`'s executions, from the program alone**
(owner request 2026-11-13 "write the end-to-end infinite-execution theorem for tLoop").

For every `E` with `infExec tLoop E` (PfxDefs.lean), by induction over the steps `E.st h k` (`conforms`: each
state is an `LStep` of `tLoop`'s program from the previous one):
* `inv0_all`, `inv1_all` — the state invariants: the address registers keep their initial constants, `pc ≤ 4`,
  every event of hart 0 is a fence or a 4-byte store at `X`/`Y`; every event of hart 1 is a fence or a 4-byte load,
  at `Y` when an EVEN number of loads precede it on the hart and at `X` otherwise.
* `pc_pat` — the path: before it halts (a not-taken `beq zero,zero,0` would halt it), hart `h` is at `pc = j % 4`
  after `j` steps.
* `memFacts` (every memory operation is a 4-byte access at `X` or `Y`) and hence `singleSizeI_loop` (NA-6 holds for
  every execution of `tLoop`), `noLoad0` (hart 0 has no loads), `par1` (hart 1's load at `Y` ↔ an even number of
  loads before it).
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.InfLoopCmp
import Weak.Prom.CoreLitLoop

noncomputable section

namespace Weak.Prom.InfLoop

open Classical
open Weak.Prom.Ref
open Weak.Prom.Pfx
open Weak.Prom.Cmp (progS3aB)
open Weak.Prom.PF.Loop (tLoop)
open Weak.Prom.Ref.Lit (X Y)

/-! ## 1. The program, as the reference sees it -/

theorem prog0 : tLoop.prog 0 = [.store 4 6 12 0, .fence ⟨false, true, false, false, false, true, false, false⟩,
    .store 4 6 13 0, .br .eq 0 0 0] := rfl

theorem prog1 : tLoop.prog 1 = [.load 4 true 10 13 0, .fence ⟨true, false, false, false, true, false, false, false⟩,
    .load 4 true 11 12 0, .br .eq 0 0 0] := rfl

theorem tLoop_S3a : progS3aB tLoop = true := by decide

theorem tLoop_len : tLoop.harts.length = 2 := rfl

/-! ## 2. Symbolic-state bookkeeping -/

/-- The number of loads in a list of symbolic events. -/
def nL (l : List SEv) : Nat := (l.filter (fun se => se.sk.kind.isLoad)).length

theorem nL_snoc (l : List SEv) (se : SEv) : nL (l ++ [se]) = nL l + (if se.sk.kind.isLoad then 1 else 0) := by
  unfold nL; rw [List.filter_append]; simp only [List.length_append, List.filter_cons, List.filter_nil]
  split <;> simp

abbrev aX : Ex := .bin .add (.c X) (.c 0)
abbrev aY : Ex := .bin .add (.c Y) (.c 0)

theorem aX_eval (ν : Val) : aX.eval ν = X := rfl
theorem aY_eval (ν : Val) : aY.eval ν = Y := rfl

theorem wr_evs (s : SSt) (r : Nat) (v : Ex × List Nat) : (s.wr r v).evs = s.evs := by
  unfold SSt.wr; split <;> rfl

theorem wr_pc (s : SSt) (r : Nat) (v : Ex × List Nat) : (s.wr r v).pc = s.pc := by
  unfold SSt.wr; split <;> rfl

theorem wr_rd (s : SSt) {r r' : Nat} (hne : r ≠ r') (v : Ex × List Nat) : (s.wr r v).rd r' = s.rd r' := by
  unfold SSt.wr; split
  · rfl
  · unfold SSt.rd; split
    · rfl
    · simp [List.getElem?_set_ne hne]

/-- A load `lw rd, 0(rs1)` with a constant, untainted `rs1`. -/
theorem stepL_load (h n : Nat) (s : SSt) (rd rs1 : Nat) (e : Ex) (hr : s.rd rs1 = (e, [])) :
    stepL h n s (.load 4 true rd rs1 0) =
      .next (((s.emit ⟨{ kind := .ld, ii := s.ii, sz := 4, adep := [], cdep := s.ctl }, .bin .add e (.c 0), .c 0⟩).wr
        rd (.ld (h, s.evs.length) 4 true, [s.evs.length])).adv) := by
  show stepI h n s (.load 4 true rd rs1 0) = _
  simp only [stepI, hr]

/-- A store `sw rs2, 0(rs1)` with constant, untainted registers. -/
theorem stepL_store (h n : Nat) (s : SSt) (rs2 rs1 : Nat) (e1 e2 : Ex) (hr1 : s.rd rs1 = (e1, []))
    (hr2 : s.rd rs2 = (e2, [])) :
    stepL h n s (.store 4 rs2 rs1 0) =
      .next ((s.emit ⟨{ kind := .st, ii := s.ii, sz := 4, adep := [], ddep := [], cdep := s.ctl },
        .bin .add e1 (.c 0), e2⟩).adv) := by
  show stepI h n s (.store 4 rs2 rs1 0) = _
  simp only [stepI, hr1, hr2]

theorem stepL_fence (h n : Nat) (s : SSt) (f : FenceSet) :
    stepL h n s (.fence f) = .next ((s.emit ⟨{ kind := .fence f, ii := s.ii, sz := 0 }, .c 0, .c 0⟩).adv) := rfl

/-- `beq zero,zero,0`: a fork to `0` (taken) or `pc + 1` (not taken); events and registers untouched. -/
theorem stepL_br (h : Nat) (s : SSt) :
    stepL h 4 s (.br .eq 0 0 0) =
      .fork { s with ii := s.ii + 1, ctl := s.ctl ++ [] ++ [], pc := 0, conds := s.conds ++ [(.eq, .c 0, .c 0, true)] }
        { s with ii := s.ii + 1, ctl := s.ctl ++ [] ++ [], pc := s.pc + 1,
                 conds := s.conds ++ [(.eq, .c 0, .c 0, false)] } := rfl

/-- Appending one event keeps a per-index property stated over the prefix before each event. -/
theorem evs_snoc {P : Nat → SEv → Prop} {l : List SEv} {se : SEv}
    (hl : ∀ i se', l[i]? = some se' → P (nL (l.take i)) se') (hse : P (nL l) se) :
    ∀ i se', (l ++ [se])[i]? = some se' → P (nL ((l ++ [se]).take i)) se' := by
  intro i se' hi
  have hlt : i < l.length + 1 := by have := (List.getElem?_eq_some_iff.1 hi).1; simpa using this
  by_cases hil : i < l.length
  · rw [List.getElem?_append_left hil] at hi
    rw [List.take_append_of_le_length (by omega)]
    exact hl i se' hi
  · have hi' : i = l.length := by omega
    subst hi'
    rw [List.getElem?_append_right (by omega), Nat.sub_self] at hi
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
    subst hi
    rw [List.take_left' rfl]
    exact hse

/-! ## 3. The invariants -/

def evOk0 (se : SEv) : Prop :=
  (∃ f, se.sk.kind = .fence f) ∨ (se.sk.kind = .st ∧ se.sk.sz = 4 ∧ (se.addr = aX ∨ se.addr = aY))

def evOk1 (m : Nat) (se : SEv) : Prop :=
  (∃ f, se.sk.kind = .fence f) ∨ (se.sk.kind = .ld ∧ se.sk.sz = 4 ∧ se.addr = if m % 2 = 0 then aY else aX)

structure Inv0 (s : SSt) : Prop where
  pc : s.pc ≤ 4
  r6 : s.rd 6 = (.c 1, [])
  r12 : s.rd 12 = (.c X, [])
  r13 : s.rd 13 = (.c Y, [])
  evs : ∀ se ∈ s.evs, evOk0 se

structure Inv1 (s : SSt) : Prop where
  pc : s.pc ≤ 4
  r12 : s.rd 12 = (.c X, [])
  r13 : s.rd 13 = (.c Y, [])
  evs : ∀ i se, s.evs[i]? = some se → evOk1 (nL (s.evs.take i)) se
  par : nL s.evs % 2 = if s.pc = 1 ∨ s.pc = 2 then 1 else 0

/-- The pc facts of one step of `tLoop`'s hart (both harts: three straight-line instructions, then the branch). -/
def PcStep (s s' : SSt) : Prop :=
  (s.pc < 3 → s'.pc = s.pc + 1) ∧ (s.pc = 3 → s'.pc = 0 ∨ s'.pc = 4) ∧ (s.pc = 4 → s'.pc = 4)

theorem pc_cases {p : List Instr} {s : SSt} {i : Instr} (hl : p.length = 4) (hi : p[s.pc]? = some i) :
    s.pc = 0 ∨ s.pc = 1 ∨ s.pc = 2 ∨ s.pc = 3 := by
  have := (List.getElem?_eq_some_iff.1 hi).1; omega

theorem inv0_step {s s' : SSt} (hi : Inv0 s) (hs : LStep (tLoop.prog 0) 0 s s') : Inv0 s' ∧ PcStep s s' := by
  rcases hs with ⟨hp, rfl⟩ | ⟨i, hget, hst⟩
  · exact ⟨hi, fun h => by rw [prog0] at hp; simp at hp; omega, fun h => by rw [prog0] at hp; simp at hp; omega,
      fun h => h⟩
  have hlen : (tLoop.prog 0).length = 4 := rfl
  rw [hlen] at hst
  rcases pc_cases hlen hget with hc | hc | hc | hc <;> rw [prog0, hc] at hget <;>
    simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at hget <;> subst hget
  · rw [stepL_store _ _ _ _ _ _ _ hi.r12 hi.r6] at hst
    rcases hst with hst | ⟨t, f, hst, _⟩
    · cases hst
      refine ⟨⟨by simp [SSt.adv, SSt.emit]; omega, hi.r6, hi.r12, hi.r13, fun se hse => ?_⟩,
        fun _ => rfl, fun h => by omega, fun h => by omega⟩
      simp only [SSt.adv, SSt.emit, List.mem_append, List.mem_singleton] at hse
      rcases hse with hse | rfl
      · exact hi.evs se hse
      · exact .inr ⟨rfl, rfl, .inl rfl⟩
    · cases hst
  · rw [stepL_fence] at hst
    rcases hst with hst | ⟨t, f, hst, _⟩
    · cases hst
      refine ⟨⟨by simp [SSt.adv, SSt.emit]; omega, hi.r6, hi.r12, hi.r13, fun se hse => ?_⟩,
        fun _ => rfl, fun h => by omega, fun h => by omega⟩
      simp only [SSt.adv, SSt.emit, List.mem_append, List.mem_singleton] at hse
      rcases hse with hse | rfl
      · exact hi.evs se hse
      · exact .inl ⟨_, rfl⟩
    · cases hst
  · rw [stepL_store _ _ _ _ _ _ _ hi.r13 hi.r6] at hst
    rcases hst with hst | ⟨t, f, hst, _⟩
    · cases hst
      refine ⟨⟨by simp [SSt.adv, SSt.emit]; omega, hi.r6, hi.r12, hi.r13, fun se hse => ?_⟩,
        fun _ => rfl, fun h => by omega, fun h => by omega⟩
      simp only [SSt.adv, SSt.emit, List.mem_append, List.mem_singleton] at hse
      rcases hse with hse | rfl
      · exact hi.evs se hse
      · exact .inr ⟨rfl, rfl, .inr rfl⟩
    · cases hst
  · rw [stepL_br] at hst
    rcases hst with hst | ⟨t, f, hst, hst'⟩
    · cases hst
    · simp only [StepR.fork.injEq] at hst
      obtain ⟨rfl, rfl⟩ := hst
      rcases hst' with rfl | rfl
      · exact ⟨⟨by simp, hi.r6, hi.r12, hi.r13, hi.evs⟩, fun h => by omega, fun _ => .inl rfl, fun h => by omega⟩
      · exact ⟨⟨by simp; omega, hi.r6, hi.r12, hi.r13, hi.evs⟩, fun h => by omega, fun _ => .inr (by simp; omega),
          fun h => by omega⟩

theorem inv1_step {s s' : SSt} (hi : Inv1 s) (hs : LStep (tLoop.prog 1) 1 s s') : Inv1 s' ∧ PcStep s s' := by
  rcases hs with ⟨hp, rfl⟩ | ⟨i, hget, hst⟩
  · exact ⟨hi, fun h => by rw [prog1] at hp; simp at hp; omega, fun h => by rw [prog1] at hp; simp at hp; omega,
      fun h => h⟩
  have hlen : (tLoop.prog 1).length = 4 := rfl
  rw [hlen] at hst
  have hpar := hi.par
  rcases pc_cases hlen hget with hc | hc | hc | hc <;> rw [prog1, hc] at hget <;>
    simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at hget <;> subst hget <;>
    rw [hc] at hpar
  · rw [stepL_load _ _ _ _ _ _ hi.r13] at hst
    rcases hst with hst | ⟨t, f, hst, _⟩
    · cases hst
      refine ⟨⟨by simp [SSt.adv, SSt.emit]; omega, ?_, ?_, ?_, ?_⟩, fun _ => ?_, fun h => by omega,
        fun h => by omega⟩
      · show ((s.emit _).wr 10 _).rd 12 = _; rw [wr_rd _ (by decide)]; exact hi.r12
      · show ((s.emit _).wr 10 _).rd 13 = _; rw [wr_rd _ (by decide)]; exact hi.r13
      · simp only [SSt.adv, wr_evs, SSt.emit]
        refine evs_snoc hi.evs (.inr ⟨rfl, rfl, ?_⟩)
        simp at hpar; simp [hpar]
      · simp only [SSt.adv, wr_evs, wr_pc, SSt.emit, nL_snoc, hc]
        simp [Kind.isLoad] at hpar ⊢; omega
      · simp [SSt.adv, SSt.emit, hc]
    · cases hst
  · rw [stepL_fence] at hst
    rcases hst with hst | ⟨t, f, hst, _⟩
    · cases hst
      refine ⟨⟨by simp [SSt.adv, SSt.emit]; omega, hi.r12, hi.r13, ?_, ?_⟩, fun _ => ?_, fun h => by omega,
        fun h => by omega⟩
      · simp only [SSt.adv, SSt.emit]
        exact evs_snoc hi.evs (.inl ⟨_, rfl⟩)
      · simp only [SSt.adv, SSt.emit, nL_snoc, hc]
        simp [Kind.isLoad] at hpar ⊢; omega
      · simp [SSt.adv, SSt.emit, hc]
    · cases hst
  · rw [stepL_load _ _ _ _ _ _ hi.r12] at hst
    rcases hst with hst | ⟨t, f, hst, _⟩
    · cases hst
      refine ⟨⟨by simp [SSt.adv, SSt.emit]; omega, ?_, ?_, ?_, ?_⟩, fun _ => ?_, fun h => by omega,
        fun h => by omega⟩
      · show ((s.emit _).wr 11 _).rd 12 = _; rw [wr_rd _ (by decide)]; exact hi.r12
      · show ((s.emit _).wr 11 _).rd 13 = _; rw [wr_rd _ (by decide)]; exact hi.r13
      · simp only [SSt.adv, wr_evs, SSt.emit]
        refine evs_snoc hi.evs (.inr ⟨rfl, rfl, ?_⟩)
        simp at hpar; simp [hpar]
      · simp only [SSt.adv, wr_evs, wr_pc, SSt.emit, nL_snoc, hc]
        simp [Kind.isLoad] at hpar ⊢; omega
      · simp [SSt.adv, SSt.emit, hc]
    · cases hst
  · rw [stepL_br] at hst
    rcases hst with hst | ⟨t, f, hst, hst'⟩
    · cases hst
    · simp only [StepR.fork.injEq] at hst
      obtain ⟨rfl, rfl⟩ := hst
      rcases hst' with rfl | rfl
      · exact ⟨⟨by simp, hi.r12, hi.r13, hi.evs, by simp at hpar ⊢; omega⟩, fun h => by omega, fun _ => .inl rfl,
          fun h => by omega⟩
      · exact ⟨⟨by simp; omega, hi.r12, hi.r13, hi.evs, by simp [hc] at hpar ⊢; omega⟩, fun h => by omega,
          fun _ => .inr (by simp; omega), fun h => by omega⟩

/-! ## 4. Over an execution -/

theorem sk_sev (E : IExec) (e : EvId) : E.sk e = (E.sev e).sk := rfl
theorem pa_sev (E : IExec) (e : EvId) : (E.ev e).pa = (E.sev e).addr.eval E.ν := rfl

section exec

variable {E : IExec} (hE : infExec tLoop E)
include hE

theorem conf_h {h : Nat} (hh : h < 2) :
    E.st h 0 = tLoop.init h ∧ ∀ k, LStep (tLoop.prog h) h (E.st h k) (E.st h (k + 1)) := by
  obtain ⟨hET, hc, _, _⟩ := hE
  have := hc h (by rw [hET]; exact hh)
  rw [hET] at this; exact this

theorem inv0_all : ∀ k, Inv0 (E.st 0 k) := by
  intro k
  induction k with
  | zero =>
    rw [(conf_h hE (by decide : 0 < 2)).1]
    exact ⟨by decide, by decide, by decide, by decide, fun _ he => by cases he⟩
  | succ k ih => exact (inv0_step ih ((conf_h hE (by decide : 0 < 2)).2 k)).1

theorem inv1_all : ∀ k, Inv1 (E.st 1 k) := by
  intro k
  induction k with
  | zero =>
    rw [(conf_h hE (by decide : 1 < 2)).1]
    exact ⟨by decide, by decide, by decide, fun _ _ he => by simp [Test.init] at he, by decide⟩
  | succ k ih => exact (inv1_step ih ((conf_h hE (by decide : 1 < 2)).2 k)).1

theorem pcStep_all {h : Nat} (hh : h < 2) (k : Nat) : PcStep (E.st h k) (E.st h (k + 1)) := by
  match h, hh with
  | 0, _ => exact (inv0_step (inv0_all hE k) ((conf_h hE (by decide : 0 < 2)).2 k)).2
  | 1, _ => exact (inv1_step (inv1_all hE k) ((conf_h hE (by decide : 1 < 2)).2 k)).2

theorem pc_le {h : Nat} (hh : h < 2) (k : Nat) : (E.st h k).pc ≤ 4 := by
  match h, hh with
  | 0, _ => exact (inv0_all hE k).pc
  | 1, _ => exact (inv1_all hE k).pc

/-- **THE PATH**: before it halts, hart `h` is at `pc = j % 4` after `j` steps. -/
theorem pc_pat {h : Nat} (hh : h < 2) :
    ∀ j, (∀ j' < j, (E.st h j').pc ≠ 4) → (E.st h j).pc = j % 4 ∨ ((E.st h j).pc = 4 ∧ j % 4 = 0) := by
  intro j
  induction j with
  | zero =>
    intro _; left
    rw [(conf_h hE hh).1]; rfl
  | succ j ih =>
    intro hnh
    have hj : (E.st h j).pc = j % 4 := by
      rcases ih (fun j' hj' => hnh j' (by omega)) with h1 | ⟨h1, _⟩
      · exact h1
      · exact absurd h1 (hnh j (by omega))
    obtain ⟨p1, p2, _⟩ := pcStep_all hE hh j
    have : j % 4 < 4 := Nat.mod_lt _ (by decide)
    by_cases h3 : j % 4 = 3
    · rcases p2 (by omega) with h0 | h4
      · left; rw [h0]; omega
      · right; exact ⟨h4, by omega⟩
    · left; rw [p1 (by omega), hj]; omega

theorem fragT_loop : FragT E.T := by
  rw [hE.1]; exact fragT_of tLoop_S3a

theorem has_lt {e : EvId} (he : E.has e) : e.1 < 2 := by
  have := he.1; rw [hE.1] at this; exact this

/-- The symbolic event of `(h, i)` is the `i`-th event of some state. -/
theorem sev_at {h i : Nat} (hi : E.has (h, i)) :
    ∃ k, i < (E.st h k).evs.length ∧ (E.st h k).evs[i]? = some (E.sev (h, i)) := by
  obtain ⟨hh, k, hk⟩ := hi
  exact ⟨k, hk, sev_eq hE.2.1 (fragT_loop hE) hh hk⟩

/-- Hart 0 issues no load. -/
theorem noLoad0 {i : Nat} (hi : E.has (0, i)) : (E.sk (0, i)).kind.isLoad = false := by
  obtain ⟨k, _, hk⟩ := sev_at hE hi
  rw [sk_sev]
  rcases (inv0_all hE k).evs _ (List.mem_of_getElem? hk) with ⟨f, hf⟩ | ⟨hf, _⟩ <;> rw [hf] <;> rfl

/-- **Every memory operation of `tLoop` is a 4-byte access at `X` or `Y`.** -/
theorem memFacts {e : EvId} (he : E.isMem e) : (E.sk e).sz = 4 ∧ ((E.ev e).pa = X ∨ (E.ev e).pa = Y) := by
  obtain ⟨hhas, hm⟩ := he
  obtain ⟨h, i⟩ := e
  have hh := has_lt hE hhas
  obtain ⟨k, _, hk⟩ := sev_at hE hhas
  rw [sk_sev] at hm ⊢
  rw [pa_sev]
  match h, hh with
  | 0, _ =>
    rcases (inv0_all hE k).evs _ (List.mem_of_getElem? hk) with ⟨f, hf⟩ | ⟨_, hsz, ha | ha⟩
    · rw [hf] at hm; cases hm
    · exact ⟨hsz, .inl (by rw [ha]; exact aX_eval _)⟩
    · exact ⟨hsz, .inr (by rw [ha]; exact aY_eval _)⟩
  | 1, _ =>
    rcases (inv1_all hE k).evs _ _ hk with ⟨f, hf⟩ | ⟨_, hsz, ha⟩
    · rw [hf] at hm; cases hm
    · refine ⟨hsz, ?_⟩
      rw [ha]; split
      · exact .inr (aY_eval _)
      · exact .inl (aX_eval _)

/-- **NA-6 holds for every execution of `tLoop`.** -/
theorem singleSizeI_loop : singleSizeI E := by
  intro a b ha hb hov
  obtain ⟨sa, pa⟩ := memFacts hE ha
  obtain ⟨sb, pb⟩ := memFacts hE hb
  refine ⟨?_, by rw [sa, sb]⟩
  unfold overlapB at hov
  have hsa : (E.ev a).sk.sz = 4 := sa
  have hsb : (E.ev b).sk.sz = 4 := sb
  rw [hsa, hsb] at hov
  simp only [decide_eq_true_eq] at hov
  simp only [X, Y] at pa pb
  omega

/-- The loads before `i` on hart `h`, counted on a state that has them. -/
theorem nL_take {h k i : Nat} (hh : h < 2) (hi : i ≤ (E.st h k).evs.length) :
    nL ((E.st h k).evs.take i) = ((List.range i).filter (fun i' => (E.sk (h, i')).kind.isLoad)).length := by
  have hh' : h < E.T.harts.length := by rw [hE.1]; exact hh
  have heq : (E.st h k).evs.take i = (List.range i).map (fun i' => E.sev (h, i')) := by
    apply List.ext_getElem?
    intro n
    rw [List.getElem?_take, List.getElem?_map]
    by_cases hn : n < i
    · rw [if_pos hn, List.getElem?_range hn, Option.map_some]
      exact sev_eq hE.2.1 (fragT_loop hE) hh' (by omega)
    · rw [if_neg hn, List.getElem?_eq_none (by simp; omega)]; rfl
  rw [heq]
  unfold nL
  rw [List.filter_map, List.length_map]
  rfl

/-- **Hart 1's loads alternate**: a load is at `Y` iff an even number of loads precede it. -/
theorem par1 {i : Nat} (hi : E.has (1, i)) (hl : (E.sk (1, i)).kind.isLoad = true) :
    ((E.ev (1, i)).pa = Y ↔ ((List.range i).filter (fun i' => (E.sk (1, i')).kind.isLoad)).length % 2 = 0) := by
  obtain ⟨k, hik, hk⟩ := sev_at hE hi
  rw [← nL_take hE (by decide) (Nat.le_of_lt hik), pa_sev]
  rw [sk_sev] at hl
  rcases (inv1_all hE k).evs _ _ hk with ⟨f, hf⟩ | ⟨_, _, ha⟩
  · rw [hf] at hl; cases hl
  · rw [ha]
    split
    · rename_i hm; simp only [aY_eval, hm]
    · rename_i hm; simp only [aX_eval, hm, iff_false]; simp [X, Y]

end exec

end Weak.Prom.InfLoop

end
