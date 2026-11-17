/-
Weak/Mini: **THE HEADLINES — reference-level verdicts on the example programs** (mini plan rev 4 §2 L6, §0 "VETTED
STATEMENTS"; owner ruling [OWN.P18] "For the reference program proofs, can we minimize the machinery").

Each headline is a statement about MiniRef ALONE (Ref.lean: `miniCut`, `miniExec`, the axiom block `MEvs.ax`) and a
program text of Prog.lean's syntax (`lbddP`, `mpFFP`, `loopP`: LitLbdd.lean, LitMpFF.lean, LitLoop.lean).  No
machine, logic, unrolling or observed set appears in a statement; they are chosen inside the proofs:
* `mini_forbidden_lbdd` — LB+data+data (RefTests.lean `lbdd`): in every FINITE execution, not both harts' first
  loads return 1 (the full stack's `ref_lbdd`, RefLitmus.lean; the cut form of the CoreLit verdict `lit_lbdd`).
* `mini_forbidden_mpFF` — MP+fence.w.w+fence.r.rw (RefTests.lean `mpFF`): in every finite execution, not (hart 1's
  flag load returns 1 and its data load returns 0) (`ref_mpFF`, `lit_mpFF`).
* `mini_inf_mpLoop` — MP FOREVER (CoreLitLoop.lean `tLoop`): in every INFINITE execution, a data load that is the
  next memory operation after a flag load that returned 1 returns 1 (`inf_mpLoop`, Weak/Prom/InfLoop.lean:172).
Route: completeness (`mini_complete`, CmpMain.lean; `mini_inf_complete`, PfxMain.lean) turns the execution into a
valid MiniMach run with the same load values; the machine-level lemma proved in MiniLogic (`mini_lit_*`) gives the
verdict on that run.  The loop also needs the alternation facts of HeadAlt.lean (the `n`-th load of hart 1 on the
machine is the `n`-th load of hart 1 in the execution, flag for even `n`, data for odd `n`).
Vacuity witnesses (K4): HeadWit.lean.  Cross-checks against the full stack: EqHead.lean.
No `sorry`, no axiom, no `native_decide`.  Imports: Weak.Mini only (no `Eq*`).
-/
import Weak.Mini.HeadAlt

namespace Weak.Mini

open Weak.Mini.Mach
open Weak.Mini.Logic (lbddP mpFFP loopP)

/-! ## 1. Observations of a finite execution -/

/-- **`C.obsLoad P h k`: the value the `k`-th load of hart `h` returned in the finite execution `C`** (in program
order; `none` if hart `h` has run fewer loads).  The cut form of the machine's `MRun.obsLoad` (Mach.lean) and of the
full stack's `PFRun.obsLoad` (CoreDefs.lean:80), which the CoreLit verdicts are stated over. -/
def MCut.obsLoad (P : MProg) (C : MCut) (h k : Nat) : Option Nat :=
  ((C.st P h).evs.filterMap (fun e => if e.kind = .ld then some e.v else none))[k]?

/-! ## 2. The programs are well formed -/

theorem lbddP_wf : lbddP.wf := by
  refine ⟨by decide, by simp [lbddP], fun h i hi => ?_⟩
  simp only [MProg.prog, lbddP] at hi
  match h, hi with
  | 0, hi => simp at hi; rcases hi with rfl | rfl <;> exact ⟨trivial, by simp [MI.regOk], trivial⟩
  | 1, hi => simp at hi; rcases hi with rfl | rfl <;> exact ⟨trivial, by simp [MI.regOk], trivial⟩
  | n + 2, hi => simp at hi

theorem mpFFP_wf : mpFFP.wf := by
  refine ⟨by decide, by simp [mpFFP], fun h i hi => ?_⟩
  simp only [MProg.prog, mpFFP] at hi
  match h, hi with
  | 0, hi => simp at hi; rcases hi with rfl | rfl | rfl <;> exact ⟨trivial, by simp [MI.regOk], trivial⟩
  | 1, hi => simp at hi; rcases hi with rfl | rfl | rfl <;> exact ⟨trivial, by simp [MI.regOk], trivial⟩
  | n + 2, hi => simp at hi

theorem loopP_wf : loopP.wf := by
  refine ⟨by decide, by simp [loopP], fun h i hi => ?_⟩
  simp only [MProg.prog, loopP] at hi
  match h, hi with
  | 0, hi =>
    simp at hi
    rcases hi with rfl | rfl | rfl | rfl <;> exact ⟨by simp [MI.tgtOk], by simp [MI.regOk], trivial⟩
  | 1, hi =>
    simp at hi
    rcases hi with rfl | rfl | rfl | rfl <;> exact ⟨by simp [MI.tgtOk], by simp [MI.regOk], trivial⟩
  | n + 2, hi => simp at hi

/-- The machine's observations of the run `mini_complete` builds are the cut's. -/
theorem obsLoad_run {P : MProg} {C : MCut} {r : MRun} (hld : ∀ h, loadVals (r.trace h) = cutLoads P C h)
    (h k : Nat) : r.obsLoad h k = C.obsLoad P h k := by
  unfold MRun.obsLoad MCut.obsLoad; rw [hld h]; rfl

/-! ## 3. THE FINITE HEADLINES -/

/-- The proof of `mini_forbidden_lbdd`. -/
theorem Head.forbiddenLbdd (C : MCut) (hC : miniCut lbddP C) :
    ¬ (C.obsLoad lbddP 0 0 = some 1 ∧ C.obsLoad lbddP 1 0 = some 1) := by
  obtain ⟨r, hr, hld, _⟩ := mini_complete lbddP lbddP_wf C hC
  rw [← obsLoad_run hld, ← obsLoad_run hld]
  exact Logic.mini_lit_lbdd _ r hr

/-- **LB+data+data is FORBIDDEN by RVWMO (MiniRef)**: in every finite execution of `lbddP` (hart 0 `lw x5,0(x6);
sw x5,0(x8)`, hart 1 the same with the addresses swapped), not both harts' first loads return 1. -/
theorem mini_forbidden_lbdd (C : MCut) (hC : miniCut lbddP C) :
    ¬ (C.obsLoad lbddP 0 0 = some 1 ∧ C.obsLoad lbddP 1 0 = some 1) :=
  Head.forbiddenLbdd C hC

/-- The proof of `mini_forbidden_mpFF`. -/
theorem Head.forbiddenMpFF (C : MCut) (hC : miniCut mpFFP C) :
    ¬ (C.obsLoad mpFFP 1 0 = some 1 ∧ C.obsLoad mpFFP 1 1 = some 0) := by
  obtain ⟨r, hr, hld, _⟩ := mini_complete mpFFP mpFFP_wf C hC
  rw [← obsLoad_run hld, ← obsLoad_run hld]
  exact Logic.mini_lit_mpFF _ r hr

/-- **MP+fence.w.w+fence.r.rw is FORBIDDEN by RVWMO (MiniRef)**: in every finite execution of `mpFFP` (hart 0 `sw
x5,0(x6); fence w,w; sw x5,0(x7)` storing 1 to the data then the flag; hart 1 `lw x5,0(x6); fence r,rw; lw x7,0(x8)`
loading the flag then the data), not (hart 1's flag load returns 1 and its data load returns 0). -/
theorem mini_forbidden_mpFF (C : MCut) (hC : miniCut mpFFP C) :
    ¬ (C.obsLoad mpFFP 1 0 = some 1 ∧ C.obsLoad mpFFP 1 1 = some 0) :=
  Head.forbiddenMpFF C hC

/-! ## 4. Rows of an infinite execution of `loopP` -/

section loop

variable {X : MExec}

theorem rowX_succ (P : MProg) (X : MExec) (h n : Nat) :
    rowX P X h (n + 1) = rowX P X h n ++
      (if ((X.evs P).ev (h, n)).kind = .ld then [((X.evs P).ev (h, n)).v] else []) := by
  unfold rowX Cmp.ldVals
  rw [List.range_succ, List.map_append, List.filterMap_append]
  simp only [List.map_cons, List.map_nil, List.filterMap_cons, List.filterMap_nil]
  split <;> simp_all

/-- Hart 1's row through iteration `q`: two loads per iteration. -/
theorem row_len {q : Nat} (hq : (X.evs loopP).has (1, 3 * q)) : (rowX loopP X 1 (3 * q)).length = 2 * q := by
  induction q with
  | zero => rfl
  | succ q ih =>
    have hh : ∀ k, k ≤ 3 * q + 2 → (X.evs loopP).has (1, k) := fun k hk => Pfx.xhas_le hq (by omega)
    have o0 := Logic.x_ok1 (hh (3 * q) (by omega))
    have o1 := Logic.x_ok1 (hh (3 * q + 1) (by omega))
    have o2 := Logic.x_ok1 (hh (3 * q + 2) (by omega))
    rw [show 3 * (q + 1) = 3 * q + 2 + 1 by omega, rowX_succ, rowX_succ, rowX_succ,
      if_pos (o0.1 (by omega)).1, if_neg (by rw [o1.2.1 (by omega)]; simp), if_pos (o2.2.2 (by omega)).1]
    simp only [List.length_append, List.length_singleton, List.length_nil, ih (hh _ (by omega))]
    omega

/-- The value of a memory entry that is a load. -/
def ldv (e : MLab × Option Nat) : Nat :=
  match e.1 with
  | .load _ _ v _ => v
  | _ => 0

theorem loadVals_loads :
    ∀ (l : List (MLab × Option Nat)), (∀ e ∈ l, ∃ a t v asr, e = (.load a t v asr, none)) →
    loadVals l = l.map ldv
  | [], _ => rfl
  | e :: l, h => by
    obtain ⟨a, t, v, asr, rfl⟩ := h e (List.mem_cons_self ..)
    rw [List.map_cons, ← loadVals_loads l (fun e' he' => h e' (List.mem_cons_of_mem _ he'))]
    rfl

/-- A machine load value at position `n` of an alternating trace is the `n`-th memory entry, at `altA n`. -/
theorem alt_get {l : List (MLab × Option Nat)} (hA : Logic.QA l) {n v : Nat} (hv : (loadVals l)[n]? = some v) :
    ∃ t asr, l[n]? = some (.load (Logic.altA n) t v asr, none) := by
  have hall : ∀ e ∈ l, ∃ a t v asr, e = (.load a t v asr, none) := by
    intro e he
    obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem he
    obtain ⟨t, v, asr, h⟩ := hA m _ (List.getElem?_eq_getElem hm)
    exact ⟨_, t, v, asr, h⟩
  rw [loadVals_loads l hall, List.getElem?_map] at hv
  cases hn : l[n]? with
  | none => rw [hn] at hv; cases hv
  | some e =>
    rw [hn] at hv
    obtain ⟨t, v', asr, rfl⟩ := hA n e hn
    simp only [Option.map_some, Option.some.injEq, ldv] at hv
    subst hv
    exact ⟨t, asr, rfl⟩

end loop

/-! ## 5. THE INFINITE HEADLINE -/

/-- The proof of `mini_inf_mpLoop`. -/
theorem Head.infMpLoop {X : MExec} (hX : miniExec loopP X) (h i j : Nat)
    (hi : (X.evs loopP).isMem (h, i)) (hj : (X.evs loopP).isMem (h, j)) (hij : i < j)
    (hnext : ∀ k, i < k → k < j → ¬ (X.evs loopP).isMem (h, k))
    (hfl : (X.evs loopP).isLd (h, i)) (hfa : ((X.evs loopP).ev (h, i)).pa = 0x2000)
    (hfv : ((X.evs loopP).ev (h, i)).v = 1)
    (hdl : (X.evs loopP).isLd (h, j)) (hda : ((X.evs loopP).ev (h, j)).pa = 0x1000) :
    ((X.evs loopP).ev (h, j)).v = 1 := by
  -- the hart is hart 1 (hart 0 never loads)
  have hh : h < 2 := hi.1.1
  have h1 : h = 1 := by
    rcases (by omega : h = 0 ∨ h = 1) with rfl | rfl
    · exact absurd hfl (Logic.x_noLd0 hi.1)
    · rfl
  subst h1
  -- the flag load is the first event of an iteration
  have hoi := Logic.x_ok1 hi.1
  have hi0 : i % 3 = 0 := by
    rcases (by omega : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2) with h | h | h
    · exact h
    · have := hoi.2.1 h; unfold MEvs.isLd at hfl; rw [this] at hfl; cases hfl
    · have := (hoi.2.2 h).2; rw [this] at hfa; exact absurd hfa (by decide)
  -- the next memory operation is the iteration's data load
  have hhas : ∀ k, k ≤ j → (X.evs loopP).has (1, k) := fun k hk => Pfx.xhas_le hj.1 hk
  have hj2 : j = i + 2 := by
    rcases (by omega : j = i + 1 ∨ j = i + 2 ∨ i + 2 < j) with h | h | h
    · subst h
      have hf := (Logic.x_ok1 hj.1).2.1 (by omega)
      rcases hj.2 with h' | h'
      · unfold MEvs.isLd at h'; rw [hf] at h'; cases h'
      · unfold MEvs.isSt at h'; rw [hf] at h'; cases h'
    · exact h
    · exact absurd ⟨hhas _ (by omega), .inl ((Logic.x_ok1 (hhas (i + 2) (by omega))).2.2 (by omega)).1⟩
        (hnext (i + 2) (by omega) h)
  subst hj2
  -- the reference row through the data load: the earlier iterations, then the flag and the data values
  obtain ⟨q, rfl⟩ : ∃ q, i = 3 * q := ⟨i / 3, by omega⟩
  have hrow : rowX loopP X 1 (3 * q + 2 + 1) =
      rowX loopP X 1 (3 * q) ++ [((X.evs loopP).ev (1, 3 * q)).v, ((X.evs loopP).ev (1, 3 * q + 2)).v] := by
    have o1 := Logic.x_ok1 (hhas (3 * q + 1) (by omega))
    rw [rowX_succ, rowX_succ, rowX_succ, if_pos (hoi.1 (by omega)).1, if_neg (by rw [o1.2.1 (by omega)]; simp),
      if_pos (show ((X.evs loopP).ev (1, 3 * q + 2)).kind = .ld from hdl)]
    simp
  have hlen := row_len (hhas (3 * q) (by omega))
  -- completeness: a valid machine run whose hart-1 load row extends the execution's
  obtain ⟨_, Mm, r, hr, hpre, _⟩ := mini_inf_complete loopP loopP_wf X hX [(1, 3 * q + 2)]
    (by intro e he; simp only [List.mem_singleton] at he; subst he; exact hj)
  obtain ⟨t, ht⟩ := hpre (1, 3 * q + 2) (by simp)
  rw [hrow] at ht
  have hm : ∀ n (hn : n < 2), (loadVals (r.trace 1))[2 * q + n]? =
      some ([((X.evs loopP).ev (1, 3 * q)).v, ((X.evs loopP).ev (1, 3 * q + 2)).v][n]) := by
    intro n hn
    rw [← ht, List.append_assoc, List.getElem?_append_right (by omega), hlen, Nat.add_sub_cancel_left,
      List.getElem?_append_left (by simp; omega), List.getElem?_eq_getElem]
  have h0 := hm 0 (by decide)
  have h1 := hm 1 (by decide)
  simp only [Nat.add_zero, List.getElem_cons_zero, List.getElem_cons_succ] at h0 h1
  -- the machine: hart 1 alternates, and MiniLogic's `qLoop` holds of its trace
  rw [Logic.loadVals_memEv] at h0 h1
  have hA := Logic.mini_alt_loop hr
  obtain ⟨t0, a0, he0⟩ := alt_get hA h0
  obtain ⟨t1, a1, he1⟩ := alt_get hA h1
  have hq := Logic.mini_lit_mpLoop Mm r hr 1 (2 * q) _ _ he0 he1
  have ha0 : Logic.altA (2 * q) = 0x2000 := by simp [Logic.altA]
  have ha1 : Logic.altA (2 * q + 1) = 0x1000 := by simp [Logic.altA]
  exact hq (by simp [Logic.ldRet, ha0, hfv]) _ (by simp [Logic.ldRet, ha1])


/-- **MP FOREVER is guaranteed by RVWMO (MiniRef)**: in every possibly-infinite execution `X` of `loopP` (hart 0
loops `sw x6,0(x12); fence w,w; sw x6,0(x13)` storing 1 to the data `0x1000` then the flag `0x2000`; hart 1 loops
`lw x10,0(x13); fence r,r; lw x11,0(x12)` loading the flag then the data), if a hart's memory operation `(h, i)` is a
load of the flag that returned 1 and the hart's NEXT memory operation `(h, j)` is a load of the data, then that
data load returned 1.  (The shape of Weak/Prom/InfLoop.lean:172 `inf_mpLoop`, over mini events.) -/
theorem mini_inf_mpLoop {X : MExec} (hX : miniExec loopP X) (h i j : Nat)
    (hi : (X.evs loopP).isMem (h, i)) (hj : (X.evs loopP).isMem (h, j)) (hij : i < j)
    (hnext : ∀ k, i < k → k < j → ¬ (X.evs loopP).isMem (h, k))
    (hfl : (X.evs loopP).isLd (h, i)) (hfa : ((X.evs loopP).ev (h, i)).pa = 0x2000)
    (hfv : ((X.evs loopP).ev (h, i)).v = 1)
    (hdl : (X.evs loopP).isLd (h, j)) (hda : ((X.evs loopP).ev (h, j)).pa = 0x1000) :
    ((X.evs loopP).ev (h, j)).v = 1 :=
  Head.infMpLoop hX h i j hi hj hij hnext hfl hfa hfv hdl hda

end Weak.Mini
