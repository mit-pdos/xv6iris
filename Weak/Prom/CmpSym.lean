/-
Weak/Prom: **completeness S3a — the reference's symbolic run** (Weak/Prom/RefProg.lean `stepI`/`symRun`).

Two kinds of facts about the per-hart symbolic interpreter, used by the simulation (Weak/Prom/CmpSim.lean):
* `StepShape` (`stepI_shape`): one instruction only APPENDS events (with the current dynamic instruction index
  `ii`, and a store's control dependencies = the current control taint), appends path conditions, appends control
  taint, and advances `ii`.  Hence `symRun_future`: along a run from `s` to the final state `sf`, `s`'s events and
  conditions are prefixes of `sf`'s, and every LATER event of `sf` has `ii ≥ s.ii`, a later store's control
  dependencies containing `s.ctl`.
* `SymWf` (`symWf_step`, `symWf_init`): program order is the order of `ii` (earlier events have smaller `ii`; two
  distinct events with equal `ii` are FENCE.TSO's two fences, not memory operations), every syntactic dependency of an
  event is an earlier MEMORY operation of the hart, and so is every register's and the control state's taint.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.CmpRef

namespace Weak.Prom.Cmp

open Weak.Prom.Ref

/-! ## 1. Register file -/

theorem SSt.rd_wr (s : SSt) (rd r : Nat) (v : Ex × List Nat) :
    (s.wr rd v).rd r = if rd ≠ 0 ∧ r = rd ∧ rd < s.regs.length then v else s.rd r := by
  unfold SSt.wr SSt.rd
  by_cases h0 : rd = 0
  · simp [h0]
  · rw [if_neg h0]
    by_cases hr0 : r = 0
    · simp only [hr0, if_true]
      split
      · rename_i hh; exact absurd hh.2.1.symm h0
      · rfl
    · simp only [hr0, if_false]
      by_cases hrr : r = rd
      · subst hrr
        by_cases hl : r < s.regs.length
        · simp [h0, hl]
        · simp [h0, hl]
      · simp [hrr, List.getElem?_set_ne (Ne.symm hrr)]

theorem SSt.rd_wr_mem {s : SSt} {rd r : Nat} {v : Ex × List Nat} {d : Nat} (h : d ∈ ((s.wr rd v).rd r).2) :
    d ∈ v.2 ∨ d ∈ (s.rd r).2 := by
  rw [SSt.rd_wr] at h
  split at h
  · exact .inl h
  · exact .inr h

theorem SSt.wr_regs_len (s : SSt) (rd : Nat) (v : Ex × List Nat) : (s.wr rd v).regs.length = s.regs.length := by
  unfold SSt.wr; split <;> simp

@[simp] theorem SSt.wr_evs (s : SSt) (rd : Nat) (v : Ex × List Nat) : (s.wr rd v).evs = s.evs := by
  unfold SSt.wr; split <;> rfl
@[simp] theorem SSt.wr_ii (s : SSt) (rd : Nat) (v : Ex × List Nat) : (s.wr rd v).ii = s.ii := by
  unfold SSt.wr; split <;> rfl
@[simp] theorem SSt.wr_ctl (s : SSt) (rd : Nat) (v : Ex × List Nat) : (s.wr rd v).ctl = s.ctl := by
  unfold SSt.wr; split <;> rfl
@[simp] theorem SSt.wr_conds (s : SSt) (rd : Nat) (v : Ex × List Nat) : (s.wr rd v).conds = s.conds := by
  unfold SSt.wr; split <;> rfl
@[simp] theorem SSt.wr_pc (s : SSt) (rd : Nat) (v : Ex × List Nat) : (s.wr rd v).pc = s.pc := by
  unfold SSt.wr; split <;> rfl

@[simp] theorem SSt.emit_evs (s : SSt) (se : SEv) : (s.emit se).evs = s.evs ++ [se] := rfl
@[simp] theorem SSt.emit_ii (s : SSt) (se : SEv) : (s.emit se).ii = s.ii := rfl
@[simp] theorem SSt.emit_ctl (s : SSt) (se : SEv) : (s.emit se).ctl = s.ctl := rfl
@[simp] theorem SSt.emit_conds (s : SSt) (se : SEv) : (s.emit se).conds = s.conds := rfl
@[simp] theorem SSt.emit_pc (s : SSt) (se : SEv) : (s.emit se).pc = s.pc := rfl
@[simp] theorem SSt.emit_regs (s : SSt) (se : SEv) : (s.emit se).regs = s.regs := rfl
@[simp] theorem SSt.emit_rd (s : SSt) (se : SEv) (r : Nat) : (s.emit se).rd r = s.rd r := rfl

@[simp] theorem SSt.adv_evs (s : SSt) : s.adv.evs = s.evs := rfl
@[simp] theorem SSt.adv_ii (s : SSt) : s.adv.ii = s.ii + 1 := rfl
@[simp] theorem SSt.adv_ctl (s : SSt) : s.adv.ctl = s.ctl := rfl
@[simp] theorem SSt.adv_conds (s : SSt) : s.adv.conds = s.conds := rfl
@[simp] theorem SSt.adv_pc (s : SSt) : s.adv.pc = s.pc + 1 := rfl
@[simp] theorem SSt.adv_regs (s : SSt) : s.adv.regs = s.regs := rfl
@[simp] theorem SSt.adv_rd (s : SSt) (r : Nat) : s.adv.rd r = s.rd r := rfl

/-! ## 2. The shape of one step -/

/-- ONE INSTRUCTION'S SHAPE: events, conditions and control taint are appended; the new events carry the current
`ii`, a new store's control dependencies are the current control taint; `ii` advances. -/
structure StepShape (s s' : SSt) : Prop where
  evs : ∃ new : List SEv, s'.evs = s.evs ++ new ∧
    ∀ se ∈ new, se.sk.ii = s.ii ∧ (se.sk.kind.isStore = true → se.sk.cdep = s.ctl)
  conds : s.conds <+: s'.conds
  ctl : s.ctl <+: s'.ctl
  ii : s.ii < s'.ii

theorem shape_mk {s s' : SSt} (new : List SEv) (he : s'.evs = s.evs ++ new)
    (hn : ∀ se ∈ new, se.sk.ii = s.ii ∧ (se.sk.kind.isStore = true → se.sk.cdep = s.ctl))
    (hc : s.conds <+: s'.conds) (hctl : s.ctl <+: s'.ctl) (hii : s.ii < s'.ii) : StepShape s s' :=
  ⟨⟨new, he, hn⟩, hc, hctl, hii⟩

theorem stepI_shape (h n : Nat) (s : SSt) (i : Instr) :
    (∀ s', stepI h n s i = .next s' → StepShape s s') ∧
    (∀ t f, stepI h n s i = .fork t f → StepShape s t ∧ StepShape s f) := by
  cases i with
  | alui op rd rs1 imm =>
    refine ⟨fun s' hs => ?_, fun t f hs => by simp [stepI] at hs⟩
    simp only [stepI, StepR.next.injEq] at hs; subst hs
    exact shape_mk [] (by simp) (by simp) (by simp [List.prefix_refl]) (by simp [List.prefix_refl]) (by simp)
  | alu op rd rs1 rs2 =>
    refine ⟨fun s' hs => ?_, fun t f hs => by simp [stepI] at hs⟩
    simp only [stepI, StepR.next.injEq] at hs; subst hs
    exact shape_mk [] (by simp) (by simp) (by simp [List.prefix_refl]) (by simp [List.prefix_refl]) (by simp)
  | load sz sgn rd rs1 off =>
    refine ⟨fun s' hs => ?_, fun t f hs => by simp [stepI] at hs⟩
    simp only [stepI, StepR.next.injEq] at hs; subst hs
    exact shape_mk [_] (by simp only [SSt.adv_evs, SSt.wr_evs, SSt.emit_evs] <;> rfl) (by simp [Kind.isStore]) (by simp [List.prefix_refl])
      (by simp [List.prefix_refl]) (by simp)
  | store sz rs2 rs1 off =>
    refine ⟨fun s' hs => ?_, fun t f hs => by simp [stepI] at hs⟩
    simp only [stepI, StepR.next.injEq] at hs; subst hs
    exact shape_mk [_] (by simp only [SSt.adv_evs, SSt.wr_evs, SSt.emit_evs] <;> rfl) (by simp) (by simp [List.prefix_refl]) (by simp [List.prefix_refl]) (by simp)
  | loadAq sz rl rd rs1 =>
    refine ⟨fun s' hs => ?_, fun t f hs => by simp [stepI] at hs⟩
    simp only [stepI, StepR.next.injEq] at hs; subst hs
    exact shape_mk [_] (by simp only [SSt.adv_evs, SSt.wr_evs, SSt.emit_evs] <;> rfl) (by simp [Kind.isStore]) (by simp [List.prefix_refl])
      (by simp [List.prefix_refl]) (by simp)
  | storeRl sz aq rs2 rs1 =>
    refine ⟨fun s' hs => ?_, fun t f hs => by simp [stepI] at hs⟩
    simp only [stepI, StepR.next.injEq] at hs; subst hs
    exact shape_mk [_] (by simp only [SSt.adv_evs, SSt.wr_evs, SSt.emit_evs] <;> rfl) (by simp) (by simp [List.prefix_refl]) (by simp [List.prefix_refl]) (by simp)
  | loadAqPc sz rl rd rs1 =>
    refine ⟨fun s' hs => ?_, fun t f hs => by simp [stepI] at hs⟩
    simp only [stepI, StepR.next.injEq] at hs; subst hs
    exact shape_mk [_] (by simp only [SSt.adv_evs, SSt.wr_evs, SSt.emit_evs] <;> rfl) (by simp [Kind.isStore]) (by simp [List.prefix_refl])
      (by simp [List.prefix_refl]) (by simp)
  | storeRlPc sz aq rs2 rs1 =>
    refine ⟨fun s' hs => ?_, fun t f hs => by simp [stepI] at hs⟩
    simp only [stepI, StepR.next.injEq] at hs; subst hs
    exact shape_mk [_] (by simp only [SSt.adv_evs, SSt.wr_evs, SSt.emit_evs] <;> rfl) (by simp) (by simp [List.prefix_refl]) (by simp [List.prefix_refl]) (by simp)
  | lr sz aq rl rd rs1 =>
    refine ⟨fun s' hs => ?_, fun t f hs => by simp [stepI] at hs⟩
    simp only [stepI, StepR.next.injEq] at hs; subst hs
    exact shape_mk [_] (by simp only [SSt.adv_evs, SSt.wr_evs, SSt.emit_evs] <;> rfl) (by simp [Kind.isStore]) (by simp [List.prefix_refl])
      (by simp [List.prefix_refl]) (by simp)
  | sc sz aq rl rd rs2 rs1 =>
    refine ⟨fun s' hs => by simp [stepI] at hs, fun t f hs => ?_⟩
    simp only [stepI, StepR.fork.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    exact ⟨shape_mk [_] (by simp only [SSt.adv_evs, SSt.wr_evs, SSt.emit_evs] <;> rfl) (by simp) (by simp [List.prefix_refl]) (by simp [List.prefix_refl]) (by simp),
      shape_mk [_] (by simp only [SSt.adv_evs, SSt.wr_evs, SSt.emit_evs] <;> rfl) (by simp [Kind.isStore]) (by simp [List.prefix_refl])
        (by simp [List.prefix_refl]) (by simp)⟩
  | amo op sz aq rl rd rs2 rs1 =>
    refine ⟨fun s' hs => ?_, fun t f hs => by simp [stepI] at hs⟩
    simp only [stepI, StepR.next.injEq] at hs; subst hs
    exact shape_mk [_] (by simp only [SSt.adv_evs, SSt.wr_evs, SSt.emit_evs] <;> rfl) (by simp) (by simp [List.prefix_refl]) (by simp [List.prefix_refl]) (by simp)
  | fence fs =>
    refine ⟨fun s' hs => ?_, fun t f hs => by simp [stepI] at hs⟩
    simp only [stepI, StepR.next.injEq] at hs; subst hs
    exact shape_mk [_] (by simp only [SSt.adv_evs, SSt.wr_evs, SSt.emit_evs] <;> rfl) (by simp [Kind.isStore]) (by simp [List.prefix_refl])
      (by simp [List.prefix_refl]) (by simp)
  | fenceTso =>
    refine ⟨fun s' hs => ?_, fun t f hs => by simp [stepI] at hs⟩
    simp only [stepI, StepR.next.injEq] at hs; subst hs
    exact shape_mk [_, _] (by simp only [SSt.adv_evs, SSt.wr_evs, SSt.emit_evs, List.append_assoc] <;> rfl) (by simp [Kind.isStore]) (by simp [List.prefix_refl])
      (by simp [List.prefix_refl]) (by simp)
  | br c rs1 rs2 tgt =>
    refine ⟨fun s' hs => ?_, fun t f hs => ?_⟩
    · simp only [stepI] at hs; split at hs <;> cases hs
    · simp only [stepI] at hs
      split at hs
      · cases hs
      · simp only [StepR.fork.injEq] at hs
        obtain ⟨rfl, rfl⟩ := hs
        exact ⟨shape_mk [] (by simp) (by simp) (by simp) (by simp) (by simp),
          shape_mk [] (by simp) (by simp) (by simp) (by simp) (by simp)⟩
  | jmp tgt =>
    refine ⟨fun s' hs => ?_, fun t f hs => ?_⟩
    · simp only [stepI] at hs
      split at hs
      · cases hs
      · simp only [StepR.next.injEq] at hs; subst hs
        exact shape_mk [] (by simp) (by simp) (by simp [List.prefix_refl]) (by simp [List.prefix_refl]) (by simp)
    · simp only [stepI] at hs; split at hs <;> cases hs
  | csrr rd v =>
    refine ⟨fun s' hs => ?_, fun t f hs => by simp [stepI] at hs⟩
    simp only [stepI, StepR.next.injEq] at hs; subst hs
    exact shape_mk [] (by simp) (by simp) (by simp [List.prefix_refl]) (by simp [List.prefix_refl]) (by simp)
  | fencei =>
    refine ⟨fun s' hs => ?_, fun t f hs => by simp [stepI] at hs⟩
    simp only [stepI, StepR.next.injEq] at hs; subst hs
    exact shape_mk [] (by simp) (by simp) (by simp [List.prefix_refl]) (by simp [List.prefix_refl]) (by simp)
  | nop =>
    refine ⟨fun s' hs => ?_, fun t f hs => by simp [stepI] at hs⟩
    simp only [stepI, StepR.next.injEq] at hs; subst hs
    exact shape_mk [] (by simp) (by simp) (by simp [List.prefix_refl]) (by simp [List.prefix_refl]) (by simp)

/-! ## 3. The future of a symbolic run -/

/-- What the rest of the run from `s` to `sf` can say about `s`. -/
structure Future (s sf : SSt) : Prop where
  evs : s.evs <+: sf.evs
  conds : s.conds <+: sf.conds
  later : ∀ (j : Nat) (se : SEv), s.evs.length ≤ j → sf.evs[j]? = some se →
    s.ii ≤ se.sk.ii ∧ (se.sk.kind.isStore = true → ∀ d ∈ s.ctl, d ∈ se.sk.cdep)

theorem future_refl (s : SSt) : Future s s :=
  ⟨List.prefix_refl _, List.prefix_refl _, fun j se hj hse => by
    rw [List.getElem?_eq_none hj] at hse; cases hse⟩

theorem future_step {s s' sf : SSt} (h1 : StepShape s s') (h2 : Future s' sf) : Future s sf := by
  obtain ⟨⟨new, he, hn⟩, hc, hctl, hii⟩ := h1
  refine ⟨?_, hc.trans h2.conds, fun j se hj hse => ?_⟩
  · exact (he ▸ List.prefix_append s.evs new).trans h2.evs
  · by_cases hj' : s'.evs.length ≤ j
    · obtain ⟨k1, k2⟩ := h2.later j se hj' hse
      refine ⟨by omega, fun hs d hd => k2 hs d (hctl.subset hd)⟩
    · have hjl : j < s'.evs.length := by omega
      have hse' : s'.evs[j]? = some se := by
        obtain ⟨tl, htl⟩ := h2.evs
        rw [← htl, List.getElem?_append_left hjl] at hse; exact hse
      rw [he] at hse'
      have hjs : s.evs.length ≤ j := hj
      rw [List.getElem?_append_right hjs] at hse'
      have hmem : se ∈ new := List.mem_of_getElem? hse'
      obtain ⟨k1, k2⟩ := hn se hmem
      exact ⟨by omega, fun hs d hd => by rw [k2 hs]; exact hd⟩

/-- Along a symbolic run from `s` to `sf`: `Future s sf`. -/
theorem symRun_future (p : List Instr) (h : Nat) :
    ∀ (fuel : Nat) (s : SSt) (ch : List Bool) (sf : SSt), symRun p h fuel s ch = some sf → Future s sf
  | 0, s, ch, sf, H => by simp [symRun] at H
  | fuel + 1, s, ch, sf, H => by
    unfold symRun at H
    by_cases hpc : s.pc = p.length
    · rw [if_pos hpc] at H
      split at H
      · cases H; exact future_refl s
      · cases H
    · rw [if_neg hpc] at H
      cases hi : p[s.pc]? with
      | none => rw [hi] at H; cases H
      | some i =>
        rw [hi] at H
        simp only at H
        have hsh := stepI_shape h p.length s i
        cases hs : stepI h p.length s i with
        | stuck => rw [hs] at H; cases H
        | next s' =>
          rw [hs] at H
          exact future_step (hsh.1 s' hs) (symRun_future p h fuel s' ch sf H)
        | fork t f =>
          rw [hs] at H
          simp only at H
          cases ch with
          | nil => cases H
          | cons b ch' =>
            cases b
            · exact future_step (hsh.2 t f hs).2 (symRun_future p h fuel f ch' sf H)
            · exact future_step (hsh.2 t f hs).1 (symRun_future p h fuel t ch' sf H)

/-! ## 4. Well-formedness of symbolic states -/

/-- Index `d` is a memory operation of the event list. -/
def okIdx (evs : List SEv) (d : Nat) : Prop := ∃ se, evs[d]? = some se ∧ se.sk.kind.isMem = true

theorem okIdx_lt {evs : List SEv} {d : Nat} (h : okIdx evs d) : d < evs.length := by
  obtain ⟨se, hse, _⟩ := h
  exact (List.getElem?_eq_some_iff.1 hse).1

theorem okIdx_app {evs : List SEv} (new : List SEv) {d : Nat} (h : okIdx evs d) : okIdx (evs ++ new) d := by
  obtain ⟨se, hse, hm⟩ := h
  exact ⟨se, by rw [List.getElem?_append_left (okIdx_lt ⟨se, hse, hm⟩)]; exact hse, hm⟩

/-- The deps of a skeleton. -/
def depsOf (sk : Skel) (d : Nat) : Prop := d ∈ sk.adep ∨ d ∈ sk.ddep ∨ d ∈ sk.cdep

/-- WELL-FORMED SYMBOLIC STATE. -/
structure SymWf (s : SSt) : Prop where
  iiLt : ∀ (j : Nat) (se : SEv), s.evs[j]? = some se → se.sk.ii < s.ii
  iiMono : ∀ (j j' : Nat) (se se' : SEv), j < j' → s.evs[j]? = some se → s.evs[j']? = some se' →
    se.sk.ii ≤ se'.sk.ii ∧ (se.sk.kind.isMem = true → se.sk.ii < se'.sk.ii)
  deps : ∀ (j : Nat) (se : SEv), s.evs[j]? = some se → ∀ d, depsOf se.sk d → d < j ∧ okIdx s.evs d
  taint : ∀ r, ∀ d ∈ (s.rd r).2, okIdx s.evs d
  ctl : ∀ d ∈ s.ctl, okIdx s.evs d
  len : s.regs.length = 32

theorem hnm1 (se0 : SEv) : ∀ (j j' : Nat) (se : SEv), j < j' → j' < [se0].length → [se0][j]? = some se →
    se.sk.kind.isMem = false := by
  intro j j' se h1 h2; simp only [List.length_singleton] at h2; omega

/-- The sufficient condition for one step. -/
theorem symWf_mk {s s' : SSt} (hw : SymWf s) (new : List SEv) (he : s'.evs = s.evs ++ new) (hii : s.ii < s'.ii)
    (hnii : ∀ se ∈ new, se.sk.ii = s.ii)
    (hnm : ∀ j j' se, j < j' → j' < new.length → new[j]? = some se → se.sk.kind.isMem = false)
    (hnd : ∀ se ∈ new, ∀ d, depsOf se.sk d → okIdx s.evs d)
    (ht : ∀ r, ∀ d ∈ (s'.rd r).2, okIdx s'.evs d) (hc : ∀ d ∈ s'.ctl, okIdx s'.evs d)
    (hl : s'.regs.length = 32) : SymWf s' := by
  refine ⟨fun j se hse => ?_, fun j j' se se' hjj hse hse' => ?_, fun j se hse d hd => ?_, ht, hc, hl⟩
  · rw [he] at hse
    rcases Nat.lt_or_ge j s.evs.length with hj | hj
    · rw [List.getElem?_append_left hj] at hse
      have := hw.iiLt j se hse; omega
    · rw [List.getElem?_append_right hj] at hse
      rw [hnii se (List.mem_of_getElem? hse)]; exact hii
  · rw [he] at hse hse'
    rcases Nat.lt_or_ge j' s.evs.length with hj' | hj'
    · rw [List.getElem?_append_left hj'] at hse'
      rw [List.getElem?_append_left (by omega)] at hse
      exact hw.iiMono j j' se se' hjj hse hse'
    · rw [List.getElem?_append_right hj'] at hse'
      have h' := hnii se' (List.mem_of_getElem? hse')
      rcases Nat.lt_or_ge j s.evs.length with hj | hj
      · rw [List.getElem?_append_left hj] at hse
        have := hw.iiLt j se hse
        exact ⟨by omega, fun _ => by omega⟩
      · rw [List.getElem?_append_right hj] at hse
        have h1 := hnii se (List.mem_of_getElem? hse)
        refine ⟨by omega, fun hm => ?_⟩
        have hl' : j' - s.evs.length < new.length := (List.getElem?_eq_some_iff.1 hse').1
        have := hnm (j - s.evs.length) (j' - s.evs.length) se (by omega) hl' hse
        rw [this] at hm; cases hm
  · rw [he] at hse
    rcases Nat.lt_or_ge j s.evs.length with hj | hj
    · rw [List.getElem?_append_left hj] at hse
      obtain ⟨k1, k2⟩ := hw.deps j se hse d hd
      exact ⟨k1, he ▸ okIdx_app new k2⟩
    · rw [List.getElem?_append_right hj] at hse
      have := hnd se (List.mem_of_getElem? hse) d hd
      exact ⟨by have := okIdx_lt this; omega, he ▸ okIdx_app new this⟩

/-- The initial state of a test is well-formed. -/
theorem symWf_init (T : Test) (h : Nat) : SymWf (T.init h) := by
  refine ⟨fun j se hse => by simp [Test.init] at hse, fun j j' se se' _ hse => by simp [Test.init] at hse,
    fun j se hse => by simp [Test.init] at hse, fun r d hd => ?_, fun d hd => by simp [Test.init] at hd,
    by simp [Test.init]⟩
  exfalso
  unfold SSt.rd Test.init at hd
  split at hd
  · simp at hd
  · simp only [List.getElem?_map] at hd
    rcases hx : (List.range 32)[r]? with _ | x <;> simp [hx] at hd

theorem okIdx_new {s : SSt} (se : SEv) (hm : se.sk.kind.isMem = true) :
    okIdx (s.evs ++ [se]) s.evs.length := ⟨se, by simp, hm⟩

theorem ctl_keep {s : SSt} (hw : SymWf s) (new : List SEv) : ∀ d ∈ s.ctl, okIdx (s.evs ++ new) d :=
  fun d hd => okIdx_app new (hw.ctl d hd)

theorem taint_wr {s : SSt} (hw : SymWf s) (new : List SEv) (rd : Nat) (v : Ex × List Nat)
    (hv : ∀ d ∈ v.2, okIdx (s.evs ++ new) d) : ∀ r, ∀ d ∈ ((s.wr rd v).rd r).2, okIdx (s.evs ++ new) d := by
  intro r d hd
  rcases SSt.rd_wr_mem hd with h | h
  · exact hv d h
  · exact okIdx_app new (hw.taint r d h)

/-- `SymWf` is preserved by every instruction. -/
theorem symWf_step (h n : Nat) {s : SSt} (hw : SymWf s) (i : Instr) :
    (∀ s', stepI h n s i = .next s' → SymWf s') ∧
    (∀ t f, stepI h n s i = .fork t f → SymWf t ∧ SymWf f) := by
  have tk := fun (r : Nat) (d : Nat) (hd : d ∈ (s.rd r).2) => okIdx_app (new := []) (hw.taint r d hd)
  have dk : ∀ r, ∀ d ∈ (s.rd r).2, ∀ new : List SEv, okIdx (s.evs ++ new) d :=
    fun r d hd new => okIdx_app new (hw.taint r d hd)
  cases i with
  | alui op rd rs1 imm =>
    refine ⟨fun s' hs => ?_, fun t f hs => by simp [stepI] at hs⟩
    simp only [stepI, StepR.next.injEq] at hs; subst hs
    refine symWf_mk hw [] (by simp) (by simp) (by simp) (by simp) (by simp) ?_ ?_ ?_
    · intro r d hd
      simp only [SSt.adv_rd, SSt.adv_evs, SSt.wr_evs] at hd ⊢
      rcases SSt.rd_wr_mem hd with h | h
      · exact hw.taint rs1 d h
      · exact hw.taint r d h
    · intro d hd; simp only [SSt.adv_ctl, SSt.wr_ctl, SSt.adv_evs, SSt.wr_evs] at hd ⊢; exact hw.ctl d hd
    · simp [SSt.wr_regs_len, hw.len]
  | alu op rd rs1 rs2 =>
    refine ⟨fun s' hs => ?_, fun t f hs => by simp [stepI] at hs⟩
    simp only [stepI, StepR.next.injEq] at hs; subst hs
    refine symWf_mk hw [] (by simp) (by simp) (by simp) (by simp) (by simp) ?_ ?_ ?_
    · intro r d hd
      simp only [SSt.adv_rd, SSt.adv_evs, SSt.wr_evs] at hd ⊢
      rcases SSt.rd_wr_mem hd with h | h
      · rcases List.mem_append.1 h with h | h
        · exact hw.taint rs1 d h
        · exact hw.taint rs2 d h
      · exact hw.taint r d h
    · intro d hd; simp only [SSt.adv_ctl, SSt.wr_ctl, SSt.adv_evs, SSt.wr_evs] at hd ⊢; exact hw.ctl d hd
    · simp [SSt.wr_regs_len, hw.len]
  | load sz sgn rd rs1 off =>
    refine ⟨fun s' hs => ?_, fun t f hs => by simp [stepI] at hs⟩
    simp only [stepI, StepR.next.injEq] at hs; subst hs
    refine symWf_mk hw [_] (by simp only [SSt.adv_evs, SSt.wr_evs, SSt.emit_evs] <;> rfl) (by simp) (by simp) (hnm1 _) ?_ ?_ ?_ ?_
    · intro se hse d hd
      simp only [List.mem_singleton] at hse; subst hse
      rcases hd with hd | hd | hd
      · exact hw.taint rs1 d hd
      · simp at hd
      · exact hw.ctl d hd
    · intro r d hd
      simp only [SSt.adv_rd, SSt.adv_evs, SSt.wr_evs, SSt.emit_evs] at hd ⊢
      rcases SSt.rd_wr_mem hd with h | h
      · simp only [List.mem_singleton] at h; subst h
        exact okIdx_new _ (by simp [Kind.isMem])
      · exact okIdx_app _ (hw.taint r d h)
    · intro d hd; simp only [SSt.adv_ctl, SSt.wr_ctl, SSt.emit_ctl, SSt.adv_evs, SSt.wr_evs, SSt.emit_evs] at hd ⊢
      exact ctl_keep hw _ d hd
    · simp [SSt.wr_regs_len, hw.len]
  | store sz rs2 rs1 off =>
    refine ⟨fun s' hs => ?_, fun t f hs => by simp [stepI] at hs⟩
    simp only [stepI, StepR.next.injEq] at hs; subst hs
    refine symWf_mk hw [_] (by simp only [SSt.adv_evs, SSt.wr_evs, SSt.emit_evs] <;> rfl) (by simp) (by simp) (hnm1 _) ?_ ?_ ?_ ?_
    · intro se hse d hd
      simp only [List.mem_singleton] at hse; subst hse
      rcases hd with hd | hd | hd
      · exact hw.taint rs1 d hd
      · exact hw.taint rs2 d hd
      · exact hw.ctl d hd
    · intro r d hd
      simp only [SSt.adv_rd, SSt.adv_evs, SSt.emit_evs, SSt.emit_rd] at hd ⊢
      exact okIdx_app _ (hw.taint r d hd)
    · intro d hd; simp only [SSt.adv_ctl, SSt.emit_ctl, SSt.adv_evs, SSt.emit_evs] at hd ⊢
      exact ctl_keep hw _ d hd
    · simp [hw.len]
  | loadAq sz rl rd rs1 =>
    refine ⟨fun s' hs => ?_, fun t f hs => by simp [stepI] at hs⟩
    simp only [stepI, StepR.next.injEq] at hs; subst hs
    refine symWf_mk hw [_] (by simp only [SSt.adv_evs, SSt.wr_evs, SSt.emit_evs] <;> rfl) (by simp) (by simp) (hnm1 _) ?_ ?_ ?_ ?_
    · intro se hse d hd
      simp only [List.mem_singleton] at hse; subst hse
      rcases hd with hd | hd | hd
      · exact hw.taint rs1 d hd
      · simp at hd
      · exact hw.ctl d hd
    · intro r d hd
      simp only [SSt.adv_rd, SSt.adv_evs, SSt.wr_evs, SSt.emit_evs] at hd ⊢
      rcases SSt.rd_wr_mem hd with h | h
      · simp only [List.mem_singleton] at h; subst h
        exact okIdx_new _ (by simp [Kind.isMem])
      · exact okIdx_app _ (hw.taint r d h)
    · intro d hd; simp only [SSt.adv_ctl, SSt.wr_ctl, SSt.emit_ctl, SSt.adv_evs, SSt.wr_evs, SSt.emit_evs] at hd ⊢
      exact ctl_keep hw _ d hd
    · simp [SSt.wr_regs_len, hw.len]
  | storeRl sz aq rs2 rs1 =>
    refine ⟨fun s' hs => ?_, fun t f hs => by simp [stepI] at hs⟩
    simp only [stepI, StepR.next.injEq] at hs; subst hs
    refine symWf_mk hw [_] (by simp only [SSt.adv_evs, SSt.wr_evs, SSt.emit_evs] <;> rfl) (by simp) (by simp) (hnm1 _) ?_ ?_ ?_ ?_
    · intro se hse d hd
      simp only [List.mem_singleton] at hse; subst hse
      rcases hd with hd | hd | hd
      · exact hw.taint rs1 d hd
      · exact hw.taint rs2 d hd
      · exact hw.ctl d hd
    · intro r d hd
      simp only [SSt.adv_rd, SSt.adv_evs, SSt.emit_evs, SSt.emit_rd] at hd ⊢
      exact okIdx_app _ (hw.taint r d hd)
    · intro d hd; simp only [SSt.adv_ctl, SSt.emit_ctl, SSt.adv_evs, SSt.emit_evs] at hd ⊢
      exact ctl_keep hw _ d hd
    · simp [hw.len]
  | loadAqPc sz rl rd rs1 =>
    refine ⟨fun s' hs => ?_, fun t f hs => by simp [stepI] at hs⟩
    simp only [stepI, StepR.next.injEq] at hs; subst hs
    refine symWf_mk hw [_] (by simp only [SSt.adv_evs, SSt.wr_evs, SSt.emit_evs] <;> rfl) (by simp) (by simp) (hnm1 _) ?_ ?_ ?_ ?_
    · intro se hse d hd
      simp only [List.mem_singleton] at hse; subst hse
      rcases hd with hd | hd | hd
      · exact hw.taint rs1 d hd
      · simp at hd
      · exact hw.ctl d hd
    · intro r d hd
      simp only [SSt.adv_rd, SSt.adv_evs, SSt.wr_evs, SSt.emit_evs] at hd ⊢
      rcases SSt.rd_wr_mem hd with h | h
      · simp only [List.mem_singleton] at h; subst h
        exact okIdx_new _ (by simp [Kind.isMem])
      · exact okIdx_app _ (hw.taint r d h)
    · intro d hd; simp only [SSt.adv_ctl, SSt.wr_ctl, SSt.emit_ctl, SSt.adv_evs, SSt.wr_evs, SSt.emit_evs] at hd ⊢
      exact ctl_keep hw _ d hd
    · simp [SSt.wr_regs_len, hw.len]
  | storeRlPc sz aq rs2 rs1 =>
    refine ⟨fun s' hs => ?_, fun t f hs => by simp [stepI] at hs⟩
    simp only [stepI, StepR.next.injEq] at hs; subst hs
    refine symWf_mk hw [_] (by simp only [SSt.adv_evs, SSt.wr_evs, SSt.emit_evs] <;> rfl) (by simp) (by simp) (hnm1 _) ?_ ?_ ?_ ?_
    · intro se hse d hd
      simp only [List.mem_singleton] at hse; subst hse
      rcases hd with hd | hd | hd
      · exact hw.taint rs1 d hd
      · exact hw.taint rs2 d hd
      · exact hw.ctl d hd
    · intro r d hd
      simp only [SSt.adv_rd, SSt.adv_evs, SSt.emit_evs, SSt.emit_rd] at hd ⊢
      exact okIdx_app _ (hw.taint r d hd)
    · intro d hd; simp only [SSt.adv_ctl, SSt.emit_ctl, SSt.adv_evs, SSt.emit_evs] at hd ⊢
      exact ctl_keep hw _ d hd
    · simp [hw.len]
  | lr sz aq rl rd rs1 =>
    refine ⟨fun s' hs => ?_, fun t f hs => by simp [stepI] at hs⟩
    simp only [stepI, StepR.next.injEq] at hs; subst hs
    refine symWf_mk hw [_] (by simp only [SSt.adv_evs, SSt.wr_evs, SSt.emit_evs] <;> rfl) (by simp) (by simp) (hnm1 _) ?_ ?_ ?_ ?_
    · intro se hse d hd
      simp only [List.mem_singleton] at hse; subst hse
      rcases hd with hd | hd | hd
      · exact hw.taint rs1 d hd
      · simp at hd
      · exact hw.ctl d hd
    · intro r d hd
      simp only [SSt.adv_rd, SSt.adv_evs, SSt.wr_evs, SSt.emit_evs] at hd ⊢
      rcases SSt.rd_wr_mem hd with h | h
      · simp only [List.mem_singleton] at h; subst h
        exact okIdx_new _ (by simp [Kind.isMem])
      · exact okIdx_app _ (hw.taint r d h)
    · intro d hd; simp only [SSt.adv_ctl, SSt.wr_ctl, SSt.emit_ctl, SSt.adv_evs, SSt.wr_evs, SSt.emit_evs] at hd ⊢
      exact ctl_keep hw _ d hd
    · simp [SSt.wr_regs_len, hw.len]
  | sc sz aq rl rd rs2 rs1 =>
    refine ⟨fun s' hs => by simp [stepI] at hs, fun t f hs => ?_⟩
    simp only [stepI, StepR.fork.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    constructor
    · refine symWf_mk hw [_] (by simp only [SSt.adv_evs, SSt.wr_evs, SSt.emit_evs] <;> rfl) (by simp) (by simp) (hnm1 _) ?_ ?_ ?_ ?_
      · intro se hse d hd
        simp only [List.mem_singleton] at hse; subst hse
        rcases hd with hd | hd | hd
        · exact hw.taint rs1 d hd
        · exact hw.taint rs2 d hd
        · exact hw.ctl d hd
      · intro r d hd
        simp only [SSt.adv_rd, SSt.adv_evs, SSt.wr_evs, SSt.emit_evs] at hd ⊢
        rcases SSt.rd_wr_mem hd with h | h
        · simp only [List.mem_singleton] at h; subst h
          exact okIdx_new _ (by simp [Kind.isMem])
        · exact okIdx_app _ (hw.taint r d h)
      · intro d hd
        simp only [SSt.adv_ctl, SSt.wr_ctl, SSt.emit_ctl, SSt.adv_evs, SSt.wr_evs, SSt.emit_evs] at hd ⊢
        exact ctl_keep hw _ d hd
      · simp [SSt.wr_regs_len, hw.len]
    · refine symWf_mk hw [_] (by simp only [SSt.adv_evs, SSt.wr_evs, SSt.emit_evs] <;> rfl) (by simp) (by simp) (hnm1 _) ?_ ?_ ?_ ?_
      · intro se hse d hd
        simp only [List.mem_singleton] at hse; subst hse
        rcases hd with hd | hd | hd
        · exact hw.taint rs1 d hd
        · exact hw.taint rs2 d hd
        · exact hw.ctl d hd
      · intro r d hd
        simp only [SSt.adv_rd, SSt.adv_evs, SSt.wr_evs, SSt.emit_evs] at hd ⊢
        rcases SSt.rd_wr_mem hd with h | h
        · exact okIdx_app _ (hw.taint rd d (by simpa using h))
        · exact okIdx_app _ (hw.taint r d h)
      · intro d hd
        simp only [SSt.adv_ctl, SSt.wr_ctl, SSt.emit_ctl, SSt.adv_evs, SSt.wr_evs, SSt.emit_evs] at hd ⊢
        exact ctl_keep hw _ d hd
      · simp [SSt.wr_regs_len, hw.len]
  | amo op sz aq rl rd rs2 rs1 =>
    refine ⟨fun s' hs => ?_, fun t f hs => by simp [stepI] at hs⟩
    simp only [stepI, StepR.next.injEq] at hs; subst hs
    refine symWf_mk hw [_] (by simp only [SSt.adv_evs, SSt.wr_evs, SSt.emit_evs] <;> rfl) (by simp) (by simp) (hnm1 _) ?_ ?_ ?_ ?_
    · intro se hse d hd
      simp only [List.mem_singleton] at hse; subst hse
      rcases hd with hd | hd | hd
      · exact hw.taint rs1 d hd
      · exact hw.taint rs2 d hd
      · exact hw.ctl d hd
    · intro r d hd
      simp only [SSt.adv_rd, SSt.adv_evs, SSt.wr_evs, SSt.emit_evs] at hd ⊢
      rcases SSt.rd_wr_mem hd with h | h
      · simp only [List.mem_singleton] at h; subst h
        exact okIdx_new _ (by simp [Kind.isMem])
      · exact okIdx_app _ (hw.taint r d h)
    · intro d hd; simp only [SSt.adv_ctl, SSt.wr_ctl, SSt.emit_ctl, SSt.adv_evs, SSt.wr_evs, SSt.emit_evs] at hd ⊢
      exact ctl_keep hw _ d hd
    · simp [SSt.wr_regs_len, hw.len]
  | fence fs =>
    refine ⟨fun s' hs => ?_, fun t f hs => by simp [stepI] at hs⟩
    simp only [stepI, StepR.next.injEq] at hs; subst hs
    refine symWf_mk hw [_] (by simp only [SSt.adv_evs, SSt.wr_evs, SSt.emit_evs] <;> rfl) (by simp) (by simp) (hnm1 _) ?_ ?_ ?_ ?_
    · intro se hse d hd
      simp only [List.mem_singleton] at hse; subst hse
      simp [depsOf] at hd
    · intro r d hd
      simp only [SSt.adv_rd, SSt.adv_evs, SSt.emit_evs, SSt.emit_rd] at hd ⊢
      exact okIdx_app _ (hw.taint r d hd)
    · intro d hd; simp only [SSt.adv_ctl, SSt.emit_ctl, SSt.adv_evs, SSt.emit_evs] at hd ⊢
      exact ctl_keep hw _ d hd
    · simp [hw.len]
  | fenceTso =>
    refine ⟨fun s' hs => ?_, fun t f hs => by simp [stepI] at hs⟩
    simp only [stepI, StepR.next.injEq] at hs; subst hs
    refine symWf_mk hw [_, _] (by simp only [SSt.adv_evs, SSt.wr_evs, SSt.emit_evs, List.append_assoc] <;> rfl) (by simp) (by simp) ?_ ?_ ?_ ?_ ?_
    · intro j j' se _ hj' hse
      simp only [List.length_cons, List.length_nil] at hj'
      have : j = 0 := by omega
      subst this
      simp at hse; subst hse; rfl
    · intro se hse d hd
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hse
      rcases hse with rfl | rfl <;> simp [depsOf] at hd
    · intro r d hd
      simp only [SSt.adv_rd, SSt.adv_evs, SSt.emit_evs, SSt.emit_rd, List.append_assoc] at hd ⊢
      exact okIdx_app _ (hw.taint r d hd)
    · intro d hd; simp only [SSt.adv_ctl, SSt.emit_ctl, SSt.adv_evs, SSt.emit_evs, List.append_assoc] at hd ⊢
      exact ctl_keep hw _ d hd
    · simp [hw.len]
  | br c rs1 rs2 tgt =>
    refine ⟨fun s' hs => ?_, fun t f hs => ?_⟩
    · simp only [stepI] at hs; split at hs <;> cases hs
    · simp only [stepI] at hs
      split at hs
      · cases hs
      · simp only [StepR.fork.injEq] at hs
        obtain ⟨rfl, rfl⟩ := hs
        have hct : ∀ d ∈ s.ctl ++ (s.rd rs1).2 ++ (s.rd rs2).2, okIdx s.evs d := by
          intro d hd
          simp only [List.mem_append] at hd
          rcases hd with (hd | hd) | hd
          · exact hw.ctl d hd
          · exact hw.taint rs1 d hd
          · exact hw.taint rs2 d hd
        exact ⟨symWf_mk hw [] (by simp) (by simp) (by simp) (by simp) (by simp)
            (fun r d hd => hw.taint r d hd) (fun d hd => hct d hd) hw.len,
          symWf_mk hw [] (by simp) (by simp) (by simp) (by simp) (by simp)
            (fun r d hd => hw.taint r d hd) (fun d hd => hct d hd) hw.len⟩
  | jmp tgt =>
    refine ⟨fun s' hs => ?_, fun t f hs => ?_⟩
    · simp only [stepI] at hs
      split at hs
      · cases hs
      · simp only [StepR.next.injEq] at hs; subst hs
        exact symWf_mk hw [] (by simp) (by simp) (by simp) (by simp) (by simp)
          (fun r d hd => hw.taint r d hd) (fun d hd => hw.ctl d hd) hw.len
    · simp only [stepI] at hs; split at hs <;> cases hs
  | csrr rd v =>
    refine ⟨fun s' hs => ?_, fun t f hs => by simp [stepI] at hs⟩
    simp only [stepI, StepR.next.injEq] at hs; subst hs
    refine symWf_mk hw [] (by simp) (by simp) (by simp) (by simp) (by simp) ?_ ?_ ?_
    · intro r d hd
      simp only [SSt.adv_rd, SSt.adv_evs, SSt.wr_evs] at hd ⊢
      rcases SSt.rd_wr_mem hd with h | h
      · simp at h
      · exact hw.taint r d h
    · intro d hd; simp only [SSt.adv_ctl, SSt.wr_ctl, SSt.adv_evs, SSt.wr_evs] at hd ⊢; exact hw.ctl d hd
    · simp [SSt.wr_regs_len, hw.len]
  | fencei =>
    refine ⟨fun s' hs => ?_, fun t f hs => by simp [stepI] at hs⟩
    simp only [stepI, StepR.next.injEq] at hs; subst hs
    exact symWf_mk hw [] (by simp) (by simp) (by simp) (by simp) (by simp)
      (fun r d hd => hw.taint r d hd) (fun d hd => hw.ctl d hd) hw.len
  | nop =>
    refine ⟨fun s' hs => ?_, fun t f hs => by simp [stepI] at hs⟩
    simp only [stepI, StepR.next.injEq] at hs; subst hs
    exact symWf_mk hw [] (by simp) (by simp) (by simp) (by simp) (by simp)
      (fun r d hd => hw.taint r d hd) (fun d hd => hw.ctl d hd) hw.len

/-- `SymWf` along a run. -/
theorem symRun_wf (p : List Instr) (h : Nat) :
    ∀ (fuel : Nat) (s : SSt) (ch : List Bool) (sf : SSt), symRun p h fuel s ch = some sf → SymWf s → SymWf sf
  | 0, s, ch, sf, H, _ => by simp [symRun] at H
  | fuel + 1, s, ch, sf, H, hw => by
    unfold symRun at H
    by_cases hpc : s.pc = p.length
    · rw [if_pos hpc] at H
      split at H
      · cases H; exact hw
      · cases H
    · rw [if_neg hpc] at H
      cases hi : p[s.pc]? with
      | none => rw [hi] at H; cases H
      | some i =>
        rw [hi] at H
        simp only at H
        have hsw := symWf_step h p.length hw i
        cases hs : stepI h p.length s i with
        | stuck => rw [hs] at H; cases H
        | next s' =>
          rw [hs] at H
          exact symRun_wf p h fuel s' ch sf H (hsw.1 s' hs)
        | fork t f =>
          rw [hs] at H
          simp only at H
          cases ch with
          | nil => cases H
          | cons b ch' =>
            cases b
            · exact symRun_wf p h fuel f ch' sf H (hsw.2 t f hs).2
            · exact symRun_wf p h fuel t ch' sf H (hsw.2 t f hs).1

end Weak.Prom.Cmp
