/-
Weak/Mini: **facts about MiniRef's harts and its axiom block**, shared by L4 (MiniCmp, completeness) and L5
(MiniPfx, the prefix lemma) (mini plan rev 4 §2 L4, L5).

* §1 one hart step (`exec`): what it does to the event list, the dynamic index, the control taint;
* §2 `RunWf`: along every hart run, events are in dynamic-index order, and every taint (register, control, an
  event's address/data/control dependencies) names an EARLIER LOAD of the hart (rvwmo.adoc:156–246: dependencies
  are on loads through registers);
* §3 runs: the event list and the control taint only grow; an event's control dependencies contain every earlier
  control taint (rvwmo.adoc:242–246 "every po-earlier branch");
* §4 the axiom block: gmo is a strict total order, `rf` is functional.
Imports: only `Weak.Mini.Ref` (plan §2 import discipline).  No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Mini.Ref

namespace Weak.Mini.Cmp

open Weak.Mini

/-! ## 1. One hart step -/

theorem wr_same (s : MSt) (r : Nat) (x : Nat × List Nat) :
    (s.wr r x).pc = s.pc ∧ (s.wr r x).evs = s.evs ∧ (s.wr r x).ii = s.ii ∧ (s.wr r x).ctl = s.ctl := by
  unfold MSt.wr; split <;> exact ⟨rfl, rfl, rfl, rfl⟩

theorem regs_wr (s : MSt) (r r' : Nat) (x : Nat × List Nat) :
    (s.wr r x).regs r' = if 0 < r ∧ r < 32 ∧ r' = r then x else s.regs r' := by
  unfold MSt.wr
  by_cases h : 0 < r ∧ r < 32
  · rw [if_pos h]
    by_cases h' : r' = r
    · subst h'; simp [h]
    · simp [h']
  · rw [if_neg h]
    have : ¬ (0 < r ∧ r < 32 ∧ r' = r) := fun ⟨a, b, _⟩ => h ⟨a, b⟩
    rw [if_neg this]

theorem rd_wr (s : MSt) (r r' : Nat) (x : Nat × List Nat) :
    (s.wr r x).rd r' = if 0 < r ∧ r < 32 ∧ r' = r then x else s.rd r' := by
  unfold MSt.rd
  rw [regs_wr]
  by_cases h : 0 < r ∧ r < 32 ∧ r' = r
  · obtain ⟨h1, h2, rfl⟩ := h; simp [h1, h2]
  · rw [if_neg h, if_neg h]

/-! ## 2. Well-formed hart states -/

/-- `j` is a load of the event list `l`. -/
def ldAt (l : List MEv) (j : Nat) : Prop := ∃ e, l[j]? = some e ∧ e.kind = .ld

theorem ldAt_lt {l : List MEv} {j : Nat} (h : ldAt l j) : j < l.length := by
  obtain ⟨e, he, _⟩ := h
  exact (List.getElem?_eq_some_iff.1 he).1

theorem ldAt_prefix {l l' : List MEv} (hp : l <+: l') {j : Nat} (h : ldAt l j) : ldAt l' j := by
  obtain ⟨t, rfl⟩ := hp
  obtain ⟨e, he, hk⟩ := h
  exact ⟨e, by rw [List.getElem?_append_left (ldAt_lt ⟨e, he, hk⟩)]; exact he, hk⟩

/-- A WELL-FORMED HART STATE: events in dynamic-index order, below the current index; every taint names an earlier
load. -/
structure RunWf (s : MSt) : Prop where
  ii_lt : ∀ e ∈ s.evs, e.ii < s.ii
  ii_mono : s.evs.Pairwise (fun a b => a.ii < b.ii)
  regs : ∀ r, ∀ j ∈ (s.regs r).2, ldAt s.evs j
  ctl : ∀ j ∈ s.ctl, ldAt s.evs j
  deps : ∀ j e, s.evs[j]? = some e → ∀ d, d ∈ e.adep ∨ d ∈ e.ddep ∨ d ∈ e.cdep → d < j ∧ ldAt s.evs d

theorem RunWf.rd {s : MSt} (hw : RunWf s) (r : Nat) : ∀ j ∈ (s.rd r).2, ldAt s.evs j := by
  unfold MSt.rd; split
  · exact hw.regs r
  · intro j hj; simp at hj

theorem wf_noemit {s s' : MSt} (hw : RunWf s) (h1 : s'.evs = s.evs) (h2 : s.ii ≤ s'.ii)
    (h3 : ∀ j ∈ s'.ctl, ldAt s.evs j) (h4 : ∀ r, ∀ j ∈ (s'.regs r).2, ldAt s.evs j) : RunWf s' := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro e he; rw [h1] at he; have := hw.ii_lt e he; omega
  · rw [h1]; exact hw.ii_mono
  · intro r j hj; rw [h1]; exact h4 r j hj
  · intro j hj; rw [h1]; exact h3 j hj
  · rw [h1]; exact hw.deps

theorem wf_emit {s s' : MSt} (hw : RunWf s) (e : MEv) (hii : e.ii = s.ii)
    (hd : ∀ d, d ∈ e.adep ∨ d ∈ e.ddep ∨ d ∈ e.cdep → ldAt s.evs d)
    (h1 : s'.evs = s.evs ++ [e]) (h2 : s'.ii = s.ii + 1)
    (h3 : ∀ j ∈ s'.ctl, ldAt s'.evs j) (h4 : ∀ r, ∀ j ∈ (s'.regs r).2, ldAt s'.evs j) : RunWf s' := by
  have hp : s.evs <+: s'.evs := h1 ▸ List.prefix_append _ _
  refine ⟨?_, ?_, h4, h3, ?_⟩
  · intro e' he'; rw [h1, List.mem_append, List.mem_singleton] at he'
    rcases he' with he' | rfl
    · have := hw.ii_lt e' he'; omega
    · omega
  · rw [h1, List.pairwise_append]
    refine ⟨hw.ii_mono, List.pairwise_singleton _ _, ?_⟩
    intro a ha b hb; rw [List.mem_singleton] at hb; subst hb; rw [hii]; exact hw.ii_lt a ha
  · intro j e' hj d hdd
    rw [h1] at hj
    rcases Nat.lt_or_ge j s.evs.length with hl | hl
    · rw [List.getElem?_append_left hl] at hj
      obtain ⟨h5, h6⟩ := hw.deps j e' hj d hdd
      exact ⟨h5, ldAt_prefix hp h6⟩
    · have hj' := hj
      rw [List.getElem?_append_right hl] at hj'
      have hj0 : j - s.evs.length = 0 := by
        rcases Nat.eq_zero_or_pos (j - s.evs.length) with h | h
        · exact h
        · rw [List.getElem?_eq_none (by simp; omega)] at hj'; cases hj'
      rw [hj0] at hj'; simp at hj'; subst hj'
      have := hd d hdd
      exact ⟨by have := ldAt_lt this; omega, ldAt_prefix hp this⟩

theorem ldAt_snoc (l : List MEv) (e : MEv) (hk : e.kind = .ld) : ldAt (l ++ [e]) l.length :=
  ⟨e, by simp, hk⟩

/-- ONE STEP keeps well-formedness, and its effect on the event list and the control taint. -/
theorem exec_wf (sz h : Nat) (V : EvId → Nat) {s : MSt} (hw : RunWf s) (i : MI) :
    RunWf (exec sz h V s i) := by
  have hrd := hw.rd
  cases i with
  | alui op rd rs1 imm =>
    rcases h1 : s.rd rs1 with ⟨v1, t1⟩
    simp only [exec, h1]
    obtain ⟨_, he, hi, hc⟩ := wr_same s rd (op.eval v1 (imm % two64), t1)
    refine wf_noemit hw (by simp [MSt.adv, he]) (by simp [MSt.adv, hi]) (by simp [MSt.adv, hc]; exact hw.ctl) ?_
    intro r j hj
    simp only [MSt.adv, regs_wr] at hj
    split at hj
    · exact hrd rs1 j (by rw [h1]; exact hj)
    · exact hw.regs r j hj
  | alu op rd rs1 rs2 =>
    rcases h1 : s.rd rs1 with ⟨v1, t1⟩
    rcases h2 : s.rd rs2 with ⟨v2, t2⟩
    simp only [exec, h1, h2]
    obtain ⟨_, he, hi, hc⟩ := wr_same s rd (op.eval v1 v2, t1 ++ t2)
    refine wf_noemit hw (by simp [MSt.adv, he]) (by simp [MSt.adv, hi]) (by simp [MSt.adv, hc]; exact hw.ctl) ?_
    intro r j hj
    simp only [MSt.adv, regs_wr] at hj
    split at hj
    · rcases List.mem_append.1 hj with hj | hj
      · exact hrd rs1 j (by rw [h1]; exact hj)
      · exact hrd rs2 j (by rw [h2]; exact hj)
    · exact hw.regs r j hj
  | load sgn rd rs1 off =>
    rcases h1 : s.rd rs1 with ⟨v1, t1⟩
    simp only [exec, h1]
    refine wf_emit hw ⟨.ld, s.ii, MAlu.add.eval v1 (off % two64), V (h, s.evs.length) % 2 ^ (8 * sz), t1, [],
      s.ctl⟩ rfl ?_ ?_ ?_ ?_ ?_
    · intro d hd
      simp only [List.not_mem_nil, false_or] at hd
      rcases hd with hd | hd
      · exact hrd rs1 d (by rw [h1]; exact hd)
      · exact hw.ctl d hd
    · simp [MSt.adv, (wr_same _ _ _).2.1, MSt.emit]
    · simp [MSt.adv, (wr_same _ _ _).2.2.1, MSt.emit]
    · simp only [MSt.adv, (wr_same _ _ _).2.2.2, (wr_same _ _ _).2.1, MSt.emit]
      intro j hj; exact ldAt_prefix (List.prefix_append _ _) (hw.ctl j hj)
    · simp only [MSt.adv, (wr_same _ _ _).2.1, MSt.emit, regs_wr]
      intro r j hj
      split at hj
      · simp only [List.mem_singleton] at hj; subst hj; exact ldAt_snoc _ _ rfl
      · exact ldAt_prefix (List.prefix_append _ _) (hw.regs r j hj)
  | store rs2 rs1 off =>
    rcases h1 : s.rd rs1 with ⟨v1, t1⟩
    rcases h2 : s.rd rs2 with ⟨v2, t2⟩
    simp only [exec, h1, h2]
    refine wf_emit hw ⟨.st, s.ii, MAlu.add.eval v1 (off % two64), v2 % 2 ^ (8 * sz), t1, t2, s.ctl⟩ rfl ?_ rfl rfl
      ?_ ?_
    · intro d hd
      rcases hd with hd | hd | hd
      · exact hrd rs1 d (by rw [h1]; exact hd)
      · exact hrd rs2 d (by rw [h2]; exact hd)
      · exact hw.ctl d hd
    · intro j hj; exact ldAt_prefix (List.prefix_append _ _) (hw.ctl j hj)
    · intro r j hj; exact ldAt_prefix (List.prefix_append _ _) (hw.regs r j hj)
  | fence f =>
    simp only [exec]
    refine wf_emit hw ⟨.fence f, s.ii, 0, 0, [], [], []⟩ rfl ?_ rfl rfl ?_ ?_
    · intro d hd; simp at hd
    · intro j hj; exact ldAt_prefix (List.prefix_append _ _) (hw.ctl j hj)
    · intro r j hj; exact ldAt_prefix (List.prefix_append _ _) (hw.regs r j hj)
  | br c rs1 rs2 tgt =>
    rcases h1 : s.rd rs1 with ⟨v1, t1⟩
    rcases h2 : s.rd rs2 with ⟨v2, t2⟩
    simp only [exec, h1, h2]
    refine wf_noemit hw rfl (by simp) ?_ hw.regs
    intro j hj
    simp only [List.mem_append] at hj
    rcases hj with (hj | hj) | hj
    · exact hw.ctl j hj
    · exact hrd rs1 j (by rw [h1]; exact hj)
    · exact hrd rs2 j (by rw [h2]; exact hj)
  | jmp tgt => exact wf_noemit hw rfl (by simp [exec]) hw.ctl hw.regs
  | nop => exact wf_noemit hw rfl (by simp [exec, MSt.adv]) hw.ctl hw.regs

/-- The effect of one step on the event list: none, or one event at the current dynamic index whose control
dependencies (a load or a store) are the control taint. -/
theorem exec_evs (sz h : Nat) (V : EvId → Nat) (s : MSt) (i : MI) :
    (exec sz h V s i).evs = s.evs ∨ ∃ e, (exec sz h V s i).evs = s.evs ++ [e] ∧
      (e.kind = .ld ∨ e.kind = .st → e.cdep = s.ctl) := by
  cases i with
  | alui op rd rs1 imm =>
    left; rcases h1 : s.rd rs1 with ⟨v1, t1⟩; simp [exec, h1, MSt.adv, (wr_same _ _ _).2.1]
  | alu op rd rs1 rs2 =>
    left; rcases h1 : s.rd rs1 with ⟨v1, t1⟩; rcases h2 : s.rd rs2 with ⟨v2, t2⟩
    simp [exec, h1, h2, MSt.adv, (wr_same _ _ _).2.1]
  | load sgn rd rs1 off =>
    right; rcases h1 : s.rd rs1 with ⟨v1, t1⟩
    exact ⟨⟨.ld, s.ii, MAlu.add.eval v1 (off % two64), V (h, s.evs.length) % 2 ^ (8 * sz), t1, [], s.ctl⟩,
      by simp [exec, h1, MSt.adv, (wr_same _ _ _).2.1, MSt.emit], fun _ => rfl⟩
  | store rs2 rs1 off =>
    right; rcases h1 : s.rd rs1 with ⟨v1, t1⟩; rcases h2 : s.rd rs2 with ⟨v2, t2⟩
    exact ⟨⟨.st, s.ii, MAlu.add.eval v1 (off % two64), v2 % 2 ^ (8 * sz), t1, t2, s.ctl⟩,
      by simp [exec, h1, h2, MSt.adv, MSt.emit], fun _ => rfl⟩
  | fence f =>
    right; exact ⟨⟨.fence f, s.ii, 0, 0, [], [], []⟩, by simp [exec, MSt.adv, MSt.emit],
      fun h => by rcases h with h | h <;> cases h⟩
  | br c rs1 rs2 tgt =>
    left; rcases h1 : s.rd rs1 with ⟨v1, t1⟩; rcases h2 : s.rd rs2 with ⟨v2, t2⟩; simp [exec, h1, h2]
  | jmp tgt => left; rfl
  | nop => left; rfl

theorem exec_ctl (sz h : Nat) (V : EvId → Nat) (s : MSt) (i : MI) : s.ctl <+: (exec sz h V s i).ctl := by
  cases i with
  | alui op rd rs1 imm =>
    rcases h1 : s.rd rs1 with ⟨v1, t1⟩; simp [exec, h1, MSt.adv, (wr_same _ _ _).2.2.2]
  | alu op rd rs1 rs2 =>
    rcases h1 : s.rd rs1 with ⟨v1, t1⟩; rcases h2 : s.rd rs2 with ⟨v2, t2⟩
    simp [exec, h1, h2, MSt.adv, (wr_same _ _ _).2.2.2]
  | load sgn rd rs1 off =>
    rcases h1 : s.rd rs1 with ⟨v1, t1⟩; simp [exec, h1, MSt.adv, (wr_same _ _ _).2.2.2, MSt.emit]
  | store rs2 rs1 off =>
    rcases h1 : s.rd rs1 with ⟨v1, t1⟩; rcases h2 : s.rd rs2 with ⟨v2, t2⟩
    simp [exec, h1, h2, MSt.adv, MSt.emit]
  | fence f => simp [exec, MSt.adv, MSt.emit]
  | br c rs1 rs2 tgt =>
    rcases h1 : s.rd rs1 with ⟨v1, t1⟩; rcases h2 : s.rd rs2 with ⟨v2, t2⟩
    simp only [exec, h1, h2, List.append_assoc]; exact List.prefix_append _ _
  | jmp tgt => exact List.prefix_refl _
  | nop => exact List.prefix_refl _

/-! ## 3. Runs -/

theorem mstep_wf (P : MProg) (V : EvId → Nat) (h : Nat) {s : MSt} (hw : RunWf s) : RunWf (mstep P V h s) := by
  unfold mstep; split
  · exact exec_wf _ _ _ hw _
  · exact hw

theorem mstep_evs (P : MProg) (V : EvId → Nat) (h : Nat) (s : MSt) :
    (mstep P V h s).evs = s.evs ∨ ∃ e, (mstep P V h s).evs = s.evs ++ [e] ∧
      (e.kind = .ld ∨ e.kind = .st → e.cdep = s.ctl) := by
  unfold mstep; split
  · exact exec_evs _ _ _ _ _
  · exact .inl rfl

theorem mstep_ctl (P : MProg) (V : EvId → Nat) (h : Nat) (s : MSt) : s.ctl <+: (mstep P V h s).ctl := by
  unfold mstep; split
  · exact exec_ctl _ _ _ _ _
  · exact List.prefix_refl _

theorem init_wf (P : MProg) (h : Nat) : RunWf (P.init h) :=
  ⟨by simp [MProg.init], by simp [MProg.init], by simp [MProg.init], by simp [MProg.init],
    by simp [MProg.init]⟩

theorem mrun_wf (P : MProg) (V : EvId → Nat) (h : Nat) : ∀ k, RunWf (mrun P V h k)
  | 0 => init_wf P h
  | k + 1 => mstep_wf P V h (mrun_wf P V h k)

theorem mstep_prefix (P : MProg) (V : EvId → Nat) (h : Nat) (s : MSt) : s.evs <+: (mstep P V h s).evs := by
  rcases mstep_evs P V h s with he | ⟨e, he, _⟩
  · rw [he]; exact List.prefix_refl _
  · rw [he]; exact List.prefix_append _ _

theorem mrun_mono (P : MProg) (V : EvId → Nat) (h : Nat) {k k' : Nat} (hk : k ≤ k') :
    (mrun P V h k).evs <+: (mrun P V h k').evs := by
  induction k' with
  | zero => rw [Nat.le_zero.1 hk]; exact List.prefix_refl _
  | succ k' ih =>
    rcases Nat.lt_or_eq_of_le hk with hlt | heq
    · exact (ih (by omega)).trans (mstep_prefix P V h _)
    · rw [heq]; exact List.prefix_refl _

theorem mrun_ctl (P : MProg) (V : EvId → Nat) (h : Nat) {k k' : Nat} (hk : k ≤ k') :
    (mrun P V h k).ctl <+: (mrun P V h k').ctl := by
  induction k' with
  | zero => rw [Nat.le_zero.1 hk]; exact List.prefix_refl _
  | succ k' ih =>
    rcases Nat.lt_or_eq_of_le hk with hlt | heq
    · exact (ih (by omega)).trans (mstep_ctl P V h _)
    · rw [heq]; exact List.prefix_refl _

theorem mrun_len_succ (P : MProg) (V : EvId → Nat) (h k : Nat) :
    (mrun P V h (k + 1)).evs.length ≤ (mrun P V h k).evs.length + 1 := by
  show (mstep P V h (mrun P V h k)).evs.length ≤ _
  rcases mstep_evs P V h (mrun P V h k) with he | ⟨e, he, _⟩ <;> rw [he] <;> simp

/-- Every event's value is an `sz`-byte word. -/
theorem exec_v (sz h : Nat) (V : EvId → Nat) {s : MSt} (hs : ∀ e ∈ s.evs, e.v < 2 ^ (8 * sz))
    (i : MI) : ∀ e ∈ (exec sz h V s i).evs, e.v < 2 ^ (8 * sz) := by
  have hp : 0 < 2 ^ (8 * sz) := Nat.two_pow_pos _
  cases i with
  | alui op rd rs1 imm =>
    rcases h1 : s.rd rs1 with ⟨v1, t1⟩; simp only [exec, h1, MSt.adv, (wr_same _ _ _).2.1]; exact hs
  | alu op rd rs1 rs2 =>
    rcases h1 : s.rd rs1 with ⟨v1, t1⟩; rcases h2 : s.rd rs2 with ⟨v2, t2⟩
    simp only [exec, h1, h2, MSt.adv, (wr_same _ _ _).2.1]; exact hs
  | load sgn rd rs1 off =>
    rcases h1 : s.rd rs1 with ⟨v1, t1⟩
    simp only [exec, h1, MSt.adv, (wr_same _ _ _).2.1, MSt.emit]
    intro e he; rcases List.mem_append.1 he with he | he
    · exact hs e he
    · rw [List.mem_singleton] at he; subst he; exact Nat.mod_lt _ hp
  | store rs2 rs1 off =>
    rcases h1 : s.rd rs1 with ⟨v1, t1⟩; rcases h2 : s.rd rs2 with ⟨v2, t2⟩
    simp only [exec, h1, h2, MSt.adv, MSt.emit]
    intro e he; rcases List.mem_append.1 he with he | he
    · exact hs e he
    · rw [List.mem_singleton] at he; subst he; exact Nat.mod_lt _ hp
  | fence f =>
    simp only [exec, MSt.adv, MSt.emit]
    intro e he; rcases List.mem_append.1 he with he | he
    · exact hs e he
    · rw [List.mem_singleton] at he; subst he; exact hp
  | br c rs1 rs2 tgt =>
    rcases h1 : s.rd rs1 with ⟨v1, t1⟩; rcases h2 : s.rd rs2 with ⟨v2, t2⟩; simp only [exec, h1, h2]; exact hs
  | jmp tgt => exact hs
  | nop => exact hs

theorem mrun_v (P : MProg) (V : EvId → Nat) (h : Nat) : ∀ k, ∀ e ∈ (mrun P V h k).evs, e.v < 2 ^ (8 * P.sz)
  | 0 => by simp [mrun, MProg.init]
  | k + 1 => by
    show ∀ e ∈ (mstep P V h (mrun P V h k)).evs, _
    unfold mstep; split
    · exact exec_v _ _ _ (mrun_v P V h k) _
    · exact mrun_v P V h k

/-- Every later load or store has every earlier control taint among its control dependencies. -/
theorem mrun_cdep (P : MProg) (V : EvId → Nat) (h k : Nat) :
    ∀ k', k ≤ k' → ∀ j e, (mrun P V h k).evs.length ≤ j → (mrun P V h k').evs[j]? = some e →
      (e.kind = .ld ∨ e.kind = .st) → ∀ x ∈ (mrun P V h k).ctl, x ∈ e.cdep := by
  intro k' hk
  induction k' with
  | zero =>
    intro j e hj he; rw [Nat.le_zero.1 hk] at hj
    have := (List.getElem?_eq_some_iff.1 he).1; omega
  | succ k' ih =>
    intro j e hj he hk2
    rcases Nat.lt_or_eq_of_le hk with hlt | heq
    · show ∀ x ∈ _, x ∈ e.cdep
      have hev := mstep_evs P V h (mrun P V h k')
      change (mstep P V h (mrun P V h k')).evs[j]? = some e at he
      rcases hev with hev | ⟨e', hev, hc⟩
      · rw [hev] at he; exact ih (by omega) j e hj he hk2
      · rw [hev] at he
        rcases Nat.lt_or_ge j (mrun P V h k').evs.length with hl | hl
        · rw [List.getElem?_append_left hl] at he; exact ih (by omega) j e hj he hk2
        · rw [List.getElem?_append_right hl] at he
          have hj0 : j - (mrun P V h k').evs.length = 0 := by
            rcases Nat.eq_zero_or_pos (j - (mrun P V h k').evs.length) with h0 | h0
            · exact h0
            · rw [List.getElem?_eq_none (by simp; omega)] at he; cases he
          rw [hj0] at he; simp at he; subst he
          rw [hc hk2]
          intro x hx; exact (mrun_ctl P V h (by omega : k ≤ k')).subset hx
    · rw [← heq] at he; have := (List.getElem?_eq_some_iff.1 he).1; omega

/-! ## 4. The axiom block -/

namespace MEvsF

variable {A : MEvs}

theorem gmo_irr (hg : A.gmoOk) (a : EvId) : ¬ A.gmo a a := hg.2.1 a
theorem gmo_trans (hg : A.gmoOk) {a b c : EvId} (h1 : A.gmo a b) (h2 : A.gmo b c) : A.gmo a c := hg.2.2.1 a b c h1 h2
theorem gmo_asymm (hg : A.gmoOk) {a b : EvId} (h1 : A.gmo a b) (h2 : A.gmo b a) : False :=
  gmo_irr hg a (gmo_trans hg h1 h2)
theorem gmo_total (hg : A.gmoOk) {a b : EvId} (ha : A.isMem a) (hb : A.isMem b) (hne : a ≠ b) :
    A.gmo a b ∨ A.gmo b a := hg.2.2.2 a b ha hb hne

theorem ld_st {e : EvId} (h1 : A.isLd e) (h2 : A.isSt e) : False := by
  unfold MEvs.isLd at h1; unfold MEvs.isSt at h2; rw [h1] at h2; cases h2

/-- `rf` is functional (gmo is a strict order). -/
theorem rf_unique (hg : A.gmoOk) {r : EvId} {o1 o2 : Option EvId} (h1 : A.rf r o1) (h2 : A.rf r o2) : o1 = o2 := by
  match o1, o2, h1, h2 with
  | none, none, _, _ => rfl
  | some w, none, h1, h2 => exact absurd h1.1 (h2 w)
  | none, some w, h1, h2 => exact absurd h2.1 (h1 w)
  | some w1, some w2, h1, h2 =>
    rcases h1.2 w2 h2.1 with h | h
    · rw [h]
    · rcases h2.2 w1 h1.1 with h' | h'
      · rw [h']
      · exact absurd (gmo_asymm hg h h') id

end MEvsF

end Weak.Mini.Cmp
