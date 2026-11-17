/-
Weak/Mini: **L5 MiniPfx — taints are sound** (mini plan rev 4 §2 L5; rvwmo.adoc:156–246: a register's value
"depends" syntactically on the loads its taint names).

Two runs of hart `h` under load values `V` and `V'` that agree (on the `sz`-byte words) at the loads of a set `B`:
as long as every control taint and every address dependency of the first run lies in `B`, the runs take the same
path — same pc, dynamic index, control taint, events up to their values (`noV`), register taints — and a register
(a load, a store) has the same value whenever its taint (the load itself, the store's data dependencies) lies in
`B` (`agree_run`).  This is what lets the cut of L5 re-source "late" loads without changing any event's address or
the hart's path.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Mini.CmpBase

namespace Weak.Mini.Pfx

open Weak.Mini Weak.Mini.Cmp

/-- An event without its value. -/
def noV (e : MEv) : MEv := { e with v := 0 }

/-- The value clause: a load's value if it is in `B`, a store's if its data dependencies are, a fence's always. -/
def VOk (B : Nat → Prop) (j : Nat) (e e' : MEv) : Prop :=
  (e.kind = .ld → B j → e.v = e'.v) ∧ (e.kind = .st → (∀ i ∈ e.ddep, B i) → e.v = e'.v) ∧
    (∀ f, e.kind = .fence f → e.v = e'.v)

/-- TWO HART STATES AGREE up to the values that depend on loads outside `B`. -/
structure Agree (B : Nat → Prop) (s s' : Weak.Mini.MSt) : Prop where
  pc : s.pc = s'.pc
  ii : s.ii = s'.ii
  ctl : s.ctl = s'.ctl
  evs : s.evs.map noV = s'.evs.map noV
  regT : ∀ r, (s.regs r).2 = (s'.regs r).2
  regV : ∀ r, (∀ i ∈ (s.regs r).2, B i) → (s.regs r).1 = (s'.regs r).1
  evV : ∀ j e e', s.evs[j]? = some e → s'.evs[j]? = some e' → VOk B j e e'

variable {B : Nat → Prop}

theorem Agree.len {s s' : Weak.Mini.MSt} (hA : Agree B s s') : s.evs.length = s'.evs.length := by
  have := congrArg List.length hA.evs; simpa using this

theorem Agree.refl (s : Weak.Mini.MSt) : Agree B s s :=
  ⟨rfl, rfl, rfl, rfl, fun _ => rfl, fun _ _ => rfl, fun j e e' h1 h2 => by
    rw [h1] at h2; cases h2; exact ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩⟩

theorem Agree.rd {s s' : Weak.Mini.MSt} (hA : Agree B s s') (r : Nat) :
    (s.rd r).2 = (s'.rd r).2 ∧ ((∀ i ∈ (s.rd r).2, B i) → (s.rd r).1 = (s'.rd r).1) := by
  unfold Weak.Mini.MSt.rd; split
  · exact ⟨hA.regT r, hA.regV r⟩
  · exact ⟨rfl, fun _ => rfl⟩

theorem agree_wr {s s' : Weak.Mini.MSt} (hA : Agree B s s') (rd : Nat) (x x' : Nat × List Nat) (ht : x.2 = x'.2)
    (hv : (∀ i ∈ x.2, B i) → x.1 = x'.1) : Agree B (s.wr rd x) (s'.wr rd x') := by
  obtain ⟨p1, e1, i1, c1⟩ := wr_same s rd x
  obtain ⟨p2, e2, i2, c2⟩ := wr_same s' rd x'
  refine ⟨by rw [p1, p2, hA.pc], by rw [i1, i2, hA.ii], by rw [c1, c2, hA.ctl], by rw [e1, e2, hA.evs], ?_, ?_,
    by rw [e1, e2]; exact hA.evV⟩
  · intro r; rw [regs_wr, regs_wr]; split
    · exact ht
    · exact hA.regT r
  · intro r; rw [regs_wr, regs_wr]; split
    · exact hv
    · exact hA.regV r

theorem agree_adv {s s' : Weak.Mini.MSt} (hA : Agree B s s') : Agree B s.adv s'.adv :=
  ⟨by simp [MSt.adv, hA.pc], by simp [MSt.adv, hA.ii], hA.ctl, hA.evs, hA.regT, hA.regV, hA.evV⟩

theorem agree_emit {s s' : Weak.Mini.MSt} (hA : Agree B s s') (e e' : MEv) (hn : noV e = noV e')
    (hv : VOk B s.evs.length e e') : Agree B (s.emit e) (s'.emit e') := by
  have hl := hA.len
  refine ⟨hA.pc, hA.ii, hA.ctl, by simp [MSt.emit, hA.evs, hn], hA.regT, hA.regV, ?_⟩
  intro j a a' h1 h2
  simp only [MSt.emit] at h1 h2
  rcases Nat.lt_or_ge j s.evs.length with hj | hj
  · rw [List.getElem?_append_left hj] at h1
    rw [List.getElem?_append_left (by omega)] at h2
    exact hA.evV j a a' h1 h2
  · rw [List.getElem?_append_right hj] at h1
    rw [List.getElem?_append_right (by omega)] at h2
    have hj0 : j - s.evs.length = 0 := by
      rcases Nat.eq_zero_or_pos (j - s.evs.length) with h | h
      · exact h
      · rw [List.getElem?_eq_none (by simp; omega)] at h1; cases h1
    rw [hj0] at h1; rw [show j - s'.evs.length = 0 by omega] at h2
    simp at h1 h2; subst h1; subst h2
    rw [show j = s.evs.length by omega]; exact hv

/-- ONE STEP keeps the agreement, if the step's control taint and its event's address dependencies lie in `B`. -/
theorem agree_exec {sz h : Nat} {V V' : EvId → Nat} (hV : ∀ i, B i → V (h, i) % 2 ^ (8 * sz) = V' (h, i) % 2 ^ (8 * sz))
    {s s' : Weak.Mini.MSt} (hA : Agree B s s') (ins : MI)
    (hc : ∀ x ∈ (exec sz h V s ins).ctl, B x) (ha : ∀ e ∈ (exec sz h V s ins).evs, ∀ x ∈ e.adep, B x) :
    Agree B (exec sz h V s ins) (exec sz h V' s' ins) := by
  have hl := hA.len
  cases ins with
  | alui op rd rs1 imm =>
    obtain ⟨t1e, v1e⟩ := hA.rd rs1
    simp only [exec]
    exact agree_adv (agree_wr hA rd _ _ t1e (fun hb => by simp only at hb ⊢; rw [v1e hb]))
  | alu op rd rs1 rs2 =>
    obtain ⟨t1e, v1e⟩ := hA.rd rs1
    obtain ⟨t2e, v2e⟩ := hA.rd rs2
    simp only [exec]
    refine agree_adv (agree_wr hA rd _ _ (by simp only; rw [t1e, t2e]) (fun hb => ?_))
    simp only at hb ⊢
    rw [v1e (fun i hi => hb i (List.mem_append_left _ hi)), v2e (fun i hi => hb i (List.mem_append_right _ hi))]
  | load sgn rd rs1 off =>
    obtain ⟨t1e, v1e⟩ := hA.rd rs1
    have hadr : ∀ i ∈ (s.rd rs1).2, B i := by
      intro i hi
      refine ha ⟨.ld, s.ii, MAlu.add.eval (s.rd rs1).1 (off % two64), V (h, s.evs.length) % 2 ^ (8 * sz),
        (s.rd rs1).2, [], s.ctl⟩ ?_ i hi
      simp [exec, MSt.adv, (wr_same _ _ _).2.1, MSt.emit]
    simp only [exec]
    refine agree_adv (agree_wr (agree_emit hA _ _ ?_ ?_) rd _ _ (by simp only; rw [hl]) ?_)
    · simp only [noV]; rw [v1e hadr, t1e, hA.ii, hA.ctl]
    · refine ⟨fun _ hb => ?_, fun h' => (by cases h'), fun _ h' => (by cases h')⟩
      simp only; rw [← hl]; exact hV _ hb
    · intro hb
      simp only at hb ⊢
      rw [← hl, hV _ (hb _ (List.mem_singleton_self _))]
  | store rs2 rs1 off =>
    obtain ⟨t1e, v1e⟩ := hA.rd rs1
    obtain ⟨t2e, v2e⟩ := hA.rd rs2
    have hadr : ∀ i ∈ (s.rd rs1).2, B i := by
      intro i hi
      refine ha ⟨.st, s.ii, MAlu.add.eval (s.rd rs1).1 (off % two64), (s.rd rs2).1 % 2 ^ (8 * sz),
        (s.rd rs1).2, (s.rd rs2).2, s.ctl⟩ ?_ i hi
      simp [exec, MSt.adv, MSt.emit]
    simp only [exec]
    refine agree_adv (agree_emit hA _ _ ?_ ?_)
    · simp only [noV]; rw [v1e hadr, t1e, t2e, hA.ii, hA.ctl]
    · refine ⟨fun h' => (by cases h'), fun _ hb => ?_, fun _ h' => (by cases h')⟩
      simp only at hb ⊢; rw [v2e hb]
  | fence f =>
    simp only [exec]
    refine agree_adv (agree_emit hA _ _ ?_ ⟨fun h' => (by cases h'), fun h' => (by cases h'), fun _ _ => rfl⟩)
    simp only [noV]; rw [hA.ii]
  | br c rs1 rs2 tgt =>
    obtain ⟨t1e, v1e⟩ := hA.rd rs1
    obtain ⟨t2e, v2e⟩ := hA.rd rs2
    have hb1 : ∀ i ∈ (s.rd rs1).2, B i := fun i hi => hc i (by simp [exec, hi])
    have hb2 : ∀ i ∈ (s.rd rs2).2, B i := fun i hi => hc i (by simp [exec, hi])
    simp only [exec]
    exact ⟨by simp only; rw [v1e hb1, v2e hb2, hA.pc], by simp only; rw [hA.ii], by simp only; rw [hA.ctl, t1e, t2e],
      hA.evs, hA.regT, hA.regV, hA.evV⟩
  | jmp tgt => exact ⟨rfl, by simp [exec, hA.ii], hA.ctl, hA.evs, hA.regT, hA.regV, hA.evV⟩
  | nop => exact agree_adv hA

/-- **THE RUNS AGREE** (file header). -/
theorem agree_run (P : MProg) {V V' : EvId → Nat} {h : Nat}
    (hV : ∀ i, B i → V (h, i) % 2 ^ (8 * P.sz) = V' (h, i) % 2 ^ (8 * P.sz)) :
    ∀ k, (∀ x ∈ (mrun P V h k).ctl, B x) → (∀ e ∈ (mrun P V h k).evs, ∀ x ∈ e.adep, B x) →
      Agree B (mrun P V h k) (mrun P V' h k)
  | 0, _, _ => Agree.refl _
  | k + 1, hc, ha => by
    have hA := agree_run P hV k (fun x hx => hc x ((mstep_ctl P V h _).subset hx))
      (fun e he => ha e ((mstep_prefix P V h _).subset he))
    show Agree B (mstep P V h (mrun P V h k)) (mstep P V' h (mrun P V' h k))
    change ∀ x ∈ (mstep P V h (mrun P V h k)).ctl, B x at hc
    change ∀ e ∈ (mstep P V h (mrun P V h k)).evs, ∀ x ∈ e.adep, B x at ha
    unfold mstep at hc ha ⊢
    rw [← hA.pc]
    split
    · rename_i ins _
      rw [‹(P.prog h)[(mrun P V h k).pc]? = some ins›] at hc ha
      exact agree_exec hV hA ins hc ha
    · exact hA

end Weak.Mini.Pfx
