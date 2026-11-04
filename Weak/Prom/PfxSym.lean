/-
Weak/Prom: **S3d — the loop front end's symbolic run** (plan rev 7 §8 S3d).  Facts about `stepL` runs of programs
in the S3a scope (`instrS3a`: ALU, plain loads/stores, FENCE, FENCE.TSO, branches, jumps, `csrr`, `fence.i`, `nop`;
CmpDefs.lean), used by the prefix lemma (PfxMain.lean):
* `stepL_ok` — one step keeps `SymWf` (CmpSym.lean: program order is the order of `ii`, every dependency is an
  earlier memory operation) and `VarsInv` (every expression's load variables lie inside the matching taint: a
  register's within its taint, an address's within the access's address dependencies, a stored value's within its
  data dependencies, a path condition's within the control taint — RefProg.lean header, rvwmo.adoc:210–246); it
  only APPENDS events, conditions and control taint; a memory operation is emitted alone, with its control
  dependencies = the current control taint, by a step that changes neither the control taint nor the conditions.
* Along an execution (`IExec.conforms`): every state is well-formed, event lists grow by appending (`evs_mono`),
  `E.sev` is the event of any state that has it (`sev_eq`), every event is emitted by one step (`emitAt`), and the
  event-level facts `po_idx`, `idx_po`, `deps_mem`, `cdep_mono`, `addr_vars`, `wval_vars`, `cut_conds`, `fragEv`.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.PfxDefs

namespace Weak.Prom.Pfx

open Weak.Prom.Ref
open Weak.Prom.Cmp

/-! ## 1. One step -/

/-- Every expression's load variables lie inside the matching taint (hart `h`'s own events). -/
structure VarsInv (h : Nat) (s : SSt) : Prop where
  regs : ∀ r, ∀ x ∈ (s.rd r).1.vars, x.1 = h ∧ x.2 ∈ (s.rd r).2
  conds : ∀ c ∈ s.conds, ∀ x ∈ c.2.1.vars ++ c.2.2.1.vars, x.1 = h ∧ x.2 ∈ s.ctl
  evs : ∀ se ∈ s.evs, (∀ x ∈ se.addr.vars, x.1 = h ∧ x.2 ∈ se.sk.adep) ∧
    (∀ x ∈ se.wval.vars, x.1 = h ∧ x.2 ∈ se.sk.ddep)

/-- An event of the S3a scope: a plain load, a plain store or a fence (no dependencies). -/
def FragEv (se : SEv) : Prop :=
  se.sk.kind = .ld ∨ se.sk.kind = .st ∨ ∃ f, se.sk.kind = .fence f ∧ se.sk.adep = [] ∧ se.sk.ddep = []

/-- What one step guarantees. -/
structure StepOkL (h : Nat) (s s' : SSt) : Prop where
  wf : SymWf s'
  vars : VarsInv h s'
  ctl : s.ctl <+: s'.ctl
  conds : s.conds <+: s'.conds
  new : ∃ new, s'.evs = s.evs ++ new ∧ ∀ se ∈ new, (∀ d ∈ se.sk.cdep, d ∈ s.ctl) ∧ FragEv se ∧
    (se.sk.kind.isMem = true → new = [se] ∧ s'.ctl = s.ctl ∧ s'.conds = s.conds ∧ se.sk.cdep = s.ctl)

theorem varsInv_init (T : Test) (h : Nat) : VarsInv h (T.init h) := by
  refine ⟨fun r x hx => ?_, fun c hc => by simp [Test.init] at hc, fun se hse => by simp [Test.init] at hse⟩
  exfalso
  unfold SSt.rd Test.init at hx
  split at hx
  · simp [Ex.vars] at hx
  · simp only [List.getElem?_map] at hx
    rcases hy : (List.range 32)[r]? with _ | y <;> simp [hy, Ex.vars] at hx

theorem regs_wr {h : Nat} {s : SSt} (hr : ∀ r, ∀ x ∈ (s.rd r).1.vars, x.1 = h ∧ x.2 ∈ (s.rd r).2) (rd : Nat)
    {v : Ex × List Nat} (hv : ∀ x ∈ v.1.vars, x.1 = h ∧ x.2 ∈ v.2) :
    ∀ r, ∀ x ∈ ((s.wr rd v).rd r).1.vars, x.1 = h ∧ x.2 ∈ ((s.wr rd v).rd r).2 := by
  intro r x hx
  rw [SSt.rd_wr] at hx ⊢
  split
  · rename_i hc; rw [if_pos hc] at hx; exact hv x hx
  · rename_i hc; rw [if_neg hc] at hx; exact hr r x hx

theorem stepOk_same {h : Nat} {s s' : SSt} (hw : SymWf s') (hv : VarsInv h s') (he : s'.evs = s.evs)
    (hc : s'.ctl = s.ctl) (hd : s'.conds = s.conds) : StepOkL h s s' :=
  ⟨hw, hv, hc ▸ List.prefix_refl _, hd ▸ List.prefix_refl _, ⟨[], by simp [he], by simp⟩⟩

/-- **ONE STEP of the loop front end** on an S3a instruction. -/
theorem stepL_ok (h n : Nat) {s s' : SSt} (hw : SymWf s) (hv : VarsInv h s) (i : Instr)
    (hi : instrS3a i = true)
    (hs : stepL h n s i = .next s' ∨ ∃ t f, stepL h n s i = .fork t f ∧ (s' = t ∨ s' = f)) :
    StepOkL h s s' := by
  have wfN : ∀ s'', stepI h n s i = .next s'' → SymWf s'' := (symWf_step h n hw i).1
  cases i with
  | alui op rd rs1 imm =>
    rcases hs with hs | ⟨t, f, hs, _⟩
    · have hw' := wfN s' hs
      simp only [stepL, stepI, StepR.next.injEq] at hs; subst hs
      refine stepOk_same hw' ⟨?_, ?_, ?_⟩ (by simp) (by simp) (by simp)
      · intro r x hx
        simp only [SSt.adv_rd] at hx ⊢
        exact regs_wr hv.regs rd (fun x hx => by simp [Ex.vars] at hx; exact hv.regs rs1 x hx) r x hx
      · intro c hc; simpa using hv.conds c (by simpa using hc)
      · intro se hse; exact hv.evs se (by simpa using hse)
    · simp [stepL, stepI] at hs
  | alu op rd rs1 rs2 =>
    rcases hs with hs | ⟨t, f, hs, _⟩
    · have hw' := wfN s' hs
      simp only [stepL, stepI, StepR.next.injEq] at hs; subst hs
      refine stepOk_same hw' ⟨?_, ?_, ?_⟩ (by simp) (by simp) (by simp)
      · intro r x hx
        simp only [SSt.adv_rd] at hx ⊢
        refine regs_wr hv.regs rd (fun x hx => ?_) r x hx
        simp only [Ex.vars, List.mem_append] at hx ⊢
        rcases hx with hx | hx
        · exact ⟨(hv.regs rs1 x hx).1, Or.inl (hv.regs rs1 x hx).2⟩
        · exact ⟨(hv.regs rs2 x hx).1, Or.inr (hv.regs rs2 x hx).2⟩
      · intro c hc; simpa using hv.conds c (by simpa using hc)
      · intro se hse; exact hv.evs se (by simpa using hse)
    · simp [stepL, stepI] at hs
  | load sz sgn rd rs1 off =>
    rcases hs with hs | ⟨t, f, hs, _⟩
    · have hw' := wfN s' hs
      simp only [stepL, stepI, StepR.next.injEq] at hs; subst hs
      refine ⟨hw', ⟨?_, ?_, ?_⟩, by simp [List.prefix_refl], by simp [List.prefix_refl],
        ⟨[_], (by simp only [SSt.adv_evs, SSt.wr_evs, SSt.emit_evs] <;> rfl), ?_⟩⟩
      · intro r x hx
        simp only [SSt.adv_rd, SSt.emit_evs] at hx ⊢
        refine regs_wr (fun r x hx => by simpa using hv.regs r x hx) rd (fun x hx => ?_) r x hx
        simp [Ex.vars] at hx; subst hx; simp
      · intro c hc; simpa using hv.conds c (by simpa using hc)
      · intro se hse
        simp only [SSt.adv_evs, SSt.wr_evs, SSt.emit_evs, List.mem_append, List.mem_singleton] at hse
        rcases hse with hse | rfl
        · exact hv.evs se hse
        · refine ⟨fun x hx => ?_, fun x hx => by simp [Ex.vars] at hx⟩
          simp only [Ex.vars, List.append_nil] at hx
          exact hv.regs rs1 x hx
      · intro se hse
        simp only [List.mem_singleton] at hse; subst hse
        refine ⟨fun d hd => hd, Or.inl rfl, fun _ => ⟨rfl, by simp, by simp, rfl⟩⟩
    · simp [stepL, stepI] at hs
  | store sz rs2 rs1 off =>
    rcases hs with hs | ⟨t, f, hs, _⟩
    · have hw' := wfN s' hs
      simp only [stepL, stepI, StepR.next.injEq] at hs; subst hs
      refine ⟨hw', ⟨?_, ?_, ?_⟩, by simp [List.prefix_refl], by simp [List.prefix_refl],
        ⟨[_], (by simp only [SSt.adv_evs, SSt.wr_evs, SSt.emit_evs] <;> rfl), ?_⟩⟩
      · intro r x hx
        simp only [SSt.adv_rd, SSt.emit_rd] at hx ⊢
        exact hv.regs r x hx
      · intro c hc; simpa using hv.conds c (by simpa using hc)
      · intro se hse
        simp only [SSt.adv_evs, SSt.emit_evs, List.mem_append, List.mem_singleton] at hse
        rcases hse with hse | rfl
        · exact hv.evs se hse
        · refine ⟨fun x hx => ?_, fun x hx => hv.regs rs2 x hx⟩
          simp only [Ex.vars, List.append_nil] at hx
          exact hv.regs rs1 x hx
      · intro se hse
        simp only [List.mem_singleton] at hse; subst hse
        refine ⟨fun d hd => hd, Or.inr (Or.inl rfl), fun _ => ⟨rfl, by simp, by simp, rfl⟩⟩
    · simp [stepL, stepI] at hs
  | fence fs =>
    rcases hs with hs | ⟨t, f, hs, _⟩
    · have hw' := wfN s' hs
      simp only [stepL, stepI, StepR.next.injEq] at hs; subst hs
      refine ⟨hw', ⟨?_, ?_, ?_⟩, by simp [List.prefix_refl], by simp [List.prefix_refl],
        ⟨[_], (by simp only [SSt.adv_evs, SSt.wr_evs, SSt.emit_evs] <;> rfl), ?_⟩⟩
      · intro r x hx; simpa using hv.regs r x (by simpa using hx)
      · intro c hc; simpa using hv.conds c (by simpa using hc)
      · intro se hse
        simp only [SSt.adv_evs, SSt.emit_evs, List.mem_append, List.mem_singleton] at hse
        rcases hse with hse | rfl
        · exact hv.evs se hse
        · exact ⟨fun x hx => by simp [Ex.vars] at hx, fun x hx => by simp [Ex.vars] at hx⟩
      · intro se hse
        simp only [List.mem_singleton] at hse; subst hse
        exact ⟨fun d hd => by simp at hd, Or.inr (Or.inr ⟨fs, rfl, rfl, rfl⟩), fun hm => by simp [Kind.isMem] at hm⟩
    · simp [stepL, stepI] at hs
  | fenceTso =>
    rcases hs with hs | ⟨t, f, hs, _⟩
    · have hw' := wfN s' hs
      simp only [stepL, stepI, StepR.next.injEq] at hs; subst hs
      refine ⟨hw', ⟨?_, ?_, ?_⟩, by simp [List.prefix_refl], by simp [List.prefix_refl],
        ⟨[_, _], (by simp only [SSt.adv_evs, SSt.emit_evs, List.append_assoc] <;> rfl), ?_⟩⟩
      · intro r x hx; simpa using hv.regs r x (by simpa using hx)
      · intro c hc; simpa using hv.conds c (by simpa using hc)
      · intro se hse
        simp only [SSt.adv_evs, SSt.emit_evs, List.mem_append, List.mem_singleton] at hse
        rcases hse with (hse | rfl) | rfl
        · exact hv.evs se hse
        · exact ⟨fun x hx => by simp [Ex.vars] at hx, fun x hx => by simp [Ex.vars] at hx⟩
        · exact ⟨fun x hx => by simp [Ex.vars] at hx, fun x hx => by simp [Ex.vars] at hx⟩
      · intro se hse
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hse
        rcases hse with rfl | rfl
        · exact ⟨fun d hd => by simp at hd, Or.inr (Or.inr ⟨_, rfl, rfl, rfl⟩), fun hm => by simp [Kind.isMem] at hm⟩
        · exact ⟨fun d hd => by simp at hd, Or.inr (Or.inr ⟨_, rfl, rfl, rfl⟩), fun hm => by simp [Kind.isMem] at hm⟩
    · simp [stepL, stepI] at hs
  | br c rs1 rs2 tgt =>
    rcases hs with hs | ⟨t, f, hs, hst⟩
    · simp only [stepL] at hs; split at hs <;> cases hs
    · simp only [stepL] at hs
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
        have hwf : ∀ (s'' : SSt), s''.evs = s.evs → s''.ii = s.ii + 1 → s''.regs = s.regs →
            s''.ctl = s.ctl ++ (s.rd rs1).2 ++ (s.rd rs2).2 → SymWf s'' := by
          intro s'' he hii hr hc
          have hrd : ∀ r, s''.rd r = s.rd r := fun r => by unfold SSt.rd; rw [hr]
          exact symWf_mk hw [] (by simp [he]) (by omega) (by simp) (by simp) (by simp)
            (fun r d hd => by rw [hrd] at hd; simpa [he] using hw.taint r d hd)
            (fun d hd => by rw [hc] at hd; simpa [he] using hct d hd) (by rw [hr]; exact hw.len)
        have hvi : ∀ (s'' : SSt) (b : Bool), s''.evs = s.evs → s''.regs = s.regs →
            s''.ctl = s.ctl ++ (s.rd rs1).2 ++ (s.rd rs2).2 →
            s''.conds = s.conds ++ [(c, (s.rd rs1).1, (s.rd rs2).1, b)] → VarsInv h s'' := by
          intro s'' b he hr hc hd
          have hrd : ∀ r, s''.rd r = s.rd r := fun r => by unfold SSt.rd; rw [hr]
          refine ⟨fun r x hx => by rw [hrd] at hx ⊢; exact hv.regs r x hx, fun cc hcc x hx => ?_,
            fun se hse => hv.evs se (by rw [he] at hse; exact hse)⟩
          rw [hc]
          rw [hd] at hcc
          rcases List.mem_append.1 hcc with hcc | hcc
          · have := hv.conds cc hcc x hx
            exact ⟨this.1, by simp [this.2]⟩
          · simp only [List.mem_singleton] at hcc; subst hcc
            simp only [List.mem_append] at hx
            rcases hx with hx | hx
            · exact ⟨(hv.regs rs1 x hx).1, by simp [(hv.regs rs1 x hx).2]⟩
            · exact ⟨(hv.regs rs2 x hx).1, by simp [(hv.regs rs2 x hx).2]⟩
        rcases hst with rfl | rfl
        · exact ⟨hwf _ rfl rfl rfl rfl, hvi _ true rfl rfl rfl rfl, by simp [List.prefix_append],
            by simp [List.prefix_append], ⟨[], by simp, by simp⟩⟩
        · exact ⟨hwf _ rfl rfl rfl rfl, hvi _ false rfl rfl rfl rfl, by simp [List.prefix_append],
            by simp [List.prefix_append], ⟨[], by simp, by simp⟩⟩
  | jmp tgt =>
    rcases hs with hs | ⟨t, f, hs, _⟩
    · simp only [stepL] at hs
      split at hs
      · cases hs
      · simp only [StepR.next.injEq] at hs; subst hs
        have hrd : ∀ r, ({ s with pc := tgt, ii := s.ii + 1 } : SSt).rd r = s.rd r := fun r => rfl
        refine stepOk_same ?_ ⟨fun r x hx => hv.regs r x hx, fun cc hcc => hv.conds cc hcc,
          fun se hse => hv.evs se hse⟩ rfl rfl rfl
        exact symWf_mk hw [] (by simp) (by simp) (by simp) (by simp) (by simp)
          (fun r d hd => by simpa using hw.taint r d hd) (fun d hd => by simpa using hw.ctl d hd) hw.len
    · simp only [stepL] at hs; split at hs <;> cases hs
  | csrr rd v =>
    rcases hs with hs | ⟨t, f, hs, _⟩
    · have hw' := wfN s' hs
      simp only [stepL, stepI, StepR.next.injEq] at hs; subst hs
      refine stepOk_same hw' ⟨?_, ?_, ?_⟩ (by simp) (by simp) (by simp)
      · intro r x hx
        simp only [SSt.adv_rd] at hx ⊢
        exact regs_wr hv.regs rd (fun x hx => by simp [Ex.vars] at hx) r x hx
      · intro c hc; simpa using hv.conds c (by simpa using hc)
      · intro se hse; exact hv.evs se (by simpa using hse)
    · simp [stepL, stepI] at hs
  | fencei =>
    rcases hs with hs | ⟨t, f, hs, _⟩
    · have hw' := wfN s' hs
      simp only [stepL, stepI, StepR.next.injEq] at hs; subst hs
      refine stepOk_same hw' ⟨?_, ?_, ?_⟩ (by simp) (by simp) (by simp)
      · intro r x hx; simpa using hv.regs r x (by simpa using hx)
      · intro c hc; simpa using hv.conds c (by simpa using hc)
      · intro se hse; exact hv.evs se (by simpa using hse)
    · simp [stepL, stepI] at hs
  | nop =>
    rcases hs with hs | ⟨t, f, hs, _⟩
    · have hw' := wfN s' hs
      simp only [stepL, stepI, StepR.next.injEq] at hs; subst hs
      refine stepOk_same hw' ⟨?_, ?_, ?_⟩ (by simp) (by simp) (by simp)
      · intro r x hx; simpa using hv.regs r x (by simpa using hx)
      · intro c hc; simpa using hv.conds c (by simpa using hc)
      · intro se hse; exact hv.evs se (by simpa using hse)
    · simp [stepL, stepI] at hs
  | loadAq _ _ _ _ => simp [instrS3a] at hi
  | storeRl _ _ _ _ => simp [instrS3a] at hi
  | loadAqPc _ _ _ _ => simp [instrS3a] at hi
  | storeRlPc _ _ _ _ => simp [instrS3a] at hi
  | lr _ _ _ _ _ => simp [instrS3a] at hi
  | sc _ _ _ _ _ _ => simp [instrS3a] at hi
  | amo _ _ _ _ _ _ _ => simp [instrS3a] at hi

/-! ## 2. Along an execution -/

/-- Every program of the test is in the S3a instruction scope (part of `progS3aB`). -/
def FragT (T : Test) : Prop := ∀ h, ∀ i ∈ T.prog h, instrS3a i = true

theorem fragT_of {T : Test} (hT : progS3aB T = true) : FragT T := by
  intro h i hi
  simp only [progS3aB, Bool.and_eq_true, List.all_eq_true] at hT
  unfold Test.prog at hi
  cases hh : T.harts[h]? with
  | none => rw [hh] at hi; simp at hi
  | some p =>
    rw [hh] at hi
    exact hT.1.2 p (List.mem_of_getElem? hh) i hi

section run

variable {E : IExec} (hc : E.conforms) (hf : FragT E.T) {h : Nat} (hh : h < E.T.harts.length)
include hc hf hh

theorem run_inv : ∀ k, SymWf (E.st h k) ∧ VarsInv h (E.st h k) ∧ StepOkL h (E.st h k) (E.st h (k + 1)) := by
  have step : ∀ k, SymWf (E.st h k) → VarsInv h (E.st h k) → StepOkL h (E.st h k) (E.st h (k + 1)) := by
    intro k hw hv
    rcases (hc h hh).2 k with ⟨_, he⟩ | ⟨i, hi, hs⟩
    · rw [he]; exact stepOk_same hw hv rfl rfl rfl
    · exact stepL_ok h _ hw hv i (hf h i (List.mem_of_getElem? hi)) hs
  intro k
  induction k with
  | zero =>
    have h0 := (hc h hh).1
    have hw : SymWf (E.st h 0) := h0 ▸ symWf_init E.T h
    have hv : VarsInv h (E.st h 0) := h0 ▸ varsInv_init E.T h
    exact ⟨hw, hv, step 0 hw hv⟩
  | succ k ih =>
    have s := ih.2.2
    exact ⟨s.wf, s.vars, step (k + 1) s.wf s.vars⟩

theorem evs_mono {k k' : Nat} (hk : k ≤ k') : (E.st h k).evs <+: (E.st h k').evs ∧ (E.st h k).ctl <+: (E.st h k').ctl := by
  induction k' with
  | zero => have : k = 0 := by omega
            subst this; exact ⟨List.prefix_refl _, List.prefix_refl _⟩
  | succ k' ih =>
    rcases Nat.lt_or_ge k (k' + 1) with h1 | h1
    · have ih := ih (by omega)
      have s := (run_inv hc hf hh k').2.2
      obtain ⟨new, he, _⟩ := s.new
      exact ⟨ih.1.trans (he ▸ List.prefix_append _ _), ih.2.trans s.ctl⟩
    · have : k = k' + 1 := by omega
      subst this; exact ⟨List.prefix_refl _, List.prefix_refl _⟩

theorem len_mono {k k' : Nat} (hk : k ≤ k') : (E.st h k).evs.length ≤ (E.st h k').evs.length :=
  (evs_mono hc hf hh hk).1.length_le

theorem get_mono {k k' i : Nat} (hk : k ≤ k') (hi : i < (E.st h k).evs.length) :
    (E.st h k').evs[i]? = (E.st h k).evs[i]? := by
  obtain ⟨t, ht⟩ := (evs_mono hc hf hh hk).1
  rw [← ht, List.getElem?_append_left hi]

/-- `E.sev` is the event of any state that has it. -/
theorem sev_eq {k i : Nat} (hi : i < (E.st h k).evs.length) : (E.st h k).evs[i]? = some (E.sev (h, i)) := by
  have hhas : E.has (h, i) := ⟨hh, k, hi⟩
  unfold IExec.sev
  rw [dif_pos hhas]
  have h0 : i < (E.st h (Classical.choose hhas.2)).evs.length := Classical.choose_spec hhas.2
  show (E.st h k).evs[i]? = some ((E.st h (Classical.choose hhas.2)).evs[i]'h0)
  rw [← List.getElem?_eq_getElem h0]
  rcases Nat.le_total k (Classical.choose hhas.2) with hk | hk
  · exact (get_mono hc hf hh hk hi).symm
  · exact get_mono hc hf hh hk h0

/-- Every event is emitted by one step. -/
theorem emitAt {i : Nat} (hi : E.has (h, i)) :
    ∃ k, (E.st h k).evs.length ≤ i ∧ i < (E.st h (k + 1)).evs.length := by
  obtain ⟨_, k0, hk0⟩ := hi
  have h0 : (E.st h 0).evs.length = 0 := by rw [(hc h hh).1]; rfl
  have : ∀ n, i < (E.st h n).evs.length → ∃ k, (E.st h k).evs.length ≤ i ∧ i < (E.st h (k + 1)).evs.length := by
    intro n
    induction n with
    | zero => intro h1; omega
    | succ n ih =>
      intro h1
      rcases Nat.lt_or_ge i (E.st h n).evs.length with h2 | h2
      · exact ih h2
      · exact ⟨n, h2, h1⟩
  exact this k0 hk0

/-- The facts of the step that emits event `i`. -/
theorem emit_facts {i : Nat} (hi : E.has (h, i)) :
    ∃ k, (E.st h k).evs.length ≤ i ∧ i < (E.st h (k + 1)).evs.length ∧
      (∀ d ∈ (E.sev (h, i)).sk.cdep, d ∈ (E.st h k).ctl) ∧ FragEv (E.sev (h, i)) ∧
      ((E.sev (h, i)).sk.kind.isMem = true → (E.st h (k + 1)).evs.length = i + 1 ∧
        (E.st h (k + 1)).ctl = (E.st h k).ctl ∧ (E.st h (k + 1)).conds = (E.st h k).conds ∧
        (E.sev (h, i)).sk.cdep = (E.st h k).ctl) := by
  obtain ⟨k, hk1, hk2⟩ := emitAt hc hf hh hi
  have s := (run_inv hc hf hh k).2.2
  obtain ⟨new, he, hn⟩ := s.new
  have hget := sev_eq hc hf hh hk2
  rw [he, List.getElem?_append_right hk1] at hget
  have hmem : E.sev (h, i) ∈ new := List.mem_of_getElem? hget
  obtain ⟨n1, n2, n3⟩ := hn _ hmem
  refine ⟨k, hk1, hk2, n1, n2, fun hm => ?_⟩
  obtain ⟨m1, m2, m3, m4⟩ := n3 hm
  refine ⟨?_, m2, m3, m4⟩
  rw [he, m1, List.length_append, List.length_singleton]
  rw [m1] at hget
  have : i - (E.st h k).evs.length < 1 := (List.getElem?_eq_some_iff.1 hget).1
  omega

theorem fragEv {i : Nat} (hi : E.has (h, i)) : FragEv (E.sev (h, i)) :=
  (emit_facts hc hf hh hi).choose_spec.2.2.2.1

theorem has_wf {i : Nat} (hi : E.has (h, i)) :
    ∃ k, (E.st h k).evs[i]? = some (E.sev (h, i)) ∧ SymWf (E.st h k) ∧ VarsInv h (E.st h k) := by
  obtain ⟨_, k, hk⟩ := hi
  exact ⟨k, sev_eq hc hf hh hk, (run_inv hc hf hh k).1, (run_inv hc hf hh k).2.1⟩

theorem has_of_lt {i j : Nat} (hj : E.has (h, j)) (hij : i ≤ j) : E.has (h, i) :=
  ⟨hh, hj.2.choose, by have := hj.2.choose_spec; simp only at this ⊢; omega⟩

theorem has_two {i j : Nat} (hi : E.has (h, i)) (hj : E.has (h, j)) :
    ∃ k, (E.st h k).evs[i]? = some (E.sev (h, i)) ∧ (E.st h k).evs[j]? = some (E.sev (h, j)) ∧
      SymWf (E.st h k) ∧ VarsInv h (E.st h k) := by
  rcases Nat.le_total i j with hij | hij
  · obtain ⟨_, k, hk⟩ := hj
    exact ⟨k, sev_eq hc hf hh (by simp only at hk; omega), sev_eq hc hf hh hk, (run_inv hc hf hh k).1,
      (run_inv hc hf hh k).2.1⟩
  · obtain ⟨_, k, hk⟩ := hi
    exact ⟨k, sev_eq hc hf hh hk, sev_eq hc hf hh (by simp only at hk; omega), (run_inv hc hf hh k).1,
      (run_inv hc hf hh k).2.1⟩

/-- Program order is index order (`poS` by `ii`, SymWf). -/
theorem po_idx {i j : Nat} (hi : E.has (h, i)) (hj : E.has (h, j)) (hpo : poS E.sk (h, i) (h, j) = true) : i < j := by
  obtain ⟨k, h1, h2, hw, _⟩ := has_two hc hf hh hi hj
  simp only [poS, Bool.and_eq_true, beq_self_eq_true, decide_eq_true_eq, true_and] at hpo
  change (E.sev (h, i)).sk.ii < (E.sev (h, j)).sk.ii at hpo
  rcases Nat.lt_or_ge i j with hij | hij
  · exact hij
  · exfalso
    rcases Nat.eq_or_lt_of_le hij with hij | hij
    · subst hij; omega
    · have := (hw.iiMono j i _ _ hij h2 h1).1; omega

theorem idx_po {i j : Nat} (hj : E.has (h, j)) (hij : i < j) (hm : (E.sk (h, i)).kind.isMem = true) :
    poS E.sk (h, i) (h, j) = true := by
  have hi := has_of_lt hc hf hh hj (Nat.le_of_lt hij)
  obtain ⟨k, h1, h2, hw, _⟩ := has_two hc hf hh hi hj
  have := (hw.iiMono i j _ _ hij h1 h2).2 hm
  simp only [poS, Bool.and_eq_true, beq_self_eq_true, decide_eq_true_eq, true_and]
  exact this

/-- Every dependency of an event is an earlier memory operation of its hart. -/
theorem deps_mem {i d : Nat} (hi : E.has (h, i)) (hd : depsOf (E.sk (h, i)) d) : d < i ∧ E.isMem (h, d) := by
  obtain ⟨k, h1, hw, _⟩ := has_wf hc hf hh hi
  obtain ⟨hlt, se, hse, hm⟩ := hw.deps i _ h1 d hd
  have hdl := (List.getElem?_eq_some_iff.1 hse).1
  have := sev_eq hc hf hh hdl
  rw [hse] at this; cases this
  exact ⟨hlt, ⟨hh, k, hdl⟩, hm⟩

/-- A later memory operation's control dependencies contain an earlier event's. -/
theorem cdep_mono {i j d : Nat} (hj : E.has (h, j)) (hij : i < j) (hm : (E.sk (h, j)).kind.isMem = true)
    (hd : d ∈ (E.sk (h, i)).cdep) : d ∈ (E.sk (h, j)).cdep := by
  have hi := has_of_lt hc hf hh hj (Nat.le_of_lt hij)
  obtain ⟨ki, a1, a2, a3, _⟩ := emit_facts hc hf hh hi
  obtain ⟨kj, b1, b2, _, _, b5⟩ := emit_facts hc hf hh hj
  have hle : ki ≤ kj := by
    rcases Nat.lt_or_ge kj ki with h1 | h1
    · have := len_mono hc hf hh (show kj + 1 ≤ ki by omega); omega
    · exact h1
  have hc' := (evs_mono hc hf hh hle).2
  change d ∈ (E.sev (h, j)).sk.cdep
  rw [(b5 hm).2.2.2]
  exact hc'.subset (a3 d hd)

theorem addr_vars {i : Nat} (hi : E.has (h, i)) {x : EvId} (hx : x ∈ (E.sev (h, i)).addr.vars) :
    x.1 = h ∧ x.2 ∈ (E.sk (h, i)).adep := by
  obtain ⟨k, h1, _, hv⟩ := has_wf hc hf hh hi
  exact (hv.evs _ (List.mem_of_getElem? h1)).1 x hx

theorem wval_vars {i : Nat} (hi : E.has (h, i)) {x : EvId} (hx : x ∈ (E.sev (h, i)).wval.vars) :
    x.1 = h ∧ x.2 ∈ (E.sk (h, i)).ddep := by
  obtain ⟨k, h1, _, hv⟩ := has_wf hc hf hh hi
  exact (hv.evs _ (List.mem_of_getElem? h1)).2 x hx

/-- THE CUT after a memory operation: the state right after it has exactly its events up to it, and its path
conditions' variables are among its control dependencies. -/
theorem cut_conds {i : Nat} (hi : E.has (h, i)) (hm : (E.sk (h, i)).kind.isMem = true) :
    ∃ k, (E.st h k).evs.length = i + 1 ∧
      ∀ c ∈ (E.st h k).conds, ∀ x ∈ c.2.1.vars ++ c.2.2.1.vars, x.1 = h ∧ x.2 ∈ (E.sk (h, i)).cdep := by
  obtain ⟨k, _, _, _, _, b5⟩ := emit_facts hc hf hh hi
  obtain ⟨b1, b2, b3, b4⟩ := b5 hm
  refine ⟨k + 1, b1, fun c hcc x hx => ?_⟩
  have hv := (run_inv hc hf hh (k + 1)).2.1
  have := hv.conds c hcc x hx
  rw [b2] at this
  change x.1 = h ∧ x.2 ∈ (E.sev (h, i)).sk.cdep
  rw [b4]; exact this

theorem reach (k : Nat) : LReach (E.T.prog h) h (E.T.init h) (E.st h k) := by
  induction k with
  | zero => rw [(hc h hh).1]; exact .refl
  | succ k ih => exact .step ih ((hc h hh).2 k)

end run

end Weak.Prom.Pfx
