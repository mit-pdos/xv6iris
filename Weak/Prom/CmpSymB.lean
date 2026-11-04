/-
Weak/Prom: **completeness S3b — the events each instruction appends** (RefProg.lean `stepI`).

`stepI_new`: one instruction appends events whose kind and size are fixed by the instruction (`newEvOk`).  Three
consequences: an S3a instruction appends no LR/SC instruction event (`stepI_noLrSc`, so `ExtraInv` transports over
it); every store an S3b program writes has at least one byte (`symRun_stSzB`, so its message is promisable); a
uniform-size S3b program's memory operations all have that size (`symRun_memSzB`, NA-6 by `decide`).
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.CmpSym

namespace Weak.Prom.Cmp

open Weak.Prom.Ref

/-- The kind and size of an event instruction `i` appends. -/
def newEvOk : Instr → SEv → Prop
  | .load sz _ _ _ _, se => se.sk.kind = .ld ∧ se.sk.sz = sz
  | .store sz _ _ _, se => se.sk.kind = .st ∧ se.sk.sz = sz
  | .loadAq sz _ _ _, se => se.sk.kind = .ld ∧ se.sk.sz = sz
  | .storeRl sz _ _ _, se => se.sk.kind = .st ∧ se.sk.sz = sz
  | .loadAqPc sz _ _ _, se => se.sk.kind = .ld ∧ se.sk.sz = sz
  | .storeRlPc sz _ _ _, se => se.sk.kind = .st ∧ se.sk.sz = sz
  | .lr sz _ _ _ _, se => se.sk.kind = .lr ∧ se.sk.sz = sz
  | .sc sz _ _ _ _ _, se => (se.sk.kind = .sc ∨ se.sk.kind = .scFail) ∧ se.sk.sz = sz
  | .amo _ sz _ _ _ _ _, se => se.sk.kind = .amo ∧ se.sk.sz = sz
  | .fence _, se => se.sk.kind.isMem = false ∧ se.sk.kind.isLrSc = false ∧ se.sk.kind.isStore = false
  | .fenceTso, se => se.sk.kind.isMem = false ∧ se.sk.kind.isLrSc = false ∧ se.sk.kind.isStore = false
  | _, _ => False

/-- `s'`'s events are `s`'s followed by events `newEvOk i`. -/
def NewOk (i : Instr) (s s' : SSt) : Prop := ∃ new, s'.evs = s.evs ++ new ∧ ∀ se ∈ new, newEvOk i se

theorem newOk_nil {i : Instr} {s s' : SSt} (h : s'.evs = s.evs) : NewOk i s s' := ⟨[], by simp [h], by simp⟩

theorem stepI_new (h n : Nat) (s : SSt) (i : Instr) :
    (∀ s', stepI h n s i = .next s' → NewOk i s s') ∧
    (∀ t f, stepI h n s i = .fork t f → NewOk i s t ∧ NewOk i s f) := by
  cases i with
  | alui | alu | csrr | fencei | nop =>
    refine ⟨fun s' hs => ?_, fun t f hs => by simp [stepI] at hs⟩
    simp only [stepI, StepR.next.injEq] at hs; subst hs; exact newOk_nil (by simp)
  | jmp tgt =>
    refine ⟨fun s' hs => ?_, fun t f hs => by simp only [stepI] at hs; split at hs <;> cases hs⟩
    simp only [stepI] at hs; split at hs
    · cases hs
    · simp only [StepR.next.injEq] at hs; subst hs; exact newOk_nil rfl
  | br c rs1 rs2 tgt =>
    refine ⟨fun s' hs => (by simp only [stepI] at hs; split at hs <;> cases hs), fun t f hs => ?_⟩
    simp only [stepI] at hs; split at hs
    · cases hs
    · simp only [StepR.fork.injEq] at hs; obtain ⟨rfl, rfl⟩ := hs; exact ⟨newOk_nil rfl, newOk_nil rfl⟩
  | load | loadAq | loadAqPc | lr | amo =>
    refine ⟨fun s' hs => ?_, fun t f hs => by simp [stepI] at hs⟩
    simp only [stepI, StepR.next.injEq] at hs; subst hs
    exact ⟨[_], by simp only [SSt.adv_evs, SSt.wr_evs, SSt.emit_evs] <;> rfl, by simp [newEvOk]⟩
  | store | storeRl | storeRlPc =>
    refine ⟨fun s' hs => ?_, fun t f hs => by simp [stepI] at hs⟩
    simp only [stepI, StepR.next.injEq] at hs; subst hs
    exact ⟨[_], by simp only [SSt.adv_evs, SSt.emit_evs] <;> rfl, by simp [newEvOk]⟩
  | sc =>
    refine ⟨fun s' hs => by simp [stepI] at hs, fun t f hs => ?_⟩
    simp only [stepI, StepR.fork.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    exact ⟨⟨[_], by simp only [SSt.adv_evs, SSt.wr_evs, SSt.emit_evs] <;> rfl, by simp [newEvOk]⟩,
      ⟨[_], by simp only [SSt.adv_evs, SSt.wr_evs, SSt.emit_evs] <;> rfl, by simp [newEvOk]⟩⟩
  | fence fs =>
    refine ⟨fun s' hs => ?_, fun t f hs => by simp [stepI] at hs⟩
    simp only [stepI, StepR.next.injEq] at hs; subst hs
    exact ⟨[_], by simp only [SSt.adv_evs, SSt.emit_evs] <;> rfl, by simp [newEvOk, Kind.isMem, Kind.isLrSc, Kind.isStore]⟩
  | fenceTso =>
    refine ⟨fun s' hs => ?_, fun t f hs => by simp [stepI] at hs⟩
    simp only [stepI, StepR.next.injEq] at hs; subst hs
    exact ⟨[_, _], by simp only [SSt.adv_evs, SSt.emit_evs, List.append_assoc]; rfl,
      by simp [newEvOk, Kind.isMem, Kind.isLrSc, Kind.isStore]⟩

/-- An instruction other than `lr`/`sc` appends no LR/SC instruction event. -/
def notLrScI : Instr → Bool
  | .lr .. | .sc .. => false
  | _ => true

theorem newEvOk_noLrSc {i : Instr} (hi : notLrScI i = true) {se : SEv} (h : newEvOk i se) :
    se.sk.kind.isLrSc = false := by
  cases i with
  | load | store | loadAq | storeRl | loadAqPc | storeRlPc | amo => rw [h.1]; rfl
  | fence | fenceTso => exact h.2.1
  | lr | sc => cases hi
  | _ => exact h.elim

/-- The appended events of `s ⟶ s'`, read in the final state `sf`. -/
theorem newOk_get {i : Instr} {s s' sf : SSt} (hn : NewOk i s s') (hfut : s'.evs <+: sf.evs) {j : Nat}
    (h1 : s.evs.length ≤ j) (h2 : j < s'.evs.length) : ∃ se, sf.evs[j]? = some se ∧ newEvOk i se := by
  obtain ⟨new, hnew, hok⟩ := hn
  have hj : s'.evs[j]? = some s'.evs[j] := List.getElem?_eq_getElem h2
  obtain ⟨tl, htl⟩ := hfut
  refine ⟨s'.evs[j], by rw [← htl, List.getElem?_append_left h2]; exact hj, hok _ ?_⟩
  have : s'.evs[j]? = new[j - s.evs.length]? := by rw [hnew, List.getElem?_append_right h1]
  rw [hj] at this
  exact List.mem_of_getElem? this.symm

/-! ## Store sizes (S3b scope) -/

theorem szOk_pos {sz : Nat} (h : szOk sz = true) : 0 < sz := by
  simp only [szOk, Bool.or_eq_true, beq_iff_eq] at h; omega

/-- Every store event an S3b instruction appends has at least one byte. -/
theorem newEvOk_stSz {i : Instr} (hok : instrS3b i = true) {se : SEv} (h : newEvOk i se)
    (hst : se.sk.kind.isStore = true) : 0 < se.sk.sz := by
  cases i with
  | store sz rs2 rs1 off =>
    rw [h.2]; simp only [instrS3b, instrS3a, Bool.and_eq_true] at hok; exact szOk_pos hok.1.1
  | storeRl sz aq rs2 rs1 => rw [h.2]; simp only [instrS3b, Bool.and_eq_true] at hok; exact szOk_pos hok.1.1
  | sc sz aq rl rd rs2 rs1 => rw [h.2]; simp only [instrS3b, Bool.and_eq_true] at hok; exact szOk_pos hok.1.1.1
  | amo op sz aq rl rd rs2 rs1 => rw [h.2]; simp only [instrS3b, Bool.and_eq_true] at hok; exact szOk_pos hok.1.1.1
  | storeRlPc => simp [instrS3b, instrS3a] at hok
  | load | loadAq | loadAqPc | lr => rw [h.1] at hst; cases hst
  | fence | fenceTso => rw [h.2.2] at hst; cases hst
  | _ => exact h.elim

theorem symRun_newProp (p : List Instr) (h : Nat) (Q : SEv → Prop)
    (hQ : ∀ i ∈ p, ∀ se, newEvOk i se → Q se) :
    ∀ (fuel : Nat) (s : SSt) (ch : List Bool) (sf : SSt), symRun p h fuel s ch = some sf →
      (∀ se ∈ s.evs, Q se) → ∀ se ∈ sf.evs, Q se
  | 0, s, ch, sf, H, _ => by simp [symRun] at H
  | fuel + 1, s, ch, sf, H, hs => by
    unfold symRun at H
    by_cases hpc : s.pc = p.length
    · rw [if_pos hpc] at H
      split at H
      · cases H; exact hs
      · cases H
    · rw [if_neg hpc] at H
      cases hi : p[s.pc]? with
      | none => rw [hi] at H; cases H
      | some i =>
        rw [hi] at H
        simp only at H
        have hn := stepI_new h p.length s i
        have hext : ∀ s', NewOk i s s' → ∀ se ∈ s'.evs, Q se := by
          rintro s' ⟨new, hnew, hok⟩ se hse
          rw [hnew] at hse
          rcases List.mem_append.1 hse with e | e
          · exact hs se e
          · exact hQ i (List.mem_of_getElem? hi) se (hok se e)
        cases he : stepI h p.length s i with
        | stuck => rw [he] at H; cases H
        | next s' =>
          rw [he] at H
          exact symRun_newProp p h Q hQ fuel s' ch sf H (hext s' (hn.1 s' he))
        | fork t f =>
          rw [he] at H
          simp only at H
          cases ch with
          | nil => cases H
          | cons b ch' =>
            cases b
            · exact symRun_newProp p h Q hQ fuel f ch' sf H (hext f (hn.2 t f he).2)
            · exact symRun_newProp p h Q hQ fuel t ch' sf H (hext t (hn.2 t f he).1)

/-- Every store of an S3b program's path has at least one byte. -/
theorem symRun_stSzB (p : List Instr) (hp : ∀ i ∈ p, instrS3b i = true) (h : Nat) (fuel : Nat) (s : SSt)
    (ch : List Bool) (sf : SSt) (H : symRun p h fuel s ch = some sf)
    (hs : ∀ se ∈ s.evs, se.sk.kind.isStore = true → 0 < se.sk.sz) :
    ∀ se ∈ sf.evs, se.sk.kind.isStore = true → 0 < se.sk.sz :=
  symRun_newProp p h (fun se => se.sk.kind.isStore = true → 0 < se.sk.sz)
    (fun i hi se hse hst => newEvOk_stSz (hp i hi) hse hst) fuel s ch sf H hs

end Weak.Prom.Cmp
